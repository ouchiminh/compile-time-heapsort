#include <iostream>
#include <type_traits>
#include <functional>
#include <utility>
#include <tuple>
#include <array>
#include <chrono>
#include <random>

template<class T, size_t N>
void print(const T(&a)[N])
{
    for (auto&& i : a) {
        std::cout << i << ' ';
    }
    std::cout << '\n';
}

template<class, class = void>
struct has_bool_value_impl : std::false_type {
    template<class ...U>
    static constexpr bool evaluate(U&&...) { return false; }
};
template<class T>
struct has_bool_value_impl<T, std::void_t<decltype((bool)T::value)>> : std::true_type {
    template<class U>
    static constexpr bool evaluate(U&&...) { return T::value; }
};

template<class T>
struct has_bool_value : has_bool_value_impl<T> {};

static_assert(!has_bool_value<int>::value);
static_assert(has_bool_value<std::true_type>::value);

template<class, class = void>
struct is_bool_impl : std::false_type {
    template<class U>
    static constexpr bool evaluate(U&&...) { return false; }
};
template<class T>
struct is_bool_impl<T, std::void_t<decltype(static_cast<bool>(std::declval<T>()))>> : std::true_type {
    static constexpr bool evaluate(T&& v) { return static_cast<bool>(v); }
    static constexpr bool evaluate(const T& v) { return static_cast<bool>(v); }
};
template<class T>
struct is_bool : is_bool_impl<T>{};

static_assert(is_bool<int>::value);
static_assert(is_bool<std::istream>::value);
static_assert(!is_bool<std::pair<int, int>>::value);

template<class, class = void>
struct invocable_impl : std::false_type {
    template<class ...U>
    static constexpr bool evaluate(U&&...) { return false; }
};
template<class T>
struct invocable_impl<T, std::void_t<decltype((bool)std::declval<T&>()())>> : std::true_type {
    static constexpr bool evaluate(T& v) { return (bool)v(); }
    static constexpr bool evaluate(T&& v) { return (bool)v(); }
};
template<class T>
struct invocable : invocable_impl<T> {};

template<class F, class ...Args>
struct function_wrapper {
    std::tuple<Args...> arguments;
    F cp;
    function_wrapper(F f, Args ...args)
        : arguments{std::forward<Args>(args)...}
        , cp(std::forward<decltype(f)>(f))
    {}
    function_wrapper() = default;
    operator const F& () const { return cp; }
    operator F& () { return cp; }
    template<class Func = F, std::enable_if_t<std::is_invocable_v<Func, Args...>>* = nullptr>
    auto operator()() { return std::apply(cp, arguments); }
};

template<class Pred, template<class> class ...Judgment>
constexpr bool predicate(Pred&& pred)
{
    bool result = false;
    return (result | ... | Judgment<Pred>::evaluate(pred));
}

template<class Int>
constexpr Int parent(Int i) noexcept
{
    return (i - 1) / 2;
}

template<class Int>
constexpr Int leftchild(Int i) noexcept
{
    return (i * 2) + 1;
}

template<class Int>
constexpr Int rightchild(Int i) noexcept
{
    return leftchild(i) + 1;
}

// cond(Int, Int) == true : upheap
// cond(Int, Int) == false : do nothing
// or F::value or (bool)cond can be evaluated.
template<class T, size_t N, class F = std::less<T>>
T (&upheap(T(&a)[N], size_t i = N - 1, F&& cond = F{}) noexcept)[N] {
    while (i > 0) {
        auto j = parent(i);
        if (predicate<function_wrapper<F, T, T>,
                invocable, is_bool, has_bool_value>
                (function_wrapper<F, T, T>(cond, a[j], a[i])))
            std::iter_swap(a + i, a + j);
        i = j;
    }
    return a;
}
template<class T, size_t N, class F = std::less<T>>
T (&downheap(T(&a)[N], size_t i = 0, size_t e = N, F&& cond = F{}) noexcept)[N] {
    auto j = leftchild(i);
    while (j < e) {
        if (j + 1 < e &&
            predicate<function_wrapper<F, T, T>,
                invocable, is_bool, has_bool_value>
                (function_wrapper<F, T, T>(cond, a[j], a[j + 1])))
            ++j;
        if (predicate<function_wrapper<F, T, T>,
                invocable, is_bool, has_bool_value>
                (function_wrapper<F, T, T>(cond, a[i], a[j])))
            std::iter_swap(a + i, a + j);
        i = j;
        j = leftchild(i);
    }
    return a;
}

template<class T, size_t N, class F = std::less<T>>
T(&makeheap(T(&a)[N], size_t begin = 0, size_t end = N, F&& cond = F{}) noexcept)[N]
{
    for (auto p = end / 2; p > begin;) {
        downheap(a, --p, end, cond);
    }
    return a;
}

template<class T, size_t N, class F = std::less<T>>
T(&popheap(T(&a)[N], size_t dest, F&& cond = F{})noexcept)[N]
{
    std::iter_swap(a, a+dest);
    return downheap(a, 0, dest, cond);
}

template<class T, size_t N, class F = std::less<T>>
T (&heapsort(T(&a)[N], F&& cmp = F{}) noexcept)[N]
{
    makeheap(a, 0, N, cmp);
    auto i = N;
    while (--i > 0) {
        std::iter_swap(a, a + i);
        downheap(a, 0, i, cmp);
    }
    return a;
}

template<class T, size_t N, class F = std::less<T>>
T(&addheap(T(&a)[N], T nvalue, size_t nidx = N-1, F&& cond = F{}) noexcept)[N]
{
    a[nidx] = nvalue;
    return upheap(a, nidx, cond);
}

template<class Clock, class F, class ...Args>
auto measure(F&& func, Args&& ...args)
-> typename Clock::duration
{
    auto begin = Clock::now();
    func(std::forward<Args>(args)...);
    return Clock::now() - begin;
}

template<size_t N>
auto sort_rnd_impl()
{
    static int a[N];
    std::mt19937 rnd{ std::random_device{}() };
    rnd.discard(N);
    for (auto& i : a) {
        i = rnd();
    }
    return std::make_pair(N, measure<std::chrono::steady_clock>([]() {heapsort(a); }));
}

template<>
auto sort_rnd_impl<0>()
{
    return std::make_pair(0, std::chrono::steady_clock::duration(0));
}

template<size_t ...I>
auto sort_rnd(std::index_sequence<I...>){
    std::vector<std::pair<size_t, std::chrono::steady_clock::duration>> r;
    r.reserve(sizeof...(I));
    (r.push_back(sort_rnd_impl<I>()), ...);
    return r;
}

int main()
{
    int a[] = { 15,31,7,24,5,19,46,2,10,29 };
    //int a[] = { 4, 1, 6, 2, 9, 7, 3, 8 };
    auto r = sort_rnd(std::index_sequence<1, 5, 10, 50, 100, 500, 1000, 5000, 10000, 50000, 100000, 500000, 1000000, 2000000, 3000000, 5000000>{});
    for (auto&& i : r) {
        std::cout << i.first << ',' << i.second.count() / 1'000'000.0 << '\n';
    }
}
