#include <iostream>
#include <type_traits>
#include <functional>
#include <algorithm>
#include <initializer_list>
#include <utility>
#include <array>
#include <tuple>

namespace kadai {

template<class Int, Int ...I>
struct my_integer_sequence {
    static constexpr Int data[sizeof...(I)] = { I... };
    using type = Int;
    static constexpr size_t size() noexcept { return sizeof...(I); }
    template<size_t Idx>
    static constexpr type at() noexcept { return data[Idx]; }
};

}

template<class Int>
constexpr Int parent(Int i) noexcept
{
    return (i + 1) / 2 - 1;
}

template<class Int>
constexpr Int leftchild(Int i) noexcept
{
    return (i + 1) * 2 - 1;
}
template<class Int>
constexpr Int rightchild(Int i) noexcept
{
    return leftchild(i) + 1;
}

// integer_sequenceの末尾に追加する
template<int Value, int ...I>
std::integer_sequence<int, I..., Value> push(std::integer_sequence<int, I...>) noexcept;

// integer_sequenceの先頭から一つ削除する
template<int Value, int ...I>
std::integer_sequence<int, I...> pop(std::integer_sequence<int, Value, I...>) noexcept;

// integer_sequenceのN番目の値を取得する
namespace detail {
template<size_t N, int ...I>
struct at_impl {
    static constexpr int value = 
        (N < sizeof...(I)
        ? kadai::my_integer_sequence<int, I...>::template at<N>()
        : int());
};

}
template<size_t N, int ...I>
constexpr int at(std::integer_sequence<int, I...>) noexcept
{
    return detail::at_impl<N, I...>::value;
}
template<size_t N, class Int,  Int ...I>
constexpr Int at(kadai::my_integer_sequence<Int, I...>) noexcept
{
    return kadai::my_integer_sequence<Int, I...>:: template at<N>();
}

// integer_sequenceのN番目の値をValueにする
namespace detail {
template<size_t C, size_t N, int Value, int ...I>
struct index_value {
    static constexpr int value = at_impl<C, I...>::value;
};
template<size_t N, int Value, int ...I>
struct index_value<N, N, Value, I...> {
    static constexpr int value = Value;
};
template<size_t C, size_t N, int Value, int ...I>
constexpr auto index_value_func(std::integer_sequence<int, I...>)
{
    return index_value<C, N, Value, I...>::value;
}
template<size_t N, int Value, class T, size_t ...Idx>
constexpr auto write_impl(T seq, std::index_sequence<Idx...>)
{
    return std::integer_sequence<int, index_value_func<Idx, N, Value>(seq)...>{};
}
} // namespace detail

template<size_t N, int Value, int ...I>
constexpr auto write(std::integer_sequence<int, I...> seq){
    return detail::write_impl<N, Value>(seq, std::make_index_sequence<sizeof...(I)>{});
}

// integer_sequenceのN番目とM番目の値をswapする
template<size_t N, size_t M, int ...I>
constexpr auto swap(std::integer_sequence<int, I...> seq){
    constexpr auto n = at<N>(seq);
    constexpr auto m = at<M>(seq);
    constexpr auto t1 = write<N, m>(seq);
    return write<M, n>(t1);
}

namespace detail {

template<size_t N, size_t M, bool Cond, int ...I>
struct swap_if_impl {
    using type = std::integer_sequence<int, I...>;
};
template<size_t N, size_t M, int ...I>
struct swap_if_impl<N, M, true, I...> {
    using type = decltype(swap<N, M>(std::integer_sequence<int, I...>{}));
};

template<size_t N, size_t M, bool Cond, int ...I>
constexpr auto swap_if(std::integer_sequence<int, I...>)
{
    return typename swap_if_impl<N, M, Cond, I...>::type{};
}

template<class Comp, size_t N, int ...I>
struct upheap_impl;

template<class Comp, int ...I>
struct upheap_impl<Comp, 0, I...> {
    using type = std::integer_sequence<int, I...>;
    using tmptype = type;
};

template<class Comp, size_t N, int ...I>
struct upheap_impl {
    static constexpr size_t m = parent(N);
    static constexpr std::integer_sequence<int, I...> seq{};
    static constexpr Comp cmp{};
    using tmptype = decltype(detail::swap_if<N, m, cmp(at_impl<m, I...>::value, at_impl<N, I...>::value)>(seq));
    template<int ...I>
    static auto f(std::integer_sequence<int, I...>)
        ->typename upheap_impl<Comp, m, I...>::type;
    using type = decltype(upheap_impl::f(std::declval<tmptype>()));
};
} // namespace detail

template<size_t N, class Comp, int ...I>
constexpr auto upheap(std::integer_sequence<int, I...>){
    // [[contruct]] n > 0
    return typename detail::upheap_impl<Comp, N, I...>::type{};
}

namespace detail {
template<class Comp, bool, size_t N, size_t M = 0, int ...Values>
struct downheap_impl;
template<class Comp, size_t N, size_t M, int ...Values>
struct downheap_impl<Comp, false, N, M, Values...> {
    using type = std::integer_sequence<int, Values...>;
};

template<class Comp, size_t N, size_t M, int ...Values>
struct downheap_impl<Comp, true, N, M, Values...> {
    static constexpr std::integer_sequence<int, Values...> seq{};
    static constexpr Comp cmp{};
    static constexpr size_t lc = leftchild(M); // < N
    static constexpr size_t rc = rightchild(M);
    static constexpr size_t j = (cmp(at<lc>(seq), at<rc>(seq)) && rc < N)
        ? rc : lc;
    static constexpr bool cond = cmp(at<M>(seq), at<j>(seq));
    using tmptype = typename swap_if_impl<j, M, cond, Values...>::type;
    template<int ...K>
    static auto f(std::integer_sequence<int, K...>)
        ->typename downheap_impl<Comp, (leftchild(j) < N), N, j, K...>::type;
    using type = decltype(downheap_impl::f(std::declval<tmptype>()));
};

} // namespace detail

template<class Comp, size_t I, int ...Values>
constexpr auto downheap(std::integer_sequence<int, Values...>)
{
    return typename detail::downheap_impl<Comp, (leftchild(0) < I), I, 0, Values...>::type{};
}

namespace detail {
template<class Comp, size_t N, int ...I>
struct enheap_impl;

template<class Comp, int ...I>
struct enheap_impl<Comp, 0, I...> {
    using type = std::integer_sequence<int, I...>;
    using tmptype = type;
};

template<class Comp, size_t N, int ...I>
struct enheap_impl {
    static constexpr std::integer_sequence<int, I...> seq{};

    using tmptype = decltype(upheap<sizeof...(I) - N, Comp>(seq));
    template<int ...J>
    static constexpr auto f(std::integer_sequence<int, J...>)
        ->typename enheap_impl<Comp, N - 1, J...>::type;
    using type = decltype(enheap_impl::f(std::declval<tmptype>()));
};

template<class Comp, int ...I>
constexpr auto enheap(std::integer_sequence<int, I...>)
{
    return typename enheap_impl<Comp, sizeof...(I), I...>::type{};
}

template<class Comp, size_t N, int ...I>
struct finalize_impl;

template<class Comp, int ...I>
struct finalize_impl<Comp, 0, I...> {
    using type = std::integer_sequence<int, I...>;
};

template<class Comp, size_t N, int ...I>
struct finalize_impl {
    static constexpr std::integer_sequence<int, I...> seq{};
    using tmptype = decltype(downheap<Comp, N>(swap<N, 0>(seq)));

    template<int ...J>
    static auto f(std::integer_sequence<int, J...>)
        ->typename finalize_impl<Comp, N - 1, J...>::type;
    using type = decltype(finalize_impl::f(std::declval<tmptype>()));
};

template<class Comp, int ...I>
constexpr auto finalize(std::integer_sequence<int, I...>)
{
    return typename finalize_impl<Comp, sizeof...(I) - 1, I...>::type{};
}

}

template<class Comp = std::less<>, int ...I>
constexpr auto heapsort(std::integer_sequence<int, I...> seq)
{
    return detail::finalize<Comp>(detail::enheap<Comp>(seq));
}

template<class T>
void print(T&& v)
{
    std::cout << v << ' ';
}

template<int ...I>
void print(std::integer_sequence<int, I...>)
{
    (print(I), ...);
}

/******************************* random *********************************/

#if 1
template<class Int = int, Int State = 1294, Int A = 48271, Int B = 0x1, Int M = (1 << 16) - 1>
class random {
public:
    static constexpr Int value = (A * State ^ B) % M;
    using type = random<Int, value, A, B, M>;
};

template<size_t N>
struct random_seq;

template<>
struct random_seq<0> {
    static constexpr int seed = __LINE__ + (__TIME__[0] << (__TIME__[0] % 16)) ^ __TIME__[1] ^ __TIME__[2];
    using rand = random<int, seed>;
    using type = std::integer_sequence<int, rand::value>;
};

template<size_t N>
struct random_seq {
    static constexpr int value = random_seq<N - 1>::rand::value;
    using rand = random<int, value>;
    using type = decltype(push<rand::value>(typename random_seq<N-1>::type{}));
};
#endif

int main() {
    constexpr typename random_seq<10>::type seq{};
    print(seq);
    //constexpr std::integer_sequence<int, 4, 3, 22, 1,77,  90, 1, 8, 32, 12, 52, 94, 41, 47, 82, 57, 19, 49, 44, 0> seq;
    //print(heaped);
    std::cout << '\n';
    print(heapsort<std::less<>>(seq));
    //std::cout << '\n';
    //print(heapsort<std::greater<>>(seq));
    //std::cout << std::endl;
}
