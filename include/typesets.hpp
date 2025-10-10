/* Copyright Victor Bogado da Silva Lins 2025.
 *
 * Do not copy or distribute this without prior authorization.
 */

#ifndef INCLUDED_TYPECOLLECTIONS_HPP
#define INCLUDED_TYPECOLLECTIONS_HPP

#include <concepts>
#include <memory>
#include <tuple>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

namespace vb::types {

template<typename T, typename... OTHERs>
concept is_one_of = (std::same_as<OTHERs, T> || ...);

template<typename T, typename... OTHERs>
concept is_none_of = !is_one_of<T, OTHERs...>;

template<typename T>
concept is_tuple = std::same_as<std::tuple<>, T> ||
                   (std::integral<decltype(std::tuple_size_v<T>)> && requires { typename std::tuple_element_t<0, T>; });

static_assert(is_tuple<std::tuple<>>);
static_assert(is_tuple<std::tuple<char>>);
static_assert(!is_tuple<std::variant<char>>);

template<typename T>
concept is_variant = requires {
    { std::variant_size_v<T> } -> std::unsigned_integral;
    typename std::variant_alternative<0, T>;
};

template<typename... TYPEs>
struct type_collection;

template<typename T>
concept is_type_collection = (std::same_as<type_collection<>, T> ||
    (
         T::cardinality > 0
         && T::template belongs<typename T::top_type>
    )) &&
    std::integral<std::remove_cvref_t<decltype(T::template count_of<char>)>> &&
    std::same_as<std::remove_cvref_t<decltype(T::template belongs<char>)>, bool> &&
    std::same_as<std::remove_cvref_t<decltype(T::is_set)>, bool>;

template<typename T>
concept is_element_or_void = !is_type_collection<T>;

template<typename T>
concept is_element_type = is_element_or_void<T> && !std::same_as<void, std::remove_cvref_t<T>>;

static_assert(is_element_type<char>);
static_assert(is_element_type<int>);

template<>
struct type_collection<>
{
    using top_type = void;
    using tail_collection = type_collection<>;

    static constexpr auto cardinality = 0z;
    static constexpr auto empty       = true;

    using as_tuple_type = std::tuple<>;

    template<std::size_t N>
    using element = void;

    using index_set = std::make_index_sequence<0>;

    template<typename OTHER>
    static constexpr std::size_t count_of = 0;

    template<typename OTHER>
    static constexpr bool belongs = false;

    static constexpr bool is_set = true;

    template<is_type_collection OTHER>
    static constexpr bool same_as_collection = std::same_as<OTHER, type_collection<>>;

    template<is_type_collection OTHER>
    static constexpr bool contains_collection = same_as_collection<OTHER>;

    template<is_element_type... OTHERs>
    static constexpr bool same_as = sizeof...(OTHERs) == 0;

    template<is_element_type... OTHERs>
    static constexpr bool contains = same_as<OTHERs...>;

    template<is_type_collection OTHER>
    using union_with_collection = OTHER;

    template<is_element_type... OTHERs>
    using union_with = union_with_collection<type_collection<OTHERs...>>;

    template<is_element_type... OTHERs>
    using intersection_with = type_collection<>;

    template<is_type_collection OTHER>
    using intersection_with_collection = type_collection<>;

    template<is_element_type... OTHERs>
    using difference_with = type_collection<>;

    template<is_type_collection OTHER>
    using difference_with_collection = type_collection<>;
};

template<is_element_type HEAD, is_element_type... TYPEs>
struct type_collection<HEAD, TYPEs...>
{
    using top_type = HEAD;
    using tail_collection = type_collection<TYPEs...>;

    static constexpr auto cardinality = sizeof...(TYPEs) + 1;
    static constexpr auto empty       = false;

    using as_tuple_type   = std::tuple<HEAD, TYPEs...>;
    using as_variant_type = std::variant<HEAD, TYPEs...>;

    template<template<typename, typename> typename COLLECTION, typename ALLOCATOR = std::allocator<as_variant_type>>
    using as_variant_collection = COLLECTION<as_variant_type, ALLOCATOR>;

    template<template<typename, typename> typename COLLECTION, typename ALLOCATOR = std::allocator<as_tuple_type>>
    using as_tuple_collection = COLLECTION<as_tuple_type, ALLOCATOR>;

    static constexpr auto index_set = std::make_index_sequence<cardinality>();

    template<std::size_t N>
    using element = std::conditional_t<N == 0, HEAD, typename tail_collection:: template element<N - 1>>;

    template<is_element_or_void OTHER>
    static constexpr auto count_of = std::same_as<void, OTHER> ? 0 : ((std::same_as<HEAD, OTHER> ? 1 : 0) + ((std::same_as<OTHER, TYPEs>?1:0) + ... + 0));

    template<is_element_or_void OTHER>
    static constexpr auto belongs = std::same_as<void, OTHER> ? false : count_of<OTHER> > 0;

    template<is_element_type OTHER>
    using append = type_collection<HEAD, TYPEs..., OTHER>;

    static constexpr bool is_set = tail_collection::is_set && !tail_collection::template belongs<top_type>;

    template<is_type_collection OTHER>
    static constexpr bool same_as_collection = []<auto... Ns>(std::index_sequence<Ns...>) {
        return cardinality == OTHER::cardinality && ((count_of<element<Ns>> == OTHER::template count_of<element<Ns>>) && ...);
    }(index_set);

    template<is_type_collection OTHER>
    static constexpr bool contains_collection = []<auto... Ns>(std::index_sequence<Ns...>) {
        return cardinality == OTHER::cardinality && ((OTHER::template count_of<typename OTHER::template element<Ns>> >= count_of<typename OTHER::template element<Ns>>) && ...);
    }(OTHER::index_set);

    template<is_element_type... OTHERs>
    static constexpr bool same_as = same_as<type_collection<OTHERs...>>;

    template<is_element_type... OTHERs>
    static constexpr bool contains = contains_collection<type_collection<OTHERs...>>;

    template<is_type_collection COLLECTION_B>
    static constexpr bool is_subset =
        COLLECTION_B::cardinality <= cardinality && []<auto... Ns>(std::index_sequence<Ns...>) {
            return (COLLECTION_B::template belongs<element<Ns>> && ... && true);
        }(index_set);

    template<is_element_or_void OTHER>
    using add_element = std::conditional_t<!is_element_type<OTHER> || belongs<OTHER>, type_collection, type_collection<HEAD, TYPEs..., OTHER>>;

    template<is_type_collection OTHER>
        using union_with_collection = decltype([]<typename SELF, std::size_t N, std::size_t... Ns, is_element_type... OTHER_TYPEs>(this const SELF& self, std::index_sequence<N, Ns...>, OTHER_TYPEs*... ts) {
            using current = OTHER::template element<N>;
            static constexpr auto last = sizeof...(Ns) == 0;
            if constexpr (last) {
                if constexpr (belongs<current>) {
                    return type_collection<HEAD, TYPEs..., OTHER_TYPEs...>{};
                } else {
                    return type_collection<HEAD, TYPEs..., OTHER_TYPEs..., current>{};
                }
            } else if constexpr (belongs<current>) {
                return self(std::index_sequence<Ns...>(), ts..., static_cast<current *>(nullptr));
            } else {
                return self(std::index_sequence<Ns...>(), ts...);
            }
        }(OTHER::index_set));

    template<is_element_type ... OTHERs>
    using union_with = union_with_collection<type_collection<OTHERs...>>;

    template <is_type_collection OTHER>
        using intersection_with_collection = decltype([]<typename SELF, is_type_collection OTHER_T, is_element_type... ELEMENTs>(this const SELF& self, OTHER_T, ELEMENTs*... elements) {
            using current = OTHER_T::top_type;
            using NEXT_OTHER = OTHER_T::tail_collection;
            static constexpr auto belong = OTHER::template belongs<current>;
            static constexpr auto last = OTHER_T::cardinality == 1;
            if constexpr (last) {
                if constexpr (belong) {
                    return type_collection<ELEMENTs..., current>{};
                } else {
                    return type_collection<ELEMENTs...>{};
                }
            } else if constexpr (belong) {
                return self(NEXT_OTHER{}, elements..., static_cast<current*>(nullptr));
            } else {
                return self(NEXT_OTHER{}, elements...);
            }
        }(OTHER{}));

    template <is_element_type ... OTHERs>
    using intersection_with = intersection_with_collection<type_collection<OTHERs...>>;

    template <is_type_collection OTHER>
        using difference_with_collection = decltype([]<typename SELF, is_element_type... ELEMENTs, auto N, auto... Ns>(this const SELF& self, std::index_sequence<N, Ns...>, ELEMENTs*... elements) {
            using current = element<N>;
            static constexpr auto NEXT_INDEXs = std::index_sequence<Ns...>{};
            static constexpr auto last = sizeof...(Ns) == 0;
            if constexpr (last) {
                if constexpr (OTHER::template belongs<current>) {
                    return type_collection<ELEMENTs...>{};
                } else {
                    return type_collection<ELEMENTs..., current>{};
                }
            } else if constexpr (OTHER::template belongs<current>) {
                return self(NEXT_INDEXs, elements...);
            } else {
                return self(NEXT_INDEXs, elements..., static_cast<current*>(nullptr));
            }
        }(index_set));

    template <is_element_type ... OTHERs>
    using difference_with = difference_with_collection<type_collection<OTHERs...>>;
};

template<typename TYPE_COLLECTION, typename... TYPEs>
concept same_collection = std::same_as<type_collection<TYPEs...>, TYPE_COLLECTION>;

template<typename TYPE_COLLECTION_A, typename TYPE_COLLECTION_B>
concept is_sub_collection = is_type_collection<TYPE_COLLECTION_A> && is_type_collection<TYPE_COLLECTION_B> &&
                            TYPE_COLLECTION_A::template is_subset<TYPE_COLLECTION_B>;

template<is_tuple TUPLE>
using collection_from_tuple = std::remove_cvref_t<decltype([]<auto... Ns>(std::index_sequence<Ns...>) {
    return std::declval<type_collection<std::tuple_element_t<Ns, TUPLE>...>>();
}(std::make_index_sequence<std::tuple_size_v<TUPLE>>()))>;

template<is_variant VARIANT>
using collection_from_variant = std::conditional_t<
    std::same_as<VARIANT, std::false_type>,
    type_collection<>,
    std::remove_cvref_t<decltype([]<auto... Ns>(std::index_sequence<Ns...>) {
        return std::declval<type_collection<std::variant_alternative_t<Ns, VARIANT>...>>();
    }(std::make_index_sequence<std::variant_size_v<VARIANT>>()))>>;

template<typename T>
using collection_from = std::conditional_t<
    is_tuple<T>,
    collection_from_tuple<T>,
    std::conditional_t<
        is_variant<T>,
        collection_from_variant<T>,
        std::conditional_t<std::same_as<T, void>, type_collection<>, type_collection<T>>>>;

namespace static_test {
using test_1 = type_collection<int, char>;
using test_2 = type_collection<char, int>;

static_assert(test_1::cardinality == 2);
static_assert(std::same_as<type_collection<int, char>::template union_with<unsigned>, type_collection<int, char, unsigned>>);
static_assert(type_collection<int, char>::template union_with<unsigned>::cardinality == 3);
static_assert(type_collection<int, char>::template union_with<int>::cardinality == 2);
static_assert(std::same_as<type_collection<int, char>::template intersection_with<int>, type_collection<int>>);
static_assert(std::same_as<type_collection<int, char, char*, int*>::template intersection_with<int, int*>, type_collection<int, int*>>);
static_assert(std::same_as<type_collection<int, char>::template difference_with<int>, type_collection<char>>);
static_assert(std::same_as<type_collection<int>::template difference_with<int, char>, type_collection<>>);
static_assert(std::same_as<type_collection<int, char, char*, int*>::template intersection_with<int, int*>, type_collection<int, int*>>);

static_assert(type_collection<int>::is_set);
static_assert(type_collection<std::vector<int>>::is_set);
static_assert(!type_collection<int, char, int>::is_set);
static_assert(type_collection<int, double, char>::cardinality == 3);
static_assert(type_collection<int, double, char>::is_set);
static_assert(type_collection<int, double, char>::count_of<int&> == 0);
static_assert(type_collection<int, double, char>::belongs<char>);
static_assert(type_collection<int, double, char>::belongs<double>);
}

template<typename T>
concept is_type_set = is_type_collection<T> && T::is_set;

template<typename T>
concept tuple_is_set = collection_from_tuple<T>::is_set;

template<typename T>
concept variant_is_set = collection_from_variant<T>::is_set;

}

#endif // INCLUDED_TYPECOLLECTIONS_HPP
