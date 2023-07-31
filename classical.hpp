#pragma once

#include <functional>
#include <type_traits>


namespace classical {


struct False {
  False() = delete;
};

struct Base {
  Base() = delete;
  Base(False) {}
};

// (A -> B)
template <typename A, typename B> struct Implies {
  using Type = std::function<B(A)>;
  Type func;
  Implies() = delete;
  Implies(False f) : func([f](A) -> B { return f; }) {}
  template <typename T> Implies(T t) : func(t) {}
  B operator()(A a) const { return func(a); }
};

// (A1 -> (A2 -> ... (An-1 -> An)))
template <typename... As> struct LongImpliesImpl;
template <typename... As> using LongImplies = typename LongImpliesImpl<As...>::type;
template <typename A> struct LongImpliesImpl<A> { using type = A; };
template <typename A, typename... As> struct LongImpliesImpl<A, As...> {
  using type = Implies<A, LongImplies<As...>>;
};

// (~A)
template <typename A> using Negation = Implies<A, False>;

// (A1 /\ A2 /\ ... /\ An)
template <typename... As> struct Conjunction {
  using Type = std::tuple<As...>;
  Type tup;
  Conjunction() = delete;
  Conjunction(False f) : tup(As(f)...) {}
  Conjunction(As... as) : tup(as...) {}
  template <size_t N> std::tuple_element_t<N, Type> get() const { return std::get<N>(tup); }
};

// (A1 \/ A2 \/ ... \/ An)
template <typename... As> using Disjunction = Negation<Conjunction<Negation<As>...>>;

// A -> (B -> A)
template <typename A, typename B> using Then1 = LongImplies<A, B, A>;
template <typename A, typename B>
inline const Then1<A, B> then1 = [](A a) { return [a](B b) -> A { return a; }; };

// (A -> (B -> C)) -> ((A -> B) -> (A -> C))
template <typename A, typename B, typename C>
using Then2 = LongImplies<LongImplies<A, B, C>, Implies<A, B>, Implies<A, C>>;
template <typename A, typename B, typename C>
inline const Then2<A, B, C> then =
    [](LongImplies<A, B, C> a2b2c) -> Implies<Implies<A, B>, Implies<A, C>> {
  return [a2b2c](Implies<A, B> a2b) -> Implies<A, C> {
    return [a2b2c, a2b](A a) -> C { return a2b2c(a)(a2b(a)); };
  };
};

// [non-intuitive] ((A -> B) -> A) -> A
template <typename A, typename B> using Peirce = Implies<Implies<Implies<A, B>, A>, A>;
template <typename A, typename B>
inline const Peirce<A, B> peirce = std::function<A(Implies<Implies<A, B>, A>)>();

// (A -> B), A |- B
template <typename A, typename B> inline B modus_ponens(Implies<A, B> a2b, A a) { return a2b(a); }
template <typename A, typename B> inline B modus_ponens(A a, Implies<A, B> a2b) { return a2b(a); }

// (A -> B), ~B |- ~A
template <typename A, typename B>
inline Negation<A> modus_tollens(Implies<A, B> a2b, Negation<B> b) {
  return [a2b, b](A a) -> False { return b(a2b(a)); };
}
template <typename A, typename B>
inline Negation<A> modus_tollens(Negation<B> b, Implies<A, B> a2b) {
  return [a2b, b](A a) -> False { return b(a2b(a)); };
}

// (A -> B), (B -> C) |- (A -> C)
template <typename A, typename B, typename C>
inline Implies<A, C> syllogism(Implies<A, B> a2b, Implies<B, C> b2c) {
  return [a2b, b2c](A a) -> C { return b2c(a2b(a)); };
}
template <typename A, typename B, typename C>
inline Implies<A, C> syllogism(Implies<B, C> b2c, Implies<A, B> a2b) {
  return [a2b, b2c](A a) -> C { return b2c(a2b(a)); };
}

// A, ~A |- B
template <typename A, typename B> inline B explosion(A a, Negation<A> na) { return na(a); }
template <typename A, typename B> inline B explosion(Negation<A> na, A a) { return na(a); }

// [non-intuitive] A |- ~~A
template <typename A> inline A double_negation_elimination(Negation<Negation<A>> nna) {
  return peirce<A, Negation<A>>([nna](LongImplies<A, A, False> aaf) -> A {
    return nna([aaf](A a) -> False { return aaf(a)(a); });
  });
}

// [non-intuitive] |- A \/ ~A
template <typename A> inline Disjunction<A, Negation<A>> exclusive_middle() {
  return [](Conjunction<Negation<A>, Negation<Negation<A>>> na_nna) -> False {
    return na_nna.template get<1>()(na_nna.template get<0>());
  };
};


}  // namespace classical

#define DECLARE_CLASSICAL_ATOMIC_PROP(NAME) \
  struct NAME : ::classical::Base {         \
    using ::classical::Base::Base;          \
  };
