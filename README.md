# prop

propositional logic on cpp

## 从图灵完备说起

简单的说，如果一个由自然数上的部分函数（某些输入不会停机）构成的集合是图灵完备的，当且仅当它满足如下条件：

1. 包含 $ x \mapsto x + 1 $
2. 包含 $ (x_1, \cdots, x_n) \mapsto x_i $
3. 关于复合封闭 $ \exists f, g \implies \exists f \circ g $
4. 关于归纳封闭 $ \exists f(y), g(x, y, z) \implies \exists h , h(0, y) = f(y), h(x + 1, y) = g(x, y, h(x, y)) $
5. 关于循环搜索封闭

目前所有的高级语言都是图灵完备的，同时 C++ 的元编程也是图灵完备的。

图灵完备的基本结论就是，图灵停机问题不能被图灵机判定。但是数理逻辑里逻辑公式的推导验证，其复杂程度是不足图灵完备的，因此是有可能用一个图灵机来验证一个推导过程是否严谨（满足一个公理化的规则）。

就像你不能写一份代码来实现判断所有代码能否停机，但是你能写一份代码判断所有代码能否通过编译（写一个编译器）。

## 类型 TYPE

| 代码 | 逻辑 |
| ---- | ---- |
| 编译 | 推理 |
| 类型 | 命题 |
| 对象 | 证明 |

类似于 Coq 语言，我们希望用 $ a : A $ 来表示类型 $A$ 有实例 $a$ ，等价的转化为代码里的类型 $A$ 有对象 $a$ ，进一步命题 $A$ 有证明 $a$ 。显然我们不能无中生有一个任意命题的证明，对应到代码里，就是声明一个 $A$ 类型的对象 $a$ 。如果我们能很随意的写出代码 ```A a;``` ，那么也就是可以很随意的“证明”一个命题 $A$ 。因此所有在我们 C++ 代码里被视为命题的类型，要删除它的默认无参数构造函数。

```cpp
struct Base {
    Base() = delete;
};

#define DECLARE_CLASSICAL_ATOMIC_PROP(NAME) \
  struct NAME : ::classical::Base {         \
    using ::classical::Base::Base;          \
  };
```

如上，我们在声明原子命题逻辑符号时，可以通过继承 ```Base``` 来解决构造函数。

对于复合命题，最经典的逻辑连接词就是 $\to$ 蕴含。一个巧合就是 $ f : A \to B $ 这个字符串，在类型论里，它表示 $f$ 是一个 $ A \to B $ 的对象，在一般数学里，他表示有个定义域为 $A$ 值域为 $B$ 的函数 $f$ ，在 C++ 语言里的一个等价是 ```B f(A);``` 。我们的目标是：能在 C++ 里定义一个这样的函数，当且仅当它对应了一个 $ A \vdash B $ 的证明。显然如果没有其他任何额外的信息，在我们删除了 ```B``` 类型的默认构造函数后，是无法无中生有出 ```B``` 对象的。但我们还有一个未使用到的信息 $A$ 。例如当 $ A = B $ 时，```A f(A a) { return a; }``` 是一份合法的代码，对应着 $ A \vdash A $ 的证明。当然可以认为这个是废话，但能用简单的代码证明的，必然都是恒真式的形式，也就是“废话”。这里“简单”二字是指，如果某个命题不是恒真式，例如 $ A \to B $ ，这里 $A,B$ 是不同的原子命题符号，还是有“作弊”的方式（后文）写出 ```B f(A) { /* */ }``` 然后得到一个 $ A \vdash B $ 的“证明”。

不过 ```B f(A);``` 准确的说它对应的是 $ A \vdash B $ 或者 $ \vdash A \to B$ ，我们还需要一个确切的能用 C++ 类型描述的 $ A \to B $ 。直觉上它其实就是函数的封装，于是结合模板：

```cpp
template <typename A, typename B> struct Implies {
  using Type = std::function<B(A)>;
  Type func;
  Implies() = delete;
  template <typename T> Implies(T t) : func(t) {}
  B operator()(A a) const { return func(a); }
};
```

这时“作弊”的方式也十分明现了，就是用 ```std::function<B(A)>()``` 这样的一个对象去构造 ```Implies<A, B>``` 对象。这也是无法规避的，即使用 ```std::enable_if``` 之类的删除 ```std::function``` 构造参数，但是无法阻止再封装一层 lambda 。因此可以在解读 C++ 代码证明的时候，类似“人工阅卷的方式”来判断，类似于 ```std::function``` 或者函数指针等代码的出现，都等价于 Coq 语言里的 ```Admitted``` 。

在经典逻辑里，有“矛盾可以推出一切的说法”。同时考虑到命题的否定，不妨在符号系统里引入一个表示矛盾的原子命题 $F$ ，然后对于命题 $P$ ，它的否定就是 $ P \to F $ 。另一方面，对任意 $P$ ，$ F \to P $ 是恒真式，所以对于原子命题符号或者是复合命题，在 C++ 语言里我们都希望任何的类型都能被 $F$ 的对象构造。

```cpp
struct False {
  False() = delete;
};

struct Base {
  Base() = delete;
  Base(False) {}
};

template <typename A, typename B> struct Implies {
  using Type = std::function<B(A)>;
  Type func;
  Implies() = delete;
  Implies(False f) : func([f](A) -> B { return f; }) {}
  template <typename T> Implies(T t) : func(t) {}
  B operator()(A a) const { return func(a); }
};

template <typename A> using Negation = Implies<A, False>;
```

到目前位置，我们已经基本实现了命题逻辑在 C++ 上的基本功能。如下是一个三段论的证明:

```cpp
Implies<A, C> syllogism(Implies<A, B> a2b, Implies<B, C> b2c) {
  return [a2b, b2c] (A a) -> C { return b2c(a2b(a)); };
}
```

对一份 C++ 代码编译，编译通过表示证明没有问题，然后再去人为解读这份代码的内容，得出它到底证明了声明，这是设计思路。

## 经典逻辑

上一节为止，我们只实现了一些基本的证明验证功能，但是我们无法证明出，$ \neg\neg A \to A $ 或 $ ((A \to B) \to A) \to A $ 这些经典命题逻辑下的恒真式。原因是目前为止，我们的能力值达到了直觉逻辑/最小逻辑，没有经典命题逻辑上的完备性，对此我们需要引入新的公理来完备化当前的证明系统。

所谓引入公理，就是提前声明定义一个该公理对应的命题类型的对象。显然如果把命题逻辑上所有的恒真式都加入进来是合法的，且能得到经典命题逻辑的完备性，但是这样有许多赘余操作。

（此处略去证明）如果将皮尔士定律也就是 $ ((A \to B) \to A) \to A $ 当作公理，那么我们的证明系统就进化到经典命题逻辑。

```cpp
template <typename A, typename B> using Peirce = Implies<Implies<Implies<A, B>, A>, A>;
template <typename A, typename B>
Peirce<A, B> peirce = std::function<A(Implies<Implies<A, B>, A>)>();
```

在皮尔士定律下，我们可以给出双重否定消去 $ \neg\neg A \vdash A $ 的证明：

```cpp
template <typename A, typename B> B explosion(Negation<A> na, A a) { return na(a); }

template <typename A> A double_negation_elimination(Negation<Negation<A>> nna) {
  return peirce<A, Negation<A>>([nna](LongImplies<A, A, False> aaf) -> A {
    return explosion<Negation<A>, A>(nna, [aaf](A a) -> False { return aaf(a)(a); });
  });
}
```

### 合取

很直观的操作是，我们可以用 ```std::pair<A, B>``` 来表示 $ A \wedge B $ 对应的类型，因为如果需要构造出一个 ```std::pair``` 对象，就必须要它的每个分量的对象。结合模板和长合取表达式：

```cpp
template <typename... As> struct Conjunction {
  using Type = std::tuple<As...>;
  Type tup;
  Conjunction() = delete;
  Conjunction(False f) : tup(As(f)...) {}
  Conjunction(As... as) : tup(as...) {}
  template <size_t N> std::tuple_element_t<N, Type> get() const { return std::get<N>(tup); }
};
```

### 析取

直觉上，类似于 ```std::variant``` 或者 ```union``` 来定义析取类型。但是实际上，这样的操作在代码层面上给出了 $ A \vee B \vdash A \wedge B $ 的证明，像 ```std::function``` 一样，它其实也“作弊”了。事实上，任何静态类型语言都无法直观的处理析取类型。在经典逻辑里，目前能有的解决办法就是用合取定义析取，即 $ A \vee B := \neg(\neg A \wedge \neg B) $ 。

```cpp
template <typename... As>
using Disjunction = Negation<Conjunction<Negation<As>...>>;
```

排中律：

```cpp
template <typename A> inline Disjunction<A, Negation<A>> exclusive_middle() {
  return [](Conjunction<Negation<A>, Negation<Negation<A>>> na_nna) -> False {
    return na_nna.template get<1>()(na_nna.template get<0>());
  };
};
```
