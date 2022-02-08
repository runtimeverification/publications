# Quipuwap TTDex Audit Report Appendix

This appendix contains our analysis of the Quipuswap system.

## Prerequisites

We list here introductory background material.
Our mathematical background includes a thorough treatment of partial functions; it can probably be skipped for readers familiar with the material.
Our property notation section defines some notation we will use when defining security properties; it is essential for further understanding of our property descriptions.

### Mathematical Background

We assume familiarity with basic set theory, including the element-of (∈), subset (⊆), and strict subset (⊂) operators, set union and intersection, as well as the set builder notation { x ∈ A | φ(x) }.

#### Equality

We use two three symbols that may be confused with equality, so we disambiguate them now:

-   (definitional equality) `a = b` asserts that these two values are defined to be equal
-   (propostional equality) `a == b` is a statement that we wish to prove, which, if true, implies that `a` and `b` are equivalent in all possible contexts
-   (pattern binding) `p := a` is a statement that pattern `p` matches term `a` in a way:

    -   all variables in `p` can be bound without clashes by subterms of `a`
    -   all non-variable subterms of `p` appear as non-variable subterms of `a` in identical positions

#### Maps and Partial Functions

Since this contract makes heavy use of LIGO `big_map`s (i.e. partial functions), we take a moment to review some concepts and terminology.
A *total* function `f : A -> B` is defined such that, for each `x ∈ A`, there exists a unique `y ∈ B` such that `f(x) = y`.
A *partial* function `f : A -> B` is defined by the following condition: for each `x` in `A` either

1.  `f(x) = y ∈ B`
2.  `f(x)` is undefined

For simplicity, for a function (partial or total), we define the sets:

-   `domain(f) = A`
-   `range(f) = B`
-   `preimage(f) = { x ∈ A | ∃y ∈ B . f(x) = y }`
-   `image(f) = { y ∈ B | ∃x ∈ A . f(x) = y }`

Further note that `f` is *partial* iff `preimage(f) ⊂ domain(f)` while `f` is *total* iff `preimage(f) = domain(f)`.

Given a function `f : A -> B`, we define the functions:

1.  the totalization of `f`, written `total(f)`, the total function from `preimage(f)` to `range(f)`
2.  the graph of `f`, written `graph(f)`, the total, surjective function from `preimage(f)` to `image(f)`

We say that `f ⊂ g` or `f ⊆ g` iff `graph(f) ⊂ graph(g)` or `graph(f) ⊆ graph(g)` in the usual set-theoretic sense.

Given two functions `f : A -> B` and `g : B -> C`, we write their composition using the in-order notation `f ; g : A -> C` and define it as the function:

`f ; g = { (x,z) ∈ A x C | ∃y ∈ B . f(x) = y ∧ g(y) = z }`

We say that a partial function `f` is injective, surjective, or bijective iff `total(f)` is so in the usual sense.
Note that, the graph of `f` is necessarily surjective, so it will be bijective iff it is injective.
The composition `f ; g` will be total, injective, or surjective, if both `f` and `g` are so.

Given a set `A`, we let `id_A : A -> A` denote the bijective identity function over `A`.

By convention, we model all `big_map k v` values as partial functions from `k -> v`.

### Property Notation

In this report, we want to formalize several security properties about the TTDex contract.

We represent the evolution of the TTDex contract storage as a transition system.
The states of the transition system are tuples of the form `TTDexStorage x List{Operation}` (fully defined in our K specification `configuration` declaration given below).
The arrows of the transition system are rewrites (`=>`) using K specification defined below.

We let the letters `S`, `T`, `W`, etc. range over transition system states.

**Notation: (State Descriptions):**
When we describe system states, we will use one of two notations:

1.  a K-style notation where individual states are described by how various cells are instantiated, e.g.,

    ```
    <pairs_count> N => N +Nat 1 </pairs_count>
    <operations> Op Ops => Ops </operations>
    ```

    When using K-style notation, we let multiple arrows occur at once to describe how different cells evolve independently.

2.  an abstract notation where that uses letters `S`, `T`, `W`, etc. to represent states and a `(.)` notation to represent storage member access.
    For example, if `S => T` then we can represent the above transformation as:

    ```
    T.pairs_count = S.pairs_count +Nat 1
    T.operations  = S.operations[1:]
    ```

**Definition (Operation Evaluation):**
In addition to rewrite arrow (`=>`), we define two other arrow notations as conveniences:

-   internal operation evaluation is represented by the plus arrow (`+>`) which corresponds to evaluating a single operation.
    **Note:** in our K specification, a single operation's evaluation:

    -   begins with the `k` cell empty;
    -   ends with the `k` cell empty, the current operation consumed, and any successor operations pushed on the operation stack.

    In particular, some operations execute all-at-once, so that the `=>` and `+>` agree.

-   full _manager_ operation evaluation is represented by the single arrow (`->`) which corresponds to evaluating an operation as well as all of the operations it emits transitively.
    **Note:** a *manager* operation refers to one with an equal sender and source.

    That is, by definition, if `S=(Storage, Op Ops)` and `Op` is a manager operation, and `S -> T`, then there exists an updated storage `Storage'` with `T=(Storage', Ops)`.
    Furthermore, this means that `Ops` must also be manager operations, since otherwise, they must have been emitted during the evaluation of `Op`.

Note that `->` is definable in terms of `+>` which is definable in terms of `=>`.

We use an arrow and parenthesized address and entrypoint (`+>(address%entrypoint)` or `->(address%entrypoint)`) notation to represent an internal or full operation evaluation resulting from calling a particular contract address at a particular entrypoint.
We let the special constant `TTDEX` represent the address of the TTDex contract.
We use star (`*`) and plus (`+`) to represent zero-or-more or one-or-more applications of a relation respectively.
By abuse of notation, when writing invariants, we directly name storage locations (e.g. `pairs_count`) without referencing the state name, since invariants apply to all states.

**Definition (Stable):**
For a `map` or `big_map` valued storage member, we say that it is `stable` over `=>` (resp. `+>` or `->`) iff it has an append-only semantics.
That is, it is stable over `=>` (resp. `+>` or `->`) iff, after each `=>` step (resp. `+>` or `->` step) old entries are never removed.
For `map`s or `big_map`s, this means that, once key `k` is assigned to value `v`, we never delete the entry named `k` or remap `k` to some distinct value `w`.
More formally, for a storage member `m` with type `map k v`, we say `m` is stable over `+>` iff for all states `S` and `T` we have:

```
∀k ∈ KeyType . S +> T ∧ k ∈ preimage(S.map) => k ∈ preimage(T.map) ∧ S.map[k] == T.map[k]
```

## Security Properties

We list below some security properties that we plan to analyze or have already analyzed.

### Application-specific Security Properties

1.  Ledger/asset isolation - interactions with one particular liquidity pool and its assets should _not_ modify the state of other liquidity pools or their underlying assets
2.  Liquidity share exchange value security - the exchange value of a liquidity share should _never_ decrease
3.  Slippage security - interactions with the liquidity pool should _not_ exceed some reasonable (or user-defined) slippage
4.  Authorization correctness - only authorized users should be able to perform requested actions (e.g. users without liquidity tokens cannot divest liquidity)
5.  Accounting correctness - the ledger balances, pool states, exchange rates, etc. should be computed correctly
6.  Bounded operation delay - operation effect time should be bounded in a reasonable scope

### General Security Properties

1.  Re-entrancy safety - all potential re-entrant calls should be safe
2.  Gas-limit DOS safety - the contract should be resistant to DOS attacks that force contract execution to exceed the gas limit

### Formalization of Important Correctness/Security Properties

1.  **Pair Count May Increment (Safety):** the value of `pairs_count` never decreases and may only increase by one each step:

    If `S +> T` then `S.pairs_count == T.pairs_count ∨ S.pairs_count + 1 == T.pairs_count`

2.  **Pair Definedness Consistency (Invariant over `+>`):** various maps defining liquidity pools are correlated:

    ```
    { i ∈ Nat | i < pairs_count } == image(token_to_id)
                                  == preimage(tokens)
                                  == preimage(pairs)
    ```

3.  **Pair Identifier Stability (Safety):** the `token_to_id` map is stable over `+>`

4.  **Pair Identifier Injectivity (Invariant over `+>`):** the `token_to_id` map is injective:

    ```
    ∀b,b' ∈ preimage(token_to_id) . token_to_id[b] == token_to_id[b'] => b == b'
    ```

5.  **Pair Metadata Stability (Safety):** the `tokens` map is stable over `+>`

6.  **Pair Metadata Injectivity (Invariant over `+>`):** the `tokens` map is injective:

    ```
    ∀n,n' ∈ preimage(tokens) . tokens[n] == tokens[n'] => n == n'
    ```

7.  **Pair Identifier and Metadata Correspondence (Invariant over `+>`):** the graphs of `pack ; token_to_id` to `tokens` maps are inverses:

    Let `TN = preimage(tokens)` and `TT = image(tokens)`.

    Then both of the following are true:

    1.  `graph(tokens) ; graph(pack ; token_to_id) = id_TN`
    2.  `graph(pack ; token_to_id) ; graph(tokens) = id_TT`

8.  **No Tez Holdings (Safety):** since the TTDex contract is not designed to hold Tez reserves, it should not send or receive Tez.

9.  **Ledger Isolation (Safety):** all TTDex `use` entrypoints should only access and/or update the `ledger`, `tokens`, and `pairs` maps for parameter-specified liquidity pair identifiers:

    -   `initialize_exchange` - using `pair` parameter, let our identifier equal `pack ; token_to_id(pair)` if `pair ∈ preimage(pack ; token_to_id)` and otherwse `pairs_count` (given that `pack ; token_to_id` is injective and stable)
    -   `invest_liquidity` and `divest_liquidity` - the specified pair identifier is the passed in `pair_id` parameter
    -   `swap` - each `pair_id` in the `swaps` list is a specified pair identifier

10. **Asset Isolation (Safety):** all TTDex `use` entrypoints should only `transfer` the appropriate assets between TTDex and the sender/receiver:

    For each operation type, we have two _transfered_ asset types, i.e., calls to a FA1.2 of FA2 `transfer` entrypoint.

    -   `initialize_exchange` and `invest_liquidty` - the two transfered assets are sent _to_ TTDex where asset types are specified by `tokens[token_id]`
    -   `divestment_liquidity` - the two transfered assets are sent _from_ TTDex for the given where asset types are specified by `tokens[token_id]`
    -   `swap` - one asset is sent _to_ TTDex while the other asset is sent _from_ TTDex where asset types are specified by:
        -   looking up the asset types `tokens[head(swaps).pair_id]` with the asset chosen using `head(swaps).operation` where `A_to_b` maps to `token_a_type` and `B_to_a` maps to `token_b_type`
        -   similarly, looking up asset types `tokens[last(swaps).pair_id]` with the asset chosen using `last(swaps).operation` where `A_to_b` maps to `token_b_type` and `B_to_a` maps to `token_a_type`

11. **Liquidity Share Consistency (Invariant over `+>`):** the total liquidity share supply for each pair should equal the balances recorded in the `ledger`:

    We define a map `balances_by_index : [(Address x Nat) -> (Nat x Set{Nat})] x Nat -> Nat` given by:

    ```
    balances_by_index(ledger,i) = sum({ s ∈ Nat | ∃a ∈ Accts . s = ledger[(a,i)].balance })
    ```

    We then have two consistency conditions:

    1.  (defined liquidity shares consistency) `∀i ∈ Nat . i < pairs_count => pairs[i].total_supply == balances_by_index(ledger,i)`
    2.  (undefined liquuidity shares consistency) `∀i ∈ Nat . i >= pairs_count => 0 == balances_by_index(ledger,i)`

    **NOTE:** Unlike property (12), since this property only involves contract-owned state that never need be modified through callbacks, it can be shown to hold after every internal operation step.

12. **Asset Reserves Sufficiency (Invariant over `->`):** the total liquidity share supply and asset reserves recorded for each pair properly correspond with the underlying system state:

    We define a map `reserves_by_index : [Nat -> PairData] x TokenType x Nat -> Nat` given by:

    ```
    reserves_by_index(pairs, tt, i) = sum({ res ∈ Nat | (tokens[i].token_a_type = tt ∧ pairs[i].token_a_pool = res) ∨ (tokens[i].token_b_type = tt ∧ pairs[i].token_b_pool = res) })
    ```

    We define a map `reserves_by_token : [Nat -> PairData] x TokenType -> Nat` given by:

    ```
    reserves_by_token(pairs, tt) = sum({ res ∈ Nat | ∃i ∈ Nat . res = reserves_by_index(pairs, tt, i) })
    ```

    Each state contains a map `balances : TokenType -> Nat` which, for the given `TokenType`, stores TTDex's balance in that `TokenType`.
    We then have a function `actual_reserves : [TokenType -> Nat] x TokenType -> Nat` given by:

    ```
    actual_reserves(balances, tt) = balances[tt]
    ```

    Then the following sufficiency condition should hold:

    ```
    ∀tt ∈ unpair(image(tokens)) . reserves_by_token(pairs,tt) <= actual_reserves(balances,tt)
    ```

    **NOTE:** Due to the ability to "donate" assets to TTDex using the underlying asset `transfer` entrypoint, it is not possible to the TTDex recorded asset reserves exactly equal to its actual asset reserves.
    **NOTE:** Due to the fact that `+>` does not include the effect of emitted transfers, this invariant cannot hold under `+>`.

13. **Liquidity Share Exchange Value Security (Safety):** the exchange value of liquidity shares never decreases between subsequent states reachable from the initial state:

    If `I` is the initial state of TTDex and `I ->* S -> T` then for each `i < S.pairs_count`, we have:

    ```
      {  S.pairs[i].total_supply != 0
       ∧ S.pairs[i].token_a_pool != 0
       ∧ S.pairs[i].token_b_pool != 0 }
    =>
                                                                         T.pairs[i].token_a_pool * T.pairs[i].token_b_pool        T.pairs[i].total_supply
       (S +>(TTDEX%divest_liquidity) T ∧ T.pairs[i].total_supply) == 0 ∨ -------------------------------------------------  >=  ( ----------------------- )^2
                                                                         S.pairs[i].token_a_pool * S.pairs[i].token_b_pool        S.pairs[i].total_supply
    ```

    In words, if this pool is initialized, then in the next state it either:

    -   it is shutdown by withdrawing all liquidity using `divest_liquidity` or;
    -   the exchange value of the liquidity shares does _not_ decrease.

14. **Maximum Divestment of Assets from Exchange is Token Pool Size (Safety):** one asset cannot drain the entire token type asset reserves:

    This property has two subcases for `divest_liquidity` and `swap`:

    -   when divesting, the maximum amount of token _A_ (resp. token _B_) divested is the size of the token _A_ (resp. token _B_) pool for the given `pair_id`
    -   when swapping, the maximum amount of tokens transferred out is bounded by:

        -   the size of token _B_ pool whne the final swap in the swaplist has direction _A-to-B_
        -   the size of token _A_ pool whne the final swap in the swaplist has direction _B-to-A_

        for the `pair_id` specified by the final swap

15. **Contract Cannot Request Tez From Non-Sender Account (Safety):** the contract's operator privileges cannot be abused:

     For each emitted transfer operation of the form:

     ```
     FATransfer(TokenType, Address, TTDEX, Amount)
     ```

     we require that `Address == Sender`.
     Note that this also protects against malicious smart contracts which attmept to create a transaction on behalf of a user to steal their money.

## Entrypoint Analysis

We now enumerate the entrypoints of the Quipuswap TTDex contract:

1.  `transfer`           - `list (pair address (list (pair address (pair nat nat))))`
2.  `update_operators`   - `list (or (pair address (pair address nat)) (pair address (pair address nat)))`
3.  `balance_of`         - `list (pair address nat)`
4.  `get_reserves`       - `list (or (pair address (pair address nat)) (pair address (pair address nat)))`
5.  `set_dex_function`   - `lambda (pair {dex_input}   {core_storage}) (pair (list operation) {core_storage})`
6.  `set_token_function` - `lambda (pair {token_input} {core_storage}) (pair (list operation) {core_storage})`
7.  `close`              - `unit`
8.  `use`                - `{dex_input}`

Note that, due to the the design of the `use` entrypoint, it can essentially be understood as four separate *virtual* entrypoints that share a tiny amount of initialization and finalization code because the bulk of the work is done by looking up a `lambda` term in a `big_map` and then `EXEC`ing.
These four virtual entrypoints include the following:

-   `use/initialize_exchange` - `pair (pair (or address (pair address nat)) (or address (pair address nat))) (pair nat nat)`
-   `use/swap`                - `pair (list (pair (or unit unit) nat)) (pair nat (pair nat address))`
-   `use/invest_liquidity`    - `pair nat (pair nat (pair nat nat))`
-   `use/divest_liquidity`    - `pair nat (pair nat (pair nat nat))`

Where in the above, we use the following notation:

-   `{core_storage}` refers to the core type of the Quipuswap TTDex storage without the dex/token/metadata big_maps
-   `{dex_input}` refers to an `or` type containing all possible dex function inputs (initialize_exchange, swap, invest_liquidity, divest_liquidity)
-   `{token_input}` refers to an `or` type containing all possible FA2 token function inputs (transfer, balance_of, update_operators)

## Entrypoint Effects

There are two side-effects that a contract can have:

-   it can update its internal storage where the updated storage may or may not be final (see below);
-   it can emit operations to other contracts.

**Definition:** *Storage Finalization* - We say that a contract **C**'s storage is finalized for entrypoint **E** when all of the intended updates to the storage implied by **E** are complete.
Note that storage finalization does not necessarily correspond to entrypoint completion, because, e.g., **E** could emit callback-like operations which later call back into **C** in order to update the storage based on the result of the call.
Note also that storage finalization for **E** does *not* imply that all recursive calls made by **E** have completed; it just means that any such calls will *not* update **C**'s storage.

**Remark:** Earlier storage finalization helps defend against re-entrancy attacks, since such attacks depend on the re-entrant call making use of inconsistent/incomplete state.

## Emitted Operations Analysis

By analysis of the code, we see that five types of operations are emittable:

| Id  | Operation Type                                                                                           | Definition Point         | Usage Points     |
| --- | -------------------------------------------------------------------------------------------------------- | ------------------------ | ---------------- |
| a   | `Transfer_tokens(TTDEX, TTDEX%close,  0mutez, unit)`                                                     | partials/Dex.ligo        | use(1x)          |
| b   | `Transfer_tokens(TTDEX, any%any,      0mutez, pair nat nat)`                                             | partials/Dex.ligo        | get_reserves(1x) |
| c   | `Transfer_tokens(TTDEX, any%any,      0mutez, list (pair (pair address nat) nat))`                       | partials/MethodsFA2.ligo | balance_of(1x)   |
| d   | `Transfer_tokens(TTDEX, any%transfer, 0mutez, pair address (pair address nat))`                          | partials/Utils.ligo      | use(*)           |
| e   | `Transfer_tokens(TTDEX, any%transfer, 0mutez, list (pair address (list (pair address (pair nat nat)))))` | partials/Utils.ligo      | use(*)           |

By use(*), we refer the following list of usages inside the use entrypoint:

-   `use/initialize_exchange` - 2x
-   `use/swap`                - 2x (N usages but only 2 are emitted)
-   `use/invest_liquidity`    - 2x
-   `use/divest_liquidity`    - 2x

## Storage Finalization Analysis

By code analysis, we note that the internal state of the contract is updated **fully** after the contract finishes execution, **unless** the operation involves a transfer of a liquidity share token (i.e. a self-directed transfer), which can happen in the following cases:

1.  initializing a dex pair where at least one side of the pair is a TTDex liquidity share token;
2.  performing a swap where at least one end of the route uses a TTDex liquidity share token;
3.  investing liquidity into a dex pair where at least one side of the pair is a TTDex liquidity share token;
4.  divesting liquidity from a dex pair where at least one side of the pair is a TTDex liquidity share token.

In the four cases above, the contract will invoke its own FA2 transfer entrypoint to send liquidity share tokens from itself or to itself.
These transfer entrypoints will then update TTDex's liquidity share token ledger state to reflect the debit or credit to the contract's balance.

## Re-entrancy Analysis

**Summary:**
Since this contract makes external contract calls, re-entering the contract is possible.
We list below the possible ways in which TTDex contract calls could re-enter itself.
By the end of the audit period, we had not found any way to abuse re-entrancy to violate contract security.

**Remark:** Letters in parentheses below refer to entries in the emitted operations **analyis** table.

**Analysis:**
We first examine the kinds of operations emitted and then which enterypoints may be re-entered.

Due to type constraints, this contract can only call itself via an emitted operation cases (a) and (e).
Self-calls of type (a) do not update any important ledger state and can be ignored.
Thus, any malicious re-entrancy must come from either a a type (e) self-call or a call to another contract which then calls back into this contract using (e).
Since type (b-c) operations are emitted from read-only entrypoints, they cannot be meaningfully used to launch a re-entrancy attack.
This leaves type (d-e) operations as the only possible means of calling an attack contract that can lead to an insecure re-entrancy.

We now examine which entrypoints are re-enterable:
Due to the fact that `use` and `close` set and unset the value `entered` in the storage, re-entrancy is not possible between them (in an earlier version of the contract, this was not the case; see **re-entrancy guard failure** section above).
We can also eliminate `set_dex_function` and `set_token_function` from consideration because they are "one-shot" entrypoints (i.e. they cannot be successfully called after contract initialization).
Since `balance_of` and `get_reserves` are read-only (enforced by LIGO `const` qualifier), re-entrancy cannot lead to any additional exploits.
This leaves `transfer` and `update_operators` as the only possible entrypoints that can be re-entered and possibly exploited.

Thus, any re-entrancy exploit must have the one of the following forms:

**Pattern A:**

1.  the attacker deploys an attack contract with an FA12 or FA2 entrypoint
2.  the attacker calls entrypoint `use` and passes an attack contract callback address
3.  while in an inconsistent state, the quipuswap ttdex calls out to the attack contract at the FA12 or FA2 `transfer` entrypoint
4.  the attack contract then re-enters ttdex using entrypoints `transfer` or `update_operators` and does something malicious

**Pattern B:**

1.  the attacker calls entrypoint `use` with maliciously crafted arguments
2.  the `use` entrypoint self-calls its `transfer` entrypoint with malicious arguments, violating the contract security

Since Tezos smart contracts can only call other contracts after finishing execution, by our storage finalization analysis, such an attack is only possible if an inconsistent state can be produced by:

-   the `use` entrypoint directly
-   the `use` entrypoint followed by a self-`transfer` (since `transfer` will be called two (2) times)

Note that, by the end of the audit, we had not found any manner to exploit re-entrancy to attack TTDex.
In general, re-entrancy locks (which this contract already implemented) are a simple and important guard against re-entracy attacks.
We also recommend testing re-entrancy locks to ensure that they operate as intended.

## DOS Susceptibility Analysis

**Summary:**
We find that TTDex uses current best practices to secure itself against both kinds of gas DOS possibilities.

**Analysis:**
Common denial-of-service (DOS) attacks on smart contracts operate by either:

1.  (txn DOS) overwhelming blockchain nodes with useless transactions with high fees so that nodes do not prefer legitimate transactions with standard fees
2.  (gas DOS) overwhelming some contract-used static resource (e.g. storage, compute time) so that contract usage becomes so expensive that contract calls exceed the gas limit

Since resistance to (i) is a property of the blockchain block-creation protocol, we focus on (ii).
There are at least two methods to cause a gas DOS which we list here:

1.  (storage deserialization gas DOS)
    Some blockchain languages like Tezos deserialize the storage upon each contract call invocation which costs a fee.
    In this attack method, the storage size is maliciously increased to the point that storage deserialization fees are as close as possible to the gas limit.
    When a legitimate transaction invokes the contract, the compute fees may push the contract execution over the gas limit, causing it to abort.

2.  (compute gas DOS)
    All computation on a smart contract costs a fee which depends on the processor time/energy required to perform the computation.
    If a smart contract's compute cost varies greatly with respect to input data, an attacker can sometimes provide contract input in such a way that all subsequent contract invocations are more expensive.
    In the limit, the contract execution becomes so expensive that all contract invocations hit the gas limit and abort.
    As an example, this can occur if the contract must iterate over a very large data structure or perform a complex mathematical calculation depending on some storage value.

We find that TTDex uses current best practices to secure itself against both kinds of gas DOS possibilities.
By definition, TTDex is _not_ suspceptible to a deserialization gas DOS, since all variable-size data structures are `big_map`s.
On the other hand, the gas cost will continually increase for `big_map` lookups of increasing sizes.
Since users can arbitrarily increase the size of contract-owned `big_map`s by creating accounts in the `ledger` or by initializing new dex pairs, at some point, the gas cost associated with large map lookups or modifications will hit the gas limit.
In practice, we expect there are contract storage limits which would make the above pattern impossible to weaponize.
We note that, if `big_map`s are represented are represented in some reasonable structure, e.g., as balanced binary trees, access cost would only grow as a factor of _log₂(n)_ where _n_ is the map size.
Given this slow rate of growth combined with possible storage limits, we expect that a malicious attacker attempting to exploit these limits would be _highly unlikely_ to succeed in practice.

Though this problem is intrinsic to contracts that work with large datasets, in theory, there are various possible solutions that can make contracts more robust when working with large datasets.
Though it is unclear if they are needed in practice, we list several below for reference:

-   minimizing the number of potential map lookups
-   enforcing limits on how map entries are added (e.g. add an additional fee when creating new pairs)
-   deleting entries over time (e.g. some form of garbage collection)
-   using a mechanism whereby new contracts can be created to handle additional storage needs

To fully analyze how expensive weaponizing `big_map` growth would be, we would need to analyze the attacker's cost by examining the precise cost of `big_map` read/write operations.
We note that this kind of attack is a _griefing attack_, i.e., it hurts the attacker and the system users by wasting everyone's money, but does not directly earn money for the attacker.
In limited cases, such attacks may be profitable if, for example, the attacker runs a competing service and via the attack can drive more users to their service.
Given that this seems unlikely to be exploitable in practice, we do not pursue it further.

## Entrypoint Abstract Effect Analysis

We use a K representation to model the entrypoint effects.
We begin with some datatype declarations we will need.

```
  sort Bool        // LIGO bool type
  sort Bytes       // LIGO bytes type
  sort Nat         // LIGO nat type
  sort Mutez       // LIGO mutez type
  sort Address     // LIGO address type
  sort Option{X}   // LIGO maybe
  sort Pair{X,Y}   // LIGO pair type
  sort Map{X,Y}    // LIGO big_map type
  sort Set{X}      // LIGO set type
  sort List{X}     // LIGO list type

  sort Address ::= "TTDEX" // the address of the TTDex contract

  sort TokenType   ::= FA12(address : Address) | FA2(address : Address, token_id : Nat)
  sort TokenData   ::= Pair{TokenType, TokenType}
  sort PairData    ::= LP(totalSupply : Nat, tokenAPool : Nat, tokenBPool : Nat)
  sort AccountName ::= Pair{Address, Nat}
  sort AccountData ::= Pair{Nat, Set{Address}}

  sort OperationParam ::= MainOperationParam
                        | HelperOperationParam
                        | FAOperationParam
                        | OtherOperationParam

  sort SwapType ::= "A_to_b" | "B_to_a"
  sort SwapData ::= SwapType(pair_id : Nat, operation : SwapType)

  sort MainOperationParam ::= InitEx(pair : TokenData, tokenA : Nat, tokenB : Nat)
                            | Invest(pair_id : Nat, shares : Nat, maxTokenA : Nat, maxTokenB : Nat)
                            | Divest(pair_id : Nat, shares : Nat, minTokenA : Nat, minTokenB : Nat)
                            | Swap(swaps : List{SwapType}, tokenIn : Nat, minTokenOut : Nat, receiver : Address)

  sort HelperOperationParam ::= "Close"
                              | GetReserves(pair_id : Nat, receiver : Nat)

  sort TransferDest   ::= TransferDest(to : Address, token_id : Nat, amount : Nat)
  sort TransferParam  ::= TransferParam(from : Address, List{TransferDest})
  sort OperatorParam  ::= AddOperator(owner : Address, operator : Address, token_id : Nat)
                        | RemoveOperator(owner : Address, operator : Address, token_id : Nat)
  sort BalanceOfReq   ::= BalanceOfReq(owner : Address, token_id : Nat)
  sort BalanceOfResp  ::= BalanceOfResp(request : BalanceOfReq, balance : Nat)
  sort BalanceOfParam ::= BalanceOfParam(requests : List{BalanceOfReq}, callback : Address)

  sort FAOperationParam ::= FA2Transfer(List{TransferParam})
                          | FA12Transfer(from : Address, to : Address, amount : Nat)
                          | UpdateOperators(List{OperatorParam})
                          | BalanceOf(BalanceOfParam)

  sort FAOperationParam ::= FATransfer(TokenType, Address, Address, Nat) [function]
  // ------------------------------------------------------------------------------
  rule FATransfer(FA12(Addr),         From, To, Amount) => FA12Transfer(From, To, Amount)
  rule FATransfer(FA2(Addr, TokenId), From, To, Amount) => FA2Transfer(TransferParam(From, TransferDest(To, TokenId, Amount)))
```

We next define our state representation using a K configuration.
In this case, the configuration has three cells:

1.  the TTDex contract storage in the `<ttdex>` cell (which includes its *recorded* asset balances in the `<pairs>` cell)
2.  the TTDex *actual* asset balances map for each token type in the `<balances>` cell
3.  the operation stack in the `<operations>`

**Remark:**
The `<balances>` map is always updated assuming that any transfers from TTDex _decrease_ its own balance.
Of course, using the `swap` entrypoint, one can desiginate TTDex as the receiver of `swap` proceeds.
However, we treat this case as a _donatation_, because users can always donate funds to TTDex by sending it assets.

```
  configuration <ttdex>
                  <entered>      false                        </entered>
                  <pairs_count>  0                            </pairs_count>
                  <token_to_id> .Map{Bytes, Nat}              </token_to_id>
                  <tokens>      .Map{Nat, TokenData}          </tokens>
                  <pairs>       .Map{Nat, PairData}           </pairs>
                  <ledger>      .Map{AccountName, AccoutData} </ledger>
                </ttdex>
                <balances>   .Map{TokenType, Nat} </balances>
                <operations> .List{Operation}     </operations>
```

The following code contains the rules defining the TTDex semantics.
Essentially, these rules present the TTDex contract in a compact form that is more amenable to the auditors for review.

```
  rule [initialize_exchange] :
    <operations> Transfer_tokens(Sender, TTDEX, 0mutez, InitEx((TokenAType, TokenBType), TokenA, TokenB))
                 Ops
              => Transfer_tokens(TTDEX, TTDEX, 0mutez, Close)
                 Transfer_tokens(TTDEX, address(TokenAType), 0mutez, FATransfer(TokenAType, Sender, TTDEX, TokenA))
                 Transfer_tokens(TTDEX, address(TokenBType), 0mutez, FATransfer(TokenBType, Sender, TTDEX, TokenB))
                 Ops
    <operations>
    <entered>     false => true </entered>
    <pairs_count> Count => Count +Nat #if Ids ∈ preimage(PairBytes) #then 0 #else 1 #fi </pairs_count>
    <token_to_id> Ids => #if Ids ∈ preimage(PairBytes)
                         #then Ids
                         #else Ids[PairBytes <- Count]
                         #fi
    </token_to_id>
    <pairs>       Pairs  => Pairs [PairId <- LP(InitShares, TokenA, TokenB)]         </pairs>
    <tokens>      Tokens => Tokens[PairId <- (TokenAType, TokenBType)]               </tokens>
    <ledger>      Ledger => Ledger[ (Sender,PairId) <- (InitShares, .Set{Address}) ] </ledger>
   where PairBytes  := PackToBytes((TokenAType, TokenBType))
         InitShares := min(TokenA, TokenB)
         PairId     := Ids[PairBytes, Count]
   requires TokenAType < TokenBType
            TokenA != 0
            TokenB != 0
            totalSupply(Pairs[PairId, LP(0, 0, 0)]) == 0

  rule [invest_liquidity] :
    <operations> Transfer_tokens(Sender, TTDEX, 0mutez, Invest(PairId, Shares, MaxTokenA, MaxTokenB))
                 Ops
              => Transfer_tokens(TTDEX,  TTDEX, 0mutez, Close)
                 Transfer_tokens(TTDEX,  address(TokenAType), 0mutez, FATransfer(TokenAType, Sender, TTDEX, TokenAReq))
                 Transfer_tokens(TTDEX,  address(TokenBType), 0mutez, FATransfer(TokenBType, Sender, TTDEX, TokenBReq))
                 Ops
    <operations>
    <entered>     false  => true                                                                                          </entered>
    <pairs>       Pairs  => Pairs [ PairId <- LP(TotalShares +Nat Shares, TokenA +Nat TokenAReq, TokenB +Nat TokenBReq) ] </pairs>
    <tokens>      Tokens                                                                                                  </tokens>
    <ledger>      Ledger => Ledger[ (Sender,PairId) <- (SenderShares +Nat Shares, Operators) ]                            </ledger>
   where LP(TotalShares, TokenA, TokenB) := Pairs[PairId]
         (TokenAType, TokenBType)        := Tokens[PairId]
         TokenAReq                       := Ceil(Shares *Nat TokenA /Nat TotalShares)
         TokenBReq                       := Ceil(Shares *Nat TokenB /Nat TotalShares)
         (SenderShares, Operators)       := Ledger[ (Sender,PairId), (0, .Set{Address}) ]
   requires
         PairId ∈ preimage( Pairs  )
         PairId ∈ preimage( Tokens )
         TokenA *Nat TokenB != 0
         Shares != 0
         TokenAReq <= MaxTokenA
         TokenBReq <= MaxTokenB
         TotalShares != 0

  rule [divest_liquidity] :
    <operations> Transfer_tokens(Sender, TTDEX, 0mutez, Divest(PairId, Shares, MinTokenA, MinTokenB))
                 Ops
              => Transfer_tokens(TTDEX,  TTDEX, 0mutez, Close)
                 Transfer_tokens(TTDEX,  address(TokenAType), 0mutez, FATransfer(TokenAType, TTDEX, Sender, TokenAReq))
                 Transfer_tokens(TTDEX,  address(TokenBType), 0mutez, FATransfer(TokenBType, TTDEX, Sender, TokenAReq))
                 Ops
    <operations>
    <pairs_count> Count                                                                                                   </pairs_count>
    <entered>     false  => true                                                                                          </entered>
    <pairs>       Pairs  => Pairs [ PairId <- LP(TotalShares -Nat Shares, TokenA -Nat TokenAReq, TokenB -Nat TokenBReq) ] </pairs>
    <tokens>      Tokens                                                                                                  </tokens>
    <ledger>      Ledger => Ledger[ (Sender,PairId) <- (SenderShares -Nat Shares, Operators) ]                            </ledger>
   where LP(TotalShares, TokenA, TokenB) := Pairs[PairId]
         (TokenAType, TokenBType)        := Tokens[PairId]
         TokenAReq                       := Shares *Nat TokenA /Nat TotalShares
         TokenBReq                       := Shares *Nat TokenB /Nat TotalShares
         (SenderShares, Operators)       := Ledger[ (Sender,PairId), (0, .Set{Address}) ]
   requires
         PairId ∈ preimage( Pairs  )
         PairId ∈ preimage( Tokens )
         PairId != Count
         TokenA *Nat TokenB != 0
         TotalShares != 0
         SenderShares >= Shares
         MinTokenA != 0     andBool MinTokenB != 0
         MinTokenA <= TokenAReq andBool MinTokenB <= TokenBReq
         // implied assertions
         Shares != 0 by (MinTokenA != 0 => MinTokenA > 0) ∧ (Shares == 0 => TokenAReq == 0) ∧ (MinTokenA <= TokenAReq)

  sort K ::= SwapInternal(sender : Address,
                          receiver : Address,
                          tokenIn : Nat,
                          tokenInType : TokenType,
                          minTokenOut : Nat,
                          inputOperation : Operation,
                          outputOperation : Option{Operation},
                          swaps : List{SwapType})

  rule [swap-init] :
    <k> . => SwapInternal(Sender, Receiver, TokenIn, TokenInType, MinTokenOut, InputOperation, None, Swaps) </k>
    <operations> Transfer_tokens(Sender, TTDEX, 0mutez, Swap(Swaps, TokenIn, MinTokenOut, Receiver)) ... </operations>
    <entered>    false  => true   </entered>
    <tokens>     Tokens           </tokens>
   where SwapType(PairId, SwapDir) := head(Swaps)
         (TokenAType, TokenBType)  := Tokens[PairId]
         TokenInType               := #if SwapDir == A_to_b #then TokenAType #else TokenBType #fi
         InputOperation            := Transfer_tokens(TTDEX, address(TokenInType), 0mutez, FATransfer(TokenInType, Sender, TTDEX, TokenIn))
   requires
         Size(Swaps) >=Nat 1
         PairId ∈ preimage(Tokens)

  rule [swap-intermediate] :
    <k> SwapInternal(Sender, Receiver, TokenIn,  TokenInType,  MinTokenOut, InputOperation, _,               SwapType(PairId, SwapDir) # Swaps)
     => SwapInternal(Sender, Receiver, TokenOut, TokenOutType, MinTokenOut, InputOperation, OutputOperation,                             Swaps)
    </k>
    <pairs> Pairs
         => Pairs [ PairId <- #if SwapDir == A_to_b
                              #then LP(TotalShares, TokenA +Nat TokenIn,  TokenB -Nat TokenOut)
                              #else LP(TotalShares, TokenA -Nat TokenOut, TokenB +Nat TokenIn )
                              #fi ]
    </pairs>
    <tokens> Tokens </tokens>
   where LP(TotalShares, TokenA, TokenB) := Pairs [ PairId ]
         (TokenAType,    TokenBType)     := Tokens[ PairId ]
         (TokenInType',  TokenOutType)   := #if SwapDir == A_to_b #then (TokenAType,TokenBType) #else (TokenBType,TokenAType) #fi
         (TokenInTotal,  TokenOutTotal)  := #if SwapDir == A_to_b #then (TokenA,    TokenB)     #else (TokenB,    TokenA)     #fi
         TokenOut                        := (TokenIn *Nat 997 *Nat TokenInTotal) /Nat [(TokenOutTotal *Nat 1000) +Nat (TokenIn *Nat 997)]
         OutputOperation                 := Transfer_tokens(TTDEX, address(TokenOutType), 0mutez, FATransfer(TokenOutType, TTDEX, Receiver, TokenOut))
   requires
         PairId ∈ preimage( Pairs  )
         PairId ∈ preimage( Tokens )
         TokenA *Nat TokenB != 0
         TokenIn != 0
         TokenInType == TokenInType'
         [(TokenOutTotal *Nat 1000) +Nat (TokenIn *Nat 997)] != 0

  rule [swap-final] :
    <k> SwapInternal(Sender, Receiver, TokenOut, TokenOutType, MinTokenOut, InputOperation, MaybeOutputOperation, .List{SwapType})
     => .
    </k>
    <operations> SwapOp
                 Ops
              => Transfer_tokens(TTDEX, TTDEX, 0mutez, Close)
                 MaybeOutputOperation
                 InputOperation
                 Ops
    <operations>
   requires
         TokenOut >=Nat MinTokenOut
         MaybeOutputOperation != None

  sort K ::= TransferInternal(Sender, List{TransferParams})

  rule [transfer-init] :
    <k> . => TransferInternal1(Sender, TransferParams) </k>
    <operations> Transfer_tokens(Sender, TTDEX, 0mutez, FA2Transfer(TransferParams)) ... <operations>

  rule [transfer-intermediate-1] :
    <k> TransferInternal(Sender, TransferParam(From, TransferDest(To, TokenId, Amount) Dests) Params)
     => TransferInternal(Sender, TransferParam(From,                                   Dests) Params)
    </k>
    <ledger> Ledger => LedgerCredited </ledger>
    <balances> Balances
            => #if       From == TTDEX               #then Balances[FA2(TTDEX,TokenId)] -= Amount
               #else #if From != TTDEX ∧ To == TTDEX #then Balances[FA2(TTDEX,TokenId)] += Amount
               #else                                       Balances
               #fi #fi
    </balances>
  where (FromBalance, FromAllowances) := Ledger        [ ( From, TokenId), (0, .Set{Address}) ]
        LedgerDebited                 := Ledger        [ ( From, TokenId) <- (FromBalance -Nat Amount, FromAllowances) ]
        (ToBalance,   ToAllowances)   := LedgerDebited [ ( To,   TokenId), (0, .Set{Address}) ]
        LedgerCredited                := LedgerDebited [ ( To,   TokenId) <- (ToBalance   +Nat Amount, ToAllowances  ) ]
  requires
    From == Sender ∨ From in Allowances
    FromBalance >= Amount

  rule [transfer-intermediate-2] :
    <k> TransferInternal(Sender, TransferParam(From, .List{TransferDest}) Params)
     => TransferInternal(Sender,                                          Params)

  rule [transfer-final] :
    <k> TransferInternal(Sender, .List{TransferParam}) => . </k>
    <operations> TransferOp Ops => Ops </operations>

  sort K ::= UpdateOpInternal(Address, List{OperatorParam})

  rule [update_operators-init] :
    <k> . => UpdateOpInternal(Sender, UpdateOperatorParams) </k>
    <operations> Transfer_tokens(Sender, TTDEX, 0mutez, UpdateOperators(UpdateOperatorParams)) ... <operations>

  rule [update_operators-intermediate] :
    <k> UpdateOpInternal(Sender, UpdateOpParam UpdateOpParams))
     => UpdateOpInternal(Sender, UpdateOpParams)
    </k>
    <ledger> Ledger => Ledger [ (Owner, PairId) <- (Balance, NewAllowances) ] </ledger>
    where Owner                 := owner(UpdateOpParam)
          Operator              := operator(UpdateOpParam)
          PairId                := token_id(UpdateOpParam)
          ToAdd                 := isAddOperator(UpdateOpParam)
          (Balance, Allowances) := Ledger [ (Owner, PairId), (0, .Set{Address}) ]
          NewAllowances         := #if ToAdd #then Allowances +Set Operator
                                             #else Allowances -Set Operator
                                   #fi
    requires
      Sender == Owner

  rule [update_operators-final] :
    <k> UpdateOpInternal(Sender, .List{UpdateOperatorParam}) => . </k>
    <operations> UpdaterOperatorsOp Ops => Ops </operations>

  sort K ::= BalanceOfInternal(List{BalanceOfReq}, List{BalanceOfResp}, Address)

  rule [balance_of-init] :
    <k> . => BalanceOfInternal(Requests, .List{BalanceOfResp}, ResponseCallback)) </k>
    <operations> Transfer_tokens(Sender, TTDEX, 0mutez, BalanceOf(BalanceOfParam(Requests, ResponseCallback))) ... <operations>

  rule [balance_of-intermediate] :
    <k> BalanceOfInternal(BalanceOfReq(Owner, PairId) Requests, Responses, ResponseCallback)
     => BalanceOfInternal(Requests, BalanceOfResp(BalanceOfReq(Owner, PairId), Balance) Responses, ResponseCallback)
    </k>
    <ledger> Ledger </ledger>
   where (Balance, Allowances) := Ledger [ (Owner,PairId), (0, .Set{Address}) ]

  rule [balance_of-final] :
    <k> BalanceOfInternal(.List{BalanceOfReq}, Responses, ResponseCallback) => . </k>
    <operations> BalanceOfOp
                 Ops
              => Transfer_tokens(TTDEX, ResponseCallback, 0mutez, Responses)
                 Ops
    </operations>

  rule [close] :
     <operations> Transfer_tokens(Sender, TTDEX, 0mutez, Close) Ops => Ops </operations>
     <entered> true => false </entered>
    requires Sender == TTDEX

  rule [get-reserves] :
     <operations> Transfer_tokens(Sender, TTDEX, 0mutez, GetReserves(PairId, Receiver))
                  Ops
               => Transfer_tokens(TTDEX, Receiver, 0mutez, (TokenA, TokenB))
                  Ops
     </operations>
     <pairs> Pairs </pairs>
    where LP(_, TokenA, TokenB) := Pairs[PairId, LP(0, 0, 0)]

  rule [other] :
     <operations> _:Op Ops => Ops' Ops </operations>
    requires Receiver != TTDEX // enforced by the type system
    [owise]
```

## Proofs of Security Properties

### Assumptions

Depending on the security property we want to prove, we need some assumptions to be satisifed:
These assumptions include:

1.  **Storage Access:**  a contract `C`'s storage only be updated via calling contract `C`
2.  **DFS Operation Evaluation:** the operations that a contract emits are added to an operation stack, i.e., the next operation executed will be the one on top of the stack, so execution proceeds via depth-first search (DFS) exploration of the call graph
3.  **FA Conformance:** the FA1.2 or FA2 tokens that are used as assets in liquidity pools properly implement the FA1.2 or FA2 interface
4.  **Strict FA Conformace:** all FA1.2 or FA2 tokens that are used as assets in liquidity pools satisfy some additional properties (which may or may not follow from the FA1.2/FA2 spec):
    -   they directly update account balances upon calling `transfer` (i.e., they do not use the pull pattern)
    -   they do not charge fees on `transfer`
    -   the balance of the TTDex token reserves _cannot decrease_ except via calling `transfer` (e.g., rebasing tokens are unsupported as well as universal admin operators)
5.  **Re-entrancy Guard Fix:** the audited version of TTDex contained a broken re-entrancy guard; we assume that it is fixed for our proofs.

### Lemmas

1.  **Sender Is Not TTDex:**
    By the type system, any transaction addressed to TTDex that does not call the `transfer` or `close` entrypoints was not sent by TTDex.

    ```
    rule [sender-is-not-ttdex] :
      <operations> ... Transfer_tokens(Sender, TTDEX, Tez, Param) ... </operations>
    requires
      not ( isFA2Transfer(Param) and isClose(Param) )
    ensures
      Sender != TTDEX
    ```

2.  **TTDex Storage Updates:**
    Different TTDex storage members are only updated by specific TTDex entrypoints.
    For storage members `pairs_count`, `token_to_id`, `pairs`, `tokens`, and `ledger`, we list which entrypoints may possibly update each map.

    -   `use/initialize_exchange`: all
    -   `use/invest_liquidity`: `pairs` and `ledger`
    -   `use/divest_liquidity`: `pairs` and `ledger`
    -   `use/swap`: `pairs` and `ledger`
    -   `transfer`: `ledger`
    -   `update_operators`: `ledger`
    -   otherwise: none

3.  **Transfer:**
    This lemma encompasses several subproperties of `transfer` operations sent to other contracts (i.e. not TTDex).
    It is only used by the assert reserves sufficiency lemma, so we specialize it to those particular needs.
    The lemma states that:

    1.   The TTDex contract has _no_ operators
    2.   By (1), calls to FA12/FA2 contracts whose sender is not TTDEX with a `transfer` entrypoint may increment but _not_ decrement the `balances` map
    3.   By (1), calls to FA12/FA2 contracts whose sender is TTDEX may increment _and_ decrement the `balances` map
    4.   By code analysis, calls of the form (3) may only occur in a state where `entered == true`

    We define claims representing the various possibilities below.
    First, we define some helper functions:

    1.  transfer authorization functions are modelled as uninterpreted functions

        ```
        sort Bool ::= isAuthorized(tokenType : TokenType, fromAddress : Address, initiatorAddress : Address, amount  : Nat) [function]
        ```

    2.  the effect of transfers on the `balances` map

        ```
        sort Int ::= Transfer(sender : Address, receiver : Address, amount : Nat) [function]
        // ---------------------------------------------------------------------------------
        rule Transfer(TTDEX,  Receiver, Amount) => 0 -Int Amount
        rule Transfer(Sender, TTDEX,    Amount) =>        Amount requires Sender != TTDEX
        rule Transfer(Sender, Receiver, Amount) => 0             requires Sender != TTDEX ∧ Receiver != TTDEX
        ```

    We now define the claims representing how foreign transfers occur:

    1.  **TTDex-Issued Foreign Token Transfers**
        In this specific case, since `entered == true`, by _TTDex Storage Updates_, we know that the only TTDex storage member that is updatable is the `ledger`.
        By _strict FA conformance_, we know that, eventually, the correct adjustment to `balances` will be made by the contract.
        By our emitted operations analysis, we know that the emitted operation will have a specific form dervied from the `FATransfer` function.
        However, since other contracts may have been called that may have increased TTDex's balances via donation, we know that the final value of `balances` may be even larger.

        ```
        rule [fa-conformance-ttdex] :
          <operations> Transfer_tokens(TTDEX, address(TokenType), 0mutez, FATransfer(TokenType, From, To, Amount)) Ops -> Ops <operations>
          <entered> True </entered>
          <balances> Balances -> Balances' </balances>
        requires Receiver != TTDEX
                 From != TTDEX implies isAuthorized(Receiver, From, TTDEX, Amount)
                 Balances'[TokenType] >= Balances[TokenType] +Int Transfer(From, To, Amount)
                 ∀tt ∈ preimage(Balances) . Balances'[tt] >= Balances[tt]
        ```

        We observe that, whether we regard this rule as a sequence of transaction or a single transaction, with respect to the asset reserves sufficiency property, semantically, there is no difference.
        Thus, we can collapse its combined effects into a rule that does not emit any transactions and performs all of its effects in one-shot.

        ```
        rule [fa-conformance-ttdex-oneshot] :
          <operations> Transfer_tokens(TTDEX, address(TokenType), 0mutez, FATransfer(TokenType, From, To, Amount)) Ops => Ops <operations>
          <entered> True </entered>
          <balances> Balances => Balances' </balances>
        requires Receiver != TTDEX
                 From != TTDEX implies isAuthorized(Receiver, From, TTDEX, Amount)
                 Balances'[TokenType] >= Balances[TokenType] +Int Transfer(From, To, Amount)
                 ∀tt ∈ preimage(Balances) . Balances'[tt] >= Balances[tt]
        ```

        For our proving purposes, we will use the one-shot variation since it simplifies the proof.

    2.  **External Foreign Token Transfers**
        Since the sender is not TTDex, we know that, by _strict FA conformance_, as far as the immediate effect of this contract is concerned, TTDex's balance _cannot_ decrease.
        In essence, from the perspective of _asset reserves sufficiency_, this case is equivalent to performing an arbitrary contract call.
        Thus, we reduce this case to a strengthening of the `[other]` rule with the constraint that the balances cannot decrease:

        ```
        rule [other-2] :
           <operations> _:Op Ops => Ops' Ops </operations>
           <balances> Balances => Balances' </balances>
          requires Receiver != TTDEX // enforced by the type system
                   ∀tt ∈ preimage(Balances) . Balances'[tt] >= Balances[tt]
        ```

        In proofs below, if needed, we will use the `[other-2]` rule instead of `[other]`.

### Pair Count May Increment

**Lemma:**
If `S +> T` then `S.pairs_count == T.pairs_count ∨ S.pairs_count + 1 == T.pairs_count`

**Proof:**
Suppose `S +> T`, i.e., we evaluated a single internal operation without evaluating its emitted operations.
This is equivalent to `S +>(Address%Entrypoint) T` for some `Address%Entrypoint` combination.
We proceed by case analysis.

-   Case 1 `Address%Entrypoint != TTDEX%initialize_exchange`:
    By the _storage access_ assumption and _TTDex storage updates_ lemma, the `pairs_count` member has not changed, so we are done.

-   Case 2 `Address%Entrypoint == TTDEX%initialize_exchange`:
    Here is the storage upate of this entrypoint on the `pairs_count` member:

    ```
    <pairs_count> Count => Count +Nat #if Condition #then 0 #else 1 #fi </pairs_count>
    ```

    There are two cases:

    -   Case 2.1 `Condition == true`
        Then the update rule simplfies to:

        `<pairs_count> Count => Count </pairs_count>`

        as required.

    -   Case 2.2 `Condition == false`
        Then the update rule simplfies to:

        `<pairs_count> Count => Count +Nat 1 </pairs_count>`

        as required.

**Remark:** If we replace `S +> T` with `S -> T`, the property is not satisfied anymore, since some contract may invoke the `initialize_exchange` entrypoint multiple times as a side-effect, causing it to grow too quickly.

### Pair Definedness Consistency

**Lemma:**
The following formula is an invariant:

```
{ i ∈ Nat | i < pairs_count } == image(token_to_id)
                              == preimage(tokens)
                              == preimage(pairs) ]
```

**Proof:**
To prove this invariant, it is sufficient to show that:

1.  the initial state `I` satisifes the formula
2.  if `S` satisfies the property, then `S +>(Address%Entrypoint) T` satisfies the property

Note that `I` trivially satisfies the formula by definition since `I.pairs_count == 0` and all maps start empty.
Thus, we assume that some state `S` satisfies the property and assume that `S +>(Address%Entrypoint) T`.
We perform a case analysis on `Address%Entrypoint`.

-   Case 1 `Address != TTDEX`:
    By the _storage access_ assumption, all storage members `pairs_count`, `token_to_id`, `tokens`, and `pairs` are identical in `S` and `T`.

-   Case 2 `Address == TTDEX`:
    We now do a case analysis on entrypoints.

    -   Case 2.1 `Entrypoint == initialize_exchange`:
        In this entrypoint, we have the following storage updates (unneeded detail has been removed):

        ```
        <pairs_count> Count  => Count +Nat #if PairBytes ∈ preimage(Ids) #then 0 #else 1 #fi      </pairs_count>
        <token_to_id> Ids    => #if PairBytes ∈ preimage(Ids) #then Ids #else Ids[_ <- Count] #fi </token_to_id>
        <pairs>       Pairs  => Pairs [PairId <- _ ]                                           </pairs>
        <tokens>      Tokens => Tokens[PairId <- _ ]                                           </tokens>
        ```

        where `PairId := Ids[PairBytes, Count]`

        Let us perform a case analysis on `PairBytes ∈ preimage(Ids)`

        -   Case 2.1.1 `Pairs ∈ preimage(Ids) == true`:
            Then, by definition of map lookup with default, the storage updates specializes to:

            ```
            <pairs_count> Count  => Count +Nat 0          </pairs_count>
            <token_to_id> Ids    => Ids                   </token_to_id>
            <pairs>       Pairs  => Pairs [PairId <- _ ]  </pairs>
            <tokens>      Tokens => Tokens[PairId <- _ ]  </tokens>
            ```

            where  `PairId := Ids[PairBytes]`.
            In this case, since `PairId ∈ image(Ids)`, by I.H., we know that `PairId < Count`.
            By I.H., we have `preimage(Pairs) == preimage(Pairs[PairId <- _])` and `preimage(Tokens) == preimage(Tokens[PairId <- _])`.

        -   Case 2.1.2 `PairId ∈ preimage(Ids) == false`:
            Then, by definition of map lookup with default, the storage updates specializes to:

            ```
            <pairs_count> Count  => Count +Nat 1         </pairs_count>
            <token_to_id> Ids    => Ids[_ <- Count]      </token_to_id>
            <pairs>       Pairs  => Pairs [Count <- _ ]  </pairs>
            <tokens>      Tokens => Tokens[Count <- _ ]  </tokens>
            ```

            where `PairId := Count`.
            Since the current value of `pairs_count` is `Count + 1`, we must show that the image and preimage of the storage maps updated accordingly.
            By definition, we have (where the second equality follows by I.H.):

            1.  `image(Ids[_ <- Count])       = image(Ids)       U { Count } = { i ∈ Nat | i < Count + 1 }`
            2.  `preimage(Pairs[Count <- _])  = preimage(Pairs)  U { Count } = { i ∈ Nat | i < Count + 1 }`
            2.  `preimage(Tokens[Count <- _]) = preimage(Tokens) U { Count } = { i ∈ Nat | i < Count + 1 }`

            as required.

    -   Case 2.2 `Entrypoint == invest_liquidity` or `Entrypoint == divest_liquidity`:
        By the _TTDex storage updates_ lemma, we know that we only need to consider how `pairs` is updated.
        In both cases, the input parameters contain a `pair_id` member; suppose it has value `PairId`.
        Suppose the `pairs` storage member has value `Pairs`.
        The storage update for both can be simplified to the following:

        ```
        <pairs> Pairs => Pairs [ PairId <- _ ] </pairs>
        ```

        with the requirement that `PairId ∈ preimage(Pairs)`.
        By requirement, `PairId ∈ preimage(Pairs)`.
        Thus, by definition of map update and set union, we have `preimage(Pairs [ PairId <- _]) = preimage(Pairs) U { PairId } = preimage(Pairs)`.
        By I.H., the property is satisfied.

    -   Case 2.3 `Entrypoint == swap`:
        By the _TTDex storage updates_ lemma, we know that we only need to consider how `pairs` storage member is updated.
        The evaluation of `swap` is slightly more complex due to the fact that the rule contains a loop.
        By definition, we see that only the loop body, contained in the `[swap-intermediate]` rule updates the `pairs` cell.
        We perform a structural induction on the `swaps` list to complete the proof.

        The base case where `swaps` is the empty is trivially satisfied, since, by definition, the `[swap-intermediate]` rule only applies to non-empty loops.
        Thus, suppose the `swaps` loop is non-empty.
        The rule evaluation proceeds by extracting the `pair_id` member from the `SwapData` constructor at the head of the list.
        Suppose the `pairs` storage member has value `Pairs`.
        The storage update for one iteration of `[swap-intermediate]` can be simplified to the following:

        ```
        <pairs> Pairs => Pairs [ PairId <- _ ] </pairs>
        ```

        with the requirement that `PairId ∈ preimage(Pairs)`.
        Thus, by I.H., using reasoning identical to Case 2.2, we can show the loop post-state satisfies the invariant.
        Thus, by structural induction, the `swap` entrypoint satisfies the invariant.

    -   Case 2.4 `¬ Entrypoint ∈ { initialize_exchange, invest_liquidity, divest_liquidity, swap }`:
        By the _TTDex storage updates_ lemma, none of the storage members mentioned in our lemma are updated.
        Thus, these entrypoints trivially satisfy the property.

### Pair Idenfitier Stability

**Lemma:**
If `S +> T` and `b ∈ preimage(S.token_to_id)` then `b ∈ preimage(T.token_to_id)` and `S.token_to_id[b] == T.token_to_id[b]`.

**Proof:**
By the _TTDex storage updates_ lemma, we know that only `initialize_exchange` entrypoint may update the `token_to_id` map.
Note it is sufficient to show that, for any write to the map with some key `d`, we have that `¬ d ∈ preimage(token_to_id)`, since this means that existing keys cannot be reset/unset.
Thus, assume `S +> T` and `b ∈ preimage(S.token_to_id)`.
By definition, `S +>(Address%Entrypoint) T` for some `Address` and `Entrypoint`.
We proceed by case analysis:

-   Case 1 `Address%Entrypoint != TTDEX%initialize_exchange`:
    By the _TTDex storage updates_ lemma, the `token_to_id` map has not changed, so we are done.

-   Case 2 `Address%Entrypoint == TTDEX%initialize_exchange`:
    Now, the internal operation evaluation rule effect on the storage is as follows:

    ```
    <token_to_id> Ids => #if PairBytes ∈ preimage(Ids) #then Ids #else Ids[PairBytes <- _] #fi </token_to_id>
    ```

    We do a case analysis on the condition `PairBytes ∈ preimage(Ids)`.

    -   Case 2.1 `PairBytes ∈ preimage(Ids) == true`:
        Then the update rule for the `token_to_id` map specializes to identity, which trivially satisfies the property.

    -   Case 2.2 `PairBytes ∈ preimage(Ids) == false`:
        Then the update rule for the `token_to_id` map specializes to:

        ```
        <token_to_id> Ids => Ids[PairBytes <- Count] </token_to_id>
        ```

        where `PairBytes` is not already in the map, which satisfies the property.

### Pair Identifier Injectivity

**Lemma:**
The following formulas are invariants over `+>` from the initial state:

`∀b,b' ∈ Bytes . token_to_id[b] == token_to_id[b'] => b == b'`

**Proof:**
To prove the invariant is satisfied, we need to show that:

1.  the initial state `I` satisfies the invariant;
2.  if some state `S` satisfies the invariant, we show that if `S +> T` then `T` satisfies the invariant.

Since `I` trivially satisfies the invariant since both the `token_to_id` and `tokens` maps are empty, we just need to prove sub-claim (2).
Thus, assume `S` satisfies the invariant and `S +>(Address%Entrypoint) T`.
We perform a case analysis on `Address%Entrypoint`.

-   Case 1 `Address%Entrypoint != TTDEX%initialize_exchange`:
    By the _TTDex storage updates_ lemma, the `token_to_id` map has not changed, so we are done.

-   Case 2 `Address%Entrypoint == TTDEX%initialize_exchange`:
    Now, the internal operation evaluation rule effect on the storage is as follows:

    ```
    <pairs_count> Count  => Count +Nat #if PairBytes ∈ preimage(Ids) #then 0 #else 1 #fi              </pairs_count>
    <token_to_id> Ids    => #if PairBytes ∈ preimage(Ids) #then Ids #else Ids[PairBytes <- Count] #fi </token_to_id>
    ```

    where `PairBytes := PackToBytes((TokenAType,TokenBType))`.
    We continue by a case analysis:

    -   Case 2.1 `PairBytes ∈ preimage(Ids) == true`:
        Then the storage updates specializes to:

        ```
        <pairs_count> Count => Count </pairs_count>
        <token_to_id> Ids   => Ids   </token_to_id>
        ```

        Then, the resulting `Ids` map is injective by I.H.

    -   Case 2.2 `PairBytes ∈ preimage(Ids) == false`:
        When fully expanded, the storage update specializes to:

        ```
        <pairs_count> Count => Count +Nat 1                                       </pairs_count>
        <token_to_id> Ids   => Ids[PackToBytes((TokenAType,TokenBType)) <- Count] </token_to_id>
        ```

        By the proof of the _pair definedness consistency_ lemma, we know that `{ i ∈ Nat | i < Count } == image(Ids)`.
        Thus, we know that `¬ PairBytes ∈ preimage(Ids)` *and* `¬ Count ∈ image(Ids)`.
        Since the union of two injective maps with disjoint preimages and images is injective, we are done, i.e., in this case, the maps `Ids` and `PairBytes <- Count`.

### Pair Metadata Stability

**Lemma:**
If `S +> T` and `n ∈ preimage(S.tokens)` then `n ∈ preimage(T.tokens)` and `S.tokens[n] == T.tokens[n]`.

**Proof:**
By the _TTDex storage updates_ lemma, we know that only `initialize_exchange` entrypoint may update the `tokens` map.
Thus, assume `S +> T` and `b ∈ preimage(S.tokens)`.
By definition, `S +>(Address%Entrypoint) T` for some `Address` and `Entrypoint`.
We proceed by case analysis:

-   Case 1 `Address%Entrypoint != TTDEX%initialize_exchange`:
    By the _TTDex storage updates_ lemma, the `tokens` map has not changed, so we are done.

-   Case 2 `Address%Entrypoint == TTDEX%initialize_exchange`:
    Now, the internal operation evaluation rule effect on the storage is as follows:

    ```
    <token_to_id> Ids    => #if PairBytes ∈ preimage(Ids) #then Ids #else Ids[PairBytes <- Count] #fi </token_to_id>
    <tokens>      Tokens => Tokens[PairId <- (TokenAType, TokenBType)]                             </tokens>
    ```

    where `PairBytes  := PackToBytes((TokenAType, TokenBType))` and `PairId := Ids[PairBytes, Count]`.
    To prove the stability of `Tokens`, it is enough to show that each modification to the `tokens` map has the form:

    `Tokens[f_i(x) <- x]`

    where `f_i` is a sequence of injective functions where if `j <= k` then `f_j ⊆ f_k`.
    In this case, violating stability would mean that, at some point, we have the update:

    `Tokens[f_j(x) <- x]`

    and later we have an update with some `j <= k`:

    `Tokens[f_k(y) <- y]`

    where `f_j(x) == f_k(y)` and `x != y`.
    But since `f_j ⊆ f_k`, we have `f_j(x) == f_k(x)`, violating injectivity of `f_k`.

    To proceed along this line of proof, we first note that `PackToBytes` is an injective function.
    By the _pair identifier injectivity_ lemma, we know that the `Ids` map is also injective.
    Since, the composition of injective functions is injective, we have that:

    `Ids[PackToBytes(_)]`

    is injective.
    We further note that, by _pair identifier stability_, we have that the values of `token_to_id` forms a sequence of injective functions where each one is a superset of its predecessor.
    We must show that the stable sequence `Ids_i[_]` is preserved under pre-composition with `PackToBytes`, i.e., `PackToBytes ; Ids_i[_]` forms a stable sequence of injective functions.
    Suppose we restrict the range of `PackToBytes` to the preimage of `Ids_i[_]` and update the domain of `PackToBytes` accordingly.
    Call this function `PackToBytes_i`.
    Then `PackToBytes_i` is surjective and thus bijective.
    Then, `PackToBytes_i ; Ids_i` must be a stable sequence of injective functions.

    But there is one wrinkle: the update rule for the `tokens` map is:

    ```
    <tokens> Tokens => Tokens[Ids[PackToBytes(x), Count] <- x] </tokens>
    ```

    To complete the proof, we must reduce `Ids[PackToBytes(_), Count]` to `Ids[PackToBytes(_)]`.
    We proceed by case analysis on the condition `PairBytes ∈ preimage(Ids)`.

    -   Case 2.1 `PairBytes ∈ preimage(Ids) == true`:
        Then `PairId := Ids[PairBytes, Count] == Ids[PairBytes]`.
        The storage update specializes to the pattern:

        ```
        <token_to_id> Ids    => Ids                              </token_to_id>
        <tokens>      Tokens => Tokens[Ids[PackToBytes(x)] <- x] </tokens>
        ```

        Since `PackToBytes(x)` is in the preimage of `Ids_i`, it also within the range of `PackToBytes_i`.
        Thus, our update function is `PackToBytes_i ; Ids_i`, a member of our sequence of injective functions, as required.

    -   Case 2.2 `PairBytes ∈ preimage(Ids) == false`:
        Then `PairId := Ids[PairBytes, Count] == Count`.
        The storage update specializes to:

        ```
        <token_to_id> Ids    => Ids[PackToBytes((TokenAType,TokenBType)) <- Count]                                   </token_to_id>
        <tokens>      Tokens => Tokens[Ids[PackToBytes((TokenAType,TokenBType)), Count] <- (TokenAType, TokenBType)] </tokens>
        ```

        Letting `Ids' := Ids[PackToBytes((TokenAType,TokenBType)) <- Count]`, i.e., the post-storage value of the `token_to_id` member, we can rewrite this update as the pattern:

        ```
        <token_to_id> Ids    => Ids'                               </token_to_id>
        <tokens>      Tokens => Tokens[Ids'[PackToBytes(x)] <- x ] </tokens>
        ```

        Since by the _pair identifier stability_ lemma, `Ids'` is also a member of our sequence of injective functions and `PackToBytes(x)` is in the preimage of `Ids'` by definition, we have an update function in our sequence `PackToBytes_i ; Ids_i`, as required.

### Pair Metadata Injectivity

**Lemma:**
The following formulas are invariants over `+>` from the initial state:

`∀n,n' ∈ Nat . tokens[n] == tokens[n'] => n == n'`

**Proof:**
To prove `tokens` is injective, for some `n,n' ∈ Nat` over which `tokens` is defined, assume:

`tokens[n] == tokens[n']`

In the proof of _pair metadata stability_, we showed that each update to the `tokens` map has the form:

`tokens[ f_i(t) <- t ]`

for `t ∈ TokenData` and `f_i` in a sequence of injective functions where `j <= k` implies `f_j ⊆ f_k`.
By the map update pattern above, for some `j` and `k`, we know that `n` and `n'` have the form:

`n = f_j(t)` and `n' = f_k(t')`.

By stability, we can pick the larger of `j` and `k` (without loss of generality, assume `k` is larger) and rewrite them as:

`n = f_k(t)` and `n' = f_k(t')`.

Thus, we can rewrite our initial pattern as:

`tokens[f_k(t)] == t == t' == tokens[f_k(t')]`.

Since `t == t'`, by functionality, `f_k(t) == f_k(t')`.
But this means `n == n'`, as required.

### Pair Identifier and Metadata Correspondence

**Lemma:**
Let `TN = preimage(tokens)` and `TT = image(tokens)`.

Then both of the following are invariants over `+>`:

1.  `graph(tokens) ; graph(pack ; token_to_id) = id_TN`
2.  `graph(pack ; token_to_id) ; graph(tokens) = id_TT`

**Proof:**
To prove the invariant is satisfied, we need to show that:

1.  the initial state `I` satisfies the invariant;
2.  if some state `S` satisfies the invariant, we show that if `S +> T` then `T` satisfies the invariant.

In case (1), `I.tokens` is the empty set, we have `preimage(tokens) = image(tokens) = {}`.
Thus, `id_TN = id_TT = {}`.
Furthermore, `I.token_to_id` is also the empty set, which implies `pack ; token_to_id` is the empty set.
Thus, `graph(tokens) : {} -> {}` and `graph(pack ; token_to_id) : {} -> {}`.
Since the composition of empty functions is empty, we are done.

Thus, let us consider case (2).
Suppose a `S` satisfies the invariant and that `S +> T`.
We proceed by case analysis:

-   Case 1 `Address%Entrypoint != TTDEX%initialize_exchange`:
    By the _TTDex storage updates_ lemma, the `tokens` and `token_to_id` maps have not changed, so by I.H., we are done.

-   Case 2 `Address%Entrypoint == TTDEX%initialize_exchange`:
    Now, the internal operation evaluation rule effect on the storage is as follows:

    ```
    <token_to_id> Ids    => #if PairBytes ∈ preimage(Ids) #then Ids #else Ids[PairBytes <- Count] #fi </token_to_id>
    <tokens>      Tokens => Tokens[PairId <- (TokenAType,TokenBType) ]                             </tokens>
    ```

    where `PairBytes := (TokenAType, TokenBType)` and `PairId := Ids[PairBytes, Count]`.
    We then proceed by a case analysis on `PairBytes ∈ preimage(Ids)`.

    -   Case 2.1 `PairBytes ∈ preimage(Ids) == true`:
        Then `PairId := Ids[PairBytes, Count] == Ids[PairBytes]`.
        The storage update specializes to the pattern:

        ```
        <token_to_id> Ids    => Ids                                                </token_to_id>
        <tokens>      Tokens => Tokens[Ids[PairBytes] <- (TokenAType, TokenBType)] </tokens>
        ```

        By definition, `Ids[PairBytes] ∈ image(Ids)`.
        Since `image(pack) ⊇ preimage(token_to_id)`, we have `image(token_to_id) = image(pack ; token_to_id) = range(graph(pack ; token_to_id))`.
        By I.H., `range(graph(pack ; token_to_id)) = domain(graph(tokens))`.
        Thus, `Ids[PairBytes] ∈ domain(graph(tokens)) = preimage(tokens)`.
        By the _pair metadata stability_ lemma, since `Ids[PairBytes] ∈ preimage(tokens)`, this means that the entry `Ids[PairBytes] <- (TokenAType, TokenBType)` is already in the map `Tokens`.
        Thus, `Tokens[Ids[PairBytes] <- (TokenAType, TokenBType)] = Tokens`.
        By I.H., the invariant holds, as required.

    -   Case 2.2 `PairBytes ∈ preimage(Ids) == false`:
        Then `PairId := Ids[PairBytes, Count] == Count`.
        The storage update specializes to the pattern:

        ```
        <token_to_id> Ids    => Ids[PairBytes <- Count]                   </token_to_id>
        <tokens>      Tokens => Tokens[Count <- (TokenAType,TokenBType) ] </tokens>
        ```

        We need to show that:

        1.  `graph(tokens[count <- (token_a_type, token_b_type)]) ; graph(pack ; token_to_id[pairbytes <- count]) = id_TN`
        2.  `graph(pack ; ids[pairbytes <- count]) ; graph(tokens[count <- (token_a_type, token_b_type)]) = id_TT`

        By the _pair definedness consistency_ lemma as well as the _pair identifier/metadata stability_ lemmas, we know that:

        -   the map `[pairbytes <- count]` is disjoint from `token_to_id`
        -   the map `[count <- (token_a_type, token_b_type)]` is disjoint from `tokens`

        Since by I.H. `graph(pack ; token_to_id)` is bijective with `graph(tokens)`, by disjointness and definition of set union, we will be done if we can prove that:

        `graph(pack ; [pairbytes <- count])` is bijective with `graph([count <- (token_a_type, token_b_type)])`

        Since the union of the two disjoint bijective functions is bijective.
        By definition, `domain(graph(pack ; [pairbytes <- count])) = {(token_a_type, token_b_type)} = range(graph([count <- (token_a_type,token_b_type)))`.
        Furthermore, `range(graph(pack ; [pairbytes <- count])) = {count} = domain(graph([count <- (token_a_type,token_b_type)))`.
        Since these are singleton functions, they must be bijective with each other, as required.

### Ledger Isolation

**Lemma:** all TTDex `use` entrypoints should only access and/or update the `ledger` and `pairs` maps for parameter-specified liquidity pairs:

-   `initialize_exchange` - using `pair` parameter, let our identifier equal `pack ; token_to_id(pair)` if `pair ∈ preimage(pack ; token_to_id)` and otherwse `pairs_count` (given that `pack ; token_to_id` is injective and stable)
-   `invest_liquidity` and `divest_liquidity` - the specified pair identifier is the passed in `pair_id` parameter
-   `swap` - each `pair_id` in the `swaps` list is a specified pair identifier

**Proof:**
The above conditions directly follow from the source code and the above lemmas.

### Asset Isolation

**Lemma:** all TTDex `use` entrypoints should only `transfer` the appropriate assets between TTDex and the sender/receiver:

For each operation type, we have two _transfered_ asset types, i.e., calls to a FA1.2 of FA2 `transfer` entrypoint.

-   `initialize_exchange` and `invest_liquidty` - the two transfered assets are sent _to_ TTDex where asset types are specified by `tokens[pair_id]`
-   `divestment_liquidity` - the two transfered assets are sent _from_ TTDex for the given where asset types are specified by `tokens[pair_id]`
-   `swap` - one asset is sent _to_ TTDex while the other asset is sent _from_ TTDex where asset types are specified by:
    -   looking up the asset types `tokens[head(swaps).pair_id]` with the asset chosen using `head(swaps).operation` where `A_to_b` maps to `token_a_type` and `B_to_a` maps to `token_b_type`
    -   similarly, looking up asset types `tokens[last(swaps).pair_id]` with the asset chosen using `last(swaps).operation` where `A_to_b` maps to `token_b_type` and `B_to_a` maps to `token_a_type`

**Proof:**
Building off of the _ledger isolation_ lemma, we just need to check that each transfer proceeds in the correction with the correct token type.
But we can read this property off directly from the source code.

### Liquidity Share Consistency

**Lemma:** the total liquidity share supply for each pair should equal the balances recorded in the `ledger`:

We define a map `balances_by_index : [(Address x Nat) -> (Nat x Set{Nat})] x Nat -> Nat` given by:

```
balances_by_index(ledger,i) == sum({ s ∈ Nat | ∃a ∈ Accts . s = ledger[(a,i)].balance })
```

We then have two consistency conditions which are invariants over `+>`:

1.  (defined liquidity shares consistency) `∀i ∈ Nat . i < pairs_count => pairs[i].total_supply == balances_by_index(ledger,i)`
2.  (undefined liquuidity shares consistency) `∀i ∈ Nat . i >= pairs_count => 0 == balances_by_index(ledger,i)`

**Proof:**
To prove an invariant we must show that it holds for the initial state and that, given that it holds for an arbitrary state, it holds for all reachable states.
Since, in the initial state, all maps are empty and `pairs_count` is 0, all properties are trivially satisfied in the initial state.
Thus, we assume that they each hold for some state `S` and assume `S +> T`.
We need to prove that the invariant still holds for `T`.

We start with property (2), since it is easiest to prove.
Since net shares are added to the ledger only in the `initialize_exchange` and `invest_liquidity` entrypoints, we just need to consider whether these entrypoints can add shares to a ledger with `pair_id >= pairs_count`.
We consider each in turn.

-   Case 1 `[initialize_exchange]`
    By definition, `initialize_exchange` only has one case where `pair_id >= pairs_count`, i.e., `pair_id == pairs_count`.
    In this case, the `ledger` is updated to provide shares for an account with asset `pair_id`, but at the same time, `pairs_count` is guaranteed to be incremented.
    By I.H., the property holds for the updated value of `pairs_count`.

-   Case 2 `[invest_liquidity]`
    Turning to `invest_liquidity`, the passed in `pair_id` is subject to the requirements `pair_id ∈ preimage(tokens)` and `pair_id ∈ preimage(pairs)`.
    By the _pair definedness consistency_ lemma, this means `pair_id < pairs_count`.
    By the _ledger isolation_ lemma, we are done.

We now move to property (1).
We can ignore entrypoints which do not modify `total_supply` or the balance of any account in the `ledger`, including `balance_of`, `update_operators`, `close`, `get_reserves`, and `swap`.
Since `transfer` preserves balances and does not modify `total_supply`, in that case, we satisfy the invariant.
Thus, we need only consider `initialize_exchange`, `invest_liquidity`, and `divest_liquidity`.

-   Case 1 `[initialize_exchange]`
    The `initialize_exchange` entrypoint only operates on pairs which have a `total_supply` of 0.
    By I.H. and sub-property (2), for the we know that `0 == balances_by_index(S.ledger, pair_id)`.
    When `initialize_exchange` terminates, some account in the ledger has received `n` units of asset `pair_id` and the `pairs[pair_id].total_supply` has increased by `n`, as required.

-   Case 2 `[invest_liquidity]`
    We do a case analyis on `(Sender, PairId) ∈ preimage(S.ledger)`.

    -   Case 2.1 `(Sender, PairId) ∈ preimage(S.ledger)`:
        In case it holds, we have:

        `T.pairs[pair_id].total_supply = S.pairs[pair_id].total_supply + shares`
        `T.ledger = S.ledger[ (Sender, PairId) <- (Balance + shares, Operators)]`

        with `(Balance, Operators) := S.ledger[(Sender, PairId)]`.
        By definition, we have: `T.ledger[(Sender,PairId) <- undef] == S.ledger[(Sender,PairId) <- undef]`.
        We also have:

        ```
        T.pairs[pair_id].total_supply = S.pairs[pair_id].total_supply + shares
                                      = balances_by_index(S.ledger, pair_id) + shares
                                      = Balance + balances_by_index(S.ledger[(Sender,PairId) <- undef], pair_id) + shares
                                      = balances_by_index(T.ledger)
        ```

        as required.

    -   Case 2.2 `¬ (Sender, PairId) ∈ preimage(S.ledger)`:
        In the other case, we have:

        `T.pairs[pair_id].total_supply = S.pairs[pair_id].total_supply + shares`
        `T.ledger = S.ledger[ (Sender, PairId) <- (0 + shares, .Set{Address})]`

        By a similar analysis, we have:

        ```
        T.pairs[pair_id].total_supply = S.pairs[pair_id].total_supply + shares
                                      = balances_by_index(S.ledger, pair_id) + shares
                                      = balances_by_index(S.ledger[(Sender,PairId) <- undef], pair_id) + shares
                                      = balances_by_index(T.ledger)
        ```

        as required.

-   Case 3 `[divest_liquidity]`
    We do a case analyis on `(Sender, PairId) ∈ preimage(S.ledger)`.

    -   Case 3.1 `(Sender, PairId) ∈ preimage(S.ledger)`:
        In case it holds, we have:

        `T.pairs[pair_id].total_supply = S.pairs[pair_id].total_supply - shares`
        `T.ledger = S.ledger[(Sender,PairId) <- (Balance - shares, Operators)`

        with `(Balance, Operators) := S.ledger[(Sender, PairId)]` and `Balance >= shares`.
        By definition, we have: `T.ledger[(Sender,PairId) <- undef] == S.ledger[(Sender,PairId) <- undef]`.
        We also have:

        ```
        T.pairs[pair_id].total_supply = S.pairs[pair_id].total_supply - shares
                                      = balances_by_index(S.ledger, pair_id) - shares
                                      = Balance + balances_by_index(S.ledger[(Sender,PairId) <- undef], pair_id) - shares
                                      = balances_by_index(T.ledger)
        ```

        For the subtraction to not underflow, we require that `S.pairs[pair_id].total_supply >= shares`.
        But since `S.pairs[pair_id].total_supply >= Balance` by I.H., and `Balance >= shares` by assertion in the code, we are OK.

    -   Case 3.2 `¬ (Sender, PairId) ∈ preimage(S.ledger)`:
        In the other case we have,

        `T.pairs[pair_id].total_supply = S.pairs[pair_id].total_supply - shares`
        `T.ledger = S.ledger[ (Sender, PairId) <- (0 - shares, .Set{Address})]`

        with `0 >= shares`.
        This means `shares == 0`.
        This causes a computed value `TokenAReq := (0 *Nat CurrTokenA) /Nat TotalShares == 0`.
        We also have a value `MinTokenA` such that `MinTokenA > 0` with a requirement that `MinTokenA < TokenAReq`, which is unsatisfiable.
        Thus, we can ignore this case as unreachable.

### Asset Reserves Sufficiency

**Theorem:**
Assuming we have the following definitions:

```
reserves_by_index(pairs, tt, i) = sum({ res ∈ Nat | (tokens[i].token_a_type = tt ∧ pairs[i].token_a_pool = res) ∨ (tokens[i].token_b_type = tt ∧ pairs[i].token_b_pool = res) })
reserves_by_token(pairs, tt)    = sum({ res ∈ Nat | ∃i ∈ Nat . res = reserves_by_index(pairs, tt, i) })
```

As defined above, state contains a map `balances : TokenType -> Nat` which, for the given `TokenType`, stores TTDex's balance in that `TokenType`.
We then have a function `actual_reserves : [TokenType -> Nat] x TokenType -> Nat` given by:

```
actual_reserves(balances, tt) = balances[tt]
```

We then define the asset reserve sufficieny property which is an invariant over `->`:

```
∀tt ∈ unpair(image(tokens)) . reserves_by_token(pairs,tt) <= actual_reserves(balances, tt)
```

**Proof:**
To prove an invariant we must show that it holds for the initial state and that, given that it holds for an arbitrary state, it holds for all reachable states.
Since, in the initial state, the `tokens` map is empty, the invariant is trivially true.
Thus, we assume that they each hold for some state `S` and assume `S -> T`.

Our initial claim will be of the form:

```
claim [asset-reserves-sufficiency] :
  <operations> Op Ops -> Ops </operations>
  <entered> false </entered>
  <pairs_count> Count -> Count' </pairs_count>
  <token_to_id> Ids -> Ids' </token_to_id>
  <tokens> Tokens -> Tokens' </tokens>
  <pairs> Pairs -> Pairs' </pairs>
  <ledger> Ledger -> Ledger' </ledger>
  <balances> Balances -> Balances' </balances>
requires
  ∀tt ∈ unpair(image(Tokens)) . reserves_by_token(Pairs, tt) <= actual_reserves(Balances,  tt)
ensures
  ∀tt ∈ unpair(image(Tokens)) . reserves_by_token(Pairs, tt) <= actual_reserves(Balances', tt)
```

We can prove it by generalizing the above claim to one that includes the intermediate effects of `FATransfer` operations on the asset balances:

```
claim [asset-reserves-sufficiency-generalized] :
  <operations> Op Ops +>* Ops' Ops </operations>
  <entered> Entered +>* Entered' </entered>
  <pairs_count> Count +>+ Count' </pairs_count>
  <token_to_id> Ids +>+ Ids' </token_to_id>
  <tokens> Tokens +>+ Tokens' </tokens>
  <pairs> Pairs +>+ Pairs' </pairs>
  <ledger> Ledger +>+ Ledger' </ledger>
  <balances> Balances +>* Balances' </balances>
requires
  ∀tt ∈ unpair(image(Tokens)) . reserves_by_token(Pairs,  tt) <= toNat(actual_reserves(Balances,  tt) +Int Transfer(tt, TTDEX, Op   Ops))
ensures
  ∀tt ∈ unpair(image(Tokens)) . reserves_by_token(Pairs', tt) <= toNat(actual_reserves(Balances', tt) +Int Transfer(tt, TTDEX, Ops' Ops))

sort Nat ::= toNat(Int) [function]
// -------------------------------
rule toNat(X) => X requires X >= 0

sort Int ::= Transfer(TokenType, Address, List{Operation}) [function]
// -------------------------------------------------------------------
rule Transfer(TT, TTDEX, .List{Operation}) = 0
rule Transfer(TT, TTDEX, Op Ops) = Transfer(TT, TTDEX, Ops) [owise]
rule Transfer(TT, TTDEX, Transfer_tokens(TTDEX, TT, FATransfer(TT, TTDEX,  Receiver, N)) Ops) = Transfer(TT, TTDEX, Ops) -Int N
rule Transfer(TT, TTDEX, Transfer_tokens(TTDEX, TT, FATransfer(TT, Sender, TTDEX,    N)) Ops) = Transfer(TT, TTDEX, Ops) +Int N
  requires Sender != TTDEX
```

The above claim generalizes the previous one in several dimensions:

1.  The transitive closure of the `->` arrow is replaced by reflexive-transitive closure;
2.  The terms on the left-hand and right-hand side of the `operations` cell are more general because there are extra variables;
3.  The terms on the left-hand and right-hand side of the `entered` cell are no longer constrained to be equivalent;
4.  The precondition drops the manager operation constraints from the operation stack;
5.  The precondition and postcondition have an extra term `Tranfer()`.

**Remark:** In order to use the generalized claim to prove the specialized claim, we must show that:

-   (a) the extra term introduced in (4) does not overly constrain the claim;
-   (b) the weakening introduced in (3) will not cause our claim to be underconstrained compared to the original, i.e.,  if `entered == false` before execution, it will be `false` after execution.

Note that (a) holds because because the value of `Transfer` is always zero for manager operations.
We can prove that (b) holds by noting that:

-   all entrypoints except `initialize_exchange`, `invest_liquidity`, `divest_liquidity`, `swap`, and `close` preserve the value of `entered`;
-   the `close` entrypoint is not callable when `entered` is `false`, so we can ignore it;
-   for each of the other operations, even though they set the value of `entered` to `true`, they always emit a `close` operation which reverts this effect, as required.

**Proof:**
We now prove the the claim `[assert-reserves-sufficiency-generalized]` by induction.
In the base case, the empty (reflexive) rewrite, we have `Ops' == Op`.
But then the postcondition is identical to the precondition, so we are done.
We now consider the inductive case, written as the claim below:

```
claim [asset-reserves-sufficiency-ind] :
  <operations> Op Ops +> Ops' Ops </operations>
  <entered> _ +> _ </entered>
  <pairs_count> Count +> Count' </pairs_count>
  <token_to_id> Ids +> Ids' </token_to_id>
  <tokens> Tokens +> Tokens' </tokens>
  <pairs> Pairs +> Pairs' </pairs>
  <ledger> Ledger +> Ledger' </ledger>
  <balances> Balances +> Balances' </ledger>
requires
  ∀tt ∈ unpair(image(Tokens)) . reserves_by_token(Pairs,  tt) <= toNat(actual_reserves(Balances,  tt) +Int Transfer(tt, TTDEX, Op   Ops))
ensures
  ∀tt ∈ unpair(image(Tokens)) . reserves_by_token(Pairs', tt) <= toNat(actual_reserves(Balances', tt) +Int Transfer(tt, TTDEX, Ops' Ops))
```

We proceed by doing a case analysis on `Op`:

-   Case 1 `Transfer_Tokens(_,_,_,_) :!=  Op`
    We know:

    -   a. `Op == Set_delegate(...) ∨ Create_contract(...)` (by definition of Tezos operation)
    -   b. `Ops' == .List{Operation}` (by definition of Tezos operation evaluation, non-contract invocations cannot emit operations)
    -   c. `Pairs == Pair'` (by _storage access_ assumption)
    -   d. `Balances == Balances'` (by _transfer_ lemma)
    -   e. `Transfer(tt, TTDEX, Op   Ops) == Transfer(tt, TTDEX, Ops)` (by definition of `Transfer`)
    -   f. `Transfer(tt, TTDEX, Ops' Ops) == Transfer(tt, TTDEX, Ops)` (by definition of `Transfer`)

    Thus, for any `tt ∈ unpair(image(Tokens))`, we have:

    ```
        reserves_by_token(Pairs,   tt) <= toNat(actual_reserves(Balances,  tt) +Int Transfer(tt, TTDEX, Op Ops))
    <=> reserves_by_token(Pairs,   tt) <= toNat(actual_reserves(Balances,  tt) +Int Transfer(tt, TTDEX, Ops))
    <=> reserves_by_token(Pairs',  tt) <= toNat(actual_reserves(Balances,  tt) +Int Transfer(tt, TTDEX, Ops))
    <=> reserves_by_token(Pairs',  tt) <= toNat(actual_reserves(Balances', tt) +Int Transfer(tt, TTDEX, Ops))
    <=> reserves_by_token(Pairs',  tt) <= toNat(actual_reserves(Balances', tt) +Int Transfer(tt, TTDEX, Ops' Ops))
    ```

    We note that facts (c-f) are sufficient to prove the above chain of equalities.
    In all subsequent cases, we will close any case where these facts are provable.

-   Case 2 `Transfer_tokens(Sender, Receiver, Tez, Params) := Op`:
    In this case, the emitted operation is of the form `Transfer_tokens()`.
    We do a case analysis on the identity of the `Sender` and `Receiver`.

    -   Case 2.1 `Sender != TTDEX ∧ Receiver != TTDEX`:
        In this case, the only rule that can apply is `[other-2]`.
        It is sufficient to observe:

        -   the sender of `Op` and `Ops'` is not `TTDEX` (by definition of operation sender)
        -   `Pairs == Pairs'` (by _storage access_ assumption)
        -   `∀tt ∈ preimage(Balances) . Balances'[tt] >= Balances[tt]` (by _transfer_ lemma)
        -   `Transfer(tt, TTDEX, Op   Ops) == Transfer(tt, TTDEX, Ops)` (by sender of `Op` is not TTDEX)
        -   `Transfer(tt, TTDEX, Ops' Ops) == Transfer(tt, TTDEX, Ops)` (by sender of `Ops'` is not TTDEX)

    -   Case 2.2 `Sender == TTDEX ∧ Receiver == TTDEX`:
        We peform a case analysis on `Params`.

        -   Case 2.2.1 `Close := Params`:
            It is sufficient to observe:

            -   `Ops' == .List{Operation}` (by definition of `[close]`)
            -   `Pairs == Pairs'` (by definition of `[close]`)
            -   `Balances == Balances'` (by _transfer_ lemma)
            -   `Transfer(tt, TTDEX, Op   Ops) == Transfer(tt, TTDEX, Ops)` (by call param is not `FATransfer`)
            -   `Transfer(tt, TTDEX, Ops' Ops) == Transfer(tt, TTDEX, Ops)` (by `Ops'` is empty)

        -   Case 2.2.2 `FATransfer(TokenType, From, To, Amount) := Params`:
            We note the following facts:

            -   `Ops' == .List{Operation}` (by definition of `transfer`)
            -   `Pairs == Pairs'` (by definition of `transfer`)
            -   `(TTDEX, TokenId) := TokenType` (by definition of `transfer`, since TTDex implements FA2)
            -   `TokenId ∈ unpair(image(Tokens))` (by precondition of `transfer`)
            -   `∀tt ∈ unpair(image(Tokens)) . tt != TokenId => Transfer(tt, TTDEX, Op Ops) == Transfer(tt, TTDEX, Ops)` (by definition of `Transfer`)
            -   `∀tt ∈ preimage(Balances) . tt != TokenType => Balances'[tt] == Balances[tt]`

            Thus, for all token types besides `TokenType`, we can conclude this proof branch.
            To show that the invariant holds for `TokenType`, we proceed by case analysis on `From` and `To`:

            -   Case 2.2.2.1 `From == TTDEX`
                We note the following facts:

                -   `Transfer(TokenType, TTDEX, FATransfer(TokenType, TTDEX, To, Amount) Ops) == Transfer(TokenType, TTDEX, Ops) -Int Amount` (by definition of `Transfer`)
                -   `Balances'[TokenType] == Balances[TokenType] -Int Amount` (by `transfer` rules)

                This gives:

                ```
                    reserves_by_token(Pairs,  TokenType) <= toNat(actual_reserves(Balances,  TokenType)             +Int Transfer(TokenType, TTDEX, Op Ops))
                <=> reserves_by_token(Pairs,  TokenType) <= toNat(actual_reserves(Balances,  TokenType)             +Int Transfer(TokenType, TTDEX, Ops))      -Int Amount
                <=> reserves_by_token(Pairs', TokenType) <= toNat(actual_reserves(Balances,  TokenType)             +Int Transfer(TokenType, TTDEX, Ops))      -Int Amount
                <=> reserves_by_token(Pairs', TokenType) <= toNat(actual_reserves(Balances', TokenType) +Int Amount +Int Transfer(TokenType, TTDEX, Ops))      -Int Amount
                <=> reserves_by_token(Pairs', TokenType) <= toNat(actual_reserves(Balances', TokenType) +Int Amount +Int Transfer(TokenType, TTDEX, Ops' Ops)) -Int Amount
                <=> reserves_by_token(Pairs', TokenType) <= toNat(actual_reserves(Balances', TokenType)             +Int Transfer(TokenType, TTDEX, Ops' Ops))
                ```

            -   Case 2.2.2.2 `From != TTDEX ∧ To == TTDEX`
                We note the following facts:

                -   `Transfer(TokenType, TTDEX, FATransfer(TokenType, From, TTDEX, Amount) Ops) == Transfer(TokenType, TTDEX, Ops) +Int Amount` (by definition of `Transfer`)
                -   `Balances'[TokenType] == Balances[TokenType] +Int Amount` (by `transfer` rules)

                This gives:

                ```
                    reserves_by_token(Pairs,  TokenType) <= toNat(actual_reserves(Balances,  TokenType)             +Int Transfer(TokenType, TTDEX, Op Ops))
                <=> reserves_by_token(Pairs,  TokenType) <= toNat(actual_reserves(Balances,  TokenType)             +Int Transfer(TokenType, TTDEX, Ops))      +Int Amount
                <=> reserves_by_token(Pairs', TokenType) <= toNat(actual_reserves(Balances,  TokenType)             +Int Transfer(TokenType, TTDEX, Ops))      +Int Amount
                <=> reserves_by_token(Pairs', TokenType) <= toNat(actual_reserves(Balances', TokenType) -Int Amount +Int Transfer(TokenType, TTDEX, Ops))      +Int Amount
                <=> reserves_by_token(Pairs', TokenType) <= toNat(actual_reserves(Balances', TokenType) -Int Amount +Int Transfer(TokenType, TTDEX, Ops' Ops)) +Int Amount
                <=> reserves_by_token(Pairs', TokenType) <= toNat(actual_reserves(Balances', TokenType)             +Int Transfer(TokenType, TTDEX, Ops' Ops))
                ```

            -   Case 2.2.2.3 `From != TTDEX ∧ To != TTDEX`
                By our emitted operation analysis, we know that this case is unreachable.

        -   Case 2.2.3 Default:
            By our entrypoint analysis, this case is unreachable, since by the type system, TTDex may only invoke itself in the above two manners.

    -   Case 2.3 `Sender == TTDEX ∧ Receiver != TTDEX`:
        We note the following facts:

        -   `Pairs == Pairs'` (by _storage access_ assumption)

        We perform a case analysis on `Params`.

        -   Case 2.3.1 `FATransfer(TokenType, From, To, Params) := Params`
            In this case, only the `[fa-conformance-ttdex-oneshot]` rule applies.
            We observe the following facts:

            -   `∀tt ∈ preimage(Balances) . tt != TokenType => Balances'[tt] >= Balances[tt]` (by `[fa-conformance-ttdex-oneshot]`)
            -   `Ops' == .List{Operation}` (by `[fa-conformance-ttdex-oneshot]`)
            -   `∀tt ∈ unpair(image(Tokens)) . tt != TokenId => Transfer(tt, TTDEX, Op Ops) == Transfer(tt, TTDEX, Ops)` (by definition of `Transfer`)
            -   `Transfer(tt, TTDEX, Ops' Ops) == Transfer(tt, TTDEX, Ops)` (by `Ops'` is empty)

            Thus, for all token types besides `TokenType`, we can conclude this proof branch.
            To show that the invariant holds for `TokenType`, we proceed by case analysis on `From` and `To`:

            -   Case 2.3.1.1 `From == TTDEX`
                We can follow the exact same reasoning as in case 2.2.2.1.

            -   Case 2.3.1.2 `From != TTDEX ∧ To == TTDEX`
                We can follow the exact same reasoning as in case 2.2.2.2.

            -   Case 2.3.1.3 `From != TTDEX ∧ To != TTDEX`
                By emitted operation analysis, we know that this case is unreachable.

        -   Case 2.3.4 Default
            In this case, by emitted operation analysis, we know the operation is not a call to `transfer`.
            Thus, the only rule that applies is `[other-2]`.
            It is sufficient to observe:

            -   `Pairs == Pairs'` (by _storage access_ assumption)
            -   `Att ∈ preimage(Balances) Balances'[tt] >= Balances[tt]` (by _transfer_ lemma)
            -   `Transfer(tt, TTDEX, Op   Ops) == Transfer(tt, TTDEX, Ops)` (by `Transfer` definition)
            -   `Transfer(tt, TTDEX, Ops' Ops) == Transfer(tt, TTDEX, Ops)` (by sender of `Ops'` is not TTDex)

    -   Case 2.4 `Sender != TTDEX ∧ Receiver == TTDEX`:
        We proceed by a case analysis on `Params`.

        -   Case 2.4.1 `GetReserves(_,_) := Params` or `BalanceOf(_) := Params` or `UpdateOperators(_) := Params`
            We observe the following facts:

            -   `Pairs' == Pairs` (by the _TTDex storage updates_ lemma)
            -   `Balances' == Balances` (by the _TTDex storage updates_ lemma)
            -   `Transfer(tt, TTDEX, Op   Ops) == Transfer(tt, TTDEX, Ops)` (by definition of `Transfer`)
            -   `Transfer(tt, TTDEX, Ops' Ops) == Transfer(tt, TTDEX, Ops)` (by definition of `Transfer`)

            Thus, we are done.

        -   Case 2.4.3 `InitEx(Pair, TokenA, TokenB) := Params`
            WIP

        -   Case 2.4.4 `Invest(PairId, Shares, MaxTokenA, MaxTokenB) := Params`
            By definition, we have `PairId ∈ preimage(Pairs)` and `PairId ∈ preimage(Tokens)`.
            Without loss of generality, let:

            -   `LP(TotalShares, CurrTokenA, CurrTokenB) := Pairs[PairId]`
            -   `(TokenAType, TokenBType) := Tokens[PairId]`

            Then we observe the following:

            -   `Pairs' == Pairs[PairId <- LP(TotalShares +Nat Shares, CurrTokenA +Nat TokenAReq, CurrTokenB +Nat TokenBReq)]`
            -   `Att ∈ preimage(Balances) Balances'[tt] == Balances[tt]` (by _transfer_ lemma)
            -   `Ops'` has three elements (by the definition of `invest_liquidity` and the re-entrancy guard fix)
                1.  `Transfer_tokens(TTDEX,  address(TokenAType), 0mutez, FATransfer(TokenAType, Sender, TTDEX, TokenAReq))`
                2.  `Transfer_tokens(TTDEX,  address(TokenBType), 0mutez, FATransfer(TokenBType, Sender, TTDEX, TokenBReq))`
                3.  `Transfer_tokens(TTDEX,  TTDEX, 0mutez, Close)`

            For any token type `tt` that is not in `unpair(Tokens[PairId])`, we have:

            -   `Transfer(tt, TTDEX, Op Ops) == Transfer(tt, TTDEX, Ops)` (by definition of `Transfer`)
            -   `Transfer(tt, TTDEX, Ops' Ops) == Transfer(tt, TTDEX, Ops)` (by definition of `Transfer`)
            -   `reserves_by_token(Pairs', tt) == reserves_by_token(Pairs, tt)`

            The above facts are enough to conclude that the invariant holds for all token types not referenced in this rule.
            We now consider the cases where the token type was referenced in this rule:

            -   Case 2.4.4.1 `tt == TokenAType`
                In this case, we observe the following facts:

                -   `Transfer(tt, TTDEX, Op   Ops) == Transfer(tt, TTDEX, Ops)`   (by definition of `Transfer`)
                -   `Transfer(tt, TTDEX, Ops' Ops) == Transfer(tt, TTDEX, Ops) +Int TokenAReq` (by definition of `Transfer`)

                Thus, we have:

                ```
                    reserves_by_token(Pairs,  TokenAType)                <= toNat(actual_reserves(Balances,  TokenAType) +Int Transfer(TokenAType, TTDEX, Op Ops))
                <=> reserves_by_token(Pairs,  TokenAType)                <= toNat(actual_reserves(Balances,  TokenAType) +Int Transfer(TokenAType, TTDEX, Ops))
                <=> reserves_by_token(Pairs', TokenAType) -Int TokenAReq <= toNat(actual_reserves(Balances,  TokenAType) +Int Transfer(TokenAType, TTDEX, Ops))
                <=> reserves_by_token(Pairs', TokenAType) -Int TokenAReq <= toNat(actual_reserves(Balances', TokenAType) +Int Transfer(TokenAType, TTDEX, Ops))
                <=> reserves_by_token(Pairs', TokenAType) -Int TokenAReq <= toNat(actual_reserves(Balances', TokenAType) +Int Transfer(TokenAType, TTDEX, Ops' Ops)) -Int TokenAReq
                <=> reserves_by_token(Pairs', TokenAType)                <= toNat(actual_reserves(Balances', TokenAType) +Int Transfer(TokenAType, TTDEX, Ops' Ops))
                ```

            -   Case 2.4.4.2 `tt == TokenBType`

                -   `Transfer(tt, TTDEX, Op   Ops) == Transfer(tt, TTDEX, Ops)`   (by definition of `Transfer`)
                -   `Transfer(tt, TTDEX, Ops' Ops) == Transfer(tt, TTDEX, Ops) +Int TokenBReq` (by definition of `Transfer`)

                Thus, we have:

                ```
                    reserves_by_token(Pairs,  TokenBType)                <= toNat(actual_reserves(Balances,  TokenBType) +Int Transfer(TokenBType, TTDEX, Op Ops))
                <=> reserves_by_token(Pairs,  TokenBType)                <= toNat(actual_reserves(Balances,  TokenBType) +Int Transfer(TokenBType, TTDEX, Ops))
                <=> reserves_by_token(Pairs', TokenBType) -Int TokenBReq <= toNat(actual_reserves(Balances,  TokenBType) +Int Transfer(TokenBType, TTDEX, Ops))
                <=> reserves_by_token(Pairs', TokenBType) -Int TokenBReq <= toNat(actual_reserves(Balances', TokenBType) +Int Transfer(TokenBType, TTDEX, Ops))
                <=> reserves_by_token(Pairs', TokenBType) -Int TokenBReq <= toNat(actual_reserves(Balances', TokenBType) +Int Transfer(TokenBType, TTDEX, Ops' Ops)) -Int TokenBReq
                <=> reserves_by_token(Pairs', TokenBType)                <= toNat(actual_reserves(Balances', TokenBType) +Int Transfer(TokenBType, TTDEX, Ops' Ops))
                ```

            Thus, all token type instances are covered, as required.

        -   Case 2.4.5 `Divest(PairId, Shares, MaxTokenA, MaxTokenB) := Params`
            By definition, we have `PairId ∈ preimage(Pairs)` and `PairId ∈ preimage(Tokens)`.
            Without loss of generality, let:

            -   `LP(TotalShares, CurrTokenA, CurrTokenB) := Pairs[PairId]`
            -   `(TokenAType, TokenBType) := Tokens[PairId]`

            Then we observe the following:

            -   `Pairs' == Pairs[PairId <- LP(TotalShares -Nat Shares, CurrTokenA -Nat TokenAReq, CurrTokenB -Nat TokenBReq)]`
            -   `Att ∈ preimage(Balances) Balances'[tt] == Balances[tt]` (by _transfer_ lemma)
            -   `Ops'` has three elements (by the definition of `divest_liquidity` and the re-entrancy guard fix)
                1.  `Transfer_tokens(TTDEX,  address(TokenAType), 0mutez, FATransfer(TokenAType, TTDEX, Sender, TokenAReq))`
                2.  `Transfer_tokens(TTDEX,  address(TokenBType), 0mutez, FATransfer(TokenBType, TTDEX, Sender, TokenBReq))`
                3.  `Transfer_tokens(TTDEX,  TTDEX, 0mutez, Close)`

            The above facts are enough to conclude that the invariant holds for all token types not referenced in this rule.
            We now consider the cases where the token type was referenced in this rule:

            -   Case 2.4.4.1 `tt == TokenAType`
                In this case, we observe the following facts:

                -   `Transfer(tt, TTDEX, Op   Ops) == Transfer(tt, TTDEX, Ops)`   (by definition of `Transfer`)
                -   `Transfer(tt, TTDEX, Ops' Ops) == Transfer(tt, TTDEX, Ops) -Int TokenAReq` (by definition of `Transfer`)

                Thus, we have:

                ```
                    reserves_by_token(Pairs,  TokenAType)                <= toNat(actual_reserves(Balances,  TokenAType) +Int Transfer(TokenAType, TTDEX, Op Ops))
                <=> reserves_by_token(Pairs,  TokenAType)                <= toNat(actual_reserves(Balances,  TokenAType) +Int Transfer(TokenAType, TTDEX, Ops))
                <=> reserves_by_token(Pairs', TokenAType) +Int TokenAReq <= toNat(actual_reserves(Balances,  TokenAType) +Int Transfer(TokenAType, TTDEX, Ops))
                <=> reserves_by_token(Pairs', TokenAType) +Int TokenAReq <= toNat(actual_reserves(Balances', TokenAType) +Int Transfer(TokenAType, TTDEX, Ops))
                <=> reserves_by_token(Pairs', TokenAType) +Int TokenAReq <= toNat(actual_reserves(Balances', TokenAType) +Int Transfer(TokenAType, TTDEX, Ops' Ops)) +Int TokenAReq
                <=> reserves_by_token(Pairs', TokenAType)                <= toNat(actual_reserves(Balances', TokenAType) +Int Transfer(TokenAType, TTDEX, Ops' Ops))
                ```

            -   Case 2.4.4.2 `tt == TokenBType`

                -   `Transfer(tt, TTDEX, Op   Ops) == Transfer(tt, TTDEX, Ops)`   (by definition of `Transfer`)
                -   `Transfer(tt, TTDEX, Ops' Ops) == Transfer(tt, TTDEX, Ops) -Int TokenBReq` (by definition of `Transfer`)

                Thus, we have:

                ```
                    reserves_by_token(Pairs,  TokenBType)                <= toNat(actual_reserves(Balances,  TokenBType) +Int Transfer(TokenBType, TTDEX, Op Ops))
                <=> reserves_by_token(Pairs,  TokenBType)                <= toNat(actual_reserves(Balances,  TokenBType) +Int Transfer(TokenBType, TTDEX, Ops))
                <=> reserves_by_token(Pairs', TokenBType) +Int TokenBReq <= toNat(actual_reserves(Balances,  TokenBType) +Int Transfer(TokenBType, TTDEX, Ops))
                <=> reserves_by_token(Pairs', TokenBType) +Int TokenBReq <= toNat(actual_reserves(Balances', TokenBType) +Int Transfer(TokenBType, TTDEX, Ops))
                <=> reserves_by_token(Pairs', TokenBType) +Int TokenBReq <= toNat(actual_reserves(Balances', TokenBType) +Int Transfer(TokenBType, TTDEX, Ops' Ops)) +Int TokenBReq
                <=> reserves_by_token(Pairs', TokenBType)                <= toNat(actual_reserves(Balances', TokenBType) +Int Transfer(TokenBType, TTDEX, Ops' Ops))
                ```

            Thus, all token type instances are covered, as required.

        -   Case 2.4.6 `FA2Transfer(TransferParams) := Params`
            We observe the following facts:

            -   `Pairs' == Pairs` (by _TTDex storage updates_ lemma)
            -   `Att ∈ preimage(Balances) Balances'[tt] >= Balances[tt]` (by _transfer_ lemma, since non-TTDex `transfer`s cannot decrease `balances`)
            -   `Transfer(tt, TTDEX, Op   Ops) == Transfer(tt, TTDEX, Ops)` (by definition of `Transfer` and not sent by TTDex)
            -   `Transfer(tt, TTDEX, Ops' Ops) == Transfer(tt, TTDEX, Ops)` (by definition of `Transfer` and `Ops' == .List{Operation}`)

            But then, the invariant holds, as required.

        -   Case 2.4.7 `Swap(Swaps, TokenIn, MinTokenOut, Receiver) := Params`
            The proof for swap is slightly more complex due to the presence of a loop.
            To analysze this loop, we first define some notation:

            -   we define the (possibly partial) functions:

                ```
                input_type(Swap)  : SwapData -> TokenType = if operation(Swap) == A_to_b
                                                            then token_a_type(tokens(pair_id(Swap)))
                                                            else token_b_type(tokens(pair_id(Swap)))
                output_type(Swap) : SwapData -> TokenType = if operation(Swap) == A_to_b
                                                            then token_b_type(tokens(pair_id(Swap)))
                                                            else token_a_type(tokens(pair_id(Swap)))

                initial_type(Swaps) : List{SwapData} -> TokenType      = input_type(Swaps[0])
                types(Swaps)    : List{SwapData} -> Set{TokenType} = U { unpair(tokens(Swap[i])) | 0 < i < len(Swaps) }

                zero_if_false(Cond,N) : Bool x Nat -> Nat = if Cond then N else 0
                ```

            For convenience, we restate the loop body here:

            ```
            sort K ::= SwapInternal(sender : Address,
                                    receiver : Address,
                                    tokenIn : Nat,
                                    tokenInType : TokenType,
                                    minTokenOut : Nat,
                                    inputOperation : Operation,
                                    outputOperation : Option{Operation},
                                    swaps : List{SwapType})

            <k> SwapInternal(Sender, Receiver, TokenIn,  TokenInType,  MinTokenOut, InputOperation, _,               SwapType(PairId, SwapDir) # Swaps)
             => SwapInternal(Sender, Receiver, TokenOut, TokenOutType, MinTokenOut, InputOperation, OutputOperation,                             Swaps)
            </k>
            <pairs> Pairs
                 => Pairs [ PairId <- #if SwapDir == A_to_b
                                      #then LP(TotalShares, TokenA +Nat TokenIn,  TokenB -Nat TokenOut)
                                      #else LP(TotalShares, TokenA -Nat TokenOut, TokenB +Nat TokenIn )
                                      #fi ]
            </pairs>
            <tokens> Tokens </tokens>
            where LP(TotalShares, TokenA, TokenB) := Pairs [ PairId ]
                  (TokenAType,    TokenBType)     := Tokens[ PairId ]
                  (TokenInType',  TokenOutType)   := #if SwapDir == A_to_b #then (TokenAType,TokenBType) #else (TokenBType,TokenAType) #fi
                  (TokenInTotal,  TokenOutTotal)  := #if SwapDir == A_to_b #then (TokenA,    TokenB)     #else (TokenB,    TokenA)     #fi
                  TokenOut                        := (TokenIn *Nat 997 *Nat TokenInTotal) /Nat [(TokenOutTotal *Nat 1000) +Nat (TokenIn *Nat 997)]
                  OutputOperation                 := Transfer_tokens(TTDEX, address(TokenOutType), 0mutez, FATransfer(TokenOutType, TTDEX, Receiver, TokenOut))
            ```

            Since we are using a functional notation, the standard loop accessible variables include:

            -   the members of the `SwapInternal` struct which thread state through the loop, e.g.,

                -   `TokenIn : Nat` - the current value of the `tokenIn` member
                -   `TokenInType : TokenType` - the current value of the `tokenInType`

            -   the environment variables that this function closes over, e.g.,

                -   `Pairs : Map{Nat, PairData}` - the current value of the `pairs` storage member

            We define the following ghost variables for use in our loop invariant and postcondition analysis:

            -   `TokenInOrig : Nat` - the original value of `tokenIn`
            -   `InitType : TokenType` - set equal to `input_type(Swaps[0])`
            -   `FinalType : TokenType` - set equal to `output_type(Swaps[length(Swaps)-1])`
            -   `Types : Set{TokenType}` - set equal to `types(Swaps)`
            -   `SwapsOrig : List{SwapData}` - the original value of the `Swaps` list
            -   `Idx : Nat` the index of the last completed loop iteration, starting from `0`
            -   `PairsOrig : Nat -> PairData` the original value of the `pairs` map

            We define our loop invariant as the conjunction of the following conditions:

            1.  (loop index condition)

                ```
                Idx <= length(Swaps)
                ```

            2.  (swapped token reserves preservation)

                ```
                Att ∈ types(Swaps) .
                  reserves_by_token(Pairs, tt) == reserves_by_token(PairsOrig, tt)
                                                + zero_if_false(Idx != 0 ∧ tt == InitType,                  TokenInOrig)
                                                - zero_if_false(Idx != 0 ∧ tt == output_type(Swaps[Idx-1]), TokenIn)
                ```

            3.  (other token reserves preservation)

                ```
                Att ∈ TokenType . tt != types(Swaps) . reserves_by_token(Pairs, tt) == reserves_by_token(PairsOrig, tt)
                ```

            4.  (final token type)

                ```
                FinalType == TokenInType
                ```

            The proof that this is a loop invariant is somewhat tedious; we leave the fully worked out details as an exercise.
            We now observe that, when the entrypoint ends:

            -   Emitted operations `Ops'` is equal to the list

                1.  `Transfer_tokens(TTDEX, address(InitType),  0mutez, FATransfer(InitType,  Sender, TTDEX,    TokenInOrig))`
                2.  `Transfer_tokens(TTDEX, address(FinalType), 0mutez, FATransfer(FinalType, TTDEX,  Receiver, TokenIn))`

            -   By the previous fact and the definition of `Transfer`, we obtain the following:

                -    `InitType == FinalType => Transfer(InitType,  TTDEX, Ops' Ops) == Transfer(tt, TTDEX, Ops) + TokenInOrig - TokenIn`
                -    `InitType != FinalTYpe => Transfer(InitType,  TTDEX, Ops' Ops) == Transfer(tt, TTDEX, Ops) + TokenInOrig`
                -    `InitType != FinalTYpe => Transfer(FinalType, TTDEX, Ops' Ops) == Transfer(tt, TTDEX, Ops) - TokenIn`

            -   By loop invariant (1), the loop index `Idx == length(Swaps)`
            -   By invariants (1-2), the token reserves for the initial and final types are updated as follows:

                -   Case A `InitType == FinalType`

                    ```
                    reserves_by_token(Pairs,InitType) = reserves_by_token(PairsOrig,InitType) + TokenInOrig - TokenIn
                    ```

                -   Case B `InitType != FinalType`

                    ```
                      reserves_by_token(Pairs,InitType)   = reserves_by_token(PairsOrig,InitType)  + TokenInOrig
                    ∧ reserves_by_token(Pairs,FinalType)) = reserves_by_token(PairsOrig,FinalType) - TokenIn
                    ```

            We make some final observations:

            -   `Balances' == Balances` (by the _transfer_ lemma)
            -   `∀tt ∈ TokenType . Transfer(tt, TTDEX, Op Ops) == Transfer(tt, TTDEX, Ops)` (by definition of `Transfer`)
            -   `∀tt ∈ TokenType . tt != InitType ∧ tt != FinalType => reserves_by_token(Pairs,tt) == reserves_by_token(PairsOrig,tt)` (by loop invariants 2 and 3)

            For all token types besides `InitType` and `FinalType`, we are done.
            We also have enough information to prove the invariant holds for `InitType` and `FinalType`.

            -   Case 2.4.7.1 `InitType == FinalType`
                Then we have:

                ```
                    reserves_by_token(Pairs,  InitType)                               <= toNat(actual_reserves(Balances,  InitType) +Int Transfer(InitType, TTDEX, Op Ops))
                <=> reserves_by_token(Pairs,  InitType)                               <= toNat(actual_reserves(Balances,  InitType) +Int Transfer(InitType, TTDEX, Ops))
                <=> reserves_by_token(Pairs', InitType) -Int TokenInOrig +Int TokenIn <= toNat(actual_reserves(Balances,  InitType) +Int Transfer(InitType, TTDEX, Ops))
                <=> reserves_by_token(Pairs', InitType) -Int TokenInOrig +Int TokenIn <= toNat(actual_reserves(Balances', InitType) +Int Transfer(InitType, TTDEX, Ops))
                <=> reserves_by_token(Pairs', InitType) -Int TokenInOrig +Int TokenIn <= toNat(actual_reserves(Balances', InitType) +Int Transfer(InitType, TTDEX, Ops' Ops)) -Int TokenInOrig +Int TokenIn
                <=> reserves_by_token(Pairs', InitType)                               <= toNat(actual_reserves(Balances', InitType) +Int Transfer(InitType, TTDEX, Ops' Ops))
                ```

            -   Case 2.4.7.2 `InitType != FinalType`
                Then we have for `InitType`:

                ```
                    reserves_by_token(Pairs,  InitType)                   <= toNat(actual_reserves(Balances,  InitType) +Int Transfer(InitType, TTDEX, Op Ops))
                <=> reserves_by_token(Pairs,  InitType)                   <= toNat(actual_reserves(Balances,  InitType) +Int Transfer(InitType, TTDEX, Ops))
                <=> reserves_by_token(Pairs', InitType) -Int TokenInOrig  <= toNat(actual_reserves(Balances,  InitType) +Int Transfer(InitType, TTDEX, Ops))
                <=> reserves_by_token(Pairs', InitType) -Int TokenInOrig  <= toNat(actual_reserves(Balances', InitType) +Int Transfer(InitType, TTDEX, Ops))
                <=> reserves_by_token(Pairs', InitType) -Int TokenInOrig  <= toNat(actual_reserves(Balances', InitType) +Int Transfer(InitType, TTDEX, Ops' Ops)) -Int TokenInOrig
                <=> reserves_by_token(Pairs', InitType)                   <= toNat(actual_reserves(Balances', InitType) +Int Transfer(InitType, TTDEX, Ops' Ops))
                ```

                For `FinalType`, we also have:

                ```
                    reserves_by_token(Pairs,  FinalType)              <= toNat(actual_reserves(Balances,  FinalType) +Int Transfer(FinalType, TTDEX, Op Ops))
                <=> reserves_by_token(Pairs,  FinalType)              <= toNat(actual_reserves(Balances,  FinalType) +Int Transfer(FinalType, TTDEX, Ops))
                <=> reserves_by_token(Pairs', FinalType) +Int TokenIn <= toNat(actual_reserves(Balances,  FinalType) +Int Transfer(FinalType, TTDEX, Ops))
                <=> reserves_by_token(Pairs', FinalType) +Int TokenIn <= toNat(actual_reserves(Balances', FinalType) +Int Transfer(FinalType, TTDEX, Ops))
                <=> reserves_by_token(Pairs', FinalType) +Int TokenIn <= toNat(actual_reserves(Balances', FinalType) +Int Transfer(FinalType, TTDEX, Ops' Ops))  +Int TokenIn
                <=> reserves_by_token(Pairs', FinalType)              <= toNat(actual_reserves(Balances', FinalType) +Int Transfer(FinalType, TTDEX, Ops' Ops))
                ```

        -   Case 2.4.8 Default
            This case is unreachable by the type system.

### Liquidity Share Exchange Value Security

**Theorem:**
The exchange value of liquidity shares never decreases between subsequent states reachable from the initial state.
If `I` is the initial state of TTDex and `I +>* S +> T` then for each `i < S.pairs_count`, we have:

```
  {  S.pairs[i].total_supply != 0
   ∧ S.pairs[i].token_a_pool != 0
   ∧ S.pairs[i].token_b_pool != 0 }
=>
                                                                     T.pairs[i].token_a_pool * T.pairs[i].token_b_pool        T.pairs[i].total_supply
   (S +>(TTDEX%divest_liquidity) T ∧ T.pairs[i].total_supply) == 0 ∨ -------------------------------------------------  >=  ( ----------------------- )^2
                                                                     S.pairs[i].token_a_pool * S.pairs[i].token_b_pool        S.pairs[i].total_supply
```

In words, if this pool is initialized, then in the next state it either:

-   it is shutdown by withdrawing all liquidity using `divest_liquidity` or;
-   the exchange value of the liquidity shares does _not_ decrease.

**Proof:**
By the liquidity shares consistency proof, we know that the `total_supply` variable is an exact match for the real liquidity supply.
By the asset reserves sufficiency proof, we know that he contract has backing reserves of each token type sufficient to cover all pairs that reference it.
Now we assert that a relationship holds between _only_ contract storage members.
By the _storage access_ assumption, external contract calls are irrelevant to this property.

**Remark:** The calculations used below in our proofs are standard in the world of constant product market makers, so we omit proofs.
See, e.g., the liquidity baking proofs in the [K-Michelson repo](https://github.com/runtimeverification/michelson-semantics), for a reference.

-   Case 1 `Receiver != TTDEX`
    Then, by the _storage access_ assumption, we are done.

-   Case 2 `Receiver == TTDEX`
    We proceed by case analysis on the operation performed.

    -   Case 2.1 `[initialize_exchange]`
        In this case, the update rule for the `pairs` map is:

        ```
        <pairs> Pairs => Pairs [PairId <- _] </pairs>
        ```

        such that `totalSupply(Pairs[PairId, LP(0, 0, 0)]) == 0`.
        Thus, either `¬ PairId ∈ preimage(Pairs)` which implies `PairId > S.pairs_count` or else `totalSupply(Pairs[PairId]) == 0`.
        In either case, the antecedent of the implication for that `PairId` is false, and the invariant holds trivially for that `PairId`.
        For all other pair identifiers `i != PairId`, by the update rule, we know `S.pairs[i] == T.pairs[i]`.
        But then, for each pair `i`, either it has zero liquidity or else it satisfies the increasing exchange value condition.

    -   Case 2.2 `[invest_liquidity]`
        In this case, the update rule for the `pairs` map is:

        ```
        <pairs> Pairs  => Pairs [ PairId <- LP(TotalShares +Nat Shares, CurrTokenA +Nat TokenAReq, CurrTokenB +Nat TokenBReq) ] </pairs>
        ```

        where:

        -   `Shares` is an entyrpoint parameter
        -   `LP(TotalShares, CurrTokenA, CurrTokenB) := Pairs[PairId]`
        -   `TokenAReq := Ceil(Shares *Nat CurrTokenA /Nat TotalShares)`
        -   `TokenBReq := Ceil(Shares *Nat CurrTokenB /Nat TotalShares)`

        We can prove that there exists a real number `P >= 1` such that:

        -   `TotalShares + Shares == TotalShares *Real P`
        -   `CurrTokenA *Real P <= CurrTokenA +Nat Ceil(Shares *Nat CurrTokenA /Nat TotalShares)`
        -   `CurrTokenB *Real P <= CurrTokenB +Nat Ceil(Shares *Nat CurrTokenB /Nat TotalShares)`

        To see that invariant finally holds for all pairs, we do a case analysis:

        -   Case 2.2.1 `i != PairId`
            Then `S.token_a_pool[i] == T.token_a_pool[i] ∧ S.token_b_pool[i] == T.token_b_pool[i] ∧ S.total_supply[i] == T.total_supply[i]`, so the invariant holds for pair `i`.

        -   Case 2.2.2 `i == PairId`
            Then since:

            -   `S.total_suppply[i] * P == T.total_supply[i]`
            -   `S.token_a_pool[i] * P <= T.token_a_pool[i]`
            -   `S.token_b_pool[i] * P <= T.token_a_pool[i]`

            We can prove that:

            ```
            S.pairs[i].token_a_pool * P * S.pairs[i].token_b_pool * P     S.pairs[i].total_supply * P
            --------------------------------------------------------- = ( --------------------------- )^2
            S.pairs[i].token_a_pool *     S.pairs[i].token_b_pool         S.pairs[i].total_supply
            ```

            But we also know that:

            ```
            S.pairs[i].token_a_pool * P * S.pairs[i].token_b_pool * P      T.pairs[i].token_a_pool * T.pairs[i].token_b_pool
            ---------------------------------------------------------  <=  -------------------------------------------------
            S.pairs[i].token_a_pool *     S.pairs[i].token_b_pool          S.pairs[i].token_a_pool * S.pairs[i].token_b_pool
            ```

            Finally, we know:

            ```
              T.pairs[i].total_supply          S.pairs[i].total_supply * P
            ( ----------------------- )^2 == ( --------------------------- )^2
              S.pairs[i].total_supply          S.pairs[i].total_supply
            ```

            Thus, we are done.

    -   Case 2.3 `[divest_liquidity]`
        In this case, the update rule for the `pairs` map is:

        ```
        <pairs> Pairs  => Pairs [ PairId <- LP(TotalShares -Nat Shares, CurrTokenA -Nat TokenAReq, CurrTokenB -Nat TokenBReq) ] </pairs>
        ```

        where:

        -   `Shares` is an entyrpoint parameter
        -   `LP(TotalShares, CurrTokenA, CurrTokenB) := Pairs[PairId]`
        -   `TokenAReq := Shares *Nat CurrTokenA /Nat TotalShares`
        -   `TokenBReq := Shares *Nat CurrTokenB /Nat TotalShares`

        By the liquidity shares consistency proof, we know that `Shares <= TotalShares`.
        We can prove that there exists a real number `0 <= P <= 1` such that:

        -   `TotalShares -Nat Shares == TotalShares *Real P`
        -   `CurrTokenA *Real P <= CurrTokenA -Nat Shares *Nat CurrTokenA /Nat TotalShares`
        -   `CurrTokenB *Real P <= CurrTokenB -Nat Shares *Nat CurrTokenB /Nat TotalShares`

        To see that invariant finally holds for all pairs, we do a case analysis:

        -   Case 2.3.1 `i != PairId`
            Then `S.token_a_pool[i] == T.token_a_pool[i] ∧ S.token_b_pool[i] == T.token_b_pool[i] ∧ S.total_supply[i] == T.total_supply[i]`, so the invariant holds for pair `i`.

        -   Case 2.3.2 `i == PairId`
            Then since:

            -   `S.total_suppply[i] * P == T.total_supply[i]`
            -   `S.token_a_pool[i] * P <= T.token_a_pool[i]`
            -   `S.token_b_pool[i] * P <= T.token_a_pool[i]`

            We proceed by case analysis:

            -   Case 2.3.2.1 `Shares == TotalShares`
                Then, the unique solution for `TotalShares -Nat Shares == TotalShares *Real P` is `P == 0`.
                Then, `S.total_supply[i] * P == 0 == T.total_supply[i]`.
                Thus, the invariant holds.

            -   Case 2.3.2.2 `Shares < TotalShares`
                Then, by algebra, we know that `P > 0`.
                In that case, the proof proceeds as in case 2.2.2.

    -   Case 2.4 `[swap]`
        In this case, the update rule for the `pairs` map is processed in a loop.
        We show that the invariant for the whole program above is _also_ an invariant for this loop.
        Clearly, it holds before the loop begins, by assumption.
        Thus, we just need to show that it still holds when the loop ends.
        Ihe loop input is parameterized by three values: `PairId:Nat`, `SwapDir:SwapType`, and `TokenIn:Nat` such that:

        -   `LP(TotalShares, TokenA, TokenB) := Pairs[PairId]`

        There are two cases:

        -   Case 2.4.1 `SwapDir == A_to_b`
            Then we have the following update rule:

            ```
            <pairs> Pairs => Pairs [ PairId <- LP(TotalShares, TokenA +Nat TokenIn,  TokenB -Nat TokenOut) ] </pairs>
            ```

            with `TokenOut := (TokenIn *Nat 997 *Nat TokenA) /Nat [(TokenB *Nat 1000) +Nat (TokenIn *Nat 997)]`.

        -   Case 2.4.2 `SwapDir == B_to_a`
            Then we have the following update rule:

            ```
            <pairs> Pairs => Pairs [ PairId <- LP(TotalShares, TokenA -Nat TokenOut, TokenB +Nat TokenIn ) ] </pairs>
            ```

            with `TokenOut := (TokenIn *Nat 997 *Nat TokenB) /Nat [(TokenA *Nat 1000) +Nat (TokenIn *Nat 997)]`.

        In either case, by arithmetic, we can prove the following:

        -   for a swap from `A` to `B`

            ```
            S.token_a_pool[PairId] * S.token_b_pool[PairId] == TokenA * TokenB
                                                            <= (TokenA +Nat TokenIn ) * (TokenB -Nat TokenOut)
                                                            == T.token_a_pool[PairId] * T.token_b_pool[PairId]
            ```

        -   for a swap from `B` to `A`

            ```
            S.token_a_pool[PairId] * S.token_b_pool[PairId] == TokenA * TokenB
                                                            <= (TokenA -Nat TokenOut) * (TokenB +Nat TokenIn )
                                                            == T.token_a_pool[PairId] * T.token_b_pool[PairId]
            ```

        Then, the union of these two cases gives us:

        ```
        S.token_a_pool[PairId] * S.token_b_pool[PairId] <= T.token_a_pool[PairId] * T.token_b_pool[PairId]
        ```

        To see that invariant finally holds for all pairs, we do a case analysis:

        -   Case 2.4.3 `i != PairId`
            Then `S.token_a_pool[i] == T.token_a_pool[i] ∧ S.token_b_pool[i] == T.token_b_pool[i]`, so the invariant holds for pair `i`.

        -   Case 2.4.4 `i == PairId`
            Then since `T.total_suppply[i] == S.total_supply[i]`, by our case analysis above, the loop invariant holds.

    -   Case 2.5 `[transfer]` or `[update_operators]` or `[balance_of]` or `[close]`
        By the _TTDex storage updates_ lemma, the `pairs` map is identical before and after rule application, as required.

### Maximum Divestment of Assets from Exchange is Token Pool Size

**Lemma:**
This property ensures that one asset cannot drain the entire token type asset reserves.
This property has two subcases for `divest_liquidity` and `swap`:

-   when divesting, the maximum amount of token _A_ (resp. token _B_) divested is the size of the token _A_ (resp. token _B_) pool for the given `pair_id`
-   when swapping, the maximum amount of tokens transferred out is bounded by:

    -   the size of token _B_ pool whne the final swap in the swaplist has direction _A-to-B_
    -   the size of token _A_ pool whne the final swap in the swaplist has direction _B-to-A_

    for the `pair_id` specified by the final swap

**Proof:**
These proofs follow from the structure of emitted transactions and the analysis done in the **subtractions implicitly guarded against underflow** condition.

### Contract Cannot Request Tez From Non-Sender Account (Safety):** the contract's operator privileges cannot be abused:

**Lemma:**
For each emitted transfer operation of the form:

```
FATransfer(TokenType, Address, TTDEX, Amount)
```

we require that `Address == Sender`.
Note that this also protects against malicious smart contracts which attmept to create a transaction on behalf of a user to steal their money.

**Proof:**
Simple inspection of the structure of emitted transactions show that this property holds.
