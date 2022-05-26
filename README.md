# A proof of [Stirling's formula](https://en.wikipedia.org/wiki/Stirling%27s_approximation) in [Lean](https://leanprover.github.io/)

We provide a proof of Stirling's formula in the following form:

$$n! = \sqrt{2\pi n}\left(\frac{n}{e}\right)^n.$$

More concretely, we define
```lean
noncomputable def an (n : ℕ) : ℝ  :=
  (n.factorial : ℝ) /
  ((real.sqrt(2*n)*((n/(exp 1)))^n))
```

and prove

```
lemma an_has_limit_sqrt_pi: tendsto
(λ (n : ℕ),  an n) at_top (𝓝 (sqrt π)) :=
```

We follow roughly [this proof](https://proofwiki.org/wiki/Stirling%27s_Formula).

Currently the proof is complete, but in very messy state.
We plan to clean and streamline the proof soon.

