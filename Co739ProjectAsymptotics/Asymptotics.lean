import Mathlib.Tactic
import Mathlib.Data.Real.Basic

set_option warningAsError false


-- f(n) ∈ O(g(n))
-- Asymptotic upper bound: for large enough n,
-- |f(n)| is bounded above by a constant factor of |g(n)|
def InBigO (f g: ℝ → ℝ) : Prop :=
  ∃ c n₀, (0 < c ∧ 0 ≤ n₀) ∧ ∀ n, n₀ ≤ n → (|f n| ≤ c * |g n|)

-- f(n) ∈ Ω(g(n))
-- Asymptotic lower bound: for large enough n,
-- |f(n)| is bounded below by a constant factor of |g(n)|
def InBigOmega (f g: ℝ → ℝ) : Prop :=
  ∃ c n₀, (0 < c ∧ 0 ≤ n₀) ∧ ∀ n, n₀ ≤ n → (c * |g n| ≤ |f n|)


-- f(n) ∈ O(g(n)) iff g(n) ∈ Ω(f(n))
-- For the → direction, we can just use 1/c and the same n₀
-- to show InBigOmega. The other direction is similar.
theorem InBigO_reverse_InBigOmega {f g : ℝ → ℝ} :
    InBigO f g ↔ InBigOmega g f := by
  constructor
  -- Forward direction
  · rintro ⟨c₁, n₁, ⟨⟨h₁, h₂⟩, h₃⟩⟩
    use c₁⁻¹, n₁
    constructor
    · exact ⟨inv_pos.mpr h₁, h₂⟩
    intro n h

    -- Multiply by c₁ on both sides
    exact (inv_mul_le_iff h₁).mpr (h₃ n h)

  -- Backward direction
  rintro ⟨c₁, n₁, ⟨⟨h₁, h₂⟩, h₃⟩⟩
  use c₁⁻¹, n₁
  constructor
  · exact ⟨inv_pos.mpr h₁, h₂⟩
  intro n h
  specialize h₃ n h

  -- Again multiply by c₁ on both sides, but more work...
  rw [mul_comm] at h₃
  refine (inv_mul_le_iff (inv_pos.mpr h₁)).mp ?_
  rw [inv_inv, mul_comm]
  exact h₃


-- f(n) ∈ Θ(g(n))
-- Asymptotic tight bound: for large enough n, |f(n)| is
-- bounded both above and below by a constant factor of |g(n)|
def InBigTheta (f g: ℝ → ℝ) : Prop :=
  ∃ c₁ c₂ n₀, (0 < c₁ ∧ 0 < c₂ ∧ 0 ≤ n₀)
    ∧ ∀ n, n₀ ≤ n → (c₁ * |g n| ≤ |f n| ∧ |f n| ≤ c₂ * |g n|)


-- f(n) ∈ Θ(g(n)) iff f(n) ∈ O(g(n)) and f(n) ∈ O(g(n))
-- Obvious from the definition!
theorem InBigTheta_iff_InBigO_and_InBigOmega {f g : ℝ → ℝ} :
    InBigTheta f g ↔ (InBigO f g ∧ InBigOmega f g) := by
  constructor
  -- Forward direction
  · rintro ⟨c₁, c₂, n₀, ⟨⟨h₁, h₂, h₃⟩, h₄⟩⟩
    constructor
    -- Show f(n) ∈ O(g(n))
    · use c₂, n₀
      constructor
      · exact ⟨h₂, h₃⟩
      intro n h'
      exact (h₄ n h').right

    -- Show f(n) ∈ Ω(g(n))
    use c₁, n₀
    constructor
    · exact ⟨h₁, h₃⟩
    intro n h'
    exact (h₄ n h').left

  -- Backward direction
  rintro ⟨⟨c₀, n₀, ⟨⟨h₁, h₂⟩, h₃⟩⟩, ⟨c₁, n₁, ⟨⟨h₄, h₅⟩, h₆⟩⟩⟩
  let n' := max n₀ n₁
  -- Proof terms to prove inequalities later
  have m₀ := le_max_left n₀ n₁
  have m₁ := le_max_right n₀ n₁
  use c₁, c₀, n'
  constructor
  · exact ⟨h₄, h₁, (le_trans h₂ m₀)⟩
  intro n h'
  constructor
  · exact h₆ n (le_trans m₁ h')
  exact h₃ n (le_trans m₀ h')

-- f(n) ∈ Θ(g(n)) iff g(n) ∈ Θ(f(n))
-- Follows immediately from the two previous theorems.
theorem InBigTheta_symm {f g : ℝ → ℝ} :
    InBigTheta f g ↔ InBigTheta g f := by
  -- The two directions are symmetric. Prove one and use it twice!
  have h (f₀ g₀ : ℝ → ℝ) : InBigTheta f₀ g₀ → InBigTheta g₀ f₀ := by
    intro H
    rw [InBigTheta_iff_InBigO_and_InBigOmega] at H
    rcases H with ⟨H₁, H₂⟩
    -- Convert the "Big O" and "Big Omega" to the other way around
    rw [InBigO_reverse_InBigOmega] at H₁
    rw [← InBigO_reverse_InBigOmega] at H₂
    exact InBigTheta_iff_InBigO_and_InBigOmega.mpr ⟨H₂, H₁⟩

  exact ⟨h f g, h g f⟩


-- f(n) ∈ o(g(n))
-- Asymptotically strictly smaller: for large enough n,
-- |f(n)| is bounded above by *any* constant factor of |g(n)|
-- (n₀ can depend on c)
def InLittleO (f g: ℝ → ℝ) : Prop :=
  ∀ c, 0 < c → ∃ n₀, 0 ≤ n₀ ∧ ∀ n, n₀ ≤ n → |f n| ≤ c * |g n|

-- f(n) ∈ ω(g(n))
-- Asymptotically strictly larger: for large enough n,
-- |f(n)| is bounded above by *any* constant factor of |g(n)|
def InLittleOmega (f g: ℝ → ℝ) : Prop :=
  ∀ c, 0 < c → ∃ n₀, 0 ≤ n₀ ∧ ∀ n, n₀ ≤ n → c * |g n| ≤ |f n|


-- f(n) ∈ o(g(n)) iff g(n) ∈ ω(g(n))
-- o/ω analogue for how f(n) ∈ O(g(n)) iff g(n) ∈ Ω(f(n))
-- Again, we use 1/c and the same n₀ for both directions
theorem InLittleO_reverse_InLittleOmega {f g : ℝ → ℝ} :
    InLittleO f g ↔ InLittleOmega g f := by
  constructor
  -- Forward direction
  · intro H
    intro c h'
    rcases H c⁻¹ (inv_pos.mpr h') with ⟨n, h'', h₁⟩
    use n, h''
    intro n' h'''
    specialize h₁ n' h'''

    -- Divide by c on both sides
    rw [mul_comm] at h₁
    exact (le_div_iff' h').mp h₁

  -- Backward direction
  intro H
  intro c h'
  rcases H c⁻¹ (inv_pos.mpr h') with ⟨n, h'', h₁⟩
  use n, h''
  intro n' h'''
  specialize h₁ n' h'''

  -- Divide by c on both sides
  exact (inv_mul_le_iff h').mp h₁

-- f(n) ∈ o(g(n)) implies f(n) ∈ O(g(n))
-- Pick any c, use the same n₀, and the result follows!
theorem InBigO_of_InLittleO {f g : ℝ → ℝ}
    (H : InLittleO f g) : InBigO f g := by
  let c := (1 : ℝ)
  have h : 0 < c := by norm_num
  use c
  rcases H c h with ⟨n₀, h', H'⟩
  use n₀

-- f(n) ∈ ω(g(n)) implies f(n) ∈ Ω(g(n))
-- The previous theorem but for ω -> Ω.
theorem InBigOmega_of_InLittleOmega {f g : ℝ → ℝ}
    (H : InLittleOmega f g) : InBigOmega f g := by
  let c := (1 : ℝ)
  have h : 0 < c := by norm_num
  use c
  rcases H c h with ⟨n₀, h', H'⟩
  use n₀


-- More rules about order notation follow.
-- Some of them only apply to (eventually) positive functions,
-- which require the following definitions:
def Positive (f : ℝ → ℝ) : Prop :=
  ∀ n, 0 < f n

def EventuallyPositive (f: ℝ → ℝ) : Prop :=
  ∃ n₀, 0 ≤ n₀ ∧ ∀ n, n₀ ≤ n → 0 < f n


-- For eventually positive functions f and g,
-- f(n) ∈ o(g(n)) implies f(n) ∉ Ω(g(n))
theorem not_InBigOmega_of_InLittleO {f g : ℝ → ℝ}
    (H₁ : InLittleO f g) (H₂ : EventuallyPositive f)
    (H₃ : EventuallyPositive g) : ¬ InBigOmega f g := by
  -- Proof by contradiction
  by_contra H'
  rcases H' with ⟨c₀, n₀, ⟨h₁, h₂⟩, H'⟩
  specialize H₁ (c₀/2) (div_pos h₁ (by norm_num))
  rcases H₁ with ⟨n₁, h₃, H₁⟩
  rcases H₃ with ⟨n₂, h₄, H₃⟩
  -- Pick a large enough n so all the inequalities that we need apply.
  -- For that, we need chain some ≤-inequalities together
  let n := max (max n₀ n₁) n₂
  specialize H' n (le_trans (le_max_left n₀ n₁) (le_max_left (max n₀ n₁) n₂))
  specialize H₁ n (le_trans (le_max_right n₀ n₁) (le_max_left (max n₀ n₁) n₂))

  -- Now, we have c₀ * |g n| ≤ |f n| ≤ c₀ / 2 * |g n|.
  -- We can soon show that c₀ is negative
  have h₀ : c₀ * |g n| ≤ c₀ / 2 * |g n| := le_trans H' H₁
  have h₅ : 0 < |g n| := by
    apply abs_pos_of_pos
    exact H₃ n (le_max_right (max n₀ n₁) n₂)
  have h₆ : c₀ ≤ c₀ / 2 := by
    exact le_of_mul_le_mul_right h₀ h₅

  -- let linarith derive a contradiction from
  -- h₁ : 0 < c₀ and h₆ : c₀ ≤ c₀ / 2
  linarith

-- Identity: f(n) ∈ Θ(f(n))
theorem InBigTheta_identity (f: ℝ → ℝ) : (InBigTheta f f) := by
  use 1, 1, 0
  norm_num

-- Constant multiplication: K * f(n) ∈ Θ(f(n))
theorem InBigTheta_const_mul (f : ℝ → ℝ) {K : ℝ} (h : 0 < K) :
    (InBigTheta (fun x ↦ K * f x) f) := by
  use K, K, 0
  norm_num
  use h
  intro n _
  -- Since it's ≤ both ways, we can just prove equality
  apply le_antisymm_iff.mp
  rw [abs_mul, abs_of_pos h]

-- Transitivity: f(n) ∈ O(g(n)) and g(n) ∈ O(h(n))
-- implies f(n) ∈ O(h(n))
theorem InBigO_trans {f g h : ℝ → ℝ}
    (H₁ : InBigO f g) (H₂ : InBigO g h) : InBigO f h := by
  rcases H₁ with ⟨c₁, n₁, ⟨⟨h₁, h₂⟩, h₃⟩⟩
  rcases H₂ with ⟨c₂, n₂, ⟨⟨h₄, h₅⟩, h₆⟩⟩

  let c' := c₁ * c₂
  let n' := max n₁ n₂

  -- Proof terms for inequalities later
  have m₁ := le_max_left n₁ n₂
  have m₂ := le_max_right n₁ n₂

  use c', n'
  constructor
  · constructor
    · exact mul_pos h₁ h₄
    exact le_trans h₂ m₁

  intro n h'
  -- Chain the inequalities: |f n| ≤ c₁ * |g n| ≤ c₁ * c₂ * |h n|
  calc
    |f n| ≤ c₁ * |g n| := h₃ n (le_trans m₁ h')
    _ ≤ c₁ * (c₂ * |h n|) :=
      mul_le_mul_of_nonneg_left (h₆ n (le_trans m₂ h')) (le_of_lt h₁)
    _ = (c₁ * c₂) * |h n| := by ring

-- Transitivity also holds for other order notations,
-- but we'll just prove it for Ω as well
theorem InBigOmega_trans {f g h : ℝ → ℝ}
    (H₁ : InBigOmega f g) (H₂ : InBigOmega g h) : InBigOmega f h := by
  -- Use InBigO transitivity! Convert every Big Omega to Big O
  apply InBigO_reverse_InBigOmega.mpr at H₁
  apply InBigO_reverse_InBigOmega.mpr at H₂
  apply InBigO_reverse_InBigOmega.mp
  exact InBigO_trans H₂ H₁

-- Addition: if f₁(n) ∈ O(g₁(n)) and f₂(n) ∈ O(g₂(n)),
-- then f₁(n) + f₂(n) ∈ O(g₁(n) + g₂(n))
theorem InBigO_add {f₁ g₁ f₂ g₂ : ℝ → ℝ}
    (H₁ : InBigO f₁ g₁) (H₂ : InBigO f₂ g₂)
    (H₃ : EventuallyPositive g₁) (H₄ : EventuallyPositive g₂) :
    InBigO (fun n ↦ f₁ n + f₂ n) (fun n ↦ g₁ n + g₂ n) := by
  rcases H₁ with ⟨c₁, n₁, ⟨⟨h₁, h₂⟩, H₁⟩⟩
  rcases H₂ with ⟨c₂, n₂, ⟨⟨h₃, h₄⟩, H₂⟩⟩
  rcases H₃ with ⟨n₃, h₅, H₃⟩
  rcases H₄ with ⟨n₄, h₆, H₄⟩

  let n₀ := max (max n₁ n₂) (max n₃ n₄)
  let c₀ := max c₁ c₂
  have c₀_pos : c₀ > 0 := lt_of_le_of_lt' (le_max_left c₁ c₂) h₁
  use c₀, n₀
  dsimp

  constructor
  -- Chain ≤-inequalities...
  · constructor
    · exact c₀_pos
    apply le_trans h₂
    apply le_trans (le_max_left n₁ n₂)
    exact (le_max_left (max n₁ n₂) (max n₃ n₄))

  intro n h'
  have H₅ : max n₁ n₂ ≤ n := le_of_max_le_left h'
  specialize H₁ n (le_trans (le_max_left n₁ n₂) H₅)
  specialize H₂ n (le_trans (le_max_right n₁ n₂) H₅)

  -- Work with assumptions to get g₁ n, g₂ n > 0
  have H₆ : max n₃ n₄ ≤ n := le_of_max_le_right h'
  have g₁_n_pos : 0 < g₁ n := by
    exact H₃ n (le_trans (le_max_left n₃ n₄) H₆)
  have g₂_n_pos : 0 < g₂ n := by
    exact H₄ n (le_trans (le_max_right n₃ n₄) H₆)
  have g₁_n_abs : |g₁ n| = g₁ n := abs_of_pos g₁_n_pos
  have g₂_n_abs : |g₂ n| = g₂ n := abs_of_pos g₂_n_pos

  -- Now, we have to show |f₁ n + f₂ n| ≤ c₀ * |g₁ n + g₂ n|
  calc
    |f₁ n + f₂ n| ≤ |f₁ n| + |f₂ n| := abs_add (f₁ n) (f₂ n)
    _ ≤ c₁ * |g₁ n| + c₂ * |g₂ n| :=  add_le_add H₁ H₂

    _ ≤ c₀ * |g₁ n| + c₀ * |g₂ n| := by
      -- Show c₁ * |g₁ n| ≤ c₀ * |g₁ n|
      -- and c₂ * |g₂ n| ≤ c₀ * |g₂ n| separately
      apply add_le_add
      · apply (mul_le_mul_right (abs_pos_of_pos g₁_n_pos)).mpr
        exact le_max_left c₁ c₂
      apply (mul_le_mul_right (abs_pos_of_pos g₂_n_pos)).mpr
      exact le_max_right c₁ c₂

    _ = c₀ * (|g₁ n| + |g₂ n|) := by ring
    _ = c₀ * |g₁ n + g₂ n| := by
      apply congrArg (fun x ↦ c₀ * x)
      -- Everything inside |⬝| is positive...
      calc
        |g₁ n| + |g₂ n| = g₁ n + g₂ n := by rw [g₁_n_abs, g₂_n_abs]
        _ = |g₁ n + g₂ n| := by
          symm
          apply abs_of_pos
          exact add_pos g₁_n_pos g₂_n_pos


-- Maximum rule: If h(n) ∈ O(f(n) + g(n)),
-- then h(n) ∈ O(max(f(n), g(n)))
theorem InBigO_of_max {f g h : ℝ → ℝ}
    (H₁ : InBigO h (fun n ↦ f n + g n))
    (H₂ : EventuallyPositive f) (H₃ : EventuallyPositive g)
    : InBigO h (fun n ↦ max (f n) (g n)) := by
  rcases H₁ with ⟨c₀, n₀, ⟨⟨h₁, h₂⟩, H₁⟩⟩
  rcases H₂ with ⟨n₂, h₃, H₂⟩
  rcases H₃ with ⟨n₃, h₄, H₃⟩
  dsimp at H₁

  -- Choose c = 2 * c₀, because f(n) + g(n) ≤ 2 * max(f(n), g(n))
  use 2 * c₀, max n₀ (max n₂ n₃)

  constructor
  -- Inequalities
  · norm_num
    exact ⟨h₁, Or.inl h₂⟩

  intro n h'
  calc
    |h n| ≤ c₀ * |f n + g n| := by
      exact H₁ n (le_trans (le_max_left n₀ (max n₂ n₃)) h')

    _ ≤ c₀ * |2 * max (f n) (g n)| := by
      apply (mul_le_mul_left h₁).mpr

      -- Remove the absolute values by showing everything is positive
      have f_n_pos : 0 < f n := by
        exact H₂ n (le_trans (le_max_left n₂ n₃) (le_trans (le_max_right n₀ (max n₂ n₃)) h'))
      have g_n_pos : 0 < g n := by
        exact H₃ n (le_trans (le_max_right n₂ n₃) (le_trans (le_max_right n₀ (max n₂ n₃)) h'))

      apply abs_le_abs_of_nonneg
      · apply le_of_lt
        exact add_pos f_n_pos g_n_pos

      -- f(n) ≤ max(f(n), g(n)) and g(n) ≤ max(f(n), g(n))
      rw [two_mul]
      apply add_le_add
      · exact le_max_left (f n) (g n)
      exact le_max_right (f n) (g n)

    _ = 2 * c₀ * |max (f n) (g n)| := by
      rw [abs_mul]
      norm_num
      ring


-- Two interesting assignment questions from S24 offering

-- Prove: For positive functions f, g, h, if f(n), h(n) ∈ Θ(g(n)),
-- then f(n) / h(n) ∈ Θ(1)
example (f g h : ℝ → ℝ) (H₁ : InBigTheta f g) (H₂ : InBigTheta h g)
    (H₃ : Positive f) (H₄ : Positive g) (H₅ : Positive h)
    : InBigTheta (fun n ↦ (f n) / (h n)) 1 := by
  -- Break down Big Theta to Big O and Big Omega
  rw [InBigTheta_iff_InBigO_and_InBigOmega] at H₁
  rw [InBigTheta_iff_InBigO_and_InBigOmega] at H₂

  rcases H₁ with ⟨h₁, h₂⟩
  rcases H₂ with ⟨h₃, h₄⟩

  -- We prove Big O and Big Omega separately
  apply InBigTheta_iff_InBigO_and_InBigOmega.mpr

  constructor
  -- We will use f(n) ∈ O(g(n)) and h(n) ∈ Ω(g(n))
  -- to show f(n)/h(n) ∈ O(1)
  · rcases h₁ with ⟨c₁, n₁, ⟨⟨q₁, q₂⟩, h₁⟩⟩
    rcases h₄ with ⟨c₂, n₂, ⟨⟨q₃, q₄⟩, h₄⟩⟩

    let c₃ := c₁ / c₂
    let n₃ := max n₁ n₂
    use c₃, n₃

    constructor
    -- Inequalities
    · constructor
      · exact div_pos q₁ q₃
      exact le_trans q₂ (le_max_left n₁ n₂)

    intro n h'
    norm_num
    unfold_let c₃
    rw [abs_div]

    specialize h₁ n (le_trans (le_max_left n₁ n₂) h')
    specialize h₄ n (le_trans (le_max_right n₁ n₂) h')

    -- The absolute values are superfluous,
    -- but we won't bother removing them.
    -- Show f(n)/h(n) ≤ (c₁ * g(n)) / (c₂ * g(n)) = c₁/c₂
    calc
      -- Use |f(n)| ≤ c₁ * |g(n)|
      |f n| / |h n| ≤ c₁ * |g n| / |h n| := by
        apply (div_le_div_right (abs_pos_of_pos (H₅ n))).mpr
        exact h₁

      -- Use |h(n)| ≥ c₂ * |g(n)|
      _ ≤ (c₁ * |g n|) / (c₂ * |g n|) := by
        apply div_le_div
        · exact le_trans (abs_nonneg (f n)) h₁
        · rfl
        · exact mul_pos q₃ (abs_pos_of_pos (H₄ n))
        exact h₄

      -- Cancel out |g(n)|
      _ = c₁ / c₂ :=
        mul_div_mul_right c₁ c₂ (ne_of_gt (abs_pos_of_pos (H₄ n)))

  -- We will use f(n) ∈ Ω(g(n)) and h(n) ∈ O(g(n))
  -- to show f(n)/h(n) ∈ Ω(1)
  rcases h₂ with ⟨c₁, n₁, ⟨⟨q₁, q₂⟩, h₂⟩⟩
  rcases h₃ with ⟨c₂, n₂, ⟨⟨q₃, q₄⟩, h₃⟩⟩

  let c₃ := c₁ / c₂
  let n₃ := max n₁ n₂
  use c₃, n₃

  constructor
  -- Inequalities
  · constructor
    · exact div_pos q₁ q₃
    exact le_trans q₂ (le_max_left n₁ n₂)

  intro n h'
  norm_num
  unfold_let c₃
  rw [abs_div]

  specialize h₂ n (le_trans (le_max_left n₁ n₂) h')
  specialize h₃ n (le_trans (le_max_right n₁ n₂) h')

  -- Show f(n)/h(n) ≥ (c₁ * g(n)) / (c₂ * g(n)) = c₁/c₂
  calc
    -- Use |f(n)| ≥ c₁ * |g(n)|
    |f n| / |h n| ≥ c₁ * |g n| / |h n| := by
      apply ge_iff_le.mpr
      apply (div_le_div_right (abs_pos_of_pos (H₅ n))).mpr
      exact h₂

    -- Use |h(n)| ≤ c₂ * |g(n)|
    _ ≥ c₁ * |g n| / (c₂ * |g n|) := by
      apply ge_iff_le.mpr
      apply div_le_div
      · apply le_of_lt
        apply mul_pos q₁ (abs_pos_of_pos (H₄ n))
      · rfl
      · exact abs_pos_of_pos (H₅ n)
      exact h₃

    -- Cancel out |g(n)|
    _ = c₁ / c₂ :=
      mul_div_mul_right c₁ c₂ (ne_of_gt (abs_pos_of_pos (H₄ n)))


-- Prove: For positive functions f and g, we have that
-- min(f(n), g(n)) ∈ Θ(f(n) g(n) / (f(n) + g(n)))

-- A lemma we'll use later
lemma prod_div_max (a b : ℝ) (H₁ : a > 0) :
    a * b / max a b = min a b := by
  -- h₁ is just a matter of possibly reordering terms
  have h₁ : a * b = min a b * max a b := by
    exact (min_mul_max a b).symm

  have h₂ : max a b ≠ 0 := by
    exact ne_of_gt (lt_max_of_lt_left H₁)

  exact (eq_div_of_mul_eq h₂ h₁.symm).symm

example (f g : ℝ → ℝ) (H₁ : Positive f) (H₂ : Positive g) :
    InBigTheta (fun n ↦ min (f n) (g n))
               (fun n ↦ ((f n * g n) / (f n + g n))) := by
  -- We prove the equivalent statement that
  -- f(n) g(n) / (f(n) + g(n)) ∈ Θ(min(f(n), g(n)))
  apply InBigTheta_symm.mpr

  -- Prove Big O and Big Omega separately
  apply InBigTheta_iff_InBigO_and_InBigOmega.mpr

  constructor
  -- Show f(n) g(n) / (f(n) + g(n)) ∈ O(min(f(n), g(n)))
  · use 1, 0
    norm_num

    intro n h'
    specialize H₁ n
    specialize H₂ n

    -- First trick: max is less than the sum
    have h₁ : max (f n) (g n) ≤ f n + g n := by
      exact max_le_add_of_nonneg (le_of_lt H₁) (le_of_lt H₂)

    calc
      -- Remove absolute value
      |(f n * g n) / (f n + g n)| = (f n * g n) / (f n + g n) := by
        apply abs_of_pos
        apply div_pos
        · exact mul_pos H₁ H₂
        exact add_pos H₁ H₂

      -- Use h₁ : max (f n) (g n) ≤ f n + g n
      _ ≤ (f n * g n) / (max (f n) (g n)) := by
        apply div_le_div_of_nonneg_left
        apply le_of_lt
        exact mul_pos H₁ H₂
        exact lt_max_of_lt_left H₁
        exact h₁

      -- Use lemma
      _ = min (f n) (g n) := prod_div_max (f n) (g n) H₁

      -- Put absolute value back
      _ = |min (f n) (g n)| := (abs_of_pos (lt_min H₁ H₂)).symm

  -- Show f(n) g(n) / (f(n) + g(n)) ∈ Ω(min(f(n), g(n)))
  use 1/2, 0
  norm_num

  intro n h'
  specialize H₁ n
  specialize H₂ n

  -- Second trick: sum is less than twice the max
  have h₂ : f n + g n ≤ 2 * max (f n) (g n) := by
    rw [two_mul]
    apply add_le_add
    · exact le_max_left (f n) (g n)
    exact le_max_right (f n) (g n)

  calc
    -- Remove absolute value
    |(f n * g n) / (f n + g n)| = (f n * g n) / (f n + g n) := by
      apply abs_of_pos
      apply div_pos
      exact mul_pos H₁ H₂
      exact add_pos H₁ H₂

    -- Use h₂
    _ ≥ (f n * g n) / (2 * max (f n) (g n)) := by
      apply div_le_div_of_nonneg_left
      · apply le_of_lt
        exact mul_pos H₁ H₂
      · exact add_pos H₁ H₂
      exact h₂

    -- Take 1/2 out
    _ = 1/2 * ((f n * g n) / max (f n) (g n)) := by
      rw [← mul_div_assoc, mul_comm (1/2),
          mul_div_assoc (f n * g n), div_div]
      exact div_eq_mul_one_div (f n * g n) (2 * max (f n) (g n))

    -- Use lemma
    _ = 1/2 * min (f n) (g n) := by
      apply congrArg (fun x ↦ (1 / 2) * x)
      exact prod_div_max (f n) (g n) H₁

    -- Put absolute value back
    _ = 1/2 * |min (f n) (g n)| := by
      apply congrArg (fun x ↦ (1 / 2) * x)
      symm
      apply abs_of_pos
      exact lt_min H₁ H₂
