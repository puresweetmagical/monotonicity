import Mathlib

open Set

-- The DenselyOrdered condition is essential for the continuity/supremum argument!
variable {α β R : Type*} [ConditionallyCompleteLinearOrder R] [DenselyOrdered R]

def IsConstantOn (f : α → β) (S : Set α) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, f x = f y

theorem constant_union {f : α → β} {S T : Set α} {c : α}
  (hcS : c ∈ S) (hcT : c ∈ T)
  (hS : IsConstantOn f S) (hT : IsConstantOn f T) :
  IsConstantOn f (S ∪ T) := by
  intro x hx y hy
  cases hx with
  | inl hxS =>
    cases hy with
    | inl hyS => 
      exact hS x hxS y hyS
    | inr hyT =>
      have h1 : f x = f c := hS x hxS c hcS
      have h2 : f c = f y := hT c hcT y hyT
      rw [h1, h2]
  | inr hxT =>
    cases hy with
    | inl hyS =>
      have h1 : f x = f c := hT x hxT c hcT
      have h2 : f c = f y := hS c hcS y hyS
      rw [h1, h2]
    | inr hyT =>
      exact hT x hxT y hyT

def IsLocallyConstantAt (f : R → R) (x : R) : Prop :=
  ∃ c d : R, c < x ∧ x < d ∧ IsConstantOn f (Ioo c d)

theorem monotonicity_case1 (a b : R) (hab : a < b) (f : R → R)
  (h_case1 : ∀ x ∈ Ioo a b, IsLocallyConstantAt f x) :
  IsConstantOn f (Ioo a b) := by

  have h_right : ∀ x₀ ∈ Ioo a b, IsConstantOn f (Ico x₀ b) := by
    intro x₀ hx₀
    -- Definition of S: the set of points x for which the function is constant on [x₀, x]
    let S := {x | x₀ < x ∧ x ≤ b ∧ IsConstantOn f (Ico x₀ x)}
    let s := sSup S
    
    -- S is bounded above by b
    have hS_bdd : BddAbove S := by
      use b
      intro y hy
      exact hy.2.1

    -- S is non-empty because f is locally constant at x₀
    have hS_nonempty : S.Nonempty := by
      rcases h_case1 x₀ hx₀ with ⟨c, d, hc_lt_x0, hx0_lt_d, h_const_cd⟩
      -- The exact proof steps go here (proving denseness and interval subsets)
      sorry

    -- Proof by contradiction: show that s = b
    have hs_eq_b : s = b := by
      by_contra h_neq
      have hs_le_b : s ≤ b := csSup_le hS_nonempty (by intro y hy; exact hy.2.1)
      have hs_lt_b : s < b := lt_of_le_of_ne hs_le_b h_neq

      have hs_in_Ioo : s ∈ Ioo a b := by
        -- Proof that a < s and s < b
        sorry
      
      rcases h_case1 s hs_in_Ioo with ⟨c, d, hc_lt_s, hs_lt_d, h_const_cd⟩
      
      have h_overlap : ∃ x ∈ S, c < x := by
        -- Using the supremum property (exists_lt_of_lt_csSup)
        sorry
      
      -- Completing the contradiction (proving y is constant up to a point > s, meaning y ∈ S)
      sorry

    -- Extension to b (using continuity or boundary properties)
    sorry

  have h_left : ∀ x₀ ∈ Ioo a b, IsConstantOn f (Ioc a x₀) := by
    intro x₀ hx₀
    -- Analogous infimum (sInf) argument going leftwards towards a
    sorry

  -- Proving global equality by gluing the left and right intervals together
  intro x hx y hy
  sorry