import Mathlib

-- 1. Az intervallum általános definíciója
def is_interval {R : Type*} [LE R] (S : Set R) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ z, x ≤ z → z ≤ y → z ∈ S

-- 2. A definíciószerű függvény predikátuma (Ideiglenes)
def DefinableFunction {R : Type*} (_f : R → R) : Prop := True

-- 3. ConstantOn és InjectiveOn definíciója
def ConstantOn {R : Type*} (f : R → R) (J : Set R) : Prop :=
  ∀ x ∈ J, ∀ y ∈ J, f x = f y

def InjectiveOn {R : Type*} (f : R → R) (J : Set R) : Prop :=
  ∀ x ∈ J, ∀ y ∈ J, f x = f y → x = y

-- =========================================================================
-- O-MINIMALITÁS AXIÓMÁI
-- =========================================================================

-- JAVÍTVA: Hozzáadva a [LinearOrder R] paraméter, hogy az is_interval működjön
axiom o_minimal_contains_interval {R : Type*} [LinearOrder R] {S : Set R} (h_inf : Set.Infinite S) :
  ∃ J ⊆ S, is_interval J ∧ Set.Infinite J

axiom infinite_image_of_injOn {R : Type*} {s : Set R} {f : R → R} :
  Set.Infinite s → Set.InjOn f s → Set.Infinite (f '' s)

-- =========================================================================

noncomputable def myInf {R : Type*} [LinearOrder R] [Nonempty R] (S : Set R) : R :=
  Classical.epsilon (fun x => x ∈ S ∧ ∀ y ∈ S, x ≤ y)

lemma myInf_spec {R : Type*} [LinearOrder R] [Nonempty R] {S : Set R}
    (hfin : S.Finite) (hne : S.Nonempty) :
    myInf S ∈ S ∧ ∀ z ∈ S, myInf S ≤ z := by
  have hex : ∃ x, x ∈ S ∧ ∀ y ∈ S, x ≤ y := by
    obtain ⟨x0, hx0⟩ := hne
    have hx0' : x0 ∈ hfin.toFinset := hfin.mem_toFinset.mpr hx0
    have hs_ne : hfin.toFinset.Nonempty := ⟨x0, hx0'⟩
    exact ⟨hfin.toFinset.min' hs_ne,
      hfin.mem_toFinset.mp (Finset.min'_mem _ hs_ne),
      fun z hz => Finset.min'_le _ z (hfin.mem_toFinset.mpr hz)⟩
  exact Classical.epsilon_spec hex

-- JAVÍTVA: A hI és hf_def kapott egy '_' előtagot a linter warningok elkerülésére
lemma lemma_0_5 {R : Type*} [LinearOrder R] [Nonempty R] {I : Set R}
  (_hI : is_interval I) (hI_inf : Set.Infinite I)
  (f : R → R) (_hf_def : DefinableFunction f) :
  ∃ J ⊆ I, is_interval J ∧ (ConstantOn f J ∨ InjectiveOn f J) := by

  by_cases h_inf_preimage : ∃ y : R, Set.Infinite (f ⁻¹' {y} ∩ I)

  · rcases h_inf_preimage with ⟨y, hy_inf⟩

    have h_contains_interval : ∃ J ⊆ (f ⁻¹' {y} ∩ I), is_interval J := by
      rcases o_minimal_contains_interval hy_inf with ⟨J, hJ_sub, hJ_int, _⟩
      exact ⟨J, hJ_sub, hJ_int⟩

    rcases h_contains_interval with ⟨J, hJ_sub, hJ_int⟩

    use J
    refine ⟨?_, hJ_int, Or.inl ?_⟩
    exact Set.Subset.trans hJ_sub Set.inter_subset_right

    unfold ConstantOn
    intro x hx z hz
    have hx_prop := (hJ_sub hx).left
    have hz_prop := (hJ_sub hz).left
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hx_prop hz_prop
    rw [hx_prop, hz_prop]

  · push Not at h_inf_preimage

    have h_fI_inf : Set.Infinite (f '' I) := by
      intro h_fin_img
      have h_I_fin : I.Finite := by
        apply Set.Finite.subset (Set.Finite.biUnion h_fin_img (fun y _ => h_inf_preimage y))
        intro x hx
        exact Set.mem_biUnion (Set.mem_image_of_mem f hx) ⟨rfl, hx⟩
      exact hI_inf h_I_fin

    -- JAVÍTVA: A 'by exact' szerkezet eltávolítva a linter warning miatt
    have h_fI_contains_interval : ∃ J_img ⊆ (f '' I), is_interval J_img ∧ Set.Infinite J_img :=
      o_minimal_contains_interval h_fI_inf

    rcases h_fI_contains_interval with ⟨J_img, hJ_img_sub, hJ_img_int, hJ_img_inf⟩

    let g : R → R := fun y => myInf {x ∈ I | f x = y}

    have h_finite_preimage : ∀ y : R, {x ∈ I | f x = y}.Finite := by
      intro y
      apply (h_inf_preimage y).subset
      rintro x ⟨hxI, hfx⟩
      exact ⟨hfx, hxI⟩

    have h_g_in_I : ∀ y ∈ J_img, g y ∈ I := by
      intro y hy
      unfold g
      have h_nonempty : {x ∈ I | f x = y}.Nonempty := by
        obtain ⟨x, hxI, hfx⟩ := hJ_img_sub hy
        exact ⟨x, hxI, hfx⟩
      exact (myInf_spec (h_finite_preimage y) h_nonempty).1.1

    have h_fg_eq : ∀ y ∈ J_img, f (g y) = y := by
      intro y hy
      unfold g
      have h_nonempty : {x ∈ I | f x = y}.Nonempty := by
        obtain ⟨x, hxI, hfx⟩ := hJ_img_sub hy
        exact ⟨x, hxI, hfx⟩
      exact (myInf_spec (h_finite_preimage y) h_nonempty).1.2

    have h_g_inj : Set.InjOn g J_img := by
      intro y1 hy1 y2 hy2 h_eq
      have h1 := h_fg_eq y1 hy1
      have h2 := h_fg_eq y2 hy2
      rw [← h1, ← h2, h_eq]

    have h_gJ_inf : Set.Infinite (g '' J_img) := infinite_image_of_injOn hJ_img_inf h_g_inj
    have h_gJ_contains_interval : ∃ J ⊆ (g '' J_img), is_interval J := by
      rcases o_minimal_contains_interval h_gJ_inf with ⟨J, hJ_sub, hJ_int, _⟩
      exact ⟨J, hJ_sub, hJ_int⟩

    rcases h_gJ_contains_interval with ⟨J, hJ_sub_gJ, hJ_int⟩

    have hJ_sub_I : J ⊆ I := by
      intro x hx
      rcases hJ_sub_gJ hx with ⟨y, hy, hgy⟩
      rw [← hgy]
      exact h_g_in_I y hy

    use J
    refine ⟨hJ_sub_I, hJ_int, Or.inr ?_⟩
    intro x1 hx1 x2 hx2 h_eq

    rcases hJ_sub_gJ hx1 with ⟨y1, hy1_in, hy1_eq⟩
    rcases hJ_sub_gJ hx2 with ⟨y2, hy2_in, hy2_eq⟩

    rw [← hy1_eq, ← hy2_eq] at h_eq
    rw [← hy1_eq, ← hy2_eq]

    have h1 := h_fg_eq y1 hy1_in
    have h2 := h_fg_eq y2 hy2_in

    have h_y_eq : y1 = y2 := by
      rw [← h1, ← h2]
      exact h_eq

    rw [h_y_eq]
