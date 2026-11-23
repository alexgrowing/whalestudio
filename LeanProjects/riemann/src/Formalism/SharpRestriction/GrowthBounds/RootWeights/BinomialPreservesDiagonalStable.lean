import Formalism.SharpRestriction.GrowthBounds.RootWeights.NontrivialIsotypicWeightZeroKilled

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section
variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem isotypic_stable_under_gl_operator (E : GLOps n K V) (mu : Fin n → ℤ) (a b : Fin n) :
    ∀ x ∈ isoSub E mu, E a b x ∈ isoSub E mu := by
  unfold isoSub
  intro x hx
  have hle : Submodule.span K {x | ∃ u ∈ Umon E, ∃ v, IsHWV E mu v ∧ x = u v} ≤
      (Submodule.span K {x | ∃ u ∈ Umon E, ∃ v, IsHWV E mu v ∧ x = u v}).comap (E a b) := by
    rw [Submodule.span_le]
    rintro y ⟨u, hu, v, hv, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap]
    apply Submodule.subset_span
    refine ⟨E a b * u, ?_, v, hv, rfl⟩
    unfold Umon at hu ⊢
    exact Submonoid.mul_mem _ (Submonoid.subset_closure ⟨(a, b), rfl⟩) hu
  exact hle hx

theorem isotypic_sum_stable_gl_operator (E : GLOps n K V) (a b : Fin n) :
    ∀ x ∈ (⨆ mu : Fin n → ℤ, isoSub E mu), E a b x ∈ (⨆ mu : Fin n → ℤ, isoSub E mu) := by
  intro x hx
  have hle : (⨆ mu : Fin n → ℤ, isoSub E mu) ≤ (⨆ mu : Fin n → ℤ, isoSub E mu).comap (E a b) :=
    iSup_le fun mu y hy =>
      Submodule.mem_comap.mpr (Submodule.mem_iSup_of_mem mu (isotypic_stable_under_gl_operator E mu a b y hy))
  exact hle hx

theorem list_prod_preserves_submodule (W : Submodule K V) (l : List (Module.End K V))
    (h : ∀ u ∈ l, ∀ x ∈ W, u x ∈ W) : ∀ x ∈ W, l.prod x ∈ W := by
  induction l with
  | nil =>
    intro x hx
    simpa using hx
  | cons u l ih =>
    intro x hx
    rw [List.prod_cons]
    show u (l.prod x) ∈ W
    exact h u (by simp) _ (ih (fun v hv => h v (by simp [hv])) x hx)

theorem binomial_preserves_diagonal_stable (E : GLOps n K V) (W : Submodule K V) (hW : ∀ a, ∀ x ∈ W, E a a x ∈ W)
    (a : Fin n) (k : ℕ) : ∀ x ∈ W, binomE E a k x ∈ W := by
  unfold binomE
  intro x hx
  rw [LinearMap.smul_apply]
  apply W.smul_mem
  refine list_prod_preserves_submodule W _ ?_ x hx
  intro u hu
  simp only [List.mem_map, List.mem_range] at hu
  obtain ⟨j, -, rfl⟩ := hu
  intro y hy
  simp only [LinearMap.sub_apply, LinearMap.smul_apply]
  exact W.sub_mem (hW a y hy) (W.smul_mem _ (by simpa using hy))

theorem binomial_subring_preserves_stable (E : GLOps n K V) (W : Submodule K V) (hW : ∀ a, ∀ x ∈ W, E a a x ∈ W)
    (u : Module.End K V) (hu : u ∈ binomialDiagonalSubring E) : ∀ x ∈ W, u x ∈ W := by
  unfold binomialDiagonalSubring at hu
  let S : Subring (Module.End K V) :=
    { carrier := {u | ∀ x ∈ W, u x ∈ W}
      mul_mem' := fun {u v} hu hv x hx => hu _ (hv x hx)
      one_mem' := fun x hx => hx
      add_mem' := fun {u v} hu hv x hx => W.add_mem (hu x hx) (hv x hx)
      zero_mem' := fun x _ => W.zero_mem
      neg_mem' := fun {u} hu x hx => W.neg_mem (hu x hx) }
  have hle : Subring.closure {u | ∃ a k, u = binomE E a k} ≤ S := by
    rw [Subring.closure_le]
    rintro v ⟨a, k, rfl⟩
    exact binomial_preserves_diagonal_stable E W hW a k
  intro x hx
  exact (hle hu : u ∈ S) x hx

theorem weight_projection_mem_weightSpace (E : GLOps n K V) (hE : IsGLRep E) (Θ : (Fin n → ℤ) → Module.End K V)
    (hΘ : ∀ μ ν, ∀ x ∈ weightSp E ν, Θ μ x = if ν = μ then x else 0) (μ : Fin n → ℤ) (x : V) :
    Θ μ x ∈ weightSp E μ := by
  unfold IsGLRep at hE
  have hx : x ∈ ⨆ ν, weightSp E ν := by
    rw [hE.2.2]
    exact Submodule.mem_top
  have hle : (⨆ ν, weightSp E ν) ≤ (weightSp E μ).comap (Θ μ) := by
    refine iSup_le fun ν y hy => ?_
    rw [Submodule.mem_comap, hΘ μ ν y hy]
    split_ifs with h
    · subst h
      exact hy
    · exact Submodule.zero_mem _
  exact hle hx

theorem sum_weight_projections_eq_self (E : GLOps n K V) (hE : IsGLRep E) (Θ : (Fin n → ℤ) → Module.End K V)
    (hΘ : ∀ μ ν, ∀ x ∈ weightSp E ν, Θ μ x = if ν = μ then x else 0) (box : Finset (Fin n → ℤ))
    (hbox : ∀ ν, weightSp E ν ≠ ⊥ → ν ∈ box) (x : V) : ∑ μ ∈ box, Θ μ x = x := by
  unfold IsGLRep at hE
  have hx : x ∈ ⨆ ν, weightSp E ν := by
    rw [hE.2.2]
    exact Submodule.mem_top
  have hle : (⨆ ν, weightSp E ν) ≤ LinearMap.ker ((∑ μ ∈ box, Θ μ) - 1) := by
    refine iSup_le fun ν y hy => ?_
    have hy' : ∀ μ, Θ μ y = if ν = μ then y else 0 := fun μ => hΘ μ ν y hy
    rw [LinearMap.mem_ker]
    by_cases hν : weightSp E ν = ⊥
    · have h0 : y = 0 := by
        rw [hν] at hy
        exact (Submodule.mem_bot K).mp hy
      subst h0
      simp
    · simp [hy', hbox ν hν]
  have h := hle hx
  rw [LinearMap.mem_ker] at h
  simpa [sub_eq_zero] using h

def negHeightFunctional (ν : Fin n → ℤ) : ℤ := - ∑ c : Fin n, ((c : ℕ) : ℤ) * ν c

theorem negHeight_add_root (ν : Fin n → ℤ) (a b : Fin n) :
    negHeightFunctional (ν + rootW a b) = negHeightFunctional ν + (((b : ℕ) : ℤ) - ((a : ℕ) : ℤ)) := by
  unfold negHeightFunctional rootW
  simp only [Pi.add_apply, Pi.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

end

theorem sum_isotypic_top_of_weight_data (D : Formalism.BasicNotions.D7) (h2 : adm2 D) {K V : Type} [Field K] [CharZero K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {n : ℕ} (E : GLOps n K V) (hE : IsGLRep E) (hs : OperatorsShiftWeightsByRoots E)
    (hb : WeightsBounded E) (hθ : WeightProjectionsIntegralBinomial E) : IsotypicComponentsSpanModule E := by
  classical
  unfold IsotypicComponentsSpanModule
  obtain ⟨W', hc, hW'⟩ := h2 K V n E hE (⨆ mu : Fin n → ℤ, isoSub E mu) (fun a b => isotypic_sum_stable_gl_operator E a b)
  by_contra hne
  have hW'ne : W' ≠ ⊥ := by
    intro h0
    rw [h0] at hc
    exact hne (by simpa using hc.sup_eq_top)
  obtain ⟨x, hxW', hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW'ne
  obtain ⟨m, hm⟩ := hb
  obtain ⟨Θ, hΘm, hΘ⟩ := hθ
  set box : Finset (Fin n → ℤ) := Fintype.piFinset (fun _ : Fin n => Finset.Icc (-(m : ℤ)) m) with hboxdef
  have hbox : ∀ ν, weightSp E ν ≠ ⊥ → ν ∈ box := by
    intro ν hν
    rw [hboxdef, Fintype.mem_piFinset]
    intro a
    rw [Finset.mem_Icc]
    exact abs_le.1 (hm ν hν a)
  have hsum := sum_weight_projections_eq_self E hE Θ hΘ box hbox x
  have hex : ∃ ν ∈ box, Θ ν x ≠ 0 := by
    apply Finset.exists_ne_zero_of_sum_ne_zero
    rw [hsum]; exact hx0
  set S : Finset (Fin n → ℤ) := box.filter (fun ν => W' ⊓ weightSp E ν ≠ ⊥) with hS
  have hSne : S.Nonempty := by
    obtain ⟨ν, hν, hν0⟩ := hex
    refine ⟨ν, ?_⟩
    rw [hS, Finset.mem_filter]
    refine ⟨hν, fun hbot => hν0 ?_⟩
    have : Θ ν x ∈ W' ⊓ weightSp E ν :=
      ⟨binomial_subring_preserves_stable E W' (fun a => hW' a a) (Θ ν) (hΘm ν) x hxW', weight_projection_mem_weightSpace E hE Θ hΘ ν x⟩
    rw [hbot] at this
    simpa using this
  obtain ⟨ν, hνS, hmax⟩ := Finset.exists_max_image S negHeightFunctional hSne
  rw [hS, Finset.mem_filter] at hνS
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hνS.2
  have hraise : ∀ a b : Fin n, a < b → E a b y = 0 := by
    intro a b hab
    by_contra hne0
    have hmem : E a b y ∈ W' ⊓ weightSp E (ν + rootW a b) := ⟨hW' a b y hy.1, hs a b ν y hy.2⟩
    have h1 : W' ⊓ weightSp E (ν + rootW a b) ≠ ⊥ := by
      intro hbot
      rw [hbot] at hmem
      exact hne0 (by simpa using hmem)
    have h2' : weightSp E (ν + rootW a b) ≠ ⊥ := by
      intro hbot
      rw [hbot] at h1
      exact h1 (by simp)
    have h3 : ν + rootW a b ∈ S := by
      rw [hS, Finset.mem_filter]
      exact ⟨hbox _ h2', h1⟩
    have h4 := hmax _ h3
    rw [negHeight_add_root] at h4
    have h5 : ((a : ℕ) : ℤ) < ((b : ℕ) : ℤ) := by exact_mod_cast hab
    linarith
  have hhw : IsHWV E ν y := ⟨hy0, hy.2, hraise⟩
  have hyiso : y ∈ isoSub E ν := Submodule.subset_span ⟨1, (Umon E).one_mem, y, hhw, rfl⟩
  have hyW : y ∈ (⨆ mu : Fin n → ℤ, isoSub E mu) := (le_iSup (fun mu : Fin n → ℤ => isoSub E mu) ν) hyiso
  have : y ∈ (⨆ mu : Fin n → ℤ, isoSub E mu) ⊓ W' := ⟨hyW, hy.1⟩
  rw [hc.inf_eq_bot] at this
  exact hy0 (by simpa using this)

end Formalism.MainNotions.G.GLWeightTheory
