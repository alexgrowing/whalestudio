import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArithVarHasHhUnique

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

namespace GlobalTheory.CovTest.SwapZ

section Reindex

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {ι κ : Type} [Fintype ι] [Fintype κ]

theorem rename_lin (e : κ ≃ ι) (m : ι → ℝ) : rename e (lin fun j => m (e j)) = lin m := by
  simp only [lin, map_sum, map_mul, rename_C, rename_X]
  exact e.sum_comp fun i => C (m i) * MvPolynomial.X i

theorem isometric_comb_equiv (e : κ ≃ ι) {L : ι → HermLB p} {M : κ → HermLB p} (h : ∀ j, (M j).Isometric (L (e j)))
    (n : κ → ℤ) : (comb L fun i => n (e.symm i)).Isometric (comb M n) :=
  HermLB.icls_eq_iff.1 (by
    rw [icls_comb, icls_comb, ← e.sum_comp]
    simp only [Equiv.symm_apply_apply, fun j => HermLB.icls_eq_iff.2 (h j)])

theorem rename_lin_int (e : κ ≃ ι) (n : κ → ℤ) :
    rename e (lin fun j => (n j : ℝ)) = lin fun i => (n (e.symm i) : ℝ) := by
  rw [← rename_lin e]
  simp only [Equiv.symm_apply_apply]

theorem isArFun_equiv [IsIntegral X] {D : ℕ} (hX : IsArithVar p D) (e : κ ≃ ι) {L : ι → HermLB p} {M : κ → HermLB p}
    (h : ∀ j, (M j).Isometric (L (e j))) {Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ} (hΦ : IsArFun L D Φ) :
    IsArFun M D (Φ ∘ₗ (rename e : MvPolynomial κ ℝ →ₐ[ℝ] MvPolynomial ι ℝ).toLinearMap) := by
  refine ⟨fun n => ?_, fun P d hd hP => hΦ.2 _ d hd hP.rename_isHomogeneous⟩
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_pow, rename_lin_int]
  exact (isometric_comb_equiv e h n).isSelfInter hX (hΦ.1 _)

theorem isGeoFun_equiv {D : ℕ} (e : κ ≃ ι) {L : ι → HermLB p} {M : κ → HermLB p}
    (h : ∀ j, (M j).Isometric (L (e j))) {Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ} (hΨ : IsGeoFun L D Ψ) :
    IsGeoFun M D (Ψ ∘ₗ (rename e : MvPolynomial κ ℝ →ₐ[ℝ] MvPolynomial ι ℝ).toLinearMap) := by
  refine ⟨fun n => ?_, fun P d hd hP => hΨ.2 _ d hd hP.rename_isHomogeneous⟩
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_pow, rename_lin_int]
  exact (hΨ.1 _).trans ((isometric_comb_equiv e h n).gdeg_eq D)

theorem rename_swapPol (e : κ ≃ ι) (G : ℕ → ℤ → ℤ → MvPolynomial (Fin 3) ℝ) (D : ℕ) (x y : κ) (n : ι → ℤ) :
    rename e (swapPol G D x y fun j => n (e j)) = swapPol G D (e x) (e y) n := by
  rw [swapPol, swapPol, ← AlgHom.comp_apply, comp_aeval]
  congr 2
  funext i
  fin_cases i
  · simp
  · simp
  · simp only [Fin.reduceFinMk, Matrix.cons_val]
    rw [← rename_lin e]
    simp only [e.injective.eq_iff]

end Reindex

def degFlLin (ι : Type) [Fintype ι] (N : ℕ) : MvPolynomial (ι × Fin N) ℝ →ₗ[ℝ] ℝ :=
  ((-1 : ℝ) ^ dimFl ι N) •
    ∑ σ : ι → Equiv.Perm (Fin N), (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) • lcoeff ℝ (permExp σ)

theorem degFlLin_apply (ι : Type) [Fintype ι] (N : ℕ) (P : MvPolynomial (ι × Fin N) ℝ) :
    degFlLin ι N P = degFl ι N P := by
  simp [degFlLin, degFl, LinearMap.sum_apply]

theorem degree_permExp {ι : Type} [Fintype ι] {N : ℕ} (σ : ι → Equiv.Perm (Fin N)) :
    (permExp σ).degree = dimFl ι N := by
  rw [Finsupp.degree_eq_sum, Fintype.sum_prod_type, dimFl]
  have h : ∀ τ, ∑ i : Fin N, permExp σ (τ, i) = N * (N - 1) / 2 := by
    intro τ
    have h1 : ∑ i : Fin N, permExp σ (τ, i) = ∑ i : Fin N, (N - 1 - (i : ℕ)) :=
      Equiv.sum_comp (σ τ) (fun i : Fin N => N - 1 - (i : ℕ))
    rw [h1, Fin.sum_univ_eq_sum_range (fun i => N - 1 - i) N,
      Finset.sum_range_reflect (fun i => i) N, Finset.sum_range_id]
  simp [h]

theorem degFl_of_ne {ι : Type} [Fintype ι] {N d : ℕ} {P : MvPolynomial (ι × Fin N) ℝ}
    (hP : P.IsHomogeneous d) (hd : d ≠ dimFl ι N) : degFl ι N P = 0 := by
  unfold degFl
  rw [Finset.sum_eq_zero, mul_zero]
  intro σ _
  rw [hP.coeff_eq_zero (by rw [degree_permExp]; exact hd.symm), mul_zero]

theorem swapAt_eq {ι : Type} [DecidableEq ι] {N : ℕ} (τ : ι) (a b : Fin N) (z : ι × Fin N) :
    swapAt τ a b z = Equiv.swap (τ, a) (τ, b) z := by
  obtain ⟨s, i⟩ := z
  unfold swapAt
  split_ifs with h
  · obtain rfl : s = τ := h
    exact ((Prod.mk_right_injective s).map_swap a b i)
  · exact (Equiv.swap_apply_of_ne_of_ne (fun e => h (congrArg Prod.fst e)) fun e => h (congrArg Prod.fst e)).symm

theorem swap_of_model
    (hM : ∀ (ι : Type) [Fintype ι] (N : ℕ), ∃ (E : ι → (Sp ℤ).Modules) (h : ∀ a, VMetric (𝟙 (Sp ℤ)) (E a) N) (H : ∀ a, (h a).IsCInf) (fl : ∀ a, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback (GlobalTheory.FlagZ.flStr ι N)).obj (E a)) N), IsFlagBundle (GlobalTheory.FlagZ.flStr ι N) E (fun _ => N) fl ∧ ∀ (a : ι) (i : Fin N), (VMetric.grLB (fl a) i ((H a).pull (GlobalTheory.FlagZ.flStr ι N) (Category.comp_id _))).Isometric (GlobalTheory.FlagZ.grLine (a, i)))
    (hD : ∀ (ι : Type) [Fintype ι] (N : ℕ) (n : ι × Fin N → ℤ), gdeg (comb (GlobalTheory.FlagZ.grLine (ι := ι) (N := N)) n) (dimFl ι N) = degFl ι N (lin (fun x => (n x : ℝ)) ^ dimFl ι N))
    (G : ℕ → ℤ → ℤ → MvPolynomial (Fin 3) ℝ) (hG : SwapFl G) (D : D7) (Y : DV.ShimX D.what₂.Tau) (hh : Fn Y)
    (H : GlobalTheory.FlagZ.IsHh D.what₂.Tau Y.N hh) : SwapEq Y G hh (degFl D.what₂.Tau Y.N) := by
  intro τ a b hab _ n
  obtain ⟨E, h, Hc, fl, hfl, hiso⟩ := hM D.what₂.Tau Y.N
  have hX := (GlobalTheory.FlagZ.isArithVar_hasHh_unique D.what₂.Tau Y.N).1
  let e : (Σ _ : D.what₂.Tau, Fin Y.N) ≃ D.what₂.Tau × Fin Y.N := Equiv.sigmaEquivProd _ _
  have hΨ : IsGeoFun (GlobalTheory.FlagZ.grLine (ι := D.what₂.Tau) (N := Y.N)) (dimFl D.what₂.Tau Y.N) (degFlLin _ _) :=
    ⟨fun m => (degFlLin_apply _ _ _).trans (hD _ _ m).symm,
      fun P d hd hP => (degFlLin_apply _ _ _).trans (degFl_of_ne hP hd)⟩
  have key := hG ℤ (Sp ℤ) _ (𝟙 _) (GlobalTheory.FlagZ.flStr D.what₂.Tau Y.N) 0 _ ArithBase.isArithVar_int hX _
    (Category.comp_id _) D.what₂.Tau E (fun _ => Y.N) h Hc fl hfl _ _
    (isArFun_equiv hX e (fun z => hiso z.1 z.2) H) (isGeoFun_equiv e (fun z => hiso z.1 z.2) hΨ) τ a b hab
    fun z => n (e z)
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_pow] at key
  rw [rename_swapPol e G _ _ _ n, rename_lin e fun z => (n z : ℝ), degFlLin_apply] at key
  have e₂ : (fun z => ((n (e (Equiv.swap ⟨τ, a⟩ ⟨τ, b⟩ z)) : ℤ) : ℝ)) =
      fun z => (fun w => ((n (swapAt τ a b w) : ℤ) : ℝ)) (e z) := by
    funext z
    simp only [e.injective.map_swap, swapAt_eq]
    congr 3
  rw [e₂, rename_lin e fun w => ((n (swapAt τ a b w) : ℤ) : ℝ)] at key
  exact key

end GlobalTheory.CovTest.SwapZ

end
