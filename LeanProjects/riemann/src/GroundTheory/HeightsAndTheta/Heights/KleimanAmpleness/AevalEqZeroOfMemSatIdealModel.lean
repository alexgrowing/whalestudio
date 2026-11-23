import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockBase
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver mIdealOver)
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver IsMultiHomog)

noncomputable section

section Objects

variable (S : Type) [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [Algebra S Ω]

def dehom (y : (Σ k, ι k) → Ω) (J : Ideal (MRingOver S ι)) (d : ∀ k, ι k) : Set Ω :=
  {u | ∃ (g : MRingOver S ι) (a : K → ℕ), g ∈ J ∧ IsMultiHomog g a ∧
    u = aeval y g * ∏ k, y ⟨k, d k⟩ ^ (-(a k : ℤ))}

def satIdeal (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) (J : Ideal (MRingOver S ι)) :
    Ideal (Kleiman.Poly S N) :=
  Ideal.span {f | ∃ n : ℕ, f.IsHomogeneous n ∧ ∀ i, baseVec y k₀ e i ≠ 0 → ∀ d : ∀ k, ι k,
    (∀ k, y ⟨k, d k⟩ ≠ 0) → aeval (fun j => baseVec y k₀ e j / baseVec y k₀ e i) f ∈
      Submodule.span (overRing (S := S) y k₀ e d i) (dehom S y J d)}

end Objects

section Facts

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [Algebra S Ω] {y : (Σ k, ι k) → Ω} {k₀ : K} {N : ℕ} {e : ι k₀ ≃ Fin (N + 1)}
  {J : Ideal (MRingOver S ι)}

theorem mem_dehom {g : MRingOver S ι} {a : K → ℕ} (hg : g ∈ J) (ha : IsMultiHomog g a) (d : ∀ k, ι k) :
    aeval y g * ∏ k, y ⟨k, d k⟩ ^ (-(a k : ℤ)) ∈ dehom S y J d :=
  ⟨g, a, hg, ha, rfl⟩

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem aeval_ratio_mem_chartRing (i : Fin (N + 1)) (p : Kleiman.Poly S N) :
    aeval (fun j => baseVec y k₀ e j / baseVec y k₀ e i) p ∈
      ReciprocityTheory.ChartRestriction.G.Geo.chartRing S (baseVec y k₀ e) i := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.chartRing
  rw [Algebra.adjoin_range_eq_range_aeval]
  exact ⟨p, rfl⟩

theorem aeval_mem_of_mem_satIdeal [DecidableEq K] {p : Kleiman.Poly S N} (hp : p ∈ satIdeal S y k₀ e J) {i : Fin (N + 1)}
    (hi : baseVec y k₀ e i ≠ 0) {d : ∀ k, ι k} (hd : ∀ k, y ⟨k, d k⟩ ≠ 0) :
    aeval (fun j => baseVec y k₀ e j / baseVec y k₀ e i) p ∈
      Submodule.span (overRing (S := S) y k₀ e d i) (dehom S y J d) := by
  induction hp using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨n, -, hf⟩ := hf
    exact hf i hi d hd
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul r a _ ha =>
    rw [smul_eq_mul, map_mul]
    have hr : aeval (fun j => baseVec y k₀ e j / baseVec y k₀ e i) r ∈ overRing (S := S) y k₀ e d i :=
      chartRing_le_overRing d i (aeval_ratio_mem_chartRing i r)
    have := Submodule.smul_mem _ (⟨_, hr⟩ : overRing (S := S) y k₀ e d i) ha
    rwa [Subalgebra.smul_def] at this

attribute [local instance] MvPolynomial.gradedAlgebra in

theorem satIdeal_isHomogeneous :
    (satIdeal S y k₀ e J).IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) S) :=
  Ideal.homogeneous_span _ _ fun _ ⟨n, hf, _⟩ => ⟨n, (mem_homogeneousSubmodule n _).2 hf⟩

attribute [local instance] MvPolynomial.gradedAlgebra in

theorem homogeneousComponent_mem_satIdeal {p : Kleiman.Poly S N} (hp : p ∈ satIdeal S y k₀ e J) (n : ℕ) :
    homogeneousComponent n p ∈ satIdeal S y k₀ e J :=
  homogeneousComponent_mem_of_mem satIdeal_isHomogeneous hp n

theorem one_mem_dehom_top (d : ∀ k, ι k) : (1 : Ω) ∈ dehom S y (⊤ : Ideal (MRingOver S ι)) d := by
  classical
  refine ⟨1, 0, Submodule.mem_top, ?_, ?_⟩
  · intro m hm k
    have : m = 0 := by
      by_contra h
      exact (mem_support_iff.mp hm) (by rw [coeff_one, if_neg (Ne.symm h)])
    simp [this]
  · simp

theorem one_mem_satIdeal_top : (1 : Kleiman.Poly S N) ∈ satIdeal S y k₀ e (⊤ : Ideal (MRingOver S ι)) := by
  classical
  refine Ideal.subset_span ⟨0, isHomogeneous_one _ _, fun i _ d _ => ?_⟩
  rw [map_one]
  exact Submodule.subset_span (one_mem_dehom_top d)

theorem mem_satIdeal_of_aeval_eq_zero {f : Kleiman.Poly S N} {n : ℕ} (hf : f.IsHomogeneous n)
    (h0 : aeval (baseVec y k₀ e) f = 0) : f ∈ satIdeal S y k₀ e J :=
  Ideal.subset_span ⟨n, hf, fun i _ d _ => by
    rw [Kleiman.aeval_div_of_isHomogeneous (x := baseVec y k₀ e) hf i, h0, zero_div]
    exact zero_mem _⟩

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem aeval_eq_zero_of_mem_mIdealOver {g : MRingOver S ι} (hg : g ∈ mIdealOver S y) : aeval y g = 0 := by
  have h : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.mConeMapOver S y g = 0 := hg
  have h1 := congrArg (MvPolynomial.eval (fun _ : K => (1 : Ω))) h
  rw [map_zero, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.mConeMapOver, MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left] at h1
  rw [MvPolynomial.aeval_def]
  convert h1 using 2
  · ext r
    rw [RingHom.comp_apply, MvPolynomial.algebraMap_apply, MvPolynomial.eval_C]
  · funext p
    simp

theorem eq_zero_of_mem_dehom_mIdealOver {d : ∀ k, ι k} {u : Ω} (hu : u ∈ dehom S y (mIdealOver S y) d) :
    u = 0 := by
  obtain ⟨g, a, hg, -, rfl⟩ := hu
  rw [aeval_eq_zero_of_mem_mIdealOver hg, zero_mul]

theorem aeval_eq_zero_of_mem_satIdeal_model [DecidableEq K] {f : Kleiman.Poly S N} {n : ℕ}
    (hf : f.IsHomogeneous n) (hmem : f ∈ satIdeal S y k₀ e (mIdealOver S y)) {d : ∀ k, ι k}
    (hd : ∀ k, y ⟨k, d k⟩ ≠ 0) : aeval (baseVec y k₀ e) f = 0 := by
  have hi : baseVec y k₀ e (e (d k₀)) ≠ 0 := by simpa [IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hd k₀
  have h1 := aeval_mem_of_mem_satIdeal hmem hi hd
  have h2 : Submodule.span (overRing (S := S) y k₀ e d (e (d k₀))) (dehom S y (mIdealOver S y) d) = ⊥ := by
    rw [Submodule.span_eq_bot]
    intro u hu
    exact eq_zero_of_mem_dehom_mIdealOver hu
  rw [h2, Submodule.mem_bot, Kleiman.aeval_div_of_isHomogeneous (x := baseVec y k₀ e) hf] at h1
  exact (div_eq_zero_iff.1 h1).resolve_right (pow_ne_zero _ hi)

end Facts

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
