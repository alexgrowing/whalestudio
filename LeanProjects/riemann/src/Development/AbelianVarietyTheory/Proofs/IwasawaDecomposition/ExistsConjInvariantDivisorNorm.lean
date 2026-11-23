import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDivisorNormOfEffCartierStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjSmoothOnPreimageChartsStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.DivFam

variable {k : Type} [Field k] {Y : Scheme.{0}} {p : Y ⟶ Sp k}

theorem spMap_conj_conj : spMap (starRingEnd ℂ) ≫ spMap (starRingEnd ℂ) = 𝟙 (Sp ℂ) := by
  rw [← Spec.map_comp, ← Spec.map_id]
  exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun x => by simp))

def conjPt (σ : k →+* ℂ) (z : CxPts p σ) : CxPts p ((starRingEnd ℂ).comp σ) :=
  ⟨spMap (starRingEnd ℂ) ≫ z.1, by
    rw [Category.assoc, z.2, ← Spec.map_comp]; rfl⟩

theorem eq_conj {σ σ' : k →+* ℂ} {y : CxPts p σ} {z : CxPts p σ'} (h : y.1 = spMap (starRingEnd ℂ) ≫ z.1) :
    σ = (starRingEnd ℂ).comp σ' := by
  have h1 : spMap σ = spMap ((starRingEnd ℂ).comp σ') := by
    rw [← y.2, h]
    exact (conjPt σ' z).2
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)

theorem isDivNorm_comp {d : ℕ} [SmoothOfRelativeDimension d p] {σ σ' : k →+* ℂ} {C : Closeds Y}
    {n : CxPts p σ → ℝ} (h : IsDivNorm (AnRead.all p σ d) C n) {j : CxPts p σ' → CxPts p σ} (hj : IsConjMap j) :
    IsDivNorm (AnRead.all p σ' d) C (n ∘ j) := by
  refine ⟨fun y => h.1 _, fun y => ?_⟩
  obtain ⟨V, t, f, hy, ht, hf, e⟩ := h.2 (j y)
  have hpt : ∀ z, (j z).1 (IsLocalRing.closedPoint ℂ) = z.1 (IsLocalRing.closedPoint ℂ) := fun z => by
    rw [hj z]
    exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg z.1 (Subsingleton.elim (α := PrimeSpectrum ℂ) _ _))
  have hm : ∀ z, j z ∈ ptsIn p σ V.1 ↔ z ∈ ptsIn p σ' V.1 := fun z => by
    rw [mem_ptsIn, mem_ptsIn, hpt]
  have hs := (GlobalTheory.T.conj_smoothOn_preimage_charts k Y p d σ σ' j hj _ f (isOpen_ptsIn _) hf).2.1
  refine ⟨V, t, f ∘ j, (hm y).1 hy, ht, hs.mono fun z hz => (hm z).2 hz, fun z hz => ?_⟩
  rw [Function.comp_apply, e _ ((hm z).2 hz), CxPts.ev_conj (hj z) hz, RCLike.norm_conj]
  rfl

end GlobalTheory.ShFam.DivFam

namespace GlobalTheory.ShFam

open DivFam in

theorem exists_isDivNorm_family : ∀ (k : Type) [Field k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (d : ℕ) [SmoothOfRelativeDimension d p] (C : Closeds Y), IsProjOver p → (∀ σ : k →+* ℂ, (starRingEnd ℂ).comp σ ≠ σ) → ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (Scheme.IdealSheafData.vanishingIdeal C) → ∃ n : ∀ σ : k →+* ℂ, CxPts p σ → ℝ, (∀ σ, IsDivNorm (AnRead.all p σ d) C (n σ)) ∧ ∀ σ σ' (j : CxPts p σ' → CxPts p σ), IsConjMap j → ∀ z, n σ' z = n σ (j z) := by
  classical
  intro k _ Y p d _ C hp hr hC
  choose n hn using fun σ => GlobalTheory.T.exists_divisor_norm_of_effCartier k Y p d σ C hp hC
  let _ : LinearOrder (k →+* ℂ) := linearOrderOfSTO WellOrderingRel
  refine ⟨fun σ => if σ < (starRingEnd ℂ).comp σ then n σ else n _ ∘ conjPt σ, fun σ => ?_, fun σ σ' j hj z => ?_⟩
  · beta_reduce
    by_cases h : σ < (starRingEnd ℂ).comp σ
    · rw [if_pos h]; exact hn σ
    · rw [if_neg h]; exact isDivNorm_comp (hn _) fun _ => rfl
  · obtain rfl := eq_conj (hj z)
    have hjz : j z = conjPt σ' z := Subtype.ext (hj z)
    have cc : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp σ') = σ' := RingHom.ext fun x => by simp
    have key : ∀ (τ : k →+* ℂ) (w : CxPts p τ), τ = σ' → w.1 = z.1 → n τ w = n σ' z := by
      rintro τ w rfl e
      rw [Subtype.ext e]
    beta_reduce
    by_cases h : σ' < (starRingEnd ℂ).comp σ'
    · rw [if_pos h, if_neg (by rw [cc]; exact h.not_gt)]
      refine (key _ _ cc ?_).symm
      show spMap (starRingEnd ℂ) ≫ (j z).1 = z.1
      rw [hj z, ← Category.assoc, spMap_conj_conj, Category.id_comp]
    · rw [if_neg h, if_pos (by rw [cc]; exact lt_of_le_of_ne (not_lt.1 h) (hr σ')), hjz]
      rfl

end GlobalTheory.ShFam
