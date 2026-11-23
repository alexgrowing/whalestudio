import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageDegreePositiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefShiftedFubiniStudyOfShortGeneratorsStatement
import Development.WeilBound.CoreStatements.NefModelVolumes.SelfInterBound

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

namespace SelfIntersectionVolumeEstimates.ImageNefG

theorem exists_nef_model_image : SelfIntersectionVolumeEstimates.VolInputs → Hypotheses2 → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (n : ℕ) (w : Fin n → cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) (abelian₂ t : ℝ), GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) → GlobalTheory.DegVal.BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) → NoBase Y.U Z (wtOf (T.Q.Dw j) u 0) → 0 < Y.dg u Z → IsShortGen (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0)) w abelian₂ → Real.log abelian₂ ≤ t → ∃ (k : Type) (_ : CommRing k) (X : AlgebraicGeometry.Scheme.{0}) (_ : AlgebraicGeometry.IsIntegral X) (p : X ⟶ Sp k) (L : GlobalTheory.HermLB p) (A : ℝ), GlobalTheory.IsArithVar p (dimFlag (T.Q.Dw j)) ∧ L.IsNef (dimFlag (T.Q.Dw j)) ∧ L.IsSelfInter A ∧ A ≤ (Module.finrank ℚ Y.d.c₂.F : ℝ) * ((dimFlag (T.Q.Dw j) : ℝ) + 1) * (Y.dg u Z * (Y.ht u Z + t)) ∧ ∀ i : ℕ, 1 ≤ i → (smallL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) (8 * i) t).encard ≤ (L.pow (8 * i)).smallSec.encard := by
  intro hPX hP D T j Y e o hY h2 Z u n w abelian₂ t hG hB hN hd hS hL
  obtain ⟨hgram, hfg, hspan⟩ := hG
  have hK : ∀ σ : Y.d.c₂.F →+* ℂ, (starRingEnd ℂ).comp σ ≠ σ := fun σ => conj_comp_ne σ
  have hconj : ∀ σ (x : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)),
      normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) ((starRingEnd ℂ).comp σ) x =
        normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) σ x :=
    fun σ x => petOn_conj Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) σ (x : Rul Y.d.Xo₂ Y.d.c₂)
  have hdeg : 0 < imageDeg (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (dimFlag (T.Q.Dw j)) := by
    have := hd
    simp only [Deep.dg, compDeg, Nat.cast_pos] at this
    exact this
  have hB' : GlobalTheory.DegVal.GenRatios (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) := hB
  obtain ⟨X, hX, p, L0, ψ, s, hM⟩ := GlobalTheory.T.image_degree_positive hP Y.d.c₂.F (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) (Om Z)
    (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0))
    (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (dimFlag (T.Q.Dw j)) hK hgram hconj hfg hspan hB hdeg
  obtain ⟨h, hh, -⟩ := hP.q11.existsUnique hM.arith (L0.shift (fun _ => t) (fun _ => rfl))
  refine ⟨𝓞 Y.d.c₂.F, inferInstance, X, hX, p, L0.shift (fun _ => t) (fun _ => rfl),
    h (genericPoint X), hM.arith, ?_, ⟨h, hh, rfl⟩, ?_, ?_⟩
  · exact GlobalTheory.T.isNef_shifted_fubiniStudy_of_short_generators Y.d.c₂.F (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) (Om Z)
      (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0))
      (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (dimFlag (T.Q.Dw j)) X p L0 ψ s n w abelian₂ t hM hB'.1 hS hL
  · have key : Hypotheses2 → ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec) (t a : ℝ), (∀ σ : K →+* ℂ, (starRingEnd ℂ).comp σ ≠ σ) → HasGram Nm → (∀ σ x, Nm ((starRingEnd ℂ).comp σ) x = Nm σ x) → W.FG → Submodule.span K (W : Set V) = ⊤ → GlobalTheory.DegVal.GenRatios ev → 0 < imageDeg ev D → GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → (L.shift (fun _ => t) (fun _ => rfl)).IsSelfInter a → a ≤ (Module.finrank ℚ K : ℝ) * ((D : ℝ) + 1) * ((imageDeg ev D : ℝ) * (imageHeight Nm W ev D + t)) := by
      exact hPX.1
    exact key hP Y.d.c₂.F (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) (Om Z)
      (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0))
      (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (dimFlag (T.Q.Dw j)) X p L0 ψ s t _ hK hgram hconj hfg hspan
      hB hdeg hM ⟨h, hh, rfl⟩
  · exact hPX.2 hP D T j Y e o hY h2 Z u X p L0 ψ s t ⟨hgram, hfg, hspan⟩ hB hN hd hM

end SelfIntersectionVolumeEstimates.ImageNefG
