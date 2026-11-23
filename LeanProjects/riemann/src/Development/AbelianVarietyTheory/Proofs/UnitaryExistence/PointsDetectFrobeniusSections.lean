import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegPFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegralityStatement

noncomputable section

namespace GlobalTheory.Frames

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GeometricValues

theorem eq_zero_of_forall_algClosed {K R : Type} [Field K] [CommRing R] [Algebra K R] [IsReduced R] (x : R)
    (h : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (φ : R →ₐ[K] Ω), φ x = 0) : x = 0 := by
  apply IsNilpotent.eq_zero
  rw [nilpotent_iff_mem_prime]
  intro J hJ
  let φ : R →ₐ[K] AlgebraicClosure (FractionRing (R ⧸ J)) :=
    (IsScalarTower.toAlgHom K (FractionRing (R ⧸ J)) (AlgebraicClosure (FractionRing (R ⧸ J)))).comp
      ((IsScalarTower.toAlgHom K (R ⧸ J) (FractionRing (R ⧸ J))).comp (Ideal.Quotient.mkₐ K J))
  have h0 := h _ φ
  have h1 : algebraMap (R ⧸ J) (FractionRing (R ⧸ J)) (Ideal.Quotient.mk J x) = 0 := by
    apply (algebraMap (FractionRing (R ⧸ J)) (AlgebraicClosure (FractionRing (R ⧸ J)))).injective
    rw [map_zero]
    exact h0
  have h2 : Ideal.Quotient.mk J x = 0 := by
    apply IsFractionRing.injective (R ⧸ J) (FractionRing (R ⧸ J))
    rw [map_zero]
    exact h1
  exact Ideal.Quotient.eq_zero_iff_mem.mp h2

theorem ptsDetect_of {K : Type} [Field K] {ι : Type} [Fintype ι]
    (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
    (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
      (S →ₐ[K] T) → pts S → pts T → Prop)
    (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop)
    (hW : EvalWD pts mapR)
    (hB : ∀ (S : Type) [CommRing S] [Algebra K S] (T : Type) [CommRing T] [Algebra K T] (φ : S →ₐ[K] T)
      (y : pts S), ∃ z : pts T, mapR φ y z)
    (e : ι → ℕ) : PtsDetect pts mapR borR e := by
  intro g hg h
  funext p y
  have : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).mp p.rad
  refine eq_zero_of_forall_algClosed (K := K) (g p y) ?_
  intro Ω _ _ _ φ
  obtain ⟨z, hz⟩ := hB p.R Ω φ y
  have hT : FromTest pts mapR z := ⟨p, φ, y, hz⟩
  have h0 := h Ω z
  unfold evalAt at h0
  rw [dif_pos hT] at h0
  rw [← h0]
  exact hW g hg.1 Ω p _ φ _ y _ z hz hT.choose_spec.choose_spec.choose_spec

end GeometricValues

theorem ptsDetect_framed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), PtsDetect (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y') (ex Dw a n) := by
  intro E _ _ _ H Dw l Xo c a n
  have hS : Out.SecBaseChangeSt := GlobalTheory.firstFiveLaws.1.secBaseChange
  exact GeometricValues.ptsDetect_of (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)
    (fun t y y' => FrBor t y y') (GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hS E H Dw l Xo c).2.2.1
    (fun S _ _ T _ _ φ y => GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c S T φ y) (ex Dw a n)

end GlobalTheory.Frames
