import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.LocalToGlobal.ProjectiveLattices.DivFinOfLawA3
import Formalism.LocalToGlobal.ProjectiveLattices.NrmContPf
import Formalism.LocalToGlobal.ProjectiveLattices.AxHSup
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import Formalism.LocalToGlobal.ProjectiveLattices.FnTrdegOf
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.KapFgTrdeg
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteSupportAndDensityAndAemeasurable

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

private theorem fg_lemma {F K : Type} [Field F] [Field K] [Algebra F K] (σ : Type) [Finite σ]
    (h : (⊤ : IntermediateField F K).FG) :
    (⊤ : IntermediateField F (FractionRing (MvPolynomial σ K))).FG := by
  rw [IntermediateField.fg_top_iff] at h ⊢
  haveI : Algebra.EssFiniteType K (FractionRing (MvPolynomial σ K)) :=
    Algebra.EssFiniteType.comp K (MvPolynomial σ K) _
  exact Algebra.EssFiniteType.comp F K _

private theorem trdeg_fractionRing_mvPolynomial {F K : Type} [Field F] [Field K] [Algebra F K] (σ : Type) [Finite σ] (n : ℕ)
    (h : Algebra.trdeg F K = n) :
    Algebra.trdeg F (FractionRing (MvPolynomial σ K)) = (n + Nat.card σ : ℕ) := by
  have h1 : Algebra.trdeg (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) = 0 :=
    trdeg_eq_zero_iff.2 (IsLocalization.isAlgebraic _ (nonZeroDivisors _))
  have h2 := trdeg_add_eq (A := FractionRing (MvPolynomial σ K)) K (MvPolynomial σ K)
  rw [h1, add_zero, MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id] at h2
  have h3 := trdeg_add_eq (A := FractionRing (MvPolynomial σ K)) F K
  rw [← h3, h, ← h2, Nat.cast_add, Nat.cast_card]

theorem divFin_of_trdeg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ [Fintype (Comp Xo c)] (d : ReciprocityTheory.ChartRestriction.G.T0.Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z)), 1 ≤ d.D → d.D = Dw.dim + Nat.card (FlagVar Dw) → (∀ Z j, d.w j Z ∈ AG Z d.wL) → (∀ Z, d.w (d.jc Z) Z ≠ 0) → (∀ Z, ReciprocityTheory.ChartRestriction.G.AR.Up.TrdegD d Z) → DivFin d := by
  intro E _ _ _ H Dw l Xo c _ d hD hdim hw hjc htr Z r hr
  obtain ⟨hfg, htd⟩ := kap_fg_trdeg E H Dw l Xo c
  have hFG : (⊤ : IntermediateField c.F (Om Z)).FG := fg_lemma (FlagVar Dw) (hfg Z)
  have hT : Algebra.trdeg c.F (Om Z) = d.D := by
    rw [hdim]; exact trdeg_fractionRing_mvPolynomial (FlagVar Dw) Dw.dim (htd Z)
  have hrk : ∀ G, Module.finrank (Om Z) (AG Z G) = 1 := fun G =>
    finrank_span_singleton (AddMonoidAlgebra.single_ne_zero.mpr one_ne_zero)
  exact (GlobalTheory.finite_support_and_density_and_aemeasurable.1 c.F (Comp Xo c) (fun Z => Om Z) (WTZ E)
    (fun Z => AC Z) (fun Z G => AG Z G) d Z hD hFG hT hrk (hw Z) (hjc Z) (htr Z)).1 r hr

end GlobalTheory.Reg
