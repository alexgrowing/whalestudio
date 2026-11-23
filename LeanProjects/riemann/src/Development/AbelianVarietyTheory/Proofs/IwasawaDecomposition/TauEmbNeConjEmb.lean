import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EvlTrueIncTInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenericLieMultiplicitiesUniformisedGroup
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.FormalGroupLaws
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HomAppHomOfRestrictImage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothRayQuotient
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompMapNsmul
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PartialDerivativeExponent
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.KillAdd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoxSumSections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ChartSer
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EqZeroOrSingleOfDegreeLeOne
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpOfPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GtPtsVal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FaceDerivSymmetricCocycle
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RigidFrameSymmetricRatioSeries
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaScaledThreeValue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RigidFrameExponentialFourth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SectionPullbackThetaValue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProperAfterLocalizationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValidGaugeImpliesValid

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.LocM.EvTrue

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.RayEv
open Formalism.MainNotions.DIV.Cons (SCF intO)

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {p : ℕ} {C : SCF p}
  {P : PointsOfFlagModel.PtC Y C} {A : DatAt Y P} {T : Type} [Fintype T] [DecidableEq T] {emb : T × Bool → E →+* ℂ}

end General

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

theorem conj_not_cm (A : Amb D) (t : D.what₂.Tau) : conjEmb (DV.tauEmb D t) (A.H.rt : D.host.E) ≠ A.H.rt0 := by
  intro h
  have h1 : starRingEnd ℂ A.H.rt0 = A.H.rt0 := by
    have h0 : DV.tauEmb D t (A.H.rt : D.host.E) = A.H.rt0 := A.cm t
    rw [← h0] at h ⊢
    exact h
  have hd : (0 : ℝ) < A.H.d := by exact_mod_cast A.H.d_prime.pos
  have h2 := congrArg Complex.re A.H.sqrt_neg_disc_sq
  have h3 : A.H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h1
  simp [pow_two, h3] at h2
  nlinarith [sq_nonneg A.H.rt0.re]

theorem tauEmb_ne_conjEmb (A : Amb D) (t t' : D.what₂.Tau) : DV.tauEmb D t ≠ conjEmb (DV.tauEmb D t') := fun h =>
  conj_not_cm A t' (h ▸ A.cm t)

end GlobalTheory.LocM.EvTrue
