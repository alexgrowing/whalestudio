import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.IsMultMapUnivZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslateUnitaryLifts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupActionEqZeroOfNoLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftIntertwinesLiftsSmoothVectors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftMemLevelOfDatumFlagCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlacesApart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLeviFlagOfMemParabolic
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

set_option maxHeartbeats 8000000 in

theorem extV_mem_levSubV_of_lift : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (P : LevelP R.Pg D.R.r ℂ) (z : (R.HV i t).H), (∀ (g0 : P.H) (κ : GA D (Vc D i)), IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0.1 κ → ∀ h, R.extV i t z (h * κ) = levChi _ (R.βV i) (flagL (R.datVt i t)) κ • ((((P.chi g0 : ℂˣ) : ℂ))⁻¹ • R.extV i t z h)) → R.extV i t z ∈ RecTie.levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (RecTie.datVP R i t P)) (levChi _ (R.βV i) (RecTie.datVP R i t P)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i t P z hz k hk g
  have hlift : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t)
      (⟨Formalism.L2.DIV.rTup (R.βV i) (RecTie.datVP R i t P) (finE (Vc D i) k), hk.2.2⟩ : P.H).1 k :=
    ⟨hk.1, hk.2.1, rfl⟩
  have h2 := (GlobalTheory.lift_mem_levVP R i t P _ k hlift).2
  rw [hz _ k hlift g, h2, smul_smul, mul_comm]

end GlobalTheory
