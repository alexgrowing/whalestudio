import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PutInSplitPlacesDatumProductOnHalf
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.putInSplitPlaces_datum_product_on_half : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt D k) (J : List ι), Places p J (fun v => ∃ i, v = (p i).v) →
    ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (α : ∀ i, Frame (p i) S n') (β : ∀ i, Frame (p i) T n) (LS : Lat S) (LT : Lat T),
    IsSelfDualC S LS → IsSelfDualC T LT → (∀ z, z ∈ LS ↔ z ∈ intVec D S.rank) → (∀ z, z ∈ LT ↔ z ∈ intVec D T.rank) →
    ∀ (Pset : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e Pset →
    (∃ eq : ι ≃ Pset, ∀ i, Formalism.L2.NTheta.IsIdemAt (p i).e (eq i).1) →
    ∀ (Ψ : ι → Matrix n n' k → ℂ) (f f' : WO S T → ℂ), IsThetaFunO ψ S T f → IsLatVac (heisO ψ S T) (stdHom S T) f →
    OverAll ψ α β LS LT Ψ J f f' →
    IsRatDatum ψ S T e (fun γ => (J.map fun i => Ψ i (rd (α i) (β i) (γ.map (incA D)))).prod) f f' := by
  first | exact @GlobalTheory.FinPl.PutIn.ratDatum_of_overAll | exact GlobalTheory.FinPl.PutIn.ratDatum_of_overAll | (intros; apply GlobalTheory.FinPl.PutIn.ratDatum_of_overAll <;> assumption)
