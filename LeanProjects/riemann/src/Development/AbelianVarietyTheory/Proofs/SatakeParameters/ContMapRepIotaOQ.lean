import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIotaOQOfDataStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalGaloisRepDecompositionInducedStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalGaloisRepInducedMatchesStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open GlobalTheory.Pst GlobalTheory.WeilDeligne

namespace GlobalTheory.LocalInv

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def PstTie (T : GlobalTheory.RowTie.WDTie N A) : Prop :=
  ∃ (P : ∀ i, LocPrime (N.l i)) (AI : ∀ i, LocAinf (N.l i) (P i)) (_ : ∀ i, Nonempty (LocTied (N.l i) (P i) (AI i)))
    (LL : ∀ i, FinExt (N.l i))
    (br : ∀ i (w : PlE H), w ∈ placesOver H.E (N.l i) →
      LocBridge (N.l i) H.E N.Om (Dec (F := H.E) (N.plOm.1 w)) ↥(OL (LL i)))
    (hj : ∀ i w hw, Induces (br i w hw)),
    ∀ (i : N.Loc) {a : ℕ} (r : G H.E N.Om →* GL (Fin a) (Qbar (N.l i))) (w : PlE H)
      (hw : w ∈ placesOver H.E (N.l i)),
      Continuous (fun g => ((r g : GL (Fin a) (Qbar (N.l i))) : Matrix (Fin a) (Fin a) (Qbar (N.l i)))) →
      A.IsdRW i r w →
      IsdRAt (P i) (br i w hw) (resDec N.plOm.1 r w) ∧
        T.e w (A.wdOf i r w) = wdAt (P i) (A.iotaQC i) (br i w hw) (N.plOm.2 w) (hj i w hw) (resDec N.plOm.1 r w)

theorem cont_mapRep_iotaOQ (i : N.Loc) {b : ℕ} (τ : G H.E N.Om →* GL (Fin b) (N.O i)) (hτ : Cont N i τ) :
    Continuous (fun g => ((mapRep (iotaOQ N A i) τ g : GL (Fin b) (Qbar (N.l i))) :
      Matrix (Fin b) (Fin b) (Qbar (N.l i)))) :=
  continuous_matrix fun p q => (GlobalTheory.T.continuous_iotaOQ' N A i).comp (hτ.matrix_elem p q)

end GlobalTheory.LocalInv
