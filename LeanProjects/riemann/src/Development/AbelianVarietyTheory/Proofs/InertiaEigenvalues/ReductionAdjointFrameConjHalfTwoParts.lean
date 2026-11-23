import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointFrameMatrixReductionEqZeroOffPlaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceModelCompTensorHalf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMapMulInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPairCharactersAtLevel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePlacesDisjointTwistPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatrixReductionEqOfHalfIdempotentSubset
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.TwoStepRed

theorem redM_part_eq {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (EAf D))
    (βT : GL (Fin T.rank) (EAf D)) (P R : Finset (Pl D.host.E)) (e f : AE D)
    (hP : IsIdemSum e P) (hR : IsIdemSum f R) (hd : Disjoint P R) (x : WO S T)
    (hx : IsHalf (cA D (e + f)) x) (hN : IsIntM (frMapAdj S T βS βT x)) :
    ∀ PP ∈ P, redM PP (frMapAdj S T βS βT (cA D e • x)) = redM PP (frMapAdj S T βS βT x) := by
  intro PP hPP
  have hsplit : x = cA D e • x + cA D f • x := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [← add_mul, ← map_add, hx i j]
  have h1 : frMapAdj S T βS βT x
      = frMapAdj S T βS βT (cA D e • x) + toEAf D f • frMapAdj S T βS βT x := by
    conv_lhs => rw [hsplit]
    rw [GlobalTheory.PlaceVec.frMapAdj_add, GlobalTheory.RedHalfDrop.frMapAdj_smul_eq βS βT (cA D f) x, cA_cA]
  have hc : toEAf D f ∈ Formalism.L2.Herm.intAf (↥D.host.F) D.host.E := by
    rw [← GlobalTheory.ExportSeries.idem_eq hR]
    unfold GlobalTheory.ExportSeries.idem
    rw [show (toEAf D) (∑ Q ∈ R, GlobalTheory.ExportSeries.idemAt Q) = ∑ Q ∈ R, (toEAf D) (GlobalTheory.ExportSeries.idemAt Q) from
      map_sum (toEAf D).toAddMonoidHom _ _]
    exact sum_mem (fun Q hQ => GlobalTheory.RedHalfDrop.int_idemAt ⟨f, hR⟩ hQ)
  rw [eq_sub_of_add_eq h1.symm]
  exact GlobalTheory.RedHalfDrop.redM_sub_smul PP hN hc
    (GlobalTheory.AdjRedOff.resS_idemSum_eq_zero hR hc (fun h => Finset.disjoint_left.mp hd hPP h))

theorem redM_twoStep : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (Pg Q : Finset (Pl D.host.E)) (eg eQ : AE D), IsIdemSum eg Pg → IsIdemSum eQ Q → Disjoint Pg Q → IsIdemSum (eg + eQ) (Pg ∪ Q) → ∀ x : WO S T, IsHalf (cA D (eg + eQ)) x → IsIntM (frMapAdj S T βS βT x) → (∀ PP ∈ Pg, redM PP (frMapAdj S T βS βT (cA D eg • x)) = redM PP (frMapAdj S T βS βT x)) ∧ (∀ PP ∈ Q, redM PP (frMapAdj S T βS βT (cA D eQ • x)) = redM PP (frMapAdj S T βS βT x)) := by
  intro D S T βS βT Pg Q eg eQ hg hQ hd _ x hx hN
  exact ⟨redM_part_eq S T βS βT Pg Q eg eQ hg hQ hd x hx hN,
    redM_part_eq S T βS βT Q Pg eQ eg hQ hg hd.symm x (by rwa [add_comm]) hN⟩

end GlobalTheory.TwoStepRed
