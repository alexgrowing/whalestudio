import Mathlib
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtOneOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AwayOfInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyLocalPeriodRingsData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalPeriodRingsDataUnramifiedLaws
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalPeriodRingsSectionEqAinfToBdRPlus
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per

namespace GlobalTheory.WittCompat

theorem u_eq_aB (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (C : Core l) (w : Wq l a) (c : ↥(MaximalUnramifiedExtension l))
    (hw : ((Per.θ l (wA l a w) : Per.OC l) : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (c : Om l)) :
    C.u c = Per.aB l (wA l a w) := by
  have ho := GlobalTheory.SeedSec.o_eq_aDp_wA l a C w (c : Om l) hw
  apply (GlobalTheory.MemLoc.ULaws.u_laws l C).2.2.2.1
  have hB : C.ι (Per.aB l (wA l a w)) =
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (wA l a w)) :=
    GlobalTheory.MemLoc.ULaws.iota_aB C (wA l a w)
  rw [hB, ← ho, C.ι_u]

theorem exists_unramified_witt_element : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (w : W0 K),
    ∃ c : ↥(K0 K), algebraMap ↥(K0 K) ↥K.1 c = oK K (thetaW (fK K) K w) ∧
      algebraMap ↥(K0 K) P.R.B c = T.eB.symm (Per.aB l (wA l (fK K) w)) := by
  intro l _ P AI T K w
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  have h1 : ((Per.θ l (wA l (fK K) w) : Per.OC l) : ℂ_[l]) =
      algebraMap (Om l) ℂ_[l] ((oK K (thetaW (fK K) K w) : ↥K.1) : Om l) :=
    (congrArg (fun y : Per.OC l => (y : ℂ_[l])) (intToOC_thetaW (fK K) K w)).symm
  have h2 : ((Per.θ l (wA l (fK K) w) : Per.OC l) : ℂ_[l]) =
      algebraMap (Om l) ℂ_[l] (GlobalTheory.TameFrob.iotaO l (fK K) w) :=
    (congrArg (fun y : Per.OC l => (y : ℂ_[l])) (intToOC_thetaW (fK K) (unrExt l (fK K)) w)).symm
  have h3 : ((oK K (thetaW (fK K) K w) : ↥K.1) : Om l) = GlobalTheory.TameFrob.iotaO l (fK K) w :=
    (algebraMap (Om l) ℂ_[l]).injective (h1.symm.trans h2)
  have hm : ((oK K (thetaW (fK K) K w) : ↥K.1) : Om l) ∈ K0 K := by
    rw [h3, ← Kunr_fK K]
    exact GlobalTheory.TameFrob.iotaO_mem l (fK K) w
  refine ⟨⟨_, hm⟩, Subtype.ext rfl, ?_⟩
  rw [RingEquiv.eq_symm_apply]
  exact (hC.u ⟨_, hm.2⟩).trans (u_eq_aB l (fK K) C w ⟨_, hm.2⟩ h1)

end GlobalTheory.WittCompat
