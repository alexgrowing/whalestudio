import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicUnitaryComponentAtPlaceLaws
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CmAdeleIdempotentOfPlaceProperties
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorFixesLatticeVacuumNonsplitUnramified

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinZeta.MoveVac

theorem mt_one' {D : D7} (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := rfl

theorem actO_one_eq {D : D7} {S T : HSp D} {v : HeightOneSpectrum (𝓞 D.host.F)} {g : GA D T}
    (hg : projV T v g = 1) {u : WO S T} (hu : u ∈ latO S T (frameLat S) (frameLat T) fun w => w = v) :
    actO S T 1 g u = u := by
  have hid : IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1)) :=
    ((GlobalTheory.PlaceTensor.idem_spec D).2.2.2.1 v).2.2
  have hgA : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.gAt T (.inl v) g = 1 := by
    show GlobalTheory.AdelicU.emb D.sp.cm.sig T.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig T.gram v g) = 1
    rw [show GlobalTheory.AdelicU.proj D.sp.cm.sig T.gram v g = 1 from hg, map_one]
  have hm : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.idem D (.inl v) • Formalism.L2.Theta.mt T g =
      GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.idem D (.inl v) • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) := by
    have h := GlobalTheory.PlaceComponent.mt_gAt T (.inl v) g
    rw [hgA, mt_one'] at h
    rw [eq_sub_of_add_eq h.symm, sub_smul, one_smul, sub_sub_cancel]
  have hu' : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.idem D (.inl v) • u = u := GlobalTheory.InertVac.placeIdem_smul_eq hid hu
  unfold actO
  rw [inv_one, mt_one', Matrix.mul_one, ← hu', Matrix.mul_smul, ← Matrix.smul_mul, hm,
    Matrix.smul_mul, Matrix.one_mul]

theorem vacFin_om_one : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GA D T), projV T v g = 1 → ∀ f, VacFin ψ S T v f → VacFin ψ S T v (om (1, g) f) := by
  intro D ψ S T χS χT om hW v g hg f hf
  obtain ⟨hth, hl1, hl2⟩ := hf
  refine ⟨hW.om_pres _ _ hth, fun u hu => ?_, fun e he u hu hh => ?_⟩
  · have h2 : 2 • u ∈ (latO S T (frameLat S) (frameLat T) fun w => w = v) := nsmul_mem hu 2
    rw [← actO_one_eq hg h2, ← hW.om_heis 1 g _ f hth, hl1 u hu]
  · rw [← actO_one_eq hg hu, ← hW.om_heis 1 g _ f hth, hl2 e he u hu hh]

end GlobalTheory.FinZeta.MoveVac

end
