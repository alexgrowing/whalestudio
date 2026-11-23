import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRFiltrationLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFilPIffEvPt
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.TiedTheta

variable {l : ℕ} [Fact l.Prime]

open Classical in

def thetaExt (x : Per.BdR l) : ℂ_[l] :=
  if h : ∃ y : Per.BdRp l, algebraMap (Per.BdRp l) (Per.BdR l) y = x then Per.θD l h.choose else 0

theorem thetaExt_alg (y : Per.BdRp l) :
    thetaExt (algebraMap (Per.BdRp l) (Per.BdR l) y) = Per.θD l y := by
  have h : ∃ z : Per.BdRp l, algebraMap (Per.BdRp l) (Per.BdR l) z =
      algebraMap (Per.BdRp l) (Per.BdR l) y := ⟨y, rfl⟩
  rw [thetaExt, dif_pos h, (BdRField.bdR_isField l).2.1 h.choose_spec]

theorem exists_of_mem_FilD_zero {x : Per.BdR l} (hx : x ∈ Per.FilD l 0) :
    ∃ y : Per.BdRp l, x = algebraMap (Per.BdRp l) (Per.BdR l) y := by
  obtain ⟨e, he⟩ := FilLaws.exists_isEps l
  obtain ⟨y, hy⟩ := (mem_FilD_iff_xi_pow l e he 0 x).1 hx
  exact ⟨y, by simpa using hy⟩

theorem actC_eq {P : LocPrime l} (AI : LocAinf l P) (g : GQ l) (c : ℂ_[l]) :
    AI.actC g c = Per.σC g c := by
  have h1 : Continuous (AI.actC g) :=
    (AddMonoidHomClass.isometry_of_norm (AI.actC g) (AI.actC_norm g)).continuous
  have h2 : Continuous (Per.σC g) :=
    (AddMonoidHomClass.isometry_of_norm (Per.σC g) (GlobalTheory.RingBasics.norm_σC g)).continuous
  induction c using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq h1 h2
  | ih a => exact (AI.actC_ext g a).trans (GlobalTheory.RingBasics.σC_coe g a).symm

theorem norm_untilt_sub (x : Per.Fl l) (y : Per.OC l)
    (h : PreTilt.coeff 0 x = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : Per.OC l)}) y) :
    ‖((x.untilt : Per.OC l) : ℂ_[l]) - (y : ℂ_[l])‖ ≤ ‖(l : ℂ_[l])‖ := by
  rw [← PreTilt.mk_untilt_eq_coeff_zero, Ideal.Quotient.eq] at h
  have h1 := (GlobalTheory.RingBasics.mem_span_pow_OC 1 (x.untilt - y)).1 (by rwa [pow_one])
  rw [pow_one] at h1
  exact h1

theorem nonempty_thetaL : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    LocTied l P AI → Nonempty (Formalism.MainNotions.LocalSituation.ThetaL P AI) := by
  intro l _ P AI T
  have hex : ∀ x ∈ (P.PD (MainNotions.LocalSituation.botExt l)).Fil 0,
      ∃ y : Per.BdRp l, T.eD x = algebraMap (Per.BdRp l) (Per.BdR l) y :=
    fun x hx => exists_of_mem_FilD_zero ((T.fil _ _ _).1 hx)
  have hU := TiedUnif.tied_uniformiser l P AI T
  refine ⟨{
    θ := fun x => thetaExt (T.eD x)
    θ_one := ?_
    θ_add := fun x hx y hy => ?_
    θ_mul := fun x hx y hy => ?_
    θ_onto := fun c => ?_
    θ_ker := fun x hx => ?_
    θ_act := fun g x hx => ?_
    θ_Om := fun x => ?_
    θ_int := fun a => ?_
    θ_teich := fun x y h => ?_
    fil_succ_iff_mul_t := hU.2.2 _
    t_μ := hU.1 _ }⟩
  · rw [map_one, ← map_one (algebraMap (Per.BdRp l) (Per.BdR l)), thetaExt_alg, map_one]
  · obtain ⟨u, hu⟩ := hex x hx
    obtain ⟨v, hv⟩ := hex y hy
    rw [map_add, hu, hv, ← map_add, thetaExt_alg, thetaExt_alg, thetaExt_alg, map_add]
  · obtain ⟨u, hu⟩ := hex x hx
    obtain ⟨v, hv⟩ := hex y hy
    rw [map_mul, hu, hv, ← map_mul, thetaExt_alg, thetaExt_alg, thetaExt_alg, map_mul]
  · obtain ⟨y, rfl⟩ := (thetaD_props l).1 c
    refine ⟨T.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) y), ?_, ?_⟩
    · rw [T.fil, RingEquiv.apply_symm_apply]
      exact TiedUnif.alg_mem_FilD_zero y
    · rw [RingEquiv.apply_symm_apply, thetaExt_alg]
  · obtain ⟨u, hu⟩ := hex x hx
    rw [T.fil, hu, thetaExt_alg, (thetaD_props l).2.1]
    exact ((filD_laws l).2.2.2.2.2.2 1 u).symm
  · obtain ⟨u, hu⟩ := hex x hx
    rw [T.actD, hu, (ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.1, thetaExt_alg, thetaExt_alg,
      (thetaD_props l).2.2.2.2, actC_eq]
  · obtain ⟨y, hy, hθ⟩ := T.om x
    rw [hy, thetaExt_alg, hθ]
  · rw [TiedUnif.eD_ιA T, thetaExt_alg, (thetaD_props l).2.2.2.1]
    exact (GlobalTheory.RingBasics.mem_OC _).1 (Per.θ l a).2
  · rw [TiedUnif.eD_ιA T, thetaExt_alg, (thetaD_props l).2.2.2.1,
      WittVector.fontaineTheta_teichmuller]
    exact norm_untilt_sub x y h

end GlobalTheory.MemLoc.TiedTheta
