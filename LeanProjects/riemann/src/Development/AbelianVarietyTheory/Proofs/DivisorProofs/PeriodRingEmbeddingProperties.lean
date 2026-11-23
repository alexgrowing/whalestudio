import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.LtChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfInAMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTateDcrisFrobeniusEigen
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnramifiedWittElementEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFilPIffEvPt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JMemFilPOfApprox
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.PMC GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.MemLoc GlobalTheory.BKReal GlobalTheory.Prism
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CrisToDR

variable {l : ℕ} [Fact l.Prime]

def psiA (C : Core l) (K : FinExt l) : AK K →+* Per.BdRp l :=
  GlobalTheory.AinfK.lift (aDp l) (C.o.comp (K.1.val.toRingHom.comp (oK K))) fun w =>
    (GlobalTheory.SeedSec.o_eq_aDp_wA l (fK K) C w _
      (congrArg (fun y : Per.OC l => (y : ℂ_[l])) (intToOC_thetaW (fK K) K w)).symm).symm

theorem psiA_inA (C : Core l) (K : FinExt l) (a : Ainf l) : psiA C K (inA K a) = aDp l a := lift_inA _ _ _ a

theorem psiA_inO (C : Core l) (K : FinExt l) (c : ↥(OL K)) :
    psiA C K (inO K c) = C.o ((oK K c : ↥K.1) : Om l) := lift_inO _ _ _ c

theorem thetaD_psiA (C : Core l) (K : FinExt l) (x : AK K) :
    Per.θD l (psiA C K x) = ((thetaK K x : OC l) : ℂ_[l]) :=
  GlobalTheory.AinfK.induction_on x (fun a c => by
    rw [map_mul, map_mul, map_mul, psiA_inA, psiA_inO, thetaK_inA, thetaK_inO, (thetaD_props l).2.2.2.1,
      C.o_sec.th]
    rfl)
    fun x y hx hy => by rw [map_add, map_add, map_add, hx, hy]; rfl

theorem mem_sq_of_psiA (C : Core l) (K : FinExt l) (x : AK K) (hx : thetaK K x = 0)
    (h2 : psiA C K x ∈ Per.FilP l 2) : x ∈ RingHom.ker (thetaK K) ^ 2 := by
  obtain ⟨π, hπ⟩ := exists_unif (K := K)
  obtain ⟨p, hp⟩ := GlobalTheory.MemLoc.FundOnto.untilt_surjective l (intToOC K π)
  have hk := ker_thetaK hπ hp
  obtain ⟨hF, hreg, -⟩ := filtration_eq_xi_pow l C.ε (core_isEps l C)
  have hdiv : ∀ y : AK K, thetaK K y = 0 → eta π p ∣ y := fun y hy => by
    rw [← Ideal.mem_span_singleton, ← hk]; exact hy
  obtain ⟨a, rfl⟩ := hdiv x hx
  have hξ : Per.θ l (xi C.ε) = 0 := by
    rw [← RingHom.mem_ker, C.ker_theta]; exact Ideal.mem_span_singleton_self _
  obtain ⟨b, hb⟩ := hdiv (inA K (xi C.ε)) (by rw [thetaK_inA, hξ])
  obtain ⟨z, hz⟩ := (hF 2 _).1 h2
  have hb' := congrArg (psiA C K) hb
  rw [psiA_inA, map_mul] at hb'
  rw [map_mul] at hz
  have h3 : psiA C K a - aDp l (xi C.ε) * (z * psiA C K b) = 0 := hreg _ (by
    linear_combination psiA C K a * hb' + psiA C K b * hz)
  have h4 := congrArg (Per.θD l) h3
  rw [map_sub, map_mul, (thetaD_props l).2.2.2.1, hξ, thetaD_psiA, map_zero] at h4
  have h5 : thetaK K a = 0 := Subtype.ext (by simpa using h4)
  rw [pow_two]
  exact Ideal.mul_mem_mul (thetaK_eta hp) h5

private theorem aB_eq_aC_pt (a : Ainf l) :
    Per.aB l a = algebraMap (Per.Acris l) (Per.Bcris l) (aC l a) := GlobalTheory.RingIface.aB_eq_alg l a

private theorem j_aC_pt (C : Core l) (a : Ainf l) : C.j (aC l a) = aDp l a :=
  (congrArg C.j (GlobalTheory.RingIface.tower l a)).trans
    (C.j_cris.on0 (algebraMap (Per.Ainf l) (Per.Acris0 l) a))

theorem exists_map : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ K : FinExt l, ∃ Ψ : BK K →+* P.R.BdR,
      (∀ c : ↥K.1, Ψ (inK K c) = algebraMap ↥K.1 P.R.BdR c) ∧
      (∀ (g : ↥(GK K)) (b : BK K), (P.PD K).actdR g (Ψ b) = Ψ (galB g b)) ∧
      (∀ b, Ψ b ∈ (P.PD K).Fil 0) ∧
      (∀ x : AK K, thetaK K x = 0 → Ψ (toB K (ofA K x)) ∈ (P.PD K).Fil 1) ∧
      (∀ x : AK K, thetaK K x = 0 → x ∉ RingHom.ker (thetaK K) ^ 2 → Ψ (toB K (ofA K x)) ∉ (P.PD K).Fil 2) := by
  intro l _ P AI ⟨T⟩ K
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  let j : Per.Acris l →+* P.R.B := T.eB.symm.toRingHom.comp (algebraMap (Per.Acris l) (Per.Bcris l))
  let u : Per.Acris l →+* P.R.BdR := (P.PD K).ι.toRingHom.comp j
  have hu : ∀ a, u a = (P.PD K).ι (T.eB.symm (algebraMap (Per.Acris l) (Per.Bcris l) a)) := fun _ => rfl
  have huv : ∀ w : W0 K, u (aC l (wA l (fK K) w)) = algebraMap ↥K.1 P.R.BdR (oK K (thetaW (fK K) K w)) := fun w =>
    (GlobalTheory.WittCompat.exists_unramified_witt_element l P AI T K w).elim fun c hc =>
      (((congrArg (fun b => (P.PD K).ι (T.eB.symm b)) (aB_eq_aC_pt _).symm).trans
        (congrArg (P.PD K).ι hc.2).symm).trans ((P.PD K).ι.commutes c)).trans
        ((IsScalarTower.algebraMap_apply ↥(K0 K) ↥K.1 P.R.BdR c).trans (congrArg _ hc.1))
  have h1 := liftB_inK u (algebraMap ↥K.1 P.R.BdR) huv
  have h2 := liftB_inC u (algebraMap ↥K.1 P.R.BdR) huv
  generalize liftB u (algebraMap ↥K.1 P.R.BdR) huv = Ψ at h1 h2
  have hD : ∀ a, T.eD (u a) = algebraMap (Per.BdRp l) (Per.BdR l) (C.j a) := fun a => by
    rw [hu, P.PD_ι, hC.ι, RingEquiv.apply_symm_apply, C.ι_j]
  have hA : ∀ x : AK K, T.eD (Ψ (toB K (ofA K x))) = algebraMap (Per.BdRp l) (Per.BdR l) (psiA C K x) := fun x =>
    GlobalTheory.AinfK.induction_on x (fun a c => by
      simp only [map_mul]
      rw [ofA_inA, ofA_inO, ← inK_oK, h1, h2, hD, psiA_inA, psiA_inO]
      congr 1
      · exact congrArg _ (j_aC_pt C a)
      · exact hC.o _)
      fun x y hx hy => by simp only [map_add, hx, hy]
  have hfil : ∀ (n : ℕ) (x : AK K), Ψ (toB K (ofA K x)) ∈ (P.PD K).Fil n ↔ psiA C K x ∈ Per.FilP l n := fun n x => by
    rw [T.fil, hA, GlobalTheory.BKGal.TaylorFil.alg_mem_FilD_iff]
  have hsm : ∀ (c : ↥K.1) (b : BK K), Ψ (inK K c * b) = c • Ψ b := fun c b => by
    rw [map_mul, h1, Algebra.smul_def]
  refine ⟨Ψ, h1, fun g b => ?_, fun b => ?_, fun x hx => ?_, fun x hx hx2 h => ?_⟩
  · refine RingHom.congr_fun (GlobalTheory.PZ.ColmezVec.ext_BK (((P.PD K).actdR g).toAlgHom.toRingHom.comp Ψ)
      (Ψ.comp (galB g)) (fun c => ?_) fun a => ?_) b
    · rw [RingHom.comp_apply, RingHom.comp_apply, galB_inK, h1]
      exact ((P.PD K).actdR g).commutes c
    · rw [RingHom.comp_apply, RingHom.comp_apply, galB_toB, galC_inC, h2, h2, hu, hu,
        ← GlobalTheory.PZ.ColmezVec.act_acris T K g, (P.PD K).ι_comm]
      rfl
  · obtain ⟨D, z, hz⟩ := exists_pow_mul b
    have hz0 : Ψ (toB K z) ∈ (P.PD K).Fil 0 := GlobalTheory.AcrisK.induction_on z (fun a c => by
      rw [map_mul, ← inK_oK, mul_comm, hsm, h2]
      refine Submodule.smul_mem _ _ ?_
      rw [T.fil, hD]
      exact GlobalTheory.MemLoc.TiedUnif.alg_mem_FilD_zero _)
      fun x y hx hy => by rw [map_add, map_add]; exact add_mem hx hy
    have hl : ((l : ↥K.1) ^ D) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
    rw [← hz, ← map_natCast (inK K), ← map_pow, hsm] at hz0
    exact (Submodule.smul_mem_iff _ hl).1 hz0
  · refine (hfil 1 x).2 (((thetaD_props l).2.1 _).1 ?_)
    rw [thetaD_psiA, hx]
    rfl
  · exact hx2 (mem_sq_of_psiA C K x hx ((hfil 2 x).1 h))

end GlobalTheory.CrisToDR

end
