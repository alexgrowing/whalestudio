import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanOfPowMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinSectionTrivialisesInvertPrimeTensor
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.GalStep
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
variable {a : ℕ} [NeZero a] {e : ℕ} [NeZero e] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  {K : Type} [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type} [Fintype ι] [DecidableEq ι]

theorem YD_xiExt (P : PhiMod O K l e a ι) (α : ℕ)
    (hb : ∀ d : P.D, E K l e ^ α • P.xi d ∈ P.Man) {w : Vec K a ι} (hw : w ∈ P.Mext (invL l (S O K e))) :
    YD t ϖ (E K l e ^ α • P.xiExt w) = ∑ k, ϖ.iD t K (fun τ => hatR O (w τ k)) •
      YD t ϖ (E K l e ^ α • P.xi (fun _ => Pi.single k 1)) := by
  funext i
  simp only [YD, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [← map_mul]
  rw [← map_sum]
  congr 1
  funext τ
  have hw' : ∀ k, w τ k ∈ Rpi O K l e := fun k => invL_S_le_Rpi l e (mem_tot.1 hw τ k)
  have hb' : ∀ k, E K l e ^ α * P.xi (fun _ => Pi.single k 1) τ i ∈ Rpi O K l e := fun k =>
    mem_Rpi_of_mem_Man (hb (fun _ => Pi.single k 1)) τ i
  have hx : ∀ k, P.xi (fun _ => Pi.single k 1) τ i = P.xiMat τ i k := fun k => by
    rw [P.xi_apply, P.xiExt_apply]
    have : (cst (fun _ => Pi.single k 1 : P.D) : Vec K a ι) τ = Pi.single k 1 := by
      funext j
      change C ((Pi.single k 1 : ι → K) j) = _
      rw [Pi.single_apply, Pi.single_apply]
      split_ifs <;> simp
    rw [this]
    simp
  have hs : E K l e ^ α * P.xiExt w τ i = ∑ k, w τ k * (E K l e ^ α * P.xi (fun _ => Pi.single k 1) τ i) := by
    simp only [hx, P.xiExt_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hm : (∑ k, w τ k * (E K l e ^ α * P.xi (fun _ => Pi.single k 1) τ i)) ∈ Rpi O K l e :=
    Subalgebra.sum_mem _ fun k _ => mul_mem (hw' k) (hb' k)
  rw [hs, hatR_of_mem (O := O) hm, Finset.sum_apply]
  simp only [Pi.mul_apply, hatR_of_mem (O := O) (hw' _), hatR_of_mem (O := O) (hb' _), ← map_mul]
  rw [← map_sum]
  congr 1
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finsetSum]
  rfl

omit [NeZero a] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] in

theorem cst_mem_Mext (P : PhiMod O K l e a ι) (d : P.D) : (cst d : Vec K a ι) ∈ P.Mext (invL l (S O K e)) := by
  refine mem_tot.2 fun τ i => ?_
  exact HasK.C_mem (d τ i)

omit [NeZero a] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] in

theorem descN_mem_Mext (P : PhiMod O K l e a ι) (i : ℕ) (w : Vec K a ι) (hw : w ∈ P.Mext (invL l (S O K e))) :
    (fun τ j => descN K i (w τ j)) ∈ P.Mext (invL l (S O K e)) := by
  refine mem_tot.2 fun τ j => ?_
  obtain ⟨n, hn⟩ := mem_tot.1 hw τ j
  refine ⟨n, ?_⟩
  have h3 : (((l : S O K e) : K⟦X⟧)) ^ n = C ((l : K) ^ n) := by simp
  have h := descN_mem_S e i hn
  rwa [h3, ← smul_eq_C_mul, map_smul, smul_eq_C_mul, ← h3] at h

theorem E_pow_xiExt_mem_Man (P : PhiMod O K l e a ι) (α : ℕ) (hα : ∀ v ∈ P.L, E K l e ^ α • v ∈ P.M)
    (w : Vec K a ι) (hw : w ∈ P.Mext (invL l (S O K e))) : E K l e ^ α • P.xiExt w ∈ P.Man := by
  have h1 : P.xiExt w ∈ P.MMl := ((GlobalTheory.BK.xi_trivialises_invL_S O K l e a ι P).2 w).2 hw
  refine P.mem_Man.2 (mem_tot.2 fun τ i => ?_)
  obtain ⟨m, hm, h⟩ := P.mem_extc.1 (mem_tot.1 h1 τ)
  have hc : ∀ k, E K l e ^ α * P.mx τ i k ∈ A O K := fun k => by
    have hv : (Pi.single τ ((P.mx τ).col k) : Vec K a ι) ∈ P.L := mem_tot.2 fun σ => by
      by_cases hσ : σ = τ
      · subst hσ
        rw [Pi.single_eq_same]
        exact Submodule.subset_span ⟨k, rfl⟩
      · rw [Pi.single_eq_of_ne hσ]
        exact zero_mem _
    have h2 := mem_tot.1 (hα _ hv) τ i
    rwa [Pi.smul_apply, Pi.single_eq_same] at h2
  rw [Pi.smul_apply, h, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Subalgebra.sum_mem _ fun k _ => ?_
  rw [← mul_assoc]
  exact mul_mem (invL_S_le_Rpi l e (le_away _ _ (A_le_S l e (hc k)))) (invL_S_le_Rpi l e (hm k))

theorem taylor_vec (P : PhiMod O K l e a ι) (α : ℕ)
    (hdesc : ∀ (i : ℕ) (w : Vec K a ι), w ∈ P.Mext (invL l (S O K e)) →
      (fun τ j => descN K i (w τ j)) ∈ P.Mext (invL l (S O K e)))
    (hman : ∀ w ∈ P.Mext (invL l (S O K e)), E K l e ^ α • P.xiExt w ∈ P.Man)
    (σ : OD l O → OD l O) (ρ : (ι → OD l O) →+ (ι → OD l O)) (hρ : ∀ c y, ρ (c • y) = σ c • ρ y) (c : OD l O)
    (hor : ∀ d : P.D, ρ (YD t ϖ (E K l e ^ α • P.xi d)) = c • YD t ϖ (E K l e ^ α • P.xi d))
    (μ : ℕ → OD l O) (R : ℕ) (J : Ideal (OD l O))
    (hscal : ∀ f : ZMod a → K⟦X⟧, (∀ τ, f τ ∈ invL l (S O K e)) → σ (ϖ.iD t K (fun τ => hatR O (f τ))) -
      ∑ i ∈ Finset.range R, μ i * ϖ.iD t K (fun τ => hatR O (descN K i (f τ))) ∈ J)
    {w : Vec K a ι} (hw : w ∈ P.Mext (invL l (S O K e))) (j : ι) :
    ρ (YD t ϖ (E K l e ^ α • P.xiExt w)) j - c * ∑ i ∈ Finset.range R, μ i *
      YD t ϖ (E K l e ^ α • P.xiExt (fun τ k => descN K i (w τ k))) j ∈ J := by
  have hb : ∀ d : P.D, E K l e ^ α • P.xi d ∈ P.Man := fun d => hman _ (cst_mem_Mext P d)
  rw [YD_xiExt t ϖ P α hb hw, map_sum]
  simp only [YD_xiExt t ϖ P α hb (hdesc _ w hw), hρ, hor, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  refine J.sum_mem fun k _ => ?_
  have h := J.mul_mem_left (c * YD t ϖ (E K l e ^ α • P.xi (fun _ => Pi.single k 1)) j)
    (hscal (fun τ => w τ k) fun τ => mem_tot.1 hw τ k)
  convert h using 1
  rw [mul_sub, Finset.mul_sum]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun i _ => by ring

end GlobalTheory.GalStep

namespace GlobalTheory.GalStep
variable {l : ℕ} [Fact l.Prime]
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

def rhoDHom {LL : FinExt l} {ι : Type} (T : QLat LL)
    (jD : (ι → OD l ↥(OL LL)) ≃ₗ[OD l ↥(OL LL)] TW (OD l ↥(OL LL)) T) (g : Gl l) :
    (ι → OD l ↥(OL LL)) →+ (ι → OD l ↥(OL LL)) :=
  AddMonoidHom.mk' (rhoD T jD g) fun x y => by
    have h1 : jD (x + y) = jD x + jD y := jD.map_add x y
    have h2 := (TWact (galOD ↥(OL LL) (sQ l g)) T g).map_add (jD x) (jD y)
    have h3 := jD.symm.map_add (TWact (galOD ↥(OL LL) (sQ l g)) T g (jD x)) (TWact (galOD ↥(OL LL) (sQ l g)) T g (jD y))
    exact (congrArg (fun z => jD.symm (TWact (galOD ↥(OL LL) (sQ l g)) T g z)) h1).trans
      ((congrArg jD.symm h2).trans h3)
end GlobalTheory.GalStep
