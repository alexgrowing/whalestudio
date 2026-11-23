import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGQQSSFCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGenTransferFn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCRadSpSmooth
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateCommuteRaisingConstant

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.GQ

noncomputable section

open Classical

theorem lagrange_all {T : Type} [Fintype T] (K : (T → ℂ) → Prop) (hc : ∀ c : ℂ, K fun _ => c)
    (hadd : ∀ f g, K f → K g → K (f + g)) (hmul : ∀ f g, K f → K g → K (f * g))
    (x : T → ℂ) (hx : K x) (hinj : Function.Injective x) : ∀ f, K f := by
  classical
  have hsum : ∀ (ι : Type) (s : Finset ι) (g : ι → T → ℂ), (∀ i ∈ s, K (g i)) → K (∑ i ∈ s, g i) := by
    intro ι s g
    refine Finset.induction_on s ?_ ?_
    · intro _
      rw [Finset.sum_empty]
      exact hc 0
    · intro a s ha ih hg
      rw [Finset.sum_insert ha]
      exact hadd _ _ (hg a (Finset.mem_insert_self a s)) (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))
  have hprod : ∀ (ι : Type) (s : Finset ι) (g : ι → T → ℂ), (∀ i ∈ s, K (g i)) → K (∏ i ∈ s, g i) := by
    intro ι s g
    refine Finset.induction_on s ?_ ?_
    · intro _
      rw [Finset.prod_empty]
      exact hc 1
    · intro a s ha ih hg
      rw [Finset.prod_insert ha]
      exact hmul _ _ (hg a (Finset.mem_insert_self a s)) (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))
  intro f
  have key : f = ∑ t, (fun _ : T => f t) *
      ∏ s ∈ Finset.univ.erase t, ((x + fun _ : T => -x s) * fun _ : T => (x t - x s)⁻¹) := by
    funext u
    simp only [Finset.sum_apply, Pi.mul_apply, Finset.prod_apply, Pi.add_apply]
    rw [Finset.sum_eq_single u]
    · rw [Finset.prod_eq_one, mul_one]
      intro s hs
      have hne : x u - x s ≠ 0 := sub_ne_zero.mpr (fun h => (Finset.ne_of_mem_erase hs) (hinj h).symm)
      rw [← sub_eq_add_neg, mul_inv_cancel₀ hne]
    · intro t _ htu
      rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm htu, Finset.mem_univ u⟩), mul_zero]
      rw [add_neg_cancel, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ u) h
  rw [key]
  exact hsum _ _ _ fun t _ => hmul _ _ (hc _) (hprod _ _ _ fun s _ => hmul _ _ (hadd _ _ hx (hc _)) (hc _))

section main

open Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.GT

theorem quadratic_kappa_identity : GQKap := by
  intro Wp Wq _ _ _ _ _ _ P Bs hk X d hA e he hQ
  obtain ⟨hpl, hL, -, -, -⟩ := hA
  have hsm : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') ρ,
      rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ ∈ MA.smSub P.r P.TT :=
    fun Φ ρ => radial_space_smoothness Wp Wq P Bs hpl hk e he Φ ρ
  have hP : P.OK := hpl.1
  have hz := fun q => (sec_pt P Bs hpl q).2
  have hgg : ∀ q : MA.Qp P.r P.TT, ((ggS P : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q =
      q.1.2 * (starRingEnd ℂ) q.1.2 - (P.TT : ℂ) := fun q => by
    show ((MA.coordQ (r := P.r) (TT := P.TT) M.vz : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q *
        ((MA.coordQ (r := P.r) (TT := P.TT) M.vzb : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q - (P.TT : ℂ) = _
    rw [coordQ_vz, coordQ_vzb]
  have hggv : ∀ q : MA.Qp P.r P.TT, ((ggS P : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q ≠ 0 :=
    fun q => by rw [hgg]; exact gg_ne P q
  have hGG : ∀ q : MA.Qp P.r P.TT, ((Q.GGl P.k P.r Bs.z Bs.z' (NF.muZ P.k P.r Bs.μsec q.1.2) : ℝ) : ℂ) =
      q.1.2 * (starRingEnd ℂ) q.1.2 - (P.TT : ℂ) := fun q => by
    rw [Complex.mul_conj]
    unfold Q.GGl
    rw [hz q, hpl.2.2.2.1, hpl.2.2.2.2.1]
    have hT : ((P.TT : ℝ) : ℂ) = (P.T : ℂ) * (P.T' : ℂ) := by
      show (((P.T * P.T' : ℝ)) : ℂ) = _
      push_cast; ring
    rw [hT]
    push_cast
    ring
  have hsc : ∀ (w : (MA.DQ P).Pr) (f : M.Ty P → MA.SmQ P.r P.TT),
      MA.actA P (MA.sc P (MA.DQ P) w) f = fun ρ => w.1 (f ρ) := VLem.actA_sc P
  have hGGi : Intw P Bs e d.L.GGi (MA.ggiA P (MA.DQ P)) := by
    intro Φ
    rw [hL.2.2.2.2.2.2.2.2.2.2.2.1]
    refine (trR_fn P Bs hpl X e 5 (Ring.inverse (ggS P))
      (fun q => by rw [inverse_apply _ hggv]; exact inv_ne_zero (hggv q))
      (fun q => by rw [inverse_apply _ hggv, hgg]; show ((Q.GGl _ _ _ _ _ : ℝ) : ℂ)⁻¹ = _; rw [hGG q]) Φ).trans ?_
    exact (hsc ((MA.DQ P).ggiP P.TT) (trR P Bs e Φ)).symm
  have hTT : 0 ≤ P.TT := (mul_pos hP.T_pos hP.T'_pos).le
  haveI : Fact ((MA.DQ P).Laws P.TT) := ⟨Formalism.FourierDecayAlt.P.analytic_laws P.r P.TT hTT⟩
  have hx : ∀ Y : ℝ, Intw P Bs e (d.κ fun ρ => M.xC P ρ (Y : ℂ)) (MA.kap P (MA.DQ P) fun ρ => M.xC P ρ (Y : ℂ)) := by
    intro Y
    have h1 := intw_mul hsm hGGi (hQ Y 1 1)
    have e1 : d.L.GGi * d.QQ (Y : ℂ) 1 1 = d.κ fun ρ => M.xC P ρ (Y : ℂ) := by
      show d.L.GGi * (d.L.GG * d.x (Y : ℂ)) = _
      rw [← mul_assoc, d.L.GGi_GG, one_mul]; rfl
    have e2 : MA.ggiA P (MA.DQ P) * MA.QQr P (MA.DQ P) (Y : ℂ) 1 1 = MA.kap P (MA.DQ P) fun ρ => M.xC P ρ (Y : ℂ) := by
      show MA.ggiA P (MA.DQ P) * (MA.ggA P (MA.DQ P) * MA.xA P (MA.DQ P) (Y : ℂ)) = _
      rw [← mul_assoc, Formalism.FourierDecayAlt.P.MAx1.D5.ggi_gg, one_mul]; rfl
    rw [e1, e2] at h1; exact h1
  obtain ⟨Y₀, hinj⟩ := Formalism.FourierDecayAlt.P5.Kfp.sep_real hP
  refine lagrange_all (fun f => Intw P Bs e (d.κ f) (MA.kap P (MA.DQ P) f)) ?_ ?_ ?_ _ (hx Y₀) hinj
  · intro c
    have e1 : d.κ (fun _ => c) = algebraMap ℂ _ c := d.κ.commutes c
    have e2 : MA.kap P (MA.DQ P) (fun _ => c) = algebraMap ℂ _ c := (MA.kap P (MA.DQ P)).commutes c
    show Intw P Bs e (d.κ (fun _ => c)) (MA.kap P (MA.DQ P) (fun _ => c))
    rw [e1, e2]; exact intw_alg hsm c
  · intro f g hf hg
    show Intw P Bs e (d.κ (f + g)) (MA.kap P (MA.DQ P) (f + g))
    rw [map_add, map_add]; exact intw_add hsm hf hg
  · intro f g hf hg
    show Intw P Bs e (d.κ (f * g)) (MA.kap P (MA.DQ P) (f * g))
    rw [map_mul, map_mul]; exact intw_mul hsm hf hg

end main

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.GQ
