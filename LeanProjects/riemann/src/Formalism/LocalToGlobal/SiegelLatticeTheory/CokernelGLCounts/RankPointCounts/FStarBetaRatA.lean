import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBetaS
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarIsomG
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarNMove
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdNA

noncomputable section

open scoped Classical
open Matrix Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BRat

open FsLA BwdBetaS OmP

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}

def projL {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → S.V) : S.V →ₗ[E] S.V where
  toFun v := lin u (pc u v)
  map_add' x y := by rw [pc_add, lin_add]
  map_smul' t x := by rw [pc_smul, lin_smul, RingHom.id_apply]

def moveL {ι : Type*} [Fintype ι] [DecidableEq ι] (u u' : ι → S.V) : S.V →ₗ[E] S.V where
  toFun v := lin u' (pc u v)
  map_add' x y := by rw [pc_add, lin_add]
  map_smul' t x := by rw [pc_smul, lin_smul, RingHom.id_apply]

theorem pc_of_orth {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → S.V) {y : S.V} (hy : ∀ k, S.hT (u k) y = 0) :
    pc u y = 0 := by
  have h0 : (fun k => S.hT (u k) y) = 0 := funext fun k => hy k
  rw [pc, h0, Matrix.mulVec_zero]

theorem lin_zero {ι : Type*} [Fintype ι] (u : ι → S.V) : lin u 0 = 0 := by simp [lin]

theorem isometry_extension_two {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (u u' : ι → S.V) (w : κ → S.V) (hG : gram S u' u' = gram S u u) (hdet : (gram S u u).det ≠ 0)
    (hdetw : (gram S w w).det ≠ 0) (hsp : ∀ i, u' i ∈ Submodule.span E (Set.range w))
    (hkey : ∀ y y', (∀ k, S.hT (u k) y = 0) → (∀ k, S.hT (u k) y' = 0) →
      S.hT (lin w (pc w y)) (lin w (pc w y')) = 0) :
    ∃ g : S.V ≃ₗ[E] S.V, (∀ x y, S.hT (g x) (g y) = S.hT x y) ∧ (∀ i, g (u i) = u' i) ∧
      (∀ y, (∀ k, S.hT (u k) y = 0) → g y = y - lin w (pc w y)) := by
  let P : S.V →ₗ[E] S.V := LinearMap.id - projL u
  let β : S.V →ₗ[E] S.V := (LinearMap.id - projL w) ∘ₗ P + moveL u u'
  have hβ : ∀ v, β v = ((v - lin u (pc u v)) - lin w (pc w (v - lin u (pc u v)))) + lin u' (pc u v) :=
    fun v => rfl
  have hsp' : ∀ c, lin u' c ∈ Submodule.span E (Set.range w) := fun c =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hsp i)
  have hGe : ∀ i j, S.hT (u' i) (u' j) = S.hT (u i) (u j) := fun i j => congrFun (congrFun hG i) j
  have hiso : ∀ x y, S.hT (β x) (β y) = S.hT x y := by
    intro x y
    set x' := x - lin u (pc u x) with hx'
    set y' := y - lin u (pc u y) with hy'
    have hx'u : ∀ k, S.hT (u k) x' = 0 := fun k => hT_u_rem u hdet x k
    have hy'u : ∀ k, S.hT (u k) y' = 0 := fun k => hT_u_rem u hdet y k
    have hk := hkey x' y' hx'u hy'u
    rw [hβ, hβ]

    have t1 : S.hT (x' - lin w (pc w x')) (lin u' (pc u y)) = 0 := (hT_span_rem w hdetw x' _ (hsp' _)).2
    have t2 : S.hT (lin u' (pc u x)) (y' - lin w (pc w y')) = 0 := (hT_span_rem w hdetw y' _ (hsp' _)).1
    have t3 : S.hT (lin u' (pc u x)) (lin u' (pc u y)) = S.hT (lin u (pc u x)) (lin u (pc u y)) := by
      rw [hT_lin_lin, hT_lin_lin]; simp only [hGe]
    have t4 : S.hT (x' - lin w (pc w x')) (lin w (pc w y')) = 0 :=
      (hT_span_rem w hdetw x' _ (lin_sub w _)).2
    have t5 : S.hT (lin w (pc w x')) (y' - lin w (pc w y')) = 0 :=
      (hT_span_rem w hdetw y' _ (lin_sub w _)).1
    have t6 : S.hT (x' - lin w (pc w x')) (y' - lin w (pc w y')) = S.hT x' y' := by
      have e1 : S.hT (x' - lin w (pc w x')) (y' - lin w (pc w y')) =
          S.hT (x' - lin w (pc w x')) y' := by
        rw [map_sub, t4, sub_zero]
      have e2 : S.hT (lin w (pc w x')) y' = 0 := by
        have := t5
        rw [map_sub, hk, sub_zero] at this
        exact this
      rw [e1, map_sub S.hT x' (lin w (pc w x')), LinearMap.sub_apply, e2, sub_zero]
    have hxy : S.hT x y = S.hT x' y' + S.hT (lin u (pc u x)) (lin u (pc u y)) := by
      have dx : x = x' + lin u (pc u x) := by rw [hx']; abel
      have dy : y = y' + lin u (pc u y) := by rw [hy']; abel
      conv_lhs => rw [dx, dy]
      simp only [map_add, LinearMap.add_apply]
      rw [(hT_span_rem u hdet x _ (lin_sub u _)).2, (hT_span_rem u hdet y _ (lin_sub u _)).1]
      ring
    rw [← hx', ← hy']
    simp only [map_add, LinearMap.add_apply]
    rw [t1, t2, t3, t6, hxy]
    ring
  have hinj : Function.Injective β := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro v hv
    rw [LinearMap.mem_ker] at hv
    refine (Submodule.mem_bot E).2 (S.nondeg.1 v fun y => ?_)
    rw [← hiso v y, hv, map_zero, LinearMap.zero_apply]
  have hbij : Function.Bijective β := ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩
  refine ⟨LinearEquiv.ofBijective β hbij, hiso, fun i => ?_, fun y hy => ?_⟩
  · show β (u i) = u' i
    rw [hβ, pc_self u hdet, lin_single, lin_single, sub_self]
    have : pc w (0 : S.V) = 0 := by
      have := pc_smul w 0 0
      simpa using this
    rw [this, lin_zero, sub_zero, zero_add]
  · show β y = y - lin w (pc w y)
    rw [hβ, pc_of_orth u hy, lin_zero, lin_zero, sub_zero, add_zero]

variable {r : ℕ}

theorem norm_om_ne {TA TB : E} (A : FlagG S r TA) (B : FlagG S r TB) (hdet : (Zhat A B).det ≠ 0) {Ω : S.V}
    (hΩ : OmV A B Ω) (hG : Gflag A B ≠ 0) : 1 + TA * S.hT Ω Ω ≠ 0 := by
  have hx := om_zcoef A B hdet hΩ
  set c := (Zhat A B)⁻¹ (Fin.last r) (Fin.last r) with hc
  set x := Ω - c • B.z with hxd
  have hΩe : Ω = x + c • B.z := by rw [hxd]; abel
  have hxx : S.hT x x = 0 := NMoveP.hT_X_X B hx hx
  have hxz : S.hT x B.z = 0 := by
    have h := NMoveP.hT_f_X B (Fin.last r) hx
    rw [NMoveP.fvecL] at h
    rw [BwdNA.hsw S B.z x, h, star_zero]
  have hzx : S.hT B.z x = 0 := by
    have h := NMoveP.hT_f_X B (Fin.last r) hx
    rwa [NMoveP.fvecL] at h
  have hnorm : S.hT Ω Ω = star c * c * (-TB) := by
    rw [hΩe]
    simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, map_smul, LinearMap.smul_apply, hxx, hxz, hzx,
      B.z_norm, smul_eq_mul, starRingEnd_apply, mul_zero, zero_add, add_zero]
    ring
  have hcl : c = leadMinorE (Zhat A B) r / (Zhat A B).det := inv_last _
  intro h0
  apply hG
  unfold Gflag Dl
  rw [FsLA.leadMinorE_full]
  rw [hnorm, hcl, star_div₀] at h0
  have hs : star (Zhat A B).det ≠ 0 := star_ne_zero.2 hdet
  field_simp at h0
  linear_combination h0

theorem key_X {TA TB : E} (A : FlagG S r TA) (B : FlagG S r TB) (hdet : (Zhat A B).det ≠ 0) {Ω : S.V}
    (hΩ : OmV A B Ω) (hG : Gflag A B ≠ 0) {q : S.V}
    (hq : q ∈ Submodule.span E (Set.range (Sum.elim A.fvec B.fvec))) (hqA : ∀ a, S.hT (A.fvec a) q = 0)
    (hqΩ : S.hT Ω q = 0) : q ∈ A.X := by
  obtain ⟨x, hx, c, rfl⟩ := dec A B hdet hΩ hq hqA
  have hΩx : S.hT Ω x = 0 := by
    rw [BwdNA.hsw S x Ω]
    have : x ∈ A.X := hx
    have h := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth S).1 (show Ω ∈ orth S A.X from ?_) x this
    · rw [h, star_zero]
    · refine (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth S).2 fun y hy => ?_
      change y ∈ Submodule.span E (Set.range A.e) at hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        rw [← fvec_cs, hΩ.2]
        simp [Fin.castSucc_ne_last]
      | zero => simp
      | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
      | smul t y _ hy => rw [BwdNA.hT_smulL, hy, mul_zero]
  have hΩz : S.hT Ω A.z = 1 := by
    rw [BwdNA.hsw S A.z Ω, ← fvec_last, hΩ.2]
    simp
  have h1 : S.hT Ω (x + c • (A.z + TA • Ω)) = c * (1 + TA * S.hT Ω Ω) := by
    rw [map_add, hΩx, zero_add, map_smul, map_add, map_smul, hΩz, smul_eq_mul, smul_eq_mul]
  rw [h1] at hqΩ
  have hc : c = 0 := (mul_eq_zero.1 hqΩ).resolve_right (norm_om_ne A B hdet hΩ hG)
  rw [hc, zero_smul, add_zero]
  exact hx

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BRat
