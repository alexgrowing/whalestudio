import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SemidefG
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsVecOfHermRep
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLand

noncomputable section

open NumberField Module Formalism.MainNotions.S
open Classical

namespace Formalism.L2.SG.Pf.Cnt.R1

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}

theorem surj_pairing {m : ℕ} (f : Fin m → S.V) (hf : LinearIndependent E f) :
    Function.Surjective (LinearMap.pi (fun a => S.hT (f a)) : S.V →ₗ[E] (Fin m → E)) := by
  rw [← LinearMap.range_eq_top]
  by_contra hne
  obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance
  set c : Fin m → E := fun a => φ (fun j => if a = j then 1 else 0) with hc
  have hφx : ∀ x : Fin m → E, φ x = ∑ a, x a * c a := by
    intro x
    conv_lhs => rw [pi_eq_sum_univ x]
    simp [map_sum, map_smul, hc]
  have hv : ∀ v : S.V, S.hT (∑ a, star (c a) • f a) v = 0 := by
    intro v
    have h1 : φ ((LinearMap.pi (fun a => S.hT (f a)) : S.V →ₗ[E] (Fin m → E)) v) = 0 := by
      have : (LinearMap.pi (fun a => S.hT (f a)) : S.V →ₗ[E] (Fin m → E)) v ∈
          LinearMap.range (LinearMap.pi (fun a => S.hT (f a)) : S.V →ₗ[E] (Fin m → E)) := ⟨v, rfl⟩
      have h2 := Submodule.mem_map_of_mem (f := φ) this
      exact (Submodule.eq_bot_iff _).1 hφ _ h2
    rw [hφx] at h1
    rw [map_sum, LinearMap.sum_apply]
    simp only [LinearMap.map_smulₛₗ, starRingEnd_apply, star_star, LinearMap.smul_apply, smul_eq_mul]
    rw [← h1]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [LinearMap.pi_apply, mul_comm]
  have h0 : ∑ a, star (c a) • f a = 0 := S.nondeg.1 _ hv
  have hc0 : ∀ a, c a = 0 := by
    intro a
    have := Fintype.linearIndependent_iff.1 hf _ h0 a
    simpa using this
  apply hφ0
  apply LinearMap.ext
  intro x
  rw [hφx]
  simp [hc0]

variable {r : ℕ}

theorem exists_dual_gen (e : Fin r → S.V) (z : S.V) (N : ℕ) (hN : 0 < N) (hind : LinearIndependent E e)
    (he : ∀ a b, S.hT (e a) (e b) = 0) (hez : ∀ a, S.hT (e a) z = 0) (hzz : S.hT z z = -(N : E)) :
    ∃ y : Fin r → S.V, Dual e y z N := by
  let f : Fin (r + 1) → S.V := Fin.snoc (α := fun _ => S.V) e z
  have hze : ∀ a, S.hT z (e a) = 0 := fun a => hsw0 S (hez a)
  have hzz0 : S.hT z z ≠ 0 := by rw [hzz, neg_ne_zero]; exact_mod_cast hN.ne'
  have hf : LinearIndependent E f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    rw [Fin.sum_univ_castSucc] at hc
    simp only [f, Fin.snoc_castSucc, Fin.snoc_last] at hc
    have hl : c (Fin.last r) = 0 := by
      have h1 := congrArg (S.hT z) hc
      rw [map_add, map_sum, map_zero] at h1
      simp only [map_smul, smul_eq_mul, hze, mul_zero, Finset.sum_const_zero, zero_add] at h1
      exact (mul_eq_zero.1 h1).resolve_right hzz0
    rw [hl, zero_smul, add_zero] at hc
    have hcs := Fintype.linearIndependent_iff.1 hind _ hc
    intro i
    induction i using Fin.lastCases with
    | last => exact hl
    | cast a => exact hcs a
  have hs := surj_pairing f hf
  choose y0 hy0 using fun a : Fin r => hs (fun j => if j = Fin.castSucc a then (1 : E) else 0)
  have hey0 : ∀ b a, S.hT (e b) (y0 a) = if b = a then 1 else 0 := by
    intro b a
    have := congrFun (hy0 a) (Fin.castSucc b)
    simp only [LinearMap.pi_apply, f, Fin.snoc_castSucc, Fin.castSucc_inj] at this
    exact this
  have hzy0 : ∀ a, S.hT z (y0 a) = 0 := by
    intro a
    have := congrFun (hy0 a) (Fin.last r)
    simp only [LinearMap.pi_apply, f, Fin.snoc_last] at this
    rw [this, if_neg (Fin.castSucc_lt_last a).ne']
  have hy0e : ∀ a d, S.hT (y0 a) (e d) = if d = a then 1 else 0 := by
    intro a d; rw [hsw, hey0]; split_ifs <;> simp
  have hL : ∀ (c : Fin r → E) (v : S.V), S.hT (∑ d, c d • e d) v = ∑ d, star (c d) * S.hT (e d) v := by
    intro c v
    rw [map_sum, LinearMap.sum_apply]
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]
  have hR : ∀ (c : Fin r → E) (v : S.V), S.hT v (∑ d, c d • e d) = ∑ d, c d * S.hT v (e d) := by
    intro c v
    simp only [map_sum, map_smul, smul_eq_mul]
  set c : Fin r → Fin r → E := fun a d => S.hT (y0 d) (y0 a) / 2 with hc
  set y : Fin r → S.V := fun a => y0 a - ∑ d, c a d • e d with hy
  have hst : ∀ a b, star (S.hT (y0 b) (y0 a)) = S.hT (y0 a) (y0 b) := fun a b => (hsw S _ _).symm
  refine ⟨y, ⟨he, fun a b => ?_, fun a b => ?_, hez, fun a => ?_, hzz⟩⟩
  · have h1 : S.hT (y0 a) (∑ d, c b d • e d) = c b a := by
      rw [hR]; simp [hy0e]
    have h2 : S.hT (∑ d, c a d • e d) (y0 b) = star (c a b) := by
      rw [hL]; simp [hey0]
    have h3 : S.hT (∑ d, c a d • e d) (∑ d, c b d • e d) = 0 := by
      rw [hL]; simp [hR, he]
    simp only [hy, map_sub, LinearMap.sub_apply, h1, h2, h3]
    simp only [hc]
    rw [star_div₀, hst, star_ofNat]
    ring
  · simp only [hy, map_sub, hR, hey0, he, mul_zero, Finset.sum_const_zero, sub_zero]
  · simp only [hy, map_sub, LinearMap.sub_apply, hL, hez, mul_zero, Finset.sum_const_zero, sub_zero]
    rw [hsw, hzy0, star_zero]

def Wsp (e y : Fin r → S.V) (z : S.V) : Submodule E S.V :=
  LinearMap.ker (LinearMap.pi (Sum.elim (Sum.elim (fun a => S.hT (e a)) (fun a => S.hT (y a)))
    (fun _ : Unit => S.hT z)) : S.V →ₗ[E] ((Fin r ⊕ Fin r) ⊕ Unit → E))

theorem mem_Wsp {e y : Fin r → S.V} {z w : S.V} : w ∈ Wsp e y z ↔ IsW e y z w := by
  simp only [Wsp, LinearMap.mem_ker, funext_iff, LinearMap.pi_apply, Pi.zero_apply, Sum.forall,
    Sum.elim_inl, Sum.elim_inr, forall_const, IsW]
  tauto

theorem finrank_Wsp (e y : Fin r → S.V) (z : S.V) :
    finrank E S.V ≤ finrank E (Wsp e y z) + (2 * r + 1) := by
  have h := LinearMap.finrank_range_add_finrank_ker (LinearMap.pi (Sum.elim (Sum.elim (fun a => S.hT (e a))
    (fun a => S.hT (y a))) (fun _ : Unit => S.hT z)) : S.V →ₗ[E] ((Fin r ⊕ Fin r) ⊕ Unit → E))
  have h2 := Submodule.finrank_le (LinearMap.range (LinearMap.pi (Sum.elim (Sum.elim (fun a => S.hT (e a))
    (fun a => S.hT (y a))) (fun _ : Unit => S.hT z)) : S.V →ₗ[E] ((Fin r ⊕ Fin r) ⊕ Unit → E)))
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit] at h2
  rw [Wsp]
  omega

end Gen

section D7

variable (D : Formalism.BasicNotions.D7)

theorem dual_of_flag {N : ℕ} (hN : 0 < N) (F0 : FlagG (VS D) D.R.rS (N : D.host.E)) :
    ∃ y, Dual F0.e y F0.z N :=
  exists_dual_gen F0.e F0.z N hN F0.e_indep F0.e_iso F0.z_orth F0.z_norm

theorem posW {N : ℕ} (hN : 0 < N) {e y : Fin D.R.rS → (VS D).V} {z : (VS D).V} (h : Dual e y z N)
    (w : (VS D).V) (hw : IsW e y z w) (hw0 : w ≠ 0) (φ : D.host.E →+* ℂ) : 0 < (φ ((VS D).hT w w)).re := by
  have hτ : ∀ τ : D.host.E →+* ℂ, ∀ a, τ (star a) = starRingEnd ℂ (τ a) := fun τ => D.sp.cm.cmUnram.2.1 τ
  have hsemi : ∀ τ : D.host.E →+* ℂ, ∀ v, IsW e y z v → 0 ≤ (τ ((VS D).hT v v)).re := by
    intro τ v hv
    have hs := D.sp.Y_sig 0 τ
    rw [D.sp.baseSpace_signature_eq τ] at hs
    exact semidefG h hN τ (hτ τ) hs v hv
  refine lt_of_le_of_ne (hsemi φ w hw) fun h0 => hw0 ?_
  refine isoZeroG h hN φ (hτ φ) (hsemi φ) w hw ?_
  apply φ.injective
  rw [real_of φ (hτ φ) w, ← h0, Complex.ofReal_zero, map_zero]

theorem two_le_Wsp (e y : Fin D.R.rS → (VS D).V) (z : (VS D).V) : 2 ≤ finrank D.host.E (Wsp e y z) := by
  have hV : finrank D.host.E (VS D).V = D.R.k + D.R.m - 1 := by
    rw [(VS D).rank_eq, D.sp.Y_rank 0 (Nat.zero_le _)]
    simp [Formalism.BasicNotions.Ranks.rankY, Formalism.BasicNotions.Ranks.r]
  have hm2 := D.R.two_le_m
  obtain ⟨j, hj⟩ := D.R.m_even
  have hrS : 2 * D.R.rS + 1 = D.R.m - 1 := by
    unfold Formalism.BasicNotions.Ranks.rS
    rw [hj]
    omega
  have h1 := finrank_Wsp e y z
  rw [hV, hrS] at h1
  have hk := D.R.f_le_k
  have he : 0 < D.R.ord := D.R.ord_pos
  generalize finrank D.host.E (Wsp e y z) = w at h1 ⊢
  omega

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem exists_W_vec {N : ℕ} (hN : 0 < N) {e y : Fin D.R.rS → (VS D).V} {z : (VS D).V} (h : Dual e y z N)
    (t : D.host.E) (ht : star t = t) (htp : Formalism.HermitianLattices.Ext.L3.TotPos t) :
    ∃ w : (VS D).V, IsW e y z w ∧ (VS D).hT w w = t := by
  let hW : Wsp e y z →ₗ⋆[D.host.E] Wsp e y z →ₗ[D.host.E] D.host.E :=
    ((VS D).hT.comp (Wsp e y z).subtype).compl₂ (Wsp e y z).subtype
  have hs : hW.IsSymm := ⟨fun x x' => (VS D).herm.eq x x'⟩
  have hd : Formalism.HermitianLattices.Ext.L3.IsTotPosDef hW := by
    intro x hx φ
    have hx' : (x : (VS D).V) ≠ 0 := fun h0 => hx (Subtype.ext h0)
    exact posW D hN h x (mem_Wsp.1 x.2) hx' φ
  obtain ⟨x, hx⟩ := Formalism.HermitianLattices.Ext.L3.exists_vec_of_hermRep Formalism.HermitianLattices.Ext.L3.hermRepUnram D.sp.cm.cmUnram hs hd
    (two_le_Wsp D e y z) t ht htp
  exact ⟨x, mem_Wsp.1 x.2, hx⟩

end D7

end Formalism.L2.SG.Pf.Cnt.R1
