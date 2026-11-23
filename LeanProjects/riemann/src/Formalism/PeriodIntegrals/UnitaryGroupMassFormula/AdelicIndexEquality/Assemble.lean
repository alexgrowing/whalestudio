import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.ModQOneOfClosure
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.ModQEqOneOfMemNormalizer

noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S

theorem mod_q_hom : ModQHom := by
  unfold ModQHom
  intro G _ K hK
  have hk1 : ∀ k ∈ K, dIdx K k = 1 := by
    intro k hk
    unfold dIdx
    rw [Subgroup.relIndex_eq_one]
    intro y hy
    refine Subgroup.mem_map.2 ⟨k⁻¹ * y * k, K.mul_mem (K.mul_mem (K.inv_mem hk) hy) hk, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  refine ⟨fun x y => modQ_mul K hK x y, fun k hk => ?_, fun x hx => ?_⟩
  · unfold modQ
    rw [hk1 k hk, hk1 k⁻¹ (K.inv_mem hk)]
    norm_num
  · unfold modQ at hx
    have hne : (dIdx K x⁻¹ : ℚ) ≠ 0 := by exact_mod_cast hK x⁻¹
    rw [div_eq_one_iff_eq hne] at hx
    exact_mod_cast hx

section Lift

variable (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))

def liftFn (hL : LiftU) (g : Uv I v) : I.Gf := Classical.choose (hL I v g g.2)

theorem liftFn_spec (hL : LiftU) (g : Uv I v) :
    matV I v ((liftFn I v hL g : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) = g ∧ SuppAt I v (liftFn I v hL g) :=
  Classical.choose_spec (hL I v g g.2)

theorem eq_liftFn (hL : LiftU) (hJ : MatVInj) (g : Uv I v) (y : I.Gf)
    (hy : matV I v (y : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) = g) (hs : SuppAt I v y) :
    y = liftFn I v hL g := by
  apply hJ I
  intro w
  by_cases hw : w = v
  · rw [hw, hy, (liftFn_spec I v hL g).1]
  · rw [hs w hw, (liftFn_spec I v hL g).2 w hw]

def liftHom (hL : LiftU) (hJ : MatVInj) : Uv I v →* I.Gf where
  toFun := liftFn I v hL
  map_one' := by
    symm
    apply eq_liftFn I v hL hJ 1 1
    · simp
    · intro w _
      simp
  map_mul' := by
    intro g h
    symm
    apply eq_liftFn I v hL hJ (g * h)
    · simp only [Subgroup.coe_mul, map_mul, Subgroup.coe_mul]
      rw [(liftFn_spec I v hL g).1, (liftFn_spec I v hL h).1]
    · intro w hw
      simp only [Subgroup.coe_mul, map_mul]
      rw [(liftFn_spec I v hL g).2 w hw, (liftFn_spec I v hL h).2 w hw, one_mul]

theorem liftHom_apply (hL : LiftU) (hJ : MatVInj) (g : Uv I v) :
    liftHom I v hL hJ g = liftFn I v hL g := rfl

def chiV (hC : KComm) (hL : LiftU) (hJ : MatVInj) : Uv I v →* ℚ where
  toFun g := modQ (PI.AdIndexEq.Ksub I) (liftHom I v hL hJ g)
  map_one' := by simp [modQ_one]
  map_mul' g h := by simp only [map_mul]; exact modQ_mul _ (hC I) _ _

private theorem modQ_eq_one_of_central {G : Type} [Group G] (K : Subgroup G) (y : G)
    (hy : ∀ x : G, y * x * y⁻¹ = x) : modQ K y = 1 := by
  have h1 : ∀ z : G, (∀ x : G, z * x * z⁻¹ = x) → dIdx K z = 1 := by
    intro z hz
    unfold dIdx
    rw [Subgroup.relIndex_eq_one]
    intro k hk
    exact Subgroup.mem_map.2 ⟨k, hk, by simp [MulAut.conj_apply, hz k]⟩
  have h2 : ∀ x : G, y⁻¹ * x * y⁻¹⁻¹ = x := by
    intro x
    have hx := hy x
    rw [inv_inv]
    calc y⁻¹ * x * y = y⁻¹ * (y * x * y⁻¹) * y := by rw [hx]
      _ = x := by group
  unfold modQ
  rw [h1 y hy, h1 y⁻¹ h2]
  norm_num

theorem chiV_props (hC : KComm) (hL : LiftU) (hJ : MatVInj) (hU : MatVU) (hK : KLocGlob) :
    (∀ g, 0 < chiV I v hC hL hJ g) ∧
    (∀ s : Uv I v, (∀ t : Uv I v, s * t = t * s) → chiV I v hC hL hJ s = 1) ∧
    (∀ s : Uv I v, (∃ m : ℕ, 1 ≤ m ∧
        (((s ^ m : Uv I v) : GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) ∈ Kv I v)) →
        chiV I v hC hL hJ s = 1) := by
  have hM := mod_q_hom I.Gf (PI.AdIndexEq.Ksub I) (hC I)
  have hpos : ∀ g, 0 < chiV I v hC hL hJ g := by
    intro g
    show 0 < modQ (PI.AdIndexEq.Ksub I) (liftHom I v hL hJ g)
    unfold modQ
    apply div_pos
    · exact_mod_cast Nat.pos_of_ne_zero (hC I _)
    · exact_mod_cast Nat.pos_of_ne_zero (hC I _)
  refine ⟨hpos, fun s hs => ?_, fun s hs => ?_⟩
  · show modQ (PI.AdIndexEq.Ksub I) (liftHom I v hL hJ s) = 1
    have hyv : matV I v ((liftHom I v hL hJ s : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) = s := by
      rw [liftHom_apply]
      exact (liftFn_spec I v hL s).1
    have hys : SuppAt I v (liftHom I v hL hJ s) := by
      rw [liftHom_apply]
      exact (liftFn_spec I v hL s).2
    apply modQ_eq_one_of_central
    intro x
    apply hJ I
    intro w
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    by_cases hw : w = v
    · rw [hw]
      have hc := congrArg Subtype.val (hs ⟨_, hU I v x⟩)
      simp only [Subgroup.coe_mul, Subgroup.coe_mk] at hc
      rw [hyv, hc, mul_inv_cancel_right]
    · rw [hys w hw, one_mul, inv_one, mul_one]
  · obtain ⟨m, hm, hsm⟩ := hs
    have hpow : chiV I v hC hL hJ (s ^ m) = 1 := by
      show modQ (PI.AdIndexEq.Ksub I) (liftHom I v hL hJ (s ^ m)) = 1
      apply hM.2.1
      refine (hK I _).2 fun w => ?_
      rw [liftHom_apply]
      by_cases hw : w = v
      · rw [hw, (liftFn_spec I v hL (s ^ m)).1]
        exact hsm
      · rw [(liftFn_spec I v hL (s ^ m)).2 w hw]
        exact (Kv I w).one_mem
    rw [map_pow] at hpow
    exact (pow_eq_one_iff_of_nonneg (hpos s).le (by omega)).1 hpow

theorem modQ_of_supp (hC : KComm) (hL : LiftU) (hJ : MatVInj) (hU : MatVU) (y : I.Gf) (hy : SuppAt I v y) :
    modQ (PI.AdIndexEq.Ksub I) y = chiV I v hC hL hJ ⟨_, hU I v y⟩ := by
  show modQ (PI.AdIndexEq.Ksub I) y = modQ (PI.AdIndexEq.Ksub I) (liftHom I v hL hJ ⟨_, hU I v y⟩)
  rw [liftHom_apply, ← eq_liftFn I v hL hJ ⟨_, hU I v y⟩ y rfl hy]

end Lift

theorem locInert_of (hC : KComm) (hL : LiftU) (hJ : MatVInj) (hU : MatVU) (hK : KLocGlob)
    (h : LocInertChi) : LocInert := by
  unfold LocInert
  intro I v hv y hy
  obtain ⟨h1, h2, h3⟩ := chiV_props I v hC hL hJ hU hK
  rw [modQ_of_supp I v hC hL hJ hU y hy]
  exact h I v hv _ h1 h2 h3 _

theorem locSplit_of (hC : KComm) (hL : LiftU) (hJ : MatVInj) (hU : MatVU) (hK : KLocGlob)
    (h : LocSplitChi) : LocSplit := by
  unfold LocSplit
  intro I v hv y hy
  obtain ⟨h1, h2, h3⟩ := chiV_props I v hC hL hJ hU hK
  rw [modQ_of_supp I v hC hL hJ hU y hy]
  exact h I v hv _ h1 h2 h3 _

theorem indexEq_of_loc (hC : KComm) (hL : LiftU) (hJ : MatVInj) (hU : MatVU) (hK : KLocGlob)
    (hR : ReduceLoc) (hS : LocSplitChi) (hI : LocInertChi) : PI.AdIndexEq.IndexEq := by
  unfold PI.AdIndexEq.IndexEq
  intro I x
  have hM := mod_q_hom I.Gf (PI.AdIndexEq.Ksub I) (hC I)
  have hloc : ∀ v (y : I.Gf), SuppAt I v y → modQ (PI.AdIndexEq.Ksub I) y = 1 := by
    intro v y hy
    by_cases hv : IsFieldAt I v
    · exact locInert_of hC hL hJ hU hK hI I v hv y hy
    · exact locSplit_of hC hL hJ hU hK hS I v hv y hy
  have hxm := hR I x
  have hx : modQ (PI.AdIndexEq.Ksub I) x = 1 := by
    induction hxm using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with ⟨v, hv⟩ | hy
      · exact hloc v y hv
      · exact hM.2.1 y hy
    | one => exact modQ_one _
    | mul a b _ _ ha hb => rw [hM.1, ha, hb, one_mul]
    | inv a _ ha =>
      have h1 := hM.1 a a⁻¹
      rw [mul_inv_cancel, modQ_one, ha, one_mul] at h1
      exact h1.symm
  exact hM.2.2 x hx

end PI.UnitaryGroupMassFormula.AdIndexEq

end
