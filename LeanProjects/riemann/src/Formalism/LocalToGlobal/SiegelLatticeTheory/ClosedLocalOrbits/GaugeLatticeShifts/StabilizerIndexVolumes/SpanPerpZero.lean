import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.VolumeIndexBCongruence

noncomputable section

open scoped Classical
open NumberField Matrix

namespace Formalism.L2.SG.Pf.StabilizerIndexVolumes

section Tw

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ} {T T' : E}
  (F : Formalism.MainNotions.S.FlagG S r T) (F' : Formalism.MainNotions.S.FlagG S r T') (L : Matrix (Fin (r + 1)) (Fin (r + 1)) E)

def Pm (β : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) E := (L * β * L⁻¹).conjTranspose

def P'm (β : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  (Formalism.MainNotions.S.Zhat F F')⁻¹ * (L * β⁻¹ * L⁻¹) * Formalism.MainNotions.S.Zhat F F'

variable {F F' L}

theorem Pm_mul (hL : IsUnit L.det) (β γ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Pm L γ * Pm L β = Pm L (β * γ) := by
  rw [Pm, Pm, Pm, ← Matrix.conjTranspose_mul]
  congr 1
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hL]

theorem P'm_mul (hL : IsUnit L.det) (hZ : IsUnit (Formalism.MainNotions.S.Zhat F F').det)
    {β γ : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hβ : IsUnit β.det) (hγ : IsUnit γ.det) :
    P'm F F' L γ * P'm F F' L β = P'm F F' L (β * γ) := by
  simp only [P'm, Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hZ,
    Matrix.nonsing_inv_mul_cancel_left _ _ hL]

theorem Pm_one (hL : IsUnit L.det) : Pm L (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) = 1 := by
  rw [Pm, Matrix.mul_one, Matrix.mul_nonsing_inv _ hL, Matrix.conjTranspose_one]

theorem P'm_one (hL : IsUnit L.det) (hZ : IsUnit (Formalism.MainNotions.S.Zhat F F').det) :
    P'm F F' L (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) = 1 := by
  rw [P'm, inv_one, Matrix.mul_one, Matrix.mul_nonsing_inv _ hL, Matrix.mul_one, Matrix.nonsing_inv_mul _ hZ]

variable (F F' L)

def tw (hL : IsUnit L.det) (hZ : IsUnit (Formalism.MainNotions.S.Zhat F F').det) (hG : IsUnit (gramOf (gg F F')).det)
    (β : Matrix.GeneralLinearGroup (Fin (r + 1)) E) : S.V ≃ₗ[E] S.V :=
  sE (gg F F') hG (UU (Pm L (β : Matrix _ _ E)) (P'm F F' L (β : Matrix _ _ E)))
    (UU (Pm L ((β⁻¹ : Matrix.GeneralLinearGroup _ E) : Matrix _ _ E))
      (P'm F F' L ((β⁻¹ : Matrix.GeneralLinearGroup _ E) : Matrix _ _ E)))
    (by
      rw [UU_mul, Pm_mul hL, P'm_mul hL hZ (Matrix.isUnits_det_units _) (Matrix.isUnits_det_units _), ← Units.val_mul,
        inv_mul_cancel, Units.val_one, Pm_one hL, P'm_one hL hZ, UU_one])
    (by
      rw [UU_mul, Pm_mul hL, P'm_mul hL hZ (Matrix.isUnits_det_units _) (Matrix.isUnits_det_units _), ← Units.val_mul,
        mul_inv_cancel, Units.val_one, Pm_one hL, P'm_one hL hZ, UU_one])

variable {F F' L}

theorem tw_apply (hL : IsUnit L.det) (hZ : IsUnit (Formalism.MainNotions.S.Zhat F F').det) (hG : IsUnit (gramOf (gg F F')).det)
    (β : Matrix.GeneralLinearGroup (Fin (r + 1)) E) (v : S.V) :
    tw F F' L hL hZ hG β v = sL (gg F F') (UU (Pm L (β : Matrix _ _ E)) (P'm F F' L (β : Matrix _ _ E))) v := rfl

theorem tw_mul (hL : IsUnit L.det) (hZ : IsUnit (Formalism.MainNotions.S.Zhat F F').det) (hG : IsUnit (gramOf (gg F F')).det)
    (β γ : Matrix.GeneralLinearGroup (Fin (r + 1)) E) :
    tw F F' L hL hZ hG (β * γ) = tw F F' L hL hZ hG γ * tw F F' L hL hZ hG β := by
  ext v
  rw [LinearEquiv.mul_apply, tw_apply, tw_apply, tw_apply, sL_comp _ hG, UU_mul, Pm_mul hL,
    P'm_mul hL hZ (Matrix.isUnits_det_units _) (Matrix.isUnits_det_units _), Units.val_mul]

theorem tw_one (hL : IsUnit L.det) (hZ : IsUnit (Formalism.MainNotions.S.Zhat F F').det) (hG : IsUnit (gramOf (gg F F')).det) :
    tw F F' L hL hZ hG 1 = 1 := by
  ext v
  rw [tw_apply, Units.val_one, Pm_one hL, P'm_one hL hZ, UU_one, sL_one]
  rfl

end Tw

section TwProps

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ} {T T' : E}
  {F : Formalism.MainNotions.S.FlagG S r T} {F' : Formalism.MainNotions.S.FlagG S r T'} {L : Matrix (Fin (r + 1)) (Fin (r + 1)) E}

theorem Pm_up (hLl : Formalism.MainNotions.S.IsLoUni L) {β : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hβ : Formalism.MainNotions.S.IsLoUni β) :
    Formalism.MainNotions.S.IsUpUni (Pm L β) := by
  exact up_conjT (lo_mul (lo_mul hLl hβ) (lo_inv hLl))

theorem Pm_Z (hL : IsUnit L.det) (hZ : IsUnit (Formalism.MainNotions.S.Zhat F F').det)
    {β : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hβ : IsUnit β.det) :
    (Pm L β).conjTranspose * Formalism.MainNotions.S.Zhat F F' * P'm F F' L β = Formalism.MainNotions.S.Zhat F F' := by
  rw [Pm, Matrix.conjTranspose_conjTranspose, P'm]
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hZ, Matrix.nonsing_inv_mul_cancel_left _ _ hL,
    Matrix.mul_nonsing_inv_cancel_left _ _ hβ, Matrix.mul_nonsing_inv_cancel_left _ _ hL]

theorem tw_isom (hLl : Formalism.MainNotions.S.IsLoUni L) (hL : IsUnit L.det) (hZ : IsUnit (Formalism.MainNotions.S.Zhat F F').det)
    (hG : IsUnit (gramOf (gg F F')).det) (β : Matrix.GeneralLinearGroup (Fin (r + 1)) E)
    (hβ : Formalism.MainNotions.S.IsLoUni (β : Matrix (Fin (r + 1)) (Fin (r + 1)) E))
    (hP' : Formalism.MainNotions.S.IsUpUni (P'm F F' L (β : Matrix (Fin (r + 1)) (Fin (r + 1)) E))) (x y : S.V) :
    S.hT (tw F F' L hL hZ hG β x) (tw F F' L hL hZ hG β y) = S.hT x y := by
  rw [tw_apply, tw_apply]
  exact sL_isom _ hG _ (UU_isom (F := F) (F' := F') (Pm_up hLl hβ) hP' (Pm_Z hL hZ (Matrix.isUnits_det_units β))) x y

theorem tw_frame (hL : IsUnit L.det) (hZ : IsUnit (Formalism.MainNotions.S.Zhat F F').det) (hG : IsUnit (gramOf (gg F F')).det)
    (β : Matrix.GeneralLinearGroup (Fin (r + 1)) E) (b : Fin (r + 1)) :
    tw F F' L hL hZ hG β (F.fvec b) = ∑ c, Pm L (β : Matrix (Fin (r + 1)) (Fin (r + 1)) E) c b • F.fvec c := by
  rw [tw_apply, sL_frame (hG := hG)]

theorem tw_frame' (hL : IsUnit L.det) (hZ : IsUnit (Formalism.MainNotions.S.Zhat F F').det) (hG : IsUnit (gramOf (gg F F')).det)
    (β : Matrix.GeneralLinearGroup (Fin (r + 1)) E) (b : Fin (r + 1)) :
    tw F F' L hL hZ hG β (F'.fvec b) = ∑ c, P'm F F' L (β : Matrix (Fin (r + 1)) (Fin (r + 1)) E) c b • F'.fvec c := by
  rw [tw_apply, sL_frame' (hG := hG)]

theorem tw_inj (hT : T ≠ 0) (hL : IsUnit L.det) (hZ : IsUnit (Formalism.MainNotions.S.Zhat F F').det)
    (hG : IsUnit (gramOf (gg F F')).det) {β : Matrix.GeneralLinearGroup (Fin (r + 1)) E}
    (h : tw F F' L hL hZ hG β = 1) : β = 1 := by

  have hli : LinearIndependent E (gg F F') := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    have ha0 : a = 0 := by
      apply Matrix.eq_zero_of_mulVec_eq_zero hG.ne_zero
      ext l
      have hl : S.hT (gg F F' l) (∑ m, a m • gg F F' m) = 0 := by rw [ha, map_zero]
      simp only [map_sum, map_smul, smul_eq_mul] at hl
      simp only [Matrix.mulVec, dotProduct, gramOf, Pi.zero_apply]
      rw [← hl]
      exact Finset.sum_congr rfl (fun m _ => mul_comm _ _)
    intro m
    rw [ha0]
    rfl
  have hliF : LinearIndependent E F.fvec := hli.comp Sum.inl Sum.inl_injective

  have hP : Pm L (β : Matrix (Fin (r + 1)) (Fin (r + 1)) E) = 1 := by
    ext c b
    have hb := tw_frame hL hZ hG β b
    rw [h] at hb
    change F.fvec b = _ at hb
    have hsum : ∑ c, (Pm L (β : Matrix (Fin (r + 1)) (Fin (r + 1)) E) c b -
        (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) c b) • F.fvec c = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, Matrix.one_apply, ite_smul, one_smul, zero_smul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [← hb, sub_self]
    have := Fintype.linearIndependent_iff.1 hliF _ hsum c
    exact sub_eq_zero.1 this
  have hLβ : L * (β : Matrix (Fin (r + 1)) (Fin (r + 1)) E) * L⁻¹ = 1 := by
    have := congrArg Matrix.conjTranspose hP
    rwa [Pm, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one] at this
  apply Units.ext
  rw [Units.val_one]
  calc (β : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
      = L⁻¹ * (L * (β : Matrix (Fin (r + 1)) (Fin (r + 1)) E) * L⁻¹) * L := by
        simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hL, Matrix.nonsing_inv_mul _ hL,
          Matrix.mul_one]
    _ = 1 := by rw [hLβ, Matrix.mul_one, Matrix.nonsing_inv_mul _ hL]

theorem sL_perp (hG : IsUnit (gramOf (gg F F')).det)
    (X : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E)
    {v : S.V} (hv : ∀ m, S.hT (gg F F' m) v = 0) : sL (gg F F') X v = v := by
  simp [sL, coordL, hv]

theorem span_perp_zero (hG : IsUnit (gramOf (gg F F')).det) (a : Fin (r + 1) ⊕ Fin (r + 1) → E)
    (h : ∀ l, S.hT (gg F F' l) (∑ m, a m • gg F F' m) = 0) : ∑ m, a m • gg F F' m = 0 := by
  have ha : a = 0 := by
    apply Matrix.eq_zero_of_mulVec_eq_zero hG.ne_zero
    ext l
    have hl := h l
    simp only [map_sum, map_smul, smul_eq_mul] at hl
    simp only [Matrix.mulVec, dotProduct, gramOf, Pi.zero_apply]
    rw [← hl]
    exact Finset.sum_congr rfl (fun m _ => mul_comm _ _)
  rw [ha]
  simp

theorem sL_mem_span (X : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E) {v : S.V}
    (hv : v ∈ Submodule.span E (Set.range (gg F F'))) : sL (gg F F') X v ∈ Submodule.span E (Set.range (gg F F')) := by
  rw [← sub_add_cancel (sL (gg F F') X v) v, sL_sub]
  refine add_mem (add_mem (sum_mem fun b _ => ?_) (sum_mem fun b _ => ?_)) hv
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl b, rfl⟩)
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr b, rfl⟩)

theorem perp_span {q : S.V} (hq : ∀ l, S.hT (gg F F' l) q = 0) :
    ∀ y ∈ Submodule.span E (Set.range (gg F F')), S.hT y q = 0 := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, rfl⟩ := hx
    exact hq l
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul a x _ hx => simp [hx]

theorem e_mem_span (i : Fin r) : F.e i ∈ Submodule.span E (Set.range (gg F F')) := by
  refine Submodule.subset_span ⟨Sum.inl i.castSucc, ?_⟩
  simp [gg, Formalism.MainNotions.S.FlagG.fvec]

theorem tw_eq_of (hL : IsUnit L.det) (hZ : IsUnit (Formalism.MainNotions.S.Zhat F F').det) (hG : IsUnit (gramOf (gg F F')).det)
    (β : Matrix.GeneralLinearGroup (Fin (r + 1)) E) (s : S.V ≃ₗ[E] S.V) (hs : ∀ x y, S.hT (s x) (s y) = S.hT x y)
    (hsf : ∀ b, s (F.fvec b) = ∑ c, Pm L (β : Matrix (Fin (r + 1)) (Fin (r + 1)) E) c b • F.fvec c)
    (hsf' : ∀ b, s (F'.fvec b) = ∑ c, P'm F F' L (β : Matrix (Fin (r + 1)) (Fin (r + 1)) E) c b • F'.fvec c)
    (hsX : ∀ x, (∀ i, S.hT (F.e i) x = 0) → s x - x ∈ Submodule.span E (Set.range F.e)) :
    s = tw F F' L hL hZ hG β := by
  set τ := tw F F' L hL hZ hG β with hτ
  set Sg := Submodule.span E (Set.range (gg F F'))
  have hg : ∀ m, s (gg F F' m) = τ (gg F F' m) := by
    rintro (b | b)
    · show s (F.fvec b) = τ (F.fvec b); rw [hsf, hτ, tw_frame]
    · show s (F'.fvec b) = τ (F'.fvec b); rw [hsf', hτ, tw_frame']
  have hspan : ∀ y ∈ Sg, s y = τ y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx => obtain ⟨m, rfl⟩ := hx; exact hg m
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
    | smul c x _ hx => rw [map_smul, map_smul, hx]
  have hτs : ∀ m, τ.symm (gg F F' m) ∈ Sg := fun m => sL_mem_span _ (Submodule.subset_span ⟨m, rfl⟩)
  have hss : ∀ m, s.symm (gg F F' m) ∈ Sg := by
    intro m
    have : s.symm (gg F F' m) = τ.symm (gg F F' m) := by
      apply s.injective
      rw [LinearEquiv.apply_symm_apply, hspan _ (hτs m), LinearEquiv.apply_symm_apply]
    rw [this]; exact hτs m
  apply LinearEquiv.ext
  intro x
  set p : S.V := ∑ k, cOf (gg F F') x k • gg F F' k with hp
  set q : S.V := x - p with hq
  have hpS : p ∈ Sg := Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hqperp : ∀ l, S.hT (gg F F' l) q = 0 := by
    intro l
    have h1 := congrFun (gram_cOf (gg F F') hG x) l
    rw [hq, hp, map_sub, map_sum]
    simp only [map_smul, smul_eq_mul]
    rw [← h1]
    simp only [Matrix.mulVec, dotProduct, gramOf]
    rw [sub_eq_zero]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hτq : τ q = q := sL_perp hG _ hqperp
  have hsq : s q = q := by
    have hd := hsX q fun i => perp_span hqperp _ (e_mem_span i)
    have hdS : s q - q ∈ Sg := Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact e_mem_span i) hd
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hdS
    have hperp : ∀ l, S.hT (gg F F' l) (∑ m, a m • gg F F' m) = 0 := by
      intro l
      rw [ha, map_sub, hqperp l, sub_zero]
      have e : gg F F' l = s (s.symm (gg F F' l)) := (LinearEquiv.apply_symm_apply s _).symm
      rw [e, hs]
      exact perp_span hqperp _ (hss l)
    have h0 := span_perp_zero hG a hperp
    rw [ha] at h0
    exact sub_eq_zero.1 h0
  have hx : x = p + q := by rw [hq]; abel
  rw [hx, map_add, map_add, hspan p hpS, hsq, hτq]

end TwProps

end Formalism.L2.SG.Pf.StabilizerIndexVolumes
