import Formalism.HermitianCurvature.FrameMinor
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OperatorRepresentations
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator

open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace CapelliCoordinates

section Parts

variable {n : ℕ}

theorem hpart1_add (H Z W : Matrix (Fin n) (Fin n) ℂ) : hpart1 H (Z + W) = hpart1 H Z + hpart1 H W := by
  simp only [hpart1, conjTranspose_add, Matrix.mul_add, Matrix.add_mul, smul_sub, smul_add]
  abel

theorem hpart2_add (H Z W : Matrix (Fin n) (Fin n) ℂ) : hpart2 H (Z + W) = hpart2 H Z + hpart2 H W := by
  simp only [hpart2, conjTranspose_add, Matrix.mul_add, Matrix.add_mul, smul_add]
  abel

theorem inv2I : (1 / (2 * Complex.I) : ℂ) = -Complex.I / 2 := by
  have h : (2 * Complex.I) * (-Complex.I / 2) = 1 := by
    linear_combination (-1 : ℂ) * Complex.I_sq
  exact (eq_one_div_of_mul_eq_one_right h).symm

theorem hpart1_smul (H Z : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) :
    hpart1 H (c • Z) = c.re • hpart1 H Z - c.im • hpart2 H Z := by
  have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
  have hs : star c = (c.re : ℂ) - (c.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  simp only [hpart1, hpart2, conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, ← Complex.coe_smul, inv2I]
  rw [hs]
  match_scalars <;> first
    | ring1
    | linear_combination (1 / 2 : ℂ) * hc
    | linear_combination (-1 / 2 : ℂ) * hc
    | linear_combination (-Complex.I / 2) * hc + (-(c.im : ℂ) / 2) * Complex.I_sq
    | linear_combination ((c.im : ℂ) / 2) * Complex.I_sq
    | linear_combination (Complex.I / 2) * hc + ((c.im : ℂ) / 2) * Complex.I_sq
    | linear_combination (-(c.im : ℂ) / 2) * Complex.I_sq

theorem hpart2_smul (H Z : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) :
    hpart2 H (c • Z) = c.re • hpart2 H Z + c.im • hpart1 H Z := by
  have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
  have hs : star c = (c.re : ℂ) - (c.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  simp only [hpart1, hpart2, conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, ← Complex.coe_smul, inv2I]
  rw [hs]
  match_scalars <;> first
    | ring1
    | linear_combination (1 / 2 : ℂ) * hc
    | linear_combination (-1 / 2 : ℂ) * hc
    | linear_combination (-Complex.I / 2) * hc + (-(c.im : ℂ) / 2) * Complex.I_sq
    | linear_combination ((c.im : ℂ) / 2) * Complex.I_sq
    | linear_combination (Complex.I / 2) * hc + ((c.im : ℂ) / 2) * Complex.I_sq
    | linear_combination (-(c.im : ℂ) / 2) * Complex.I_sq

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def cx (H : Matrix (Fin n) (Fin n) ℂ) (L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] E) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] E where
  toFun := fun Z => L (hpart1 H Z) + Complex.I • L (hpart2 H Z)
  map_add' := fun Z W => by
    rw [hpart1_add, hpart2_add, map_add, map_add, smul_add]
    abel
  map_smul' := fun c Z => by
    rw [hpart1_smul, hpart2_smul, map_sub, map_add, map_smul, map_smul, map_smul, map_smul, RingHom.id_apply]
    have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
    conv_rhs => rw [hc]
    simp only [← Complex.coe_smul, smul_add, add_smul, smul_smul]
    have h : Complex.I * Complex.I = -1 := Complex.I_mul_I
    have e : ((c.re : ℂ) + (c.im : ℂ) * Complex.I) * Complex.I = (c.re : ℂ) * Complex.I - (c.im : ℂ) := by
      linear_combination (c.im : ℂ) * h
    rw [e, sub_smul, mul_comm Complex.I (c.re : ℂ), mul_comm Complex.I (c.im : ℂ)]
    abel

end Parts

section Sup

variable {k r : ℕ} {i : Fin (r + 1)}

def Sup (k r : ℕ) (i : Fin (r + 1)) (Z : Mx k r) : Prop :=
  ∀ p, ¬ Qx2.inV k r i p → Z *ᵥ bvec p = 0 ∧ (Hpk k r * Zᴴ * Hpk k r) *ᵥ bvec p = 0

theorem sup_zero : Sup k r i 0 := fun p _ => by simp

theorem Sup.add {Z W : Mx k r} (hZ : Sup k r i Z) (hW : Sup k r i W) : Sup k r i (Z + W) := fun p hp => by
  obtain ⟨h1, h2⟩ := hZ p hp
  obtain ⟨h3, h4⟩ := hW p hp
  refine ⟨by rw [Matrix.add_mulVec, h1, h3, add_zero], ?_⟩
  rw [conjTranspose_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mulVec, h2, h4, add_zero]

theorem Sup.smul {Z : Mx k r} (hZ : Sup k r i Z) (c : ℂ) : Sup k r i (c • Z) := fun p hp => by
  obtain ⟨h1, h2⟩ := hZ p hp
  refine ⟨by rw [Matrix.smul_mulVec, h1, smul_zero], ?_⟩
  rw [conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mulVec, h2, smul_zero]

private theorem sup_single_of_inV (p q : Fin (2 * r + k + 1)) (hp : Qx2.inV k r i p) (hq : Qx2.inV k r i q) :
    Sup k r i (Matrix.single p q (1 : ℂ)) := by
  have hi := i.isLt
  have hcol : ∀ (M : Mx k r) (x y : Fin (2 * r + k + 1)), (M *ᵥ bvec x) y = M y x := by
    intro M x y
    simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hz : ∀ x y : Fin (2 * r + k + 1), Qx2.inV k r i x → ¬ Qx2.inV k r i y → Hpk k r x y = 0 := by
    intro x y hx hy
    have hne : x ≠ y := by rintro rfl; exact hy hx
    simp only [Qx2.inV] at hx hy
    simp only [Hpk, hne, and_false, ↓reduceIte]
    rw [if_neg (by omega), if_neg (by omega)]
  intro x hx
  have hne : q ≠ x := by rintro rfl; exact hx hq
  refine ⟨?_, ?_⟩
  · ext y
    rw [hcol]
    simp [Matrix.single_apply, hne]
  · ext y
    rw [hcol, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro z _
    by_cases hz' : z = p
    · subst hz'
      rw [hz _ _ hp hx, mul_zero]
    · rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
      intro w _
      simp [Matrix.conjTranspose_apply, Matrix.single_apply, Ne.symm hz']

theorem sup_single (a b : Fin (mdim k r i)) : Sup k r i (Matrix.single (posL k r i a) (posL k r i b) 1) := by
  have hj := a.isLt
  have hj' := b.isLt
  have hi := i.isLt
  apply sup_single_of_inV <;> simp only [Qx2.inV, posL, mdim] at hj hj' ⊢ <;> omega

theorem sup_sum {ι : Type*} (s : Finset ι) (Z : ι → Mx k r) (h : ∀ j ∈ s, Sup k r i (Z j)) :
    Sup k r i (∑ j ∈ s, Z j) := by
  exact Finset.sum_induction _ (Sup k r i) (fun _ _ ha hb => ha.add hb) sup_zero h

theorem Sup.lie {Z : Mx k r} (hZ : Sup k r i Z) :
    inLieLev k r i (hpart1 (Hpk k r) Z) ∧ inLieLev k r i (hpart2 (Hpk k r) Z) := by
  have hinv : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv Qx2.hpk_sq'
  have hh : (Hpk k r)ᴴ = Hpk k r := Qx2.hpk_h
  have hsq : Hpk k r * Hpk k r = 1 := Qx2.hpk_sq'
  have hsq' : ∀ X : Mx k r, Hpk k r * (Hpk k r * X) = X := by
    intro X
    rw [← Matrix.mul_assoc, hsq, Matrix.one_mul]
  have hout : ∀ a : Fin r, a.val < i.val → ¬ Qx2.inV k r i (eI k r a) ∧ ¬ Qx2.inV k r i (esI k r a) := by
    intro a ha
    have := i.isLt
    simp only [Qx2.inV, eI, esI, Fin.val_mk]
    omega
  have hst1 : star (1 / 2 : ℂ) = 1 / 2 := by
    apply Complex.ext <;> simp
  have hst2 : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by
    rw [inv2I]
    apply Complex.ext <;> simp <;> norm_num
  refine ⟨⟨?_, fun a ha => ?_⟩, ⟨?_, fun a ha => ?_⟩⟩
  · simp only [hpart1, hinv, conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose,
      hh, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hsq, hsq',
      Matrix.mul_one, hst1]
    module
  · obtain ⟨h1, h2⟩ := hout a ha
    refine ⟨?_, ?_⟩
    · rw [hpart1, hinv, Matrix.smul_mulVec, Matrix.sub_mulVec, (hZ _ h1).1, (hZ _ h1).2, sub_zero, smul_zero]
    · rw [hpart1, hinv, Matrix.smul_mulVec, Matrix.sub_mulVec, (hZ _ h2).1, (hZ _ h2).2, sub_zero, smul_zero]
  · simp only [hpart2, hinv, conjTranspose_smul, conjTranspose_add, conjTranspose_mul, conjTranspose_conjTranspose,
      hh, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hsq, hsq',
      Matrix.mul_one, hst2]
    module
  · obtain ⟨h1, h2⟩ := hout a ha
    refine ⟨?_, ?_⟩
    · rw [hpart2, hinv, Matrix.smul_mulVec, Matrix.add_mulVec, (hZ _ h1).1, (hZ _ h1).2, add_zero, smul_zero]
    · rw [hpart2, hinv, Matrix.smul_mulVec, Matrix.add_mulVec, (hZ _ h2).1, (hZ _ h2).2, add_zero, smul_zero]

end Sup

section Lin

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}

theorem rd_linear {F : Mx k r → E} (hF : SmoothLev k r i D F) {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) :
    ∃ L : Mx k r →ₗ[ℝ] E, ∀ X, inLieLev k r i X → RdV X F g = L X := by
  obtain ⟨U, G, hU, hgU, hG, he⟩ := hF g hg
  have hGd : DifferentiableAt ℝ G g :=
    (hG.contDiffAt (hU.mem_nhds hgU)).differentiableAt (by simp)
  refine ⟨(fderiv ℝ G g).toLinearMap ∘ₗ LinearMap.mulLeft ℝ g, fun X hX => ?_⟩
  have h1 := Qx2.rd_hasDeriv hF hg hX
  have h2 := Qx2.hasDeriv_ext hU hgU hg.1 hX hGd he
  rw [h1.unique h2]
  rfl

theorem rz_linear {F : Mx k r → E} (hF : SmoothLev k r i D F) {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) :
    ∃ L : Mx k r →ₗ[ℂ] E, ∀ Z, Sup k r i Z → RZ (Hpk k r) Z F g = L Z := by
  obtain ⟨L, hL⟩ := rd_linear hF hg
  refine ⟨cx (Hpk k r) L, fun Z hZ => ?_⟩
  obtain ⟨h1, h2⟩ := hZ.lie
  show RdV (hpart1 (Hpk k r) Z) F g + Complex.I • RdV (hpart2 (Hpk k r) Z) F g = _
  rw [hL _ h1, hL _ h2]
  rfl

end Lin

end CapelliCoordinates

theorem right_lowering_linear : Formalism.FourierDecayAlt.Qr.RZLin := by
  intro E _ _ k r i D hD c F hF g hg
  obtain ⟨L, hL⟩ := CapelliCoordinates.rz_linear hF hg
  have hs : ∀ a b, CapelliCoordinates.Sup k r i (Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ)) :=
    fun a b => CapelliCoordinates.sup_single a b
  rw [hL _ (CapelliCoordinates.sup_sum _ _ fun a _ => CapelliCoordinates.sup_sum _ _ fun b _ => (hs a b).smul (c a b))]
  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← hL _ (hs a b)]
  rfl

namespace CapelliCoordinates

section Cap

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}

theorem good_rz (hD : IsOpen D) {Z : Mx k r} (h1 : inLieLev k r i (hpart1 (Hpk k r) Z))
    (h2 : inLieLev k r i (hpart2 (Hpk k r) Z)) : Qx2.Good k r i D (fun f : Mx k r → E => RZ (Hpk k r) Z f) := by
  exact (Qx2.good_rd hD h1).add ((Qx2.good_rd hD h2).smul Complex.I)

theorem good_factor {T : (Mx k r → E) → Mx k r → E} (hT : Qx2.Good k r i D T) (p : Prop) [Decidable p] (c : ℂ) :
    Qx2.Good k r i D (fun y : Mx k r → E => (if p then c • y else 0) + T y) := by
  by_cases hp : p
  · simp only [hp, ↓reduceIte]
    exact (Qx2.good_id.smul c).add hT
  · simp only [hp, ↓reduceIte, zero_add]
    exact hT

private theorem apply_eq_zero_of_inWb_not_inV {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) {p : Fin (2 * r + k + 1)}
    (hp : ¬ Qx2.inV k r (Fin.last r) p) : v p = 0 := by
  apply hv
  unfold Qx2.inV at hp
  simp only [Fin.val_last] at hp
  omega

private theorem herm_bvec_eq_zero_of_not_inV {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) {p : Fin (2 * r + k + 1)}
    (hp : ¬ Qx2.inV k r (Fin.last r) p) : herm (Hpk k r) (bvec p) v = 0 := by
  have hcol : ∀ q, (Hpk k r *ᵥ bvec p) q = Hpk k r q p := by
    intro q
    simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
  unfold Qx2.inV at hp
  simp only [Fin.val_last] at hp
  unfold herm
  simp only [dotProduct, hcol]
  apply Finset.sum_eq_zero
  intro q _
  by_cases hq : q.val < r ∨ r + k < q.val
  · simp [hv q hq]
  · have hp' : p.val < r ∨ r + k < p.val := by omega
    have hne : q ≠ p := fun h => by subst h; omega
    have h0 : Hpk k r q p = 0 := by
      simp only [Hpk, hne, and_false, ↓reduceIte]
      rw [if_neg (by omega), if_neg (by omega)]
    rw [h0, mul_zero]

private theorem unitB_eq_sum_single_of_inWb {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (hB : ∀ a, inWb k r (Bs a)) (a b : Fin m) :
    unitB (Hpk k r) Bs a b = ∑ c, ∑ d, (Bs a (posL k r (Fin.last r) c) *
      herm (Hpk k r) (bvec (posL k r (Fin.last r) d)) (Bs b)) •
        Matrix.single (posL k r (Fin.last r) c) (posL k r (Fin.last r) d) (1 : ℂ) := by
  have hinj : ∀ c c' : Fin (mdim k r (Fin.last r)), posL k r (Fin.last r) c = posL k r (Fin.last r) c' → c = c' := by
    intro c c' h
    ext
    simp only [posL, Fin.ext_iff] at h
    omega
  have hlast' : ∀ c : Fin (mdim k r (Fin.last r)), Qx2.inV k r (Fin.last r) (posL k r (Fin.last r) c) := by
    intro c
    have hc := c.isLt
    simp only [Qx2.inV, posL, mdim, Fin.val_last] at hc ⊢
    omega
  have hsurj : ∀ p, Qx2.inV k r (Fin.last r) p → ∃ c, posL k r (Fin.last r) c = p := by
    intro p hp
    simp only [Qx2.inV, Fin.val_last] at hp
    refine ⟨⟨p.val - r, ?_⟩, ?_⟩
    · simp only [mdim, Fin.val_last]
      omega
    · ext
      simp only [posL, Fin.val_last]
      omega
  ext p q
  simp only [unitB, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
  by_cases hp : Qx2.inV k r (Fin.last r) p
  · by_cases hq : Qx2.inV k r (Fin.last r) q
    · obtain ⟨c0, rfl⟩ := hsurj p hp
      obtain ⟨d0, rfl⟩ := hsurj q hq
      rw [Fintype.sum_eq_single c0, Fintype.sum_eq_single d0]
      · simp
      · intro d hd
        have hne : posL k r (Fin.last r) d ≠ posL k r (Fin.last r) d0 := fun h => hd (hinj _ _ h)
        simp [hne]
      · intro c hc
        have hne : posL k r (Fin.last r) c ≠ posL k r (Fin.last r) c0 := fun h => hc (hinj _ _ h)
        apply Finset.sum_eq_zero
        intro d _
        simp [hne]
    · rw [herm_bvec_eq_zero_of_not_inV (hB b) hq, mul_zero]
      symm
      apply Finset.sum_eq_zero
      intro c _
      apply Finset.sum_eq_zero
      intro d _
      have hne : posL k r (Fin.last r) d ≠ q := fun h => hq (h ▸ hlast' d)
      simp [hne]
  · rw [apply_eq_zero_of_inWb_not_inV (hB a) hp, zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro c _
    apply Finset.sum_eq_zero
    intro d _
    have hne : posL k r (Fin.last r) c ≠ p := fun h => hp (h ▸ hlast' c)
    simp [hne]

theorem good_capR (hD : IsOpen D) {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (hB : ∀ a, inWb k r (Bs a)) (w : ℂ) :
    Qx2.Good k r i D (capR (E := E) k r Bs w) := by
  have hcong : ∀ {T S : (Mx k r → E) → Mx k r → E}, Qx2.Good k r i D T → (∀ f x, T f x = S f x) →
      Qx2.Good k r i D S := by
    intro T S hT e
    have : S = T := funext fun f => funext fun x => (e f x).symm
    subst this
    exact hT
  have hZ : ∀ a b, Qx2.Good k r i D (RZ (E := E) (Hpk k r) (unitB (Hpk k r) Bs a b)) := by
    intro a b
    have hs : Sup k r i (unitB (Hpk k r) Bs a b) := by
      rw [unitB_eq_sum_single_of_inWb Bs hB a b]
      refine sup_sum _ _ fun c _ => sup_sum _ _ fun d _ => (sup_single_of_inV _ _ ?_ ?_).smul _ <;>
      · have hc := c.isLt
        have hd := d.isLt
        have hi := i.isLt
        simp only [Qx2.inV, posL, mdim, Fin.val_last] at hc hd ⊢
        omega
    obtain ⟨h1, h2⟩ := hs.lie
    exact good_rz hD h1 h2
  have hfold : ∀ (L : List ((Mx k r → E) → Mx k r → E)), (∀ T ∈ L, Qx2.Good k r i D T) →
      Qx2.Good k r i D (fun f => L.foldr (fun T h => T h) f) := by
    intro L hL
    induction L with
    | nil => exact Qx2.good_id
    | cons T L ih =>
      exact (hL T List.mem_cons_self).comp (ih fun S hS => hL S (List.mem_cons_of_mem _ hS))
  have hsum : ∀ (s : Finset (Equiv.Perm (Fin m))) (c : Equiv.Perm (Fin m) → ℂ)
      (T : Equiv.Perm (Fin m) → (Mx k r → E) → Mx k r → E),
      (∀ σ, Qx2.Good k r i D (T σ)) → Qx2.Good k r i D (fun f => ∑ σ ∈ s, c σ • T σ f) := by
    intro s c T hT
    induction s using Finset.cons_induction with
    | empty => exact hcong (Qx2.good_id.smul 0) (fun f x => by simp)
    | cons σ s hσ ih => exact hcong (((hT σ).smul (c σ)).add ih) (fun f x => by simp [Finset.sum_insert hσ])
  unfold capR qmF
  refine hsum _ _ _ fun σ => hfold _ fun T hT => ?_
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hT
  exact good_factor (hZ _ _) _ _

end Cap

end CapelliCoordinates

theorem capelli_right_good : Formalism.FourierDecayAlt.Qr.CapRGood := by
  intro E _ _ k r m i D hD Bs hB w
  exact CapelliCoordinates.good_capR hD Bs hB w

namespace CapelliCoordinates

section Frame

variable {k r : ℕ}

theorem out_of_inWb {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) {p : Fin (2 * r + k + 1)}
    (hp : ¬ Qx2.inV k r (Fin.last r) p) : v p = 0 := apply_eq_zero_of_inWb_not_inV hv hp

theorem herm_out {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) {p : Fin (2 * r + k + 1)}
    (hp : ¬ Qx2.inV k r (Fin.last r) p) : herm (Hpk k r) (bvec p) v = 0 := herm_bvec_eq_zero_of_not_inV hv hp

theorem unitB_expand {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (hB : ∀ a, inWb k r (Bs a)) (a b : Fin m) :
    unitB (Hpk k r) Bs a b = ∑ c, ∑ d, (Bs a (posL k r (Fin.last r) c) *
      herm (Hpk k r) (bvec (posL k r (Fin.last r) d)) (Bs b)) •
        Matrix.single (posL k r (Fin.last r) c) (posL k r (Fin.last r) d) (1 : ℂ) := unitB_eq_sum_single_of_inWb Bs hB a b

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)}

private theorem operator_rep_smul {i : Fin (r + 1)} {X : Module.End ℂ (SV k r i D E)}
    {T : (Mx k r → E) → Mx k r → E} (h : OperatorRepresentations.Rep X T) (c : ℂ) :
    OperatorRepresentations.Rep (c • X) (fun f x => c • T f x) :=
  ⟨h.1.smul c, fun φ g hg => by simp [h.2 φ g hg]⟩

private theorem operator_rep_add {i : Fin (r + 1)} {X Y : Module.End ℂ (SV k r i D E)}
    {T S : (Mx k r → E) → Mx k r → E} (hX : OperatorRepresentations.Rep X T) (hY : OperatorRepresentations.Rep Y S) :
    OperatorRepresentations.Rep (X + Y) (fun f x => T f x + S f x) :=
  ⟨hX.1.add hY.1, fun φ g hg => by simp [hX.2 φ g hg, hY.2 φ g hg]⟩

private theorem congrHermitianCurvature {i : Fin (r + 1)} {X : Module.End ℂ (SV k r i D E)}
    {T S : (Mx k r → E) → Mx k r → E} (h : OperatorRepresentations.Rep X T) (e : ∀ f x, T f x = S f x) : OperatorRepresentations.Rep X S := by
  have : S = T := funext fun f => funext fun x => (e f x).symm
  subst this
  exact h

theorem rep_econj (hD : IsOpen D) {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (hB : ∀ a, inWb k r (Bs a))
    (P Q : Matrix (Fin (mdim k r (Fin.last r))) (Fin (mdim k r (Fin.last r))) ℂ)
    (ι : Fin m → Fin (mdim k r (Fin.last r)))
    (hP : ∀ a c, P c (ι a) = Bs a (posL k r (Fin.last r) c))
    (hQ : ∀ b d, Q (ι b) d = herm (Hpk k r) (bvec (posL k r (Fin.last r) d)) (Bs b)) (a b : Fin m) :
    OperatorRepresentations.Rep (Econj (EV k r (Fin.last r) D E) P Q (ι a) (ι b))
      (fun f => RZ (Hpk k r) (unitB (Hpk k r) Bs a b) f) := by
  have hin : ∀ c : Fin (mdim k r (Fin.last r)), Qx2.inV k r (Fin.last r) (posL k r (Fin.last r) c) := by
    intro c
    have hc := c.isLt
    simp only [Qx2.inV, posL, mdim, Fin.val_last] at hc ⊢
    omega
  have hS : ∀ c d, Sup k r (Fin.last r)
      (Matrix.single (posL k r (Fin.last r) c) (posL k r (Fin.last r) d) (1 : ℂ)) :=
    fun c d => sup_single_of_inV _ _ (hin c) (hin d)
  have hGs : ∀ c d, Qx2.Good k r (Fin.last r) D
      (fun f : Mx k r → E => EH k r (posL k r (Fin.last r) c) (posL k r (Fin.last r) d) f) := by
    intro c d
    obtain ⟨h1, h2⟩ := (hS c d).lie
    exact good_rz hD h1 h2
  have hSu : Sup k r (Fin.last r) (unitB (Hpk k r) Bs a b) := by
    rw [unitB_expand Bs hB a b]
    exact sup_sum _ _ fun c _ => sup_sum _ _ fun d _ => (hS c d).smul _
  obtain ⟨hu1, hu2⟩ := hSu.lie
  have hrep : OperatorRepresentations.Rep (Econj (EV k r (Fin.last r) D E) P Q (ι a) (ι b))
      (fun f x => ∑ c, ∑ d, (P c (ι a) * Q (ι b) d) •
        EH k r (posL k r (Fin.last r) c) (posL k r (Fin.last r) d) f x) := by
    unfold Econj
    exact OperatorRepresentations.rep_sum _ _ _ fun c _ => OperatorRepresentations.rep_sum _ _ _ fun d _ =>
      operator_rep_smul (OperatorRepresentations.rep_opV hD (hGs c d)) _
  refine ⟨good_rz hD hu1 hu2, fun φ g hg => ?_⟩
  rw [hrep.2 φ g hg]
  obtain ⟨L, hL⟩ := rz_linear φ.2.1 hg
  show _ = RZ (Hpk k r) (unitB (Hpk k r) Bs a b) φ.1 g
  rw [hL _ hSu, unitB_expand Bs hB a b, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [map_smul, ← hL _ (hS c d), hP, hQ]
  rfl

theorem rep_tm (hD : IsOpen D) {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (hB : ∀ a, inWb k r (Bs a))
    (P Q : Matrix (Fin (mdim k r (Fin.last r))) (Fin (mdim k r (Fin.last r))) ℂ)
    (ι : Fin m → Fin (mdim k r (Fin.last r))) (hι : Function.Injective ι)
    (hP : ∀ a c, P c (ι a) = Bs a (posL k r (Fin.last r) c))
    (hQ : ∀ b d, Q (ι b) d = herm (Hpk k r) (bvec (posL k r (Fin.last r) d)) (Bs b)) (u : ℂ) (a b : Fin m) :
    OperatorRepresentations.Rep (Tm (Econj (EV k r (Fin.last r) D E) P Q) u (ι a) (ι b))
      (fun y : Mx k r → E => (if id a = id b then u • y else 0) + RZ (Hpk k r) (unitB (Hpk k r) Bs (id a) (id b)) y) := by
  have he := rep_econj (E := E) hD Bs hB P Q ι hP hQ a b
  unfold Tm
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    exact congrHermitianCurvature (operator_rep_add (OperatorRepresentations.rep_algebraMap u) he) (fun f x => by simp)
  · rw [if_neg (fun h => hab (hι h)), zero_add]
    exact congrHermitianCurvature he (fun f x => by simp [hab])

end Frame

end CapelliCoordinates

private theorem intCast_mul' {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {i : Fin (r + 1)} {D : Set (Mx k r)} {X : Module.End ℂ (SV k r i D E)}
    {T : (Mx k r → E) → Mx k r → E} (z : ℤ) (h : OperatorRepresentations.Rep X T) :
    OperatorRepresentations.Rep ((z : Module.End ℂ (SV k r i D E)) * X) (fun f x => (z : ℂ) • T f x) :=
  ⟨h.1.smul _, fun φ g hg => by
    simp [Module.End.mul_apply, Module.End.intCast_apply, h.2 φ g hg, Int.cast_smul_eq_zsmul]⟩

theorem frame_minor : Formalism.FourierDecayAlt.Qr.FrameMinor := by
  intro E _ _ k r m D hD Bs hB P Q ι hι hP hQ w φ g hg
  have hrep : OperatorRepresentations.Rep (qminor (Econj (EV k r (Fin.last r) D E) P Q) ι ι w) (capR (E := E) k r Bs w) := by
    unfold qminor
    refine CapelliCoordinates.congrHermitianCurvature (OperatorRepresentations.rep_sum _ _ _ fun σ _ => intCast_mul' _
      (OperatorRepresentations.rep_prod m _ _ fun l => CapelliCoordinates.rep_tm hD Bs hB P Q ι hι hP hQ _ (σ l) l)) ?_
    intro f x
    simp [capR, qmF, Finset.sum_apply]
  exact hrep.2 φ g hg

end Formalism.FourierDecayAlt.P
