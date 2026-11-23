import Formalism.HermitianCurvature.FrameMinor
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OperatorRepresentations
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LemmaDDeterminantIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliCoordinates
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AnisotropicColumnSums
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameEntries

open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace CapelliTwoByTwo

theorem capelli_two_general_frame (t n : ℕ) (h : t = n + 2) (A : Type) [Ring A] [Algebra ℂ A] (Eop : Fin t → Fin t → A)
    (P Q : Matrix (Fin t) (Fin t) ℂ) (i0 i1 : Fin t) (h0 : i0.val = 0) (h1 : i1.val = 1) (ι : Fin n → Fin t)
    (hι : ∀ a, (ι a).val = a.val + 2) (hE : GlRel Eop) (hQP : Q * P = 1) (hPQ : P * Q = 1) (u : ℂ) (β β' : Fin t → ℂ)
    (hβ : ∀ j : Fin t, 2 ≤ j.val → (β ᵥ* P) j = 0 ∧ (β' ᵥ* P) j = 0) :
    chat2A Eop u (fun p => P p i0) (fun p => P p i1) β β' =
      ((β ᵥ* P) i0 * (β' ᵥ* P) i1 - (β ᵥ* P) i1 * (β' ᵥ* P) i0) • qminor (Econj Eop P Q) ι ι u := by
  subst h
  have e0 : i0 = 0 := Fin.ext (by simp [h0])
  have e1 : i1 = 1 := Fin.ext (by simp [h1])
  have eι : ι = skip2 (t := n + 2) 0 1 := by
    funext a
    apply Fin.ext
    rw [hι]
    simp [skip2]
  subst e0 e1
  rw [eι]
  exact second_contraction_adapted A n Eop P Q hE hQP hPQ u β β' hβ

section Eval

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}

theorem capelli_two_eval (hD : IsOpen D) (z : Fin (2 * r + k + 1) → ℂ) (u : ℂ) (x ξ : Fin (mdim k r i) → ℂ)
    (ψ : SV k r i D E) {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) :
    (ch2 (EV k r i D E) u (yV k r z i D E) x (etaV k r z i D E) ξ ψ).1 g =
      (chat2A (EV k r i D E) u (yv k r z i g) x (ybv k r z i g) ξ ψ).1 g := by
  have hy : ∀ (c : Fin (mdim k r i)) (φ : SV k r i D E),
      ((yV k r z i D E c) φ).1 g = yv k r z i g c • φ.1 g := by
    intro c φ
    unfold yV opV
    rw [dif_pos ⟨hD, OperatorRepresentations.good_yv z c⟩]
    show cutF k r i D (mulF _ φ.1) g = _
    rw [cutF_of_mem hg]
    rfl
  have hη : ∀ (c : Fin (mdim k r i)) (φ : SV k r i D E),
      ((etaV k r z i D E c) φ).1 g = ybv k r z i g c • φ.1 g := by
    intro c φ
    unfold etaV opV
    rw [dif_pos ⟨hD, OperatorRepresentations.good_ybv z c⟩]
    show cutF k r i D (mulF _ φ.1) g = _
    rw [cutF_of_mem hg]
    rfl
  unfold ch2 chat2A
  simp only [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ =>
    Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  split_ifs
  · simp only [LinearMap.smul_apply, Module.End.mul_apply, LinearMap.sub_apply, Submodule.coe_smul,
      Submodule.coe_sub, Pi.smul_apply, Pi.sub_apply, hy, hη]
    module
  · rfl

end Eval

section Zero

theorem Hpk_zero (r : ℕ) (a : Fin (2 * r + 0 + 1)) :
    Hpk 0 r a ⟨r, by omega⟩ = if a = ⟨r, by omega⟩ then -1 else 0 := by
  by_cases ha : a = ⟨r, by omega⟩
  · subst ha
    simp [Hpk]
  · rw [if_neg ha]
    have hv : a.val ≠ r := fun h => ha (Fin.ext h)
    simp only [Hpk]
    rw [if_neg (by omega), if_neg (by omega),
      if_neg (fun h => ha h.2.2)]

theorem herm_zero {r : ℕ} {v : Fin (2 * r + 0 + 1) → ℂ} (hv : inWb 0 r v) (w : Fin (2 * r + 0 + 1) → ℂ) :
    herm (Hpk 0 r) v w = -(star (w ⟨r, by omega⟩) * v ⟨r, by omega⟩) := by
  have hmv : Hpk 0 r *ᵥ v = fun i => (if i = ⟨r, by omega⟩ then -1 else 0) * v ⟨r, by omega⟩ := by
    ext i
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single ⟨r, by omega⟩]
    · rw [Hpk_zero]
    · intro b _ hb
      have hb' : b.val ≠ r := fun h => hb (Fin.ext h)
      rw [hv b (by have := b.isLt; omega), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [herm, hmv]
  simp only [dotProduct, Pi.star_apply]
  rw [Finset.sum_eq_single ⟨r, by omega⟩]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem normSq_zero {r : ℕ} {v w : Fin (2 * r + 0 + 1) → ℂ} (hv : inWb 0 r v) (hw : inWb 0 r w) :
    Complex.normSq (herm (Hpk 0 r) v w) = Tz 0 r v * Tz 0 r w := by
  have e : ∀ z : ℂ, (star z * z).re = Complex.normSq z := fun z => by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  have e2 : ∀ z : ℂ, Complex.normSq (star z) = Complex.normSq z := fun z => Complex.normSq_conj z
  rw [herm_zero hv, Tz, Tz, herm_zero hv, herm_zero hw]
  simp only [Complex.normSq_neg, Complex.normSq_mul, Complex.neg_re, neg_neg, e, e2]
  ring

end Zero

section Frame

variable {k r : ℕ}

def gd (k r : ℕ) (y x : Fin (2 * r + k + 1) → ℂ) : ℂ :=
  herm (Hpk k r) y y * herm (Hpk k r) x x - herm (Hpk k r) x y * herm (Hpk k r) y x

theorem idx {j : Fin (mdim k r (Fin.last r))} (h0 : ¬ j.val = 0) (h1 : ¬ j.val = 1) : j.val - 2 < k - 1 := by
  have hj := j.isLt
  simp only [mdim, Fin.val_last, Nat.sub_self, mul_zero, zero_add] at hj
  omega

def bc (k r : ℕ) (y x : Fin (2 * r + k + 1) → ℂ) (Bs : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ)
    (j : Fin (mdim k r (Fin.last r))) : Fin (2 * r + k + 1) → ℂ :=
  if h0 : j.val = 0 then y else if h1 : j.val = 1 then x else Bs ⟨j.val - 2, idx h0 h1⟩

def qrow (k r : ℕ) (y x : Fin (2 * r + k + 1) → ℂ) (Bs : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ)
    (j : Fin (mdim k r (Fin.last r))) (v : Fin (2 * r + k + 1) → ℂ) : ℂ :=
  if h0 : j.val = 0 then
    (herm (Hpk k r) x x * herm (Hpk k r) v y - herm (Hpk k r) x y * herm (Hpk k r) v x) / gd k r y x
  else if h1 : j.val = 1 then
    (herm (Hpk k r) y y * herm (Hpk k r) v x - herm (Hpk k r) y x * herm (Hpk k r) v y) / gd k r y x
  else herm (Hpk k r) v (Bs ⟨j.val - 2, idx h0 h1⟩)

theorem bc_inWb {y x : Fin (2 * r + k + 1) → ℂ} {Bs : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ} (hy : inWb k r y)
    (hx : inWb k r x) (hB : ∀ a, inWb k r (Bs a)) (j : Fin (mdim k r (Fin.last r))) : inWb k r (bc k r y x Bs j) := by
  unfold bc
  split_ifs
  · exact hy
  · exact hx
  · exact hB _

theorem qrow_sum (y x : Fin (2 * r + k + 1) → ℂ) (Bs : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ)
    (j : Fin (mdim k r (Fin.last r))) {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) :
    ∑ d, qrow k r y x Bs j (bvec (posL k r (Fin.last r) d)) * v (posL k r (Fin.last r) d) = qrow k r y x Bs j v := by
  have hl1 : ∀ v w u, herm (Hpk k r) (v + w) u = herm (Hpk k r) v u + herm (Hpk k r) w u := by
    intro v w u
    simp [herm, Matrix.mulVec_add, dotProduct_add]
  have hl2 : ∀ (c : ℂ) v u, herm (Hpk k r) (c • v) u = c * herm (Hpk k r) v u := by
    intro c v u
    simp [herm, Matrix.mulVec_smul, dotProduct_smul]
  let Lq : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := qrow k r y x Bs j
      map_add' := fun v w => by
        unfold qrow
        split_ifs
        · rw [hl1, hl1]
          ring
        · rw [hl1, hl1]
          ring
        · rw [hl1]
      map_smul' := fun c v => by
        show qrow k r y x Bs j (c • v) = c • qrow k r y x Bs j v
        unfold qrow
        split_ifs
        · rw [hl2, hl2, smul_eq_mul]
          ring
        · rw [hl2, hl2, smul_eq_mul]
          ring
        · rw [hl2, smul_eq_mul] }
  have hv' : v = ∑ d, v (posL k r (Fin.last r) d) • bvec (posL k r (Fin.last r) d) := by
    ext i
    simp only [Finset.sum_apply, Pi.smul_apply, bvec, smul_eq_mul, Pi.single_apply]
    by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
    · have hd0 : i.val - r < mdim k r (Fin.last r) := by
        simp only [mdim, Fin.val_last, Nat.sub_self, mul_zero, zero_add]
        omega
      rw [Finset.sum_eq_single ⟨i.val - r, hd0⟩]
      · have hp : posL k r (Fin.last r) ⟨i.val - r, hd0⟩ = i := by
          ext
          simp only [posL, Fin.val_last]
          omega
        rw [hp, if_pos rfl, mul_one]
      · intro b _ hb
        rw [if_neg, mul_zero]
        intro h
        apply hb
        ext
        have h2 := congrArg Fin.val h
        simp only [posL, Fin.val_last] at h2 ⊢
        omega
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [hv i (by omega)]
      symm
      apply Finset.sum_eq_zero
      intro d _
      rw [if_neg, mul_zero]
      intro h
      apply hi
      have hd := d.isLt
      simp only [mdim, Fin.val_last, Nat.sub_self, mul_zero, zero_add] at hd
      rw [h]
      simp only [posL, Fin.val_last]
      omega
  calc ∑ d, qrow k r y x Bs j (bvec (posL k r (Fin.last r) d)) * v (posL k r (Fin.last r) d)
      = Lq (∑ d, v (posL k r (Fin.last r) d) • bvec (posL k r (Fin.last r) d)) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [map_smul, smul_eq_mul, mul_comm]
        rfl
    _ = qrow k r y x Bs j v := by
        rw [← hv']
        rfl

theorem bc_herm {y x : Fin (2 * r + k + 1) → ℂ} {Bs : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ}
    (hB : IsFrameOf k r [y, x] Bs) (j : Fin (mdim k r (Fin.last r))) (w : Fin (2 * r + k + 1) → ℂ) (hw : w ∈ [y, x]) :
    herm (Hpk k r) (bc k r y x Bs j) w =
      if j.val = 0 then herm (Hpk k r) y w else if j.val = 1 then herm (Hpk k r) x w else 0 := by
  have hBw : ∀ a, herm (Hpk k r) (Bs a) w = 0 := fun a => hB.2.2 a w hw
  by_cases h0 : j.val = 0
  · rw [bc, dif_pos h0, if_pos h0]
  · by_cases h1 : j.val = 1
    · rw [bc, dif_neg h0, dif_pos h1, if_neg h0, if_pos h1]
    · rw [bc, dif_neg h0, dif_neg h1, if_neg h0, if_neg h1, hBw]

theorem gram {y x : Fin (2 * r + k + 1) → ℂ} {Bs : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ}
    (hd : gd k r y x ≠ 0) (hB : IsFrameOf k r [y, x] Bs) (j j' : Fin (mdim k r (Fin.last r))) :
    qrow k r y x Bs j (bc k r y x Bs j') = if j = j' then 1 else 0 := by
  have hBy : ∀ a, herm (Hpk k r) (Bs a) y = 0 := fun a => hB.2.2 a y (by simp)
  have hBx : ∀ a, herm (Hpk k r) (Bs a) x = 0 := fun a => hB.2.2 a x (by simp)
  have hyB : ∀ a, herm (Hpk k r) y (Bs a) = 0 := fun a => by
    rw [← Qx2.herm_star (Bs a) y, hBy, star_zero]
  have hxB : ∀ a, herm (Hpk k r) x (Bs a) = 0 := fun a => by
    rw [← Qx2.herm_star (Bs a) x, hBx, star_zero]
  have hne : ∀ {m m' : Fin (mdim k r (Fin.last r))}, m.val ≠ m'.val → m ≠ m' := fun h e => h (congrArg Fin.val e)
  by_cases h0 : j.val = 0
  · rw [qrow, dif_pos h0]
    by_cases h0' : j'.val = 0
    · rw [bc, dif_pos h0', if_pos (Fin.ext (h0.trans h0'.symm)), div_eq_one_iff_eq hd, gd]
      ring
    · by_cases h1' : j'.val = 1
      · rw [bc, dif_neg h0', dif_pos h1', if_neg (hne (by omega)), div_eq_zero_iff]
        left
        ring
      · rw [bc, dif_neg h0', dif_neg h1', if_neg (hne (by omega)), hBy, hBx]
        simp
  · by_cases h1 : j.val = 1
    · rw [qrow, dif_neg h0, dif_pos h1]
      by_cases h0' : j'.val = 0
      · rw [bc, dif_pos h0', if_neg (hne (by omega)), div_eq_zero_iff]
        left
        ring
      · by_cases h1' : j'.val = 1
        · rw [bc, dif_neg h0', dif_pos h1', if_pos (Fin.ext (h1.trans h1'.symm)), div_eq_one_iff_eq hd, gd]
          ring
        · rw [bc, dif_neg h0', dif_neg h1', if_neg (hne (by omega)), hBy, hBx]
          simp
    · rw [qrow, dif_neg h0, dif_neg h1]
      by_cases h0' : j'.val = 0
      · rw [bc, dif_pos h0', if_neg (hne (by omega)), hyB]
      · by_cases h1' : j'.val = 1
        · rw [bc, dif_neg h0', dif_pos h1', if_neg (hne (by omega)), hxB]
        · rw [bc, dif_neg h0', dif_neg h1', hB.2.1]
          by_cases hjj : j = j'
          · subst hjj
            simp
          · rw [if_neg hjj, if_neg]
            intro h
            apply hjj
            ext
            have h2 := congrArg Fin.val h
            simp only at h2
            omega

end Frame

end CapelliTwoByTwo

open CapelliTwoByTwo in
theorem capelli_two_by_two : Formalism.FourierDecayAlt.Q.CapelliIdentityEntry := by
  intro E _ _ k r z z' D f hz hz' hD hf g hg hGG Bs hB Y
  have hgi := FrameEntries.glev_inv hg.1
  have hy : inWb k r (g⁻¹ *ᵥ z) := Qx8.inWb_mulVec hgi hz
  have hk : 1 ≤ k := by
    by_contra hk
    obtain rfl : k = 0 := by omega
    apply hGG
    unfold GGl zetaL
    rw [Qx8.fvec_last, Qx8.fvec_last, normSq_zero (Qx8.inWb_mulVec hg.1 hz') hz]
    unfold Tz
    rw [Qx2.herm_uh hg.1.1]
    ring
  have hδ : gd k r (g⁻¹ *ᵥ z) z' = -((GGl k r z z' g : ℝ) : ℂ) := by
    unfold gd GGl zetaL
    rw [Qx8.fvec_last, Qx8.fvec_last, Qx2.herm_uh hgi.1, FrameEntries.herm_self, FrameEntries.herm_self, FrameEntries.herm_inv hg.1.1,
      ← Qx2.herm_star z' (g⁻¹ *ᵥ z)]
    push_cast
    rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]
    ring
  have hd : gd k r (g⁻¹ *ᵥ z) z' ≠ 0 := by
    rw [hδ, neg_ne_zero, Complex.ofReal_ne_zero]
    exact hGG
  set y : Fin (2 * r + k + 1) → ℂ := g⁻¹ *ᵥ z with hydef
  set P : Matrix (Fin (mdim k r (Fin.last r))) (Fin (mdim k r (Fin.last r))) ℂ :=
    Matrix.of fun c j => bc k r y z' Bs j (posL k r (Fin.last r) c) with hP
  set Q : Matrix (Fin (mdim k r (Fin.last r))) (Fin (mdim k r (Fin.last r))) ℂ :=
    Matrix.of fun j d => qrow k r y z' Bs j (bvec (posL k r (Fin.last r) d)) with hQ
  have hQP : Q * P = 1 := by
    ext j j'
    rw [Matrix.mul_apply, Matrix.one_apply, ← gram hd hB j j', ← qrow_sum y z' Bs j (bc_inWb hy hz' hB.1 j')]
    rfl
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  let i0 : Fin (mdim k r (Fin.last r)) := ⟨0, by rw [AnisotropicColumnSums.mdim_last]; omega⟩
  let i1 : Fin (mdim k r (Fin.last r)) := ⟨1, by rw [AnisotropicColumnSums.mdim_last]; omega⟩
  let ι : Fin (k - 1) → Fin (mdim k r (Fin.last r)) := fun a => ⟨a.val + 2, by
    have := a.isLt
    rw [AnisotropicColumnSums.mdim_last]; omega⟩
  have hβP : ∀ w ∈ [y, z'], ∀ j, ((fun j => herm (Hpk k r) (bvec (posL k r (Fin.last r) j)) w) ᵥ* P) j =
      if j.val = 0 then herm (Hpk k r) y w else if j.val = 1 then herm (Hpk k r) z' w else 0 := by
    intro w hw j
    rw [← bc_herm hB j w hw, ← AnisotropicColumnSums.sum_last (bc_inWb hy hz' hB.1 j)]
    rfl
  have e1 : yv k r z (Fin.last r) g = fun p => P p i0 := by
    funext j; simp [yv, Qx8.fvec_last, hP, bc, i0, hydef]
  have e2 : ybv k r z (Fin.last r) g = fun j => herm (Hpk k r) (bvec (posL k r (Fin.last r) j)) y := by
    funext j; simp only [ybv, Qx8.fvec_last]; exact FrameEntries.herm_inv hg.1.1 _ _
  have e4 : xv k r z' (Fin.last r) = fun p => P p i1 := by
    funext j; simp [xv, Qx8.fvec_last, hP, bc, i1]
  have e5 : xbv k r z' (Fin.last r) = fun j => herm (Hpk k r) (bvec (posL k r (Fin.last r) j)) z' := by
    funext j; simp only [xbv, Qx8.fvec_last]
  have key := capelli_two_general_frame (mdim k r (Fin.last r)) (k - 1) (by rw [AnisotropicColumnSums.mdim_last]; omega)
    (Module.End ℂ (SV k r (Fin.last r) D E)) (EV k r (Fin.last r) D E) P Q i0 i1 rfl rfl ι (fun _ => rfl)
    (relation_representation E k r 0 (Fin.last r) D hD).1 hQP hPQ (uC k r (Fin.last r) Y - 1)
    (fun j => herm (Hpk k r) (bvec (posL k r (Fin.last r) j)) y)
    (fun j => herm (Hpk k r) (bvec (posL k r (Fin.last r) j)) z') (by
      intro j hj
      rw [hβP y (by simp), hβP z' (by simp), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega)]
      exact ⟨rfl, rfl⟩)
  have hm := frame_minor E k r (k - 1) D hD Bs hB.1 P Q ι
    (fun a b e => Fin.ext (by have e' : a.val + 2 = b.val + 2 := congrArg Fin.val e; omega))
    (by
      intro a c
      simp [hP, bc, ι])
    (by
      intro b d
      simp [hQ, qrow, ι])
    (uC k r (Fin.last r) Y - 1) (mkV hD f hf) g hg
  rw [(transfer_representation E k r z z' (Fin.last r) D hD f hf Y 1 1).2 g hg]
  show -((ch2 (EV k r (Fin.last r) D E) (uC k r (Fin.last r) Y - 1) (yV k r z (Fin.last r) D E) (xv k r z' (Fin.last r))
    (etaV k r z (Fin.last r) D E) (xbv k r z' (Fin.last r)) (mkV hD f hf)).1 g) = _
  rw [capelli_two_eval hD z _ _ _ _ hg, e1, e2, e4, e5, key, hβP y (by simp), hβP y (by simp), hβP z' (by simp),
    hβP z' (by simp)]
  show -((herm (Hpk k r) y y * herm (Hpk k r) z' z' - herm (Hpk k r) z' y * herm (Hpk k r) y z') •
    (qminor (Econj (EV k r (Fin.last r) D E) P Q) ι ι (uC k r (Fin.last r) Y - 1) (mkV hD f hf)).1 g) = _
  rw [hm, ← neg_smul]
  have hs : -(herm (Hpk k r) y y * herm (Hpk k r) z' z' - herm (Hpk k r) z' y * herm (Hpk k r) y z') =
      ((GGl k r z z' g : ℝ) : ℂ) := by
    have := hδ
    unfold gd at this
    rw [this, neg_neg]
  have hu : uC k r (Fin.last r) Y - 1 = Y + ((k : ℂ) - 2) / 2 := by
    rw [FrameEntries.uC_last]; ring
  rw [hs, hu]
  congr 1
  exact (capelli_right_good E k r (k - 1) (Fin.last r) D hD Bs hB.1 _).loc _ _ (fun x hx => cutF_of_mem hx) g hg

end Formalism.FourierDecayAlt.P
