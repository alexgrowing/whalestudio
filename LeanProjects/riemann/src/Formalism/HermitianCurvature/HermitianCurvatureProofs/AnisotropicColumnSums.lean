import Formalism.HermitianCurvature.FrameMinor
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OperatorRepresentations
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LemmaDDeterminantIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator

open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace AnisotropicColumnSums

theorem chat_gen (t n : ℕ) (h : t = n + 1) (A : Type) [Ring A] [Algebra ℂ A] (Eop : Fin t → Fin t → A)
    (P Q : Matrix (Fin t) (Fin t) ℂ) (la : Fin t) (hla : la.val = n) (ι : Fin n → Fin t)
    (hι : ∀ a, (ι a).val = a.val) (hE : GlRel Eop) (hQP : Q * P = 1) (hPQ : P * Q = 1) (u : ℂ) (β : Fin t → ℂ)
    (hβ : ∀ j, j ≠ la → (β ᵥ* P) j = 0) :
    chatA Eop u (fun p => P p la) β = (β ᵥ* P) la • qminor (Econj Eop P Q) ι ι u := by
  subst h
  have e1 : la = Fin.last n := Fin.ext hla
  subst e1
  have e2 : ι = skip1 (Fin.last n) := by
    funext a
    apply Fin.ext
    have := a.isLt
    simp [skip1, hι]
  rw [e2]
  exact first_contraction_adapted A n Eop P Q hE hQP hPQ u β hβ

variable {k r : ℕ}

theorem sum_last {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) (w : Fin (2 * r + k + 1) → ℂ) :
    ∑ d, herm (Hpk k r) (bvec (posL k r (Fin.last r) d)) w * v (posL k r (Fin.last r) d) = herm (Hpk k r) v w := by
  have hinj : ∀ c c' : Fin (mdim k r (Fin.last r)), posL k r (Fin.last r) c = posL k r (Fin.last r) c' → c = c' := by
    intro c c' h
    ext
    simp only [posL, Fin.ext_iff] at h
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
  have hv' : v = ∑ d, v (posL k r (Fin.last r) d) • bvec (posL k r (Fin.last r) d) := by
    ext q
    simp only [Finset.sum_apply, Pi.smul_apply, bvec, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    by_cases hq : Qx2.inV k r (Fin.last r) q
    · obtain ⟨d0, rfl⟩ := hsurj q hq
      rw [Fintype.sum_eq_single d0]
      · simp
      · intro d hd
        have hne : posL k r (Fin.last r) d0 ≠ posL k r (Fin.last r) d := fun h => hd (hinj _ _ h).symm
        simp [hne]
    · rw [Finset.sum_eq_zero]
      · apply hv
        simp only [Qx2.inV, Fin.val_last] at hq
        omega
      · intro d _
        have hne : q ≠ posL k r (Fin.last r) d := by
          rintro rfl
          apply hq
          have hd := d.isLt
          simp only [Qx2.inV, posL, mdim, Fin.val_last] at hd ⊢
          omega
        simp [hne]
  conv_rhs => rw [hv']
  unfold herm
  rw [Matrix.mulVec_sum, dotProduct_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  ring

def bcol (k r : ℕ) (x : Fin (2 * r + k + 1) → ℂ) (Bs : Fin k → Fin (2 * r + k + 1) → ℂ)
    (j : Fin (mdim k r (Fin.last r))) : Fin (2 * r + k + 1) → ℂ :=
  if h : j.val < k then Bs ⟨j.val, h⟩ else x

def nrm (k r : ℕ) (x : Fin (2 * r + k + 1) → ℂ) (j : Fin (mdim k r (Fin.last r))) : ℂ :=
  if j.val < k then 1 else (herm (Hpk k r) x x)⁻¹

theorem mdim_last : mdim k r (Fin.last r) = k + 1 := by
  simp [mdim]

theorem bcol_inWb {x : Fin (2 * r + k + 1) → ℂ} {Bs : Fin k → Fin (2 * r + k + 1) → ℂ} (hx : inWb k r x)
    (hB : IsFrameOf k r [x] Bs) (j : Fin (mdim k r (Fin.last r))) : inWb k r (bcol k r x Bs j) := by
  unfold bcol
  split_ifs
  · exact hB.1 _
  · exact hx

theorem herm_bcol_eq_ite {x : Fin (2 * r + k + 1) → ℂ} {Bs : Fin k → Fin (2 * r + k + 1) → ℂ}
    (hB : IsFrameOf k r [x] Bs) (j : Fin (mdim k r (Fin.last r))) :
    herm (Hpk k r) (bcol k r x Bs j) x = if j.val < k then 0 else herm (Hpk k r) x x := by
  unfold bcol
  by_cases h : j.val < k
  · rw [dif_pos h, if_pos h]
    exact hB.2.2 _ x (List.mem_singleton_self x)
  · rw [dif_neg h, if_neg h]

private theorem herm_eq_star_herm_swap (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v w = star (herm (Hpk k r) w v) := by
  unfold herm
  rw [Matrix.star_dotProduct, Matrix.star_mulVec, Qx2.hpk_h, ← Matrix.dotProduct_mulVec]

theorem gram {x : Fin (2 * r + k + 1) → ℂ} {Bs : Fin k → Fin (2 * r + k + 1) → ℂ}
    (hxx : herm (Hpk k r) x x ≠ 0) (hB : IsFrameOf k r [x] Bs) (j j' : Fin (mdim k r (Fin.last r))) :
    herm (Hpk k r) (bcol k r x Bs j') (bcol k r x Bs j) * nrm k r x j = if j = j' then 1 else 0 := by
  obtain ⟨hBw, hBo, hBx⟩ := hB
  have hx0 : ∀ a, herm (Hpk k r) (Bs a) x = 0 := fun a => hBx a x (List.mem_singleton_self x)
  have hx0' : ∀ a, herm (Hpk k r) x (Bs a) = 0 := fun a => by rw [herm_eq_star_herm_swap, hx0, star_zero]
  have hj : j.val < k + 1 := by
    have := j.isLt
    simp only [mdim, Fin.val_last] at this
    omega
  have hj' : j'.val < k + 1 := by
    have := j'.isLt
    simp only [mdim, Fin.val_last] at this
    omega
  unfold bcol nrm
  by_cases h1 : j.val < k <;> by_cases h2 : j'.val < k
  · rw [dif_pos h2, dif_pos h1, if_pos h1, mul_one, hBo]
    by_cases hjj : j = j'
    · subst hjj
      simp
    · have hne : ¬ j'.val = j.val := fun h => hjj (Fin.ext h.symm)
      simp [hjj, hne]
  · rw [dif_neg h2, dif_pos h1, if_pos h1, mul_one, hx0', if_neg]
    rintro rfl
    exact h2 h1
  · rw [dif_pos h2, dif_neg h1, if_neg h1, hx0, zero_mul, if_neg]
    rintro rfl
    exact h1 h2
  · have hjj : j = j' := by
      ext
      omega
    rw [dif_neg h2, dif_neg h1, if_neg h1, if_pos hjj, mul_inv_cancel₀ hxx]

end AnisotropicColumnSums

open AnisotropicColumnSums in
theorem qr_chatFrame_of : Formalism.FourierDecayAlt.Qr.FrameMinor → Formalism.FourierDecayAlt.Qr.ChatFrame := by
  intro hFM E _ _ k r D hD x Bs hx hxx hB u φ g hg
  set P : Matrix (Fin (mdim k r (Fin.last r))) (Fin (mdim k r (Fin.last r))) ℂ :=
    Matrix.of fun c j => bcol k r x Bs j (posL k r (Fin.last r) c) with hP
  set Q : Matrix (Fin (mdim k r (Fin.last r))) (Fin (mdim k r (Fin.last r))) ℂ :=
    Matrix.of fun j d => herm (Hpk k r) (bvec (posL k r (Fin.last r) d)) (bcol k r x Bs j) * nrm k r x j with hQ
  have hQP : Q * P = 1 := by
    ext j j'
    rw [Matrix.mul_apply, Matrix.one_apply, ← gram hxx hB j j', ← sum_last (bcol_inWb hx hB j'), Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d _
    simp only [hP, hQ, Matrix.of_apply]
    ring
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  let la : Fin (mdim k r (Fin.last r)) := ⟨k, by rw [mdim_last]; omega⟩
  let ι : Fin k → Fin (mdim k r (Fin.last r)) := fun a => ⟨a.val, by rw [mdim_last]; omega⟩
  have hβP : ∀ j, ((fun j => herm (Hpk k r) (bvec (posL k r (Fin.last r) j)) x) ᵥ* P) j =
      if j.val < k then 0 else herm (Hpk k r) x x := by
    intro j
    rw [← herm_bcol_eq_ite hB j, ← sum_last (bcol_inWb hx hB j)]
    rfl
  have hcol : (fun j => x (posL k r (Fin.last r) j)) = fun p => P p la := by
    funext p
    simp [hP, bcol, la]
  have key := chat_gen (mdim k r (Fin.last r)) k mdim_last (Module.End ℂ (SV k r (Fin.last r) D E))
    (EV k r (Fin.last r) D E) P Q la rfl ι (fun _ => rfl) (relation_representation E k r 0 (Fin.last r) D hD).1 hQP hPQ u
    (fun j => herm (Hpk k r) (bvec (posL k r (Fin.last r) j)) x) (by
      intro j hj
      rw [hβP, if_pos]
      have h1 : j.val < k + 1 := lt_of_lt_of_eq j.isLt mdim_last
      have : j.val ≠ k := fun e => hj (Fin.ext e)
      omega)
  rw [hcol, key, hβP, if_neg (by simp [la])]
  have hm := hFM E k r k D hD Bs hB.1 P Q ι (fun a b e => Fin.ext (by have e' := congrArg Fin.val e; exact e'))
    (by
      intro a c
      simp [hP, bcol, ι])
    (by
      intro b d
      simp [hQ, bcol, nrm, ι])
    u φ g hg
  rw [← hm]
  rfl

end Formalism.FourierDecayAlt.P
