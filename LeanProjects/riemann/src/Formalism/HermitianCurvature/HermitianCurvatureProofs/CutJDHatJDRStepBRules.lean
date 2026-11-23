import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPTop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QminorZero
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellMulVecBasis
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedLocSec

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.StepB

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx3 Formalism.FourierDecayAlt.P.WeylCellAction

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem tailW (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0) (b : Fin r) : ∀ n : ℕ, ∀ i : Fin (r + 1), i.val = b.val + 1 + n →
    ∃ T : Mx k r, wCell k r i c = wCell k r b.succ c * T ∧ T ∈ Glev k r b.succ ∧
      (∀ v, inWb k r v → T *ᵥ v = v)
  | 0, i, hi => by
    have : i = b.succ := Fin.ext (by simp [hi])
    subst this
    exact ⟨1, by simp, glev_one _, fun v _ => by simp⟩
  | n + 1, i, hi => by
    have hl : b.val + 1 + n < r := by have := i.isLt; omega
    set l : Fin r := ⟨b.val + 1 + n, hl⟩ with hldef
    have hil : i = l.succ := Fin.ext (by simp [l, hi]; omega)
    subst hil
    obtain ⟨T, hT, hTG, hTv⟩ := tailW c hc b n l.castSucc (by simp [l])
    have hw := (Formalism.FourierDecayAlt.P.weyl_level_element_properties k r l (c l) (hc l)).1
    refine ⟨T * w1 k r l (c l), ?_, ?_, ?_⟩
    · rw [Formalism.FourierDecayAlt.P.Qx6.wCell_succ, hT, Matrix.mul_assoc]
    · exact glev_mul hTG (glev_mono (by rw [Fin.le_def]; simp [l]) hw)
    · intro v hv
      rw [← Matrix.mulVec_mulVec, Formalism.FourierDecayAlt.P.CutMP.unipotent_fixes_anisotropic_vector l _ v hv, hTv v hv]

theorem bvec_wI_inWb (v : Fin (k + 1)) : inWb k r (bvec (wI k r v)) := by
  intro i hi
  simp only [bvec, Pi.single_apply]
  rw [if_neg]
  intro h
  have := congrArg Fin.val h
  simp [wI] at this
  omega

section rules

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rightRuleB (z' : Fin (2 * r + k + 1) → ℂ) (D : Set (Mx k r)) (f : Mx k r → E) (hz' : inWb k r z')
    (hD : IsOpen D) (hS : SmoothLev k r 0 D f) (hR : RightEq k r z' 0 D f) (g : Mx k r) (hg : g ∈ Glev k r 0 ∩ D)
    (a : Fin r) (ha : a.val + 1 < r) (w : Fin (k + 1)) : EH k r (eI k r a) (wI k r w) f g = 0 := by
  have hc : Continuous fun x : Mx k r => g * x := cont_lmul g
  have hD' : IsOpen {x : Mx k r | g * x ∈ D} := hD.preimage hc
  have hS' : SmoothLev k r a.castSucc {x | g * x ∈ D} (fun x => f (g * x)) :=
    smooth_left g (fun x hx => glev0 hg.1 hx) hS
  have hR' : RightEq k r z' a.castSucc {x | g * x ∈ D} (fun x => f (g * x)) := by
    intro x hx n hn
    have := hR (g * x) ⟨glev0 hg.1 hx.1, hx.2⟩ n (nlev_mono (zero_le' _) hn)
    simpa [Matrix.mul_assoc] using this
  have h1 : (1 : Mx k r) ∈ Glev k r a.castSucc ∩ {x | g * x ∈ D} :=
    ⟨glev_one _, by simpa using hg.2⟩
  have hrule := (Formalism.FourierDecayAlt.P.right_action_rule E k r z' a {x | g * x ∈ D} (fun x => f (g * x)) hz' hD' hS' hR'
    1 h1).1
  have hjlt : r + w.val - a.val - 1 < mdim k r a.succ := by simp [mdim]; omega
  have hpos : posL k r a.succ ⟨r + w.val - a.val - 1, hjlt⟩ = wI k r w := by
    simp [posL, wI, Fin.ext_iff]; omega
  have h := hrule ⟨r + w.val - a.val - 1, hjlt⟩
  rw [hpos, eH_left, Matrix.mul_one] at h
  rw [h]
  have hx : xv k r z' a.succ ⟨r + w.val - a.val - 1, hjlt⟩ = 0 := by
    simp only [xv, fvec, hpos]
    rw [dif_pos (show (a.succ : Fin (r + 1)).val < r by simp; omega)]
    simp only [bvec, Pi.single_apply]
    rw [if_neg]
    intro h'
    have := congrArg Fin.val h'
    simp [wI, eI] at this
    omega
  rw [hx, zero_smul]

theorem leftRuleB (z : Fin (2 * r + k + 1) → ℂ) (D : Set (Mx k r)) (f : Mx k r → E) (hz : inWb k r z)
    (hD : IsOpen D) (hDN : ∀ g ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * g ∈ D) (hS : SmoothLev k r 0 D f)
    (hL : LeftEq k r z 0 D f) (c : Fin r → ℂ) (hc : c ∈ OmX r) (g : Mx k r) (hg : g ∈ Glev k r (Fin.last r))
    (hWD : wCell k r (Fin.last r) c * g ∈ D) (b : Fin r) (hb : b.val + 1 < r) (v : Fin (k + 1)) :
    EH k r (wI k r v) (eI k r b) f (wCell k r (Fin.last r) c * g) = 0 := by
  have hcne : ∀ l, c l ≠ 0 := hc
  obtain ⟨hW0, hWcomm⟩ := head_comm (k := k) c hcne b.val b.castSucc (by simp)
  obtain ⟨T, hT, hTG, hTv⟩ := tailW (k := k) c hcne b (r - b.val - 1) (Fin.last r) (by simp; omega)
  have hg₁ : T * g ∈ Glev k r b.succ := glev_mul hTG (glev_mono (Fin.le_last _) hg)
  have hsplit : wCell k r (Fin.last r) c * g = wCell k r b.castSucc c * (w1 k r b (c b) * (T * g)) := by
    simp only [hT, Formalism.FourierDecayAlt.P.Qx6.wCell_succ, Matrix.mul_assoc]
  have hWx : ∀ x ∈ Glev k r b.castSucc, wCell k r b.castSucc c * x ∈ Glev k r 0 := fun x hx => glev0 hW0 hx
  have hS' := smooth_left (E := E) (f := f) (D := D) (wCell k r b.castSucc c) hWx hS
  have hcont : Continuous fun x : Mx k r => wCell k r b.castSucc c * x := cont_lmul _
  have hD' : IsOpen {x : Mx k r | wCell k r b.castSucc c * x ∈ D} := hD.preimage hcont
  have hN' : ∀ x ∈ Glev k r b.castSucc ∩ {x | wCell k r b.castSucc c * x ∈ D}, ∀ n ∈ Nlev k r b.castSucc,
      n * x ∈ {x | wCell k r b.castSucc c * x ∈ D} := by
    intro x hx n hn
    show wCell k r b.castSucc c * (n * x) ∈ D
    rw [← Matrix.mul_assoc, hWcomm b.castSucc le_rfl n hn.2, Matrix.mul_assoc]
    exact hDN _ ⟨hWx x hx.1, hx.2⟩ n (nlev_mono (zero_le' _) hn)
  have hL' : LeftEq k r z b.castSucc {x | wCell k r b.castSucc c * x ∈ D}
      (fun x => f (wCell k r b.castSucc c * x)) := by
    intro x hx n hn
    show f (wCell k r b.castSucc c * (n * x)) = _ • f (wCell k r b.castSucc c * x)
    rw [← Matrix.mul_assoc, hWcomm b.castSucc le_rfl n hn.2, Matrix.mul_assoc]
    exact hL _ ⟨hWx x hx.1, hx.2⟩ n (nlev_mono (zero_le' _) hn)
  have hpt : w1 k r b (c b) * (T * g) ∈ {x | wCell k r b.castSucc c * x ∈ D} := by
    show _ ∈ D
    rw [← hsplit]; exact hWD
  have hrule := (Formalism.FourierDecayAlt.P.left_action_rule E k r z b {x | wCell k r b.castSucc c * x ∈ D}
    (fun x => f (wCell k r b.castSucc c * x)) hz hD' hS' hN' hL' (c b) (hcne b) (T * g) hg₁ hpt).1
  have hjlt : r + v.val - b.val - 1 < mdim k r b.succ := by simp [mdim]; omega
  have hpos : posL k r b.succ ⟨r + v.val - b.val - 1, hjlt⟩ = wI k r v := by
    simp [posL, wI, Fin.ext_iff]; omega
  have h := hrule ⟨r + v.val - b.val - 1, hjlt⟩
  rw [hpos, eH_left, ← hsplit] at h
  rw [h]
  have hb1 : (b.succ : Fin (r + 1)).val < r := by simp; omega
  have hy : ybv k r z b.succ (T * g) ⟨r + v.val - b.val - 1, hjlt⟩ = 0 := by
    simp only [ybv, hpos, fvec, dif_pos hb1]
    rw [Formalism.FourierDecayAlt.P.SignAntidiagonal.herm_bvec_eI, ← Matrix.mulVec_mulVec]
    have hgw : inWb k r (g *ᵥ bvec (wI k r v)) :=
      Formalism.FourierDecayAlt.P.NFRadRedLocSec.inWb_uwb (Formalism.FourierDecayAlt.P5.Rad.glev_last_uwb hg) (bvec_wI_inWb v)
    rw [hTv _ hgw]
    exact hgw _ (Or.inr (by simp [esI]; omega))
  rw [hy, mul_zero, zero_smul]

end rules

section ring

theorem zcomm {A : Type} [Ring A] (z : ℤ) (X Y : A) : ((z : ℤ) : A) * (X * Y) = X * (((z : ℤ) : A) * Y) := by
  rw [← mul_assoc, (Int.cast_commute z X).eq, mul_assoc]

theorem succ_above_one_val {t : ℕ} (i : Fin (t + 1)) :
    ((Fin.succ (0 : Fin (t + 1))).succAbove i).val = if i.val = 0 then 0 else i.val + 1 := by
  unfold Fin.succAbove
  split_ifs with h1 h2 h2 <;> simp_all [Fin.lt_def]

theorem zmul {A : Type} [Ring A] [Algebra ℂ A] (z : ℤ) (x : A) : ((z : ℤ) : A) * x = ((z : ℂ)) • x := by
  rw [Algebra.smul_def, map_intCast]

theorem stepB_ring {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E)
    {M : Type} [AddCommGroup M] [Module ℂ M] (Λ : A →ₗ[ℂ] M) (p0 p1 : Fin n) (h01 : p0 ≠ p1) (κ : ℂ)
    {t : ℕ} (a b : Fin (t + 2) → Fin n) (ha0 : a 0 = p0) (ha1 : a 1 = p1) (hb0 : b 0 = p0) (hb1 : b 1 = p1)
    (haR : ∀ m : Fin (t + 2), 2 ≤ m.val → a m ≠ p0)
    (hbR : ∀ m : Fin (t + 2), 2 ≤ m.val → b m ≠ p0)
    (hL0 : ∀ m : Fin (t + 2), 2 ≤ m.val → ∀ X, Λ (E (a m) p0 * X) = 0)
    (hL1 : ∀ X, Λ (E p1 p0 * X) = κ • Λ X)
    (hR0 : ∀ m : Fin (t + 2), 2 ≤ m.val → ∀ X, Λ (X * E p0 (b m)) = 0)
    (hR1 : ∀ X, Λ (X * E p0 p1) = Λ X) (u : ℂ) :
    Λ (qminor E a b u) = Λ (Tm E u p0 p0 * qminor E (a ∘ Fin.succ) (b ∘ Fin.succ) (u - 1)) -
      κ • Λ (qminor E (fun j : Fin t => a ⟨j.val + 2, by omega⟩) (fun j : Fin t => b ⟨j.val + 2, by omega⟩)
        (u - 1 - 1)) := by

  set a' : Fin (t + 1) → Fin n := a ∘ (Fin.succ (0 : Fin (t + 1))).succAbove with ha'
  set b' : Fin (t + 1) → Fin n := b ∘ Fin.succ with hb'
  set τ : Equiv.Perm (Fin (t + 1)) := (Fin.last t).cycleRange with hτ
  have hsq : ((Equiv.Perm.sign τ : ℤ) : A) * ((Equiv.Perm.sign τ : ℤ) : A) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hsg : ((Equiv.Perm.sign τ : ℤ) : A) = (((-1 : ℤ) ^ t : ℤ) : A) := by
    rw [hτ, Fin.sign_cycleRange]
    simp
  have hlast : (a' ∘ τ) (Fin.last t) = p0 := by
    show a ((Fin.succ (0 : Fin (t + 1))).succAbove (τ (Fin.last t))) = p0
    rw [hτ, Fin.cycleRange_self, ← ha0]
    congr 1
  have hcs : (a' ∘ τ) ∘ Fin.castSucc = fun j : Fin t => a ⟨j.val + 2, by omega⟩ := by
    funext j
    simp only [Function.comp_apply, hτ, ha']
    congr 1
    apply Fin.ext
    rw [succ_above_one_val, Fin.coe_cycleRange_of_lt (by rw [Fin.lt_def]; simp)]
    try simp
  have hbs : b' ∘ Fin.succ = fun j : Fin t => b ⟨j.val + 2, by omega⟩ := by
    funext j
    simp only [Function.comp_apply, hb']
    rfl
  have hQ' : Λ (qminor E a' b' (u - 1)) =
      Λ (qminor E (fun j : Fin t => a ⟨j.val + 2, by omega⟩) (fun j : Fin t => b ⟨j.val + 2, by omega⟩)
        (u - 1 - 1)) := by
    have hsk := Formalism.REAL.quantumMinorRowSkew_holds A n (t + 1) E a' b' τ (u - 1)
    have e1 : qminor E a' b' (u - 1) = ((Equiv.Perm.sign τ : ℤ) : A) * qminor E (a' ∘ τ) b' (u - 1) := by
      rw [hsk, ← mul_assoc, hsq, one_mul]
    rw [e1, Formalism.FourierDecayAlt.P.expansion_last_line A n t E hE (a' ∘ τ) b' (u - 1), Finset.mul_sum, map_sum,
      Fin.sum_univ_succ]
    have hrest : ∀ m : Fin t, Λ (((Equiv.Perm.sign τ : ℤ) : A) * ((((-1 : ℤ) ^ (t + ((m.succ : Fin (t + 1)) : ℕ)) : ℤ) : A) *
        (qminor E ((a' ∘ τ) ∘ Fin.castSucc) (b' ∘ m.succ.succAbove) (u - 1 - 1) *
          Tm E (u - 1) ((a' ∘ τ) (Fin.last t)) (b' m.succ)))) = 0 := by
      intro m
      have hbm : b' m.succ = b ⟨m.val + 2, by omega⟩ := rfl
      rw [hlast, hbm]
      unfold Tm
      rw [if_neg (Ne.symm (hbR ⟨m.val + 2, by omega⟩ (by simp))), zero_add, ← mul_assoc, ← mul_assoc]
      exact hR0 ⟨m.val + 2, by omega⟩ (by simp) _
    rw [Finset.sum_eq_zero (fun m _ => hrest m), add_zero, hlast]
    have hb0' : b' 0 = p1 := by simp only [hb', Function.comp_apply]; exact hb1
    rw [hb0']
    unfold Tm
    rw [if_neg h01, zero_add, ← mul_assoc, ← mul_assoc, hR1, Fin.succAbove_zero, hcs, hbs, hsg, ← Int.cast_mul]
    have h11 : ((-1 : ℤ) ^ t * (-1) ^ (t + ((0 : Fin (t + 1)) : ℕ))) = 1 := by
      rw [Fin.val_zero, add_zero, ← pow_add, ← two_mul, pow_mul]
      norm_num
    rw [h11, Int.cast_one, one_mul]

  rw [Formalism.FourierDecayAlt.P.expansion_first_column A n (t + 1) E a b u, map_sum, Fin.sum_univ_succ, Fin.sum_univ_succ]
  have hrest : ∀ m : Fin t, Λ ((((-1 : ℤ) ^ ((m.succ.succ : Fin (t + 2)) : ℕ) : ℤ) : A) *
      (Tm E u (a m.succ.succ) (b 0) * qminor E (a ∘ m.succ.succ.succAbove) (b ∘ Fin.succ) (u - 1))) = 0 := by
    intro m
    rw [hb0]
    unfold Tm
    rw [if_neg (haR _ (by simp)), zero_add, zcomm]
    exact hL0 _ (by simp) _
  rw [Finset.sum_eq_zero (fun m _ => hrest m), add_zero]
  have h1 : Λ ((((-1 : ℤ) ^ (((0 : Fin (t + 1)).succ : Fin (t + 2)) : ℕ) : ℤ) : A) *
      (Tm E u (a (0 : Fin (t + 1)).succ) (b 0) * qminor E (a ∘ (0 : Fin (t + 1)).succ.succAbove) (b ∘ Fin.succ) (u - 1))) =
      -(κ • Λ (qminor E a' b' (u - 1))) := by
    have ha1' : a (0 : Fin (t + 1)).succ = p1 := ha1
    rw [ha1', hb0]
    unfold Tm
    rw [if_neg (Ne.symm h01), zero_add, zcomm, hL1, zmul, map_smul]
    simp <;> rfl
  rw [h1, hQ']
  simp only [Fin.val_zero, pow_zero, Int.cast_one, one_mul, Fin.succAbove_zero, hb0, ha0]
  rw [hb']
  exact (sub_eq_add_neg _ _).symm
