import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MemInvCoeIdeal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.WeightPositive

noncomputable section

open NumberField Module Formalism.MainNotions.S
open Classical

namespace Formalism.L2.SG.Pf.Cnt.R1

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) {r : ℕ}

theorem hsw (x y : S.V) : S.hT y x = star (S.hT x y) := (S.herm.eq x y).symm

theorem hsw0 {x y : S.V} (h : S.hT x y = 0) : S.hT y x = 0 := by rw [hsw, h, star_zero]

variable {S}
variable (e y : Fin r → S.V) (z : S.V) (N : ℕ)

structure Dual : Prop where
  ee : ∀ a b, S.hT (e a) (e b) = 0
  yy : ∀ a b, S.hT (y a) (y b) = 0
  ey : ∀ a b, S.hT (e a) (y b) = if a = b then 1 else 0
  ez : ∀ a, S.hT (e a) z = 0
  yz : ∀ a, S.hT (y a) z = 0
  zz : S.hT z z = -(N : E)

def IsW (w : S.V) : Prop := (∀ a, S.hT (e a) w = 0) ∧ (∀ a, S.hT (y a) w = 0) ∧ S.hT z w = 0

variable {e y z N}

theorem Dual.ye (h : Dual e y z N) (a b) : S.hT (y a) (e b) = if b = a then 1 else 0 := by
  rw [hsw, h.ey]; split_ifs <;> simp

theorem real_of (τ : E →+* ℂ) (hτc : ∀ a, τ (star a) = starRingEnd ℂ (τ a)) (w : S.V) :
    τ (S.hT w w) = ((τ (S.hT w w)).re : ℂ) := by
  have h1 : starRingEnd ℂ (τ (S.hT w w)) = τ (S.hT w w) := by
    rw [← hτc, ← hsw]
  have him : (τ (S.hT w w)).im = 0 := Complex.conj_eq_iff_im.1 h1
  exact Complex.ext (by simp) (by simp [him])

theorem semidefG (h : Dual e y z N) (hN : 0 < N) (τ : E →+* ℂ) (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a))
    {p' : ℕ} (hsig : Formalism.UG.HasSignature (S.gram.map τ) p' (r + 1)) (w : S.V) (hw : IsW e y z w) :
    0 ≤ (τ (S.hT w w)).re := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨hE, hF, hz⟩ := hw
  have hT0 : (0 : ℝ) < N := by exact_mod_cast hN
  let wv : Fin r ⊕ Bool → S.V := Sum.elim (fun a => e a - y a) (fun b => if b then w else z)
  let d : Fin r ⊕ Bool → ℝ := Sum.elim (fun _ => -2) (fun b => if b then (τ (S.hT w w)).re else -(N : ℝ))
  have hoff : ∀ i j, i ≠ j → S.hT (wv i) (wv j) = 0 := by
    intro i j hij
    rcases i with a | b <;> rcases j with a' | b'
    · have ha : a ≠ a' := fun h => hij (by rw [h])
      have ha' : a' ≠ a := fun h => ha h.symm
      simp only [wv, Sum.elim_inl, map_sub, LinearMap.sub_apply, h.ee, h.yy, h.ey, h.ye, if_neg ha, if_neg ha']
      simp
    · cases b'
      · simp only [wv, Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true, if_false, map_sub,
          LinearMap.sub_apply, h.ez, h.yz, sub_zero]
      · simp only [wv, Sum.elim_inl, Sum.elim_inr, if_true, map_sub, LinearMap.sub_apply, hE, hF, sub_zero]
    · cases b
      · simp only [wv, Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true, if_false, map_sub,
          hsw0 S (h.ez a'), hsw0 S (h.yz a'), sub_zero]
      · simp only [wv, Sum.elim_inl, Sum.elim_inr, if_true, map_sub, hsw0 S (hE a'), hsw0 S (hF a'), sub_zero]
    · cases b <;> cases b'
      · exact absurd rfl hij
      · simpa [wv] using hz
      · simpa [wv] using hsw0 S hz
      · exact absurd rfl hij
  have hdiag : ∀ i, τ (S.hT (wv i) (wv i)) = (d i : ℂ) := by
    intro i
    rcases i with a | b
    · simp only [wv, d, Sum.elim_inl, map_sub, LinearMap.sub_apply, h.ee, h.yy, h.ey, h.ye, if_true]
      simp only [map_zero, map_one]
      push_cast; ring
    · cases b
      · simp only [wv, d, Sum.elim_inr, Bool.false_eq_true, if_false, h.zz, map_neg, map_natCast]
        push_cast; ring
      · simp only [wv, d, Sum.elim_inr, if_true]
        exact real_of τ hτ w
  have hneg : ∀ i, d i < 0 := by
    intro i
    rcases i with a | b
    · simp [d]
    · cases b
      · simp only [d, Sum.elim_inr, Bool.false_eq_true, if_false]; linarith
      · simpa [d] using hlt
  have hc := PI.CntNotPosW.card_le_of_negFamily S τ hτ hsig wv d hoff hdiag hneg
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_bool] at hc
  omega

theorem isoZeroG (h : Dual e y z N) (hN : 0 < N) (τ : E →+* ℂ) (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a))
    (hsemi : ∀ w, IsW e y z w → 0 ≤ (τ (S.hT w w)).re) (w : S.V) (hw : IsW e y z w) (h0 : S.hT w w = 0) :
    w = 0 := by
  obtain ⟨hE, hF, hz⟩ := hw
  have orthW : ∀ v : S.V, IsW e y z v → S.hT w v = 0 := by
    rintro v ⟨hvE, hvF, hvz⟩
    by_contra hx
    set x := S.hT w v with hxdef
    have hτx : τ x ≠ 0 := (map_ne_zero τ).2 hx
    have hNq : 0 < Complex.normSq (τ x) := Complex.normSq_pos.2 hτx
    set v' : S.V := star x • v with hv'
    have hxx : τ (x * star x) = ((Complex.normSq (τ x) : ℝ) : ℂ) := by
      rw [map_mul, hτ, Complex.mul_conj]
    have key : ∀ n : ℕ, 2 * n * Complex.normSq (τ x) ≤ (τ (S.hT v' v')).re := by
      intro n
      set u : S.V := (n : E) • w - v' with hu
      have huW : IsW e y z u := by
        refine ⟨fun a => ?_, fun a => ?_, ?_⟩
        · simp [hu, hv', map_sub, map_smul, hE a, hvE a]
        · simp [hu, hv', map_sub, map_smul, hF a, hvF a]
        · simp [hu, hv', map_sub, map_smul, hz, hvz]
      have hs := hsemi u huW
      have hyw : S.hT v w = star x := by rw [hsw]
      have e1 : S.hT u u = -(2 * (n : E)) * (x * star x) + S.hT v' v' := by
        simp only [hu, map_sub, LinearMap.sub_apply, map_smulₛₗ, LinearMap.smul_apply,
          smul_eq_mul, starRingEnd_apply, star_natCast, h0, hv', star_star, hyw, ← hxdef, RingHom.id_apply]
        ring
      have e2 : (τ (S.hT u u)).re = -(2 * n * Complex.normSq (τ x)) + (τ (S.hT v' v')).re := by
        rw [e1, map_add, map_mul, hxx, map_neg, map_mul, map_ofNat, map_natCast, Complex.add_re]
        congr 1
        have : -(2 * (n : ℂ)) * ((Complex.normSq (τ x) : ℝ) : ℂ) =
            ((-(2 * n * Complex.normSq (τ x)) : ℝ) : ℂ) := by push_cast; ring
        rw [this, Complex.ofReal_re]
      linarith
    obtain ⟨n, hn⟩ := exists_nat_gt ((τ (S.hT v' v')).re / (2 * Complex.normSq (τ x)))
    have h2 := key n
    rw [div_lt_iff₀ (by positivity)] at hn
    nlinarith
  have hzz : S.hT z z ≠ 0 := by
    rw [h.zz, neg_ne_zero]; exact_mod_cast hN.ne'
  apply S.nondeg.1 w
  intro x
  set xW : S.V := x - ∑ a, (S.hT (y a) x • e a + S.hT (e a) x • y a) - (S.hT z x / S.hT z z) • z with hxW
  have hzE : ∀ a, S.hT z (e a) = 0 := fun a => hsw0 S (h.ez a)
  have hzF : ∀ a, S.hT z (y a) = 0 := fun a => hsw0 S (h.yz a)
  have hWE : ∀ b, S.hT (e b) xW = 0 := by
    intro b
    simp [hxW, map_sub, map_sum, map_add, map_smul, h.ee, h.ey, h.ez]
  have hWF : ∀ b, S.hT (y b) xW = 0 := by
    intro b
    simp [hxW, map_sub, map_sum, map_add, map_smul, h.yy, h.ye, h.yz]
  have hWz : S.hT z xW = 0 := by
    simp [hxW, map_sub, map_sum, map_add, map_smul, hzE, hzF, hzz]
  have h1 := orthW xW ⟨hWE, hWF, hWz⟩
  have hwE : ∀ a, S.hT w (e a) = 0 := fun a => hsw0 S (hE a)
  have hwF : ∀ a, S.hT w (y a) = 0 := fun a => hsw0 S (hF a)
  have hwz : S.hT w z = 0 := hsw0 S hz
  simpa [hxW, map_sub, map_sum, map_add, map_smul, hwE, hwF, hwz] using h1

end Gen

end Formalism.L2.SG.Pf.Cnt.R1
