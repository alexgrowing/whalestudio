import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.CoeffSubstInvMemOfTwoLeOrder

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh

noncomputable section

namespace GlobalTheory.IntegralEndLimit

theorem exists_real_le (x : WithTop ℝ) : ∃ t : ℝ, (t : WithTop ℝ) ≤ x := by
  cases x with
  | top => exact ⟨0, le_top⟩
  | coe t => exact ⟨t, le_rfl⟩

theorem le_val_mul {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {x y : C} {s t u : ℝ}
    (hx : (s : WithTop ℝ) ≤ v x) (hy : (t : WithTop ℝ) ≤ v y) (h : u ≤ s + t) :
    (u : WithTop ℝ) ≤ v (x * y) := by
  rw [v.map_mul]
  refine le_trans ?_ (add_le_add hx hy)
  rw [← WithTop.coe_add]
  exact WithTop.coe_le_coe.2 h

theorem eval_close {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {ι : Type}
    (x : ι → C) (Q : MvPolynomial ι C) (s : ℝ) :
    ∃ r : ℝ, ∀ x' : ι → C, (∀ i, (r : WithTop ℝ) ≤ v (x i - x' i)) →
      (s : WithTop ℝ) ≤ v (MvPolynomial.eval x Q - MvPolynomial.eval x' Q) := by
  induction Q using MvPolynomial.induction_on generalizing s with
  | C a => exact ⟨0, fun x' _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨r₁, h₁⟩ := hp s
    obtain ⟨r₂, h₂⟩ := hq s
    refine ⟨max r₁ r₂, fun x' hx' => ?_⟩
    have e : MvPolynomial.eval x (p + q) - MvPolynomial.eval x' (p + q) =
        (MvPolynomial.eval x p - MvPolynomial.eval x' p) +
          (MvPolynomial.eval x q - MvPolynomial.eval x' q) := by
      simp only [map_add]; ring
    rw [e]
    refine le_trans (le_min (h₁ x' fun i => le_trans ?_ (hx' i))
      (h₂ x' fun i => le_trans ?_ (hx' i))) (v.map_add _ _)
    · exact WithTop.coe_le_coe.2 (le_max_left _ _)
    · exact WithTop.coe_le_coe.2 (le_max_right _ _)
  | mul_X p i hp =>
    obtain ⟨a, ha⟩ := exists_real_le (v (MvPolynomial.eval x p))
    obtain ⟨b, hb⟩ := exists_real_le (v (x i))
    obtain ⟨r, hr⟩ := hp (s - b)
    refine ⟨max r (max (s - a) b), fun x' hx' => ?_⟩
    have h1 := hr x' fun j => le_trans (WithTop.coe_le_coe.2 (le_max_left _ _)) (hx' j)
    have h2 := hx' i
    have e : MvPolynomial.eval x (p * MvPolynomial.X i) - MvPolynomial.eval x' (p * MvPolynomial.X i)
        = MvPolynomial.eval x p * (x i - x' i) +
          ((MvPolynomial.eval x p - MvPolynomial.eval x' p) * x i +
            -((MvPolynomial.eval x p - MvPolynomial.eval x' p) * (x i - x' i))) := by
      simp only [map_mul, MvPolynomial.eval_X]; ring
    have m1 : s - a ≤ max r (max (s - a) b) := le_trans (le_max_left _ _) (le_max_right _ _)
    have m2 : b ≤ max r (max (s - a) b) := le_trans (le_max_right _ _) (le_max_right _ _)
    rw [e]
    refine le_trans (le_min (le_val_mul v ha h2 (by linarith))
      (le_trans (le_min (le_val_mul v h1 hb (by linarith)) ?_) (v.map_add _ _))) (v.map_add _ _)
    rw [v.map_neg]
    exact le_val_mul v h1 h2 (by linarith)

theorem exists_poly_coeff {C : Type} [Field C] {d : ℕ} (l : Fin d → MvPowerSeries (Fin d) C)
    (hl : ∀ a, constantCoeff (l a) = 0) (f : MvPowerSeries (Fin d) C) (α : Fin d →₀ ℕ) :
    ∃ Q : MvPolynomial (Fin d × Fin d) C, ∀ A : Matrix (Fin d) (Fin d) C,
      coeff α (subst (fun a => ∑ b, A a b • l b) f) =
        MvPolynomial.eval (fun p => A p.1 p.2) Q := by
  let ι : C →+* MvPolynomial (Fin d × Fin d) C := MvPolynomial.C
  let L : Fin d → MvPowerSeries (Fin d) (MvPolynomial (Fin d × Fin d) C) :=
    fun a => ∑ b, MvPowerSeries.C (MvPolynomial.X (a, b)) * map ι (l b)
  have hL : HasSubst L := hasSubst_of_constantCoeff_zero fun a => by
    simp [L, hl]
  refine ⟨coeff α (subst L (map ι f)), fun A => ?_⟩
  have hm : ∀ g : MvPowerSeries (Fin d) C,
      map (MvPolynomial.eval fun p : Fin d × Fin d => A p.1 p.2) (map ι g) = g := by
    intro g; ext β; simp [ι]
  rw [← coeff_map, map_subst hL, hm]
  congr 2
  funext a
  simp only [L, map_sum, map_mul, hm, map_C, MvPolynomial.eval_X, smul_eq_C_mul]

theorem integral_of_limit :
  (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (d : ℕ) (G : LogFGL v d) (A : Matrix (Fin d) (Fin d) C),
    (∀ r : ℝ, ∃ A' : Matrix (Fin d) (Fin d) C, (∀ a b, (r : WithTop ℝ) ≤ v (A a b - A' a b)) ∧ ∃ φ : Fin d → MvPowerSeries (Fin d) C, (∀ a, MvIsInt v (φ a)) ∧ (∀ a, constantCoeff (φ a) = 0) ∧ ∀ a, subst φ (G.lg a) = ∑ b, A' a b • G.lg b) →
    ∃ φ : Fin d → MvPowerSeries (Fin d) C, (∀ a, MvIsInt v (φ a)) ∧ (∀ a, constantCoeff (φ a) = 0) ∧ ∀ a, subst φ (G.lg a) = ∑ b, A a b • G.lg b) := by
  intro C _ _ v d G A hA
  obtain ⟨ex, ⟨hex0, hr, hl⟩, -⟩ := GlobalTheory.FormalInv.formal_inverse_function_theorem.1 C d G.lg
    G.lg_const (by
      have : (Matrix.of fun i j => coeff (Finsupp.single j 1) (G.lg i) :
          Matrix (Fin d) (Fin d) C) = 1 := by
        ext i j; simp [G.lg_lin, Matrix.one_apply]
      rw [this]; exact isUnit_one)
  have hex : HasSubst ex := hasSubst_of_constantCoeff_zero hex0
  have hlg : HasSubst G.lg := hasSubst_of_constantCoeff_zero G.lg_const
  have h0 : ∀ a, constantCoeff (∑ b, A a b • G.lg b) = 0 := fun a => by
    simp [G.lg_const]
  have hs : HasSubst fun a => ∑ b, A a b • G.lg b := hasSubst_of_constantCoeff_zero h0
  refine ⟨fun a => subst (fun a => ∑ b, A a b • G.lg b) (ex a), fun a α => ?_,
    fun a => constantCoeff_subst_eq_zero hs h0 (hex0 a), fun a => ?_⟩
  · obtain ⟨Q, hQ⟩ := exists_poly_coeff G.lg G.lg_const (ex a) α
    obtain ⟨r, hr'⟩ := eval_close v (fun p : Fin d × Fin d => A p.1 p.2) Q 0
    obtain ⟨A', hA', φ, hφi, hφ0, hφ⟩ := hA r
    have hφs : HasSubst φ := hasSubst_of_constantCoeff_zero hφ0
    have e : subst (fun a => ∑ b, A' a b • G.lg b) (ex a) = φ a := by
      rw [← funext hφ, ← subst_comp_subst_apply hlg hφs, hl, subst_X hφs]
    have h1 := hr' (fun p => A' p.1 p.2) fun p => hA' p.1 p.2
    have h2 : (0 : WithTop ℝ) ≤ v (MvPolynomial.eval (fun p : Fin d × Fin d => A' p.1 p.2) Q) := by
      rw [← hQ, e]; exact hφi a α
    show 0 ≤ v _
    rw [hQ, ← sub_add_cancel (MvPolynomial.eval (fun p : Fin d × Fin d => A p.1 p.2) Q)
      (MvPolynomial.eval (fun p : Fin d × Fin d => A' p.1 p.2) Q)]
    exact le_trans (le_min h1 h2) (v.map_add _ _)
  · rw [← subst_comp_subst_apply hex hs, hr, subst_X hs]

end GlobalTheory.IntegralEndLimit
