import Formalism.PeriodIntegrals.FockDegreeTwoParts

noncomputable section

open FockH1Action

namespace PI.FockWtDegWork

def lw {p q r s : ℕ} (l : Ln p q r s) (α : Ln p q r s →₀ ℕ) : ℚ :=
  if linePos l then (α l : ℚ) + 1 / 2 else -(α l : ℚ) - 1 / 2

theorem X_mul_monomial' {σ : Type*} (l : σ) (β : σ →₀ ℕ) (c : ℂ) :
    MvPolynomial.X l * MvPolynomial.monomial β c =
      MvPolynomial.monomial (Finsupp.single l 1 + β) c := by
  first
    | (rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul])
    | simp [MvPolynomial.X, MvPolynomial.monomial_mul]

theorem omE_diag_monomial {p q r s : ℕ} (l : Ln p q r s) (α : Ln p q r s →₀ ℕ) :
    omE l l (MvPolynomial.monomial α (1 : ℂ)) =
      ((lw l α : ℚ) : ℂ) • MvPolynomial.monomial α (1 : ℂ) := by
  have hE : FockH1Action.omE l l (MvPolynomial.monomial α (1 : ℂ)) =
      FockH1Action.raiB l (FockH1Action.lowB l (MvPolynomial.monomial α 1)) + (1 / 2 : ℂ) • MvPolynomial.monomial α 1 := by
    unfold FockH1Action.omE
    rw [if_pos rfl] <;> rfl
  have hm : ∀ c : ℂ, MvPolynomial.monomial α c = c • MvPolynomial.monomial α (1 : ℂ) := fun c => by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  have hpd : ∀ (m : FockH1Action.Ln p q r s →₀ ℕ) (c : ℂ), MvPolynomial.pderiv l (MvPolynomial.monomial m c) =
      MvPolynomial.monomial (m - Finsupp.single l 1) (c * (m l : ℂ)) := fun m c =>
    MvPolynomial.pderiv_monomial
  rw [hE]
  cases hl : FockH1Action.linePos l
  · have hc : ¬ (FockH1Action.linePos l = true) := by simp [hl]
    have h1 : FockH1Action.lowB l (MvPolynomial.monomial α (1 : ℂ)) = MvPolynomial.X l * MvPolynomial.monomial α 1 := by
      rw [FockH1Action.lowB, if_neg hc] <;> rfl
    have h2 : ∀ x, FockH1Action.raiB l x = -MvPolynomial.pderiv l x := fun x => by
      rw [FockH1Action.raiB, if_neg hc] <;> rfl
    have hw : ((lw l α : ℚ) : ℂ) = -(α l : ℂ) - 1 / 2 := by
      rw [lw, if_neg hc]; push_cast; ring
    have hs : Finsupp.single l 1 + α - Finsupp.single l 1 = α := by
      first
        | exact add_tsub_cancel_left _ _
        | (ext k; simp)
    have hv : (((Finsupp.single l 1 + α : FockH1Action.Ln p q r s →₀ ℕ) l : ℕ) : ℂ) = (α l : ℂ) + 1 := by
      rw [Finsupp.add_apply, Finsupp.single_eq_same]; push_cast; ring
    rw [h1, h2, X_mul_monomial', hpd, hs, hv, one_mul, hm ((α l : ℂ) + 1), ← neg_smul,
      ← add_smul, hw]
    congr 1
    ring
  · have h1 : FockH1Action.lowB l (MvPolynomial.monomial α (1 : ℂ)) =
        MvPolynomial.pderiv l (MvPolynomial.monomial α 1) := by
      rw [FockH1Action.lowB, if_pos hl] <;> rfl
    have h2 : ∀ x, FockH1Action.raiB l x = MvPolynomial.X l * x := fun x => by
      rw [FockH1Action.raiB, if_pos hl] <;> rfl
    have hw : ((lw l α : ℚ) : ℂ) = (α l : ℂ) + 1 / 2 := by
      rw [lw, if_pos hl]; push_cast; ring
    have key : MvPolynomial.X l * MvPolynomial.monomial (α - Finsupp.single l 1) (1 * (α l : ℂ)) =
        (α l : ℂ) • MvPolynomial.monomial α 1 := by
      rw [one_mul]
      by_cases h0 : α l = 0
      · simp [h0]
      · have hs : Finsupp.single l 1 + (α - Finsupp.single l 1) = α := by
          first
            | exact add_tsub_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 h0))
            | (ext k
               simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
               split_ifs with hk <;> (try subst hk) <;> omega)
        rw [X_mul_monomial', hs, hm (α l : ℂ)]
    rw [h2, h1, hpd, key, hw, add_smul]

theorem omAct_apply' (p q r s : ℕ) (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) :
    omAct p q r s M = ∑ l, ∑ l', M l l' • omE l l' := by
  unfold FockH1Action.omAct
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [LinearMap.sum_apply] <;> rfl

theorem sum_diag_of {p q r s : ℕ} (M : Matrix (Ln p q r s) (Ln p q r s) ℂ)
    (g : Ln p q r s → Prop) [DecidablePred g]
    (hM : ∀ l l', M l l' = if l = l' ∧ g l then 1 else 0) :
    ∑ l, ∑ l', M l l' • omE l l' = ∑ l, if g l then omE l l else 0 := by
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single l]
  · rw [hM]
    by_cases h : g l <;> simp [h]
  · intro l' _ hne
    rw [hM, if_neg (show ¬ (l = l' ∧ g l) from fun h => hne h.1.symm), zero_smul]
  · intro h
    exact absurd (Finset.mem_univ l) h

theorem fockAct1_diag (p q r s : ℕ) (a : Ix p q) :
    fockAct1 p q r s (Eab a a) = ∑ c : Ix r s, omE ((a, c) : Ln p q r s) (a, c) := by
  have hM : ∀ l l' : FockH1Action.Ln p q r s,
      ((Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ)).flip (1 : FockH1Action.Mat r s)
        (FockH1Action.Eab a a)) l l' = if l = l' ∧ l.1 = a then 1 else 0 := by
    rintro ⟨x, y⟩ ⟨x', y'⟩
    show FockH1Action.Eab a a x x' * (1 : FockH1Action.Mat r s) y y' = _
    first
      | simp only [FockH1Action.Eab, Matrix.single_apply, Matrix.one_apply, Prod.mk.injEq]
      | simp only [FockH1Action.Eab, Matrix.single, Matrix.of_apply, Matrix.one_apply, Prod.mk.injEq]
    split_ifs <;> first | (simp_all; done) | aesop
  rw [show FockH1Action.fockAct1 p q r s (FockH1Action.Eab a a) = FockH1Action.omAct p q r s
      ((Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ)).flip (1 : FockH1Action.Mat r s)
        (FockH1Action.Eab a a)) from rfl, omAct_apply',
    sum_diag_of _ (fun l => l.1 = a) hM, Fintype.sum_prod_type,
    Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem fockAct2_diag (p q r s : ℕ) (c : Ix r s) :
    fockAct2 p q r s (Eab c c) = ∑ a : Ix p q, omE ((a, c) : Ln p q r s) (a, c) := by
  have hM : ∀ l l' : FockH1Action.Ln p q r s,
      ((Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ)) (1 : FockH1Action.Mat p q)
        (FockH1Action.Eab c c)) l l' = if l = l' ∧ l.2 = c then 1 else 0 := by
    rintro ⟨x, y⟩ ⟨x', y'⟩
    show (1 : FockH1Action.Mat p q) x x' * FockH1Action.Eab c c y y' = _
    first
      | simp only [FockH1Action.Eab, Matrix.single_apply, Matrix.one_apply, Prod.mk.injEq]
      | simp only [FockH1Action.Eab, Matrix.single, Matrix.of_apply, Matrix.one_apply, Prod.mk.injEq]
    split_ifs <;> first | (simp_all; done) | aesop
  rw [show FockH1Action.fockAct2 p q r s (FockH1Action.Eab c c) = FockH1Action.omAct p q r s
      ((Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ)) (1 : FockH1Action.Mat p q)
        (FockH1Action.Eab c c)) from rfl, omAct_apply',
    sum_diag_of _ (fun l => l.2 = c) hM, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single c]
  · simp
  · intro y _ hy
    simp [hy]
  · intro h
    exact absurd (Finset.mem_univ c) h

def W1 {p q r s : ℕ} (a : Ix p q) (α : Ln p q r s →₀ ℕ) : ℚ :=
  ∑ c : Ix r s, lw ((a, c) : Ln p q r s) α

def W2 {p q r s : ℕ} (c : Ix r s) (α : Ln p q r s →₀ ℕ) : ℚ :=
  ∑ a : Ix p q, lw ((a, c) : Ln p q r s) α

theorem fockAct1_monomial (p q r s : ℕ) (a : Ix p q) (β : Ln p q r s →₀ ℕ) :
    fockAct1 p q r s (Eab a a) (MvPolynomial.monomial β (1 : ℂ)) =
      ((W1 a β : ℚ) : ℂ) • MvPolynomial.monomial β (1 : ℂ) := by
  rw [fockAct1_diag, LinearMap.sum_apply]
  simp only [omE_diag_monomial]
  rw [← Finset.sum_smul, W1, Rat.cast_sum]

theorem fockAct2_monomial (p q r s : ℕ) (c : Ix r s) (β : Ln p q r s →₀ ℕ) :
    fockAct2 p q r s (Eab c c) (MvPolynomial.monomial β (1 : ℂ)) =
      ((W2 c β : ℚ) : ℂ) • MvPolynomial.monomial β (1 : ℂ) := by
  rw [fockAct2_diag, LinearMap.sum_apply]
  simp only [omE_diag_monomial]
  rw [← Finset.sum_smul, W2, Rat.cast_sum]

theorem coeff_of_diag {σ : Type*} (T : Module.End ℂ (MvPolynomial σ ℂ)) (f : (σ →₀ ℕ) → ℂ)
    (hT : ∀ β, T (MvPolynomial.monomial β 1) = f β • MvPolynomial.monomial β 1)
    (P : MvPolynomial σ ℂ) (α : σ →₀ ℕ) :
    MvPolynomial.coeff α (T P) = f α * MvPolynomial.coeff α P := by
  classical
  induction P using MvPolynomial.induction_on'
  next u a =>
    have hm : MvPolynomial.monomial u a = a • MvPolynomial.monomial u (1 : ℂ) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [hm, map_smul, hT]
    simp only [MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial, smul_eq_mul]
    split_ifs with h
    · subst h
      ring
    · simp
  next P Q hP hQ =>
    rw [map_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add, hP, hQ, mul_add]

theorem exists_monomial_weight {σ ι : Type*} [Fintype σ]
    (T : ι → Module.End ℂ (MvPolynomial σ ℂ)) (f : ι → (σ →₀ ℕ) → ℚ)
    (hT : ∀ a β, T a (MvPolynomial.monomial β 1) =
      ((f a β : ℚ) : ℂ) • MvPolynomial.monomial β 1)
    (μ : ι → ℚ) (d : ℕ) (P : MvPolynomial σ ℂ) (hP : P ∈ homog σ d) (h0 : P ≠ 0)
    (hw : ∀ a, (T a - ((μ a : ℚ) : ℂ) • (LinearMap.id : Module.End ℂ (MvPolynomial σ ℂ))) P = 0) :
    ∃ α : σ →₀ ℕ, ∑ i, α i = d ∧ ∀ a, μ a = f a α := by
  obtain ⟨α, hα⟩ : ∃ α, MvPolynomial.coeff α P ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact h0 (MvPolynomial.ext _ _ fun β => by simp [hne β])
  refine ⟨α, ?_, fun a => ?_⟩
  · have hh : MvPolynomial.IsHomogeneous P d := (MvPolynomial.mem_homogeneousSubmodule d P).1 hP
    have h2 := hh hα
    have key : ∑ i ∈ α.support, α i = ∑ i, α i :=
      Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by simpa using hi
    first
      | (rw [← key]; exact h2)
      | (rw [← key]; simpa [Finsupp.weight_apply, Finsupp.sum] using h2)
      | (rw [← key]; simpa [Finsupp.degree_eq_weight_one.symm, Finsupp.degree] using h2)
      | (rw [← key]; simpa [Finsupp.degree, Finsupp.weight, Finsupp.sum] using h2)
  · have h1 := coeff_of_diag (T a) (fun β => ((f a β : ℚ) : ℂ)) (hT a) P α
    have h2 : T a P = ((μ a : ℚ) : ℂ) • P := by
      have h3 := hw a
      rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h3
      exact h3
    rw [h2, MvPolynomial.coeff_smul, smul_eq_mul] at h1
    have h3 : ((μ a : ℚ) : ℂ) = ((f a α : ℚ) : ℂ) := mul_right_cancel₀ hα h1
    exact_mod_cast h3

theorem wt_of_isHW {p q : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) (v : V) (h : IsHW act μ v) :
    v ≠ 0 ∧ ∀ a, (act (Eab a a) - ((μ a : ℚ) : ℂ) • (LinearMap.id : Module.End ℂ V)) v = 0 := by
  refine ⟨h.1, fun a => ?_⟩
  have h2 : v ∈ FockH1Action.wtSub act μ := (Submodule.mem_inf.1 h.2).1
  simp only [FockH1Action.wtSub, Submodule.mem_iInf, LinearMap.mem_ker] at h2
  exact h2 a

theorem abs_le_of (x A B : ℚ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hx : x = A - B) : |x| ≤ A + B := by
  rw [hx, abs_le]
  constructor <;> linarith

private theorem sum_add_half_add_sum_neg_sub_half (A B : ℕ) (f : Fin A → ℚ) (g : Fin B → ℚ) :
    ∑ c, (f c + 1 / 2) + ∑ c, (-g c - 1 / 2) = (∑ c, f c) - (∑ c, g c) + ((A : ℚ) - B) / 2 := by
  first
    | (simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring)
    | (simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]; ring)

private theorem sum_neg_sub_half_add_sum_add_half (A B : ℕ) (f : Fin A → ℚ) (g : Fin B → ℚ) :
    ∑ c, (-f c - 1 / 2) + ∑ c, (g c + 1 / 2) = (∑ c, g c) - (∑ c, f c) - ((A : ℚ) - B) / 2 := by
  first
    | (simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring)
    | (simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]; ring)

theorem shift1_le {p q r s : ℕ} (α : Ln p q r s →₀ ℕ) (a : Ix p q) :
    |shiftNu (cPair r s) (fun b => W1 b α) a| ≤ ∑ c : Ix r s, (α (a, c) : ℚ) := by
  rw [Fintype.sum_sum_type]
  cases a with
  | inl i =>
    have hL : W1 (Sum.inl i) α = ∑ c : Fin r, ((α (Sum.inl i, Sum.inl c) : ℚ) + 1 / 2) +
        ∑ c : Fin s, (-(α (Sum.inl i, Sum.inr c) : ℚ) - 1 / 2) := by
      rw [W1, Fintype.sum_sum_type] <;> first | rfl | simp [lw, FockH1Action.linePos]
    have hx : FockH1Action.shiftNu (FockH1Action.cPair r s) (fun b => W1 b α) (Sum.inl i) =
        (∑ c : Fin r, (α (Sum.inl i, Sum.inl c) : ℚ)) - ∑ c : Fin s, (α (Sum.inl i, Sum.inr c) : ℚ) := by
      show W1 (Sum.inl i) α - FockH1Action.cPair r s = _
      rw [hL, sum_add_half_add_sum_neg_sub_half, FockH1Action.cPair]
      ring
    exact abs_le_of _ _ _ (by exact Finset.sum_nonneg fun c _ => Nat.cast_nonneg _)
      (by exact Finset.sum_nonneg fun c _ => Nat.cast_nonneg _) hx
  | inr j =>
    have hL : W1 (Sum.inr j) α = ∑ c : Fin r, (-(α (Sum.inr j, Sum.inl c) : ℚ) - 1 / 2) +
        ∑ c : Fin s, ((α (Sum.inr j, Sum.inr c) : ℚ) + 1 / 2) := by
      rw [W1, Fintype.sum_sum_type] <;> first | rfl | simp [lw, FockH1Action.linePos]
    have hx : FockH1Action.shiftNu (FockH1Action.cPair r s) (fun b => W1 b α) (Sum.inr j) =
        (∑ c : Fin s, (α (Sum.inr j, Sum.inr c) : ℚ)) - ∑ c : Fin r, (α (Sum.inr j, Sum.inl c) : ℚ) := by
      show W1 (Sum.inr j) α + FockH1Action.cPair r s = _
      rw [hL, sum_neg_sub_half_add_sum_add_half, FockH1Action.cPair]
      ring
    exact (abs_le_of _ _ _ (by exact Finset.sum_nonneg fun c _ => Nat.cast_nonneg _)
      (by exact Finset.sum_nonneg fun c _ => Nat.cast_nonneg _) hx).trans_eq (add_comm _ _)

theorem shift2_le {p q r s : ℕ} (α : Ln p q r s →₀ ℕ) (c : Ix r s) :
    |shiftNu (cPair p q) (fun b => W2 b α) c| ≤ ∑ a : Ix p q, (α (a, c) : ℚ) := by
  rw [Fintype.sum_sum_type]
  cases c with
  | inl k =>
    have hL : W2 (Sum.inl k) α = ∑ a : Fin p, ((α (Sum.inl a, Sum.inl k) : ℚ) + 1 / 2) +
        ∑ a : Fin q, (-(α (Sum.inr a, Sum.inl k) : ℚ) - 1 / 2) := by
      rw [W2, Fintype.sum_sum_type] <;> first | rfl | simp [lw, FockH1Action.linePos]
    have hx : FockH1Action.shiftNu (FockH1Action.cPair p q) (fun b => W2 b α) (Sum.inl k) =
        (∑ a : Fin p, (α (Sum.inl a, Sum.inl k) : ℚ)) - ∑ a : Fin q, (α (Sum.inr a, Sum.inl k) : ℚ) := by
      show W2 (Sum.inl k) α - FockH1Action.cPair p q = _
      rw [hL, sum_add_half_add_sum_neg_sub_half, FockH1Action.cPair]
      ring
    exact abs_le_of _ _ _ (by exact Finset.sum_nonneg fun a _ => Nat.cast_nonneg _)
      (by exact Finset.sum_nonneg fun a _ => Nat.cast_nonneg _) hx
  | inr k =>
    have hL : W2 (Sum.inr k) α = ∑ a : Fin p, (-(α (Sum.inl a, Sum.inr k) : ℚ) - 1 / 2) +
        ∑ a : Fin q, ((α (Sum.inr a, Sum.inr k) : ℚ) + 1 / 2) := by
      rw [W2, Fintype.sum_sum_type] <;> first | rfl | simp [lw, FockH1Action.linePos]
    have hx : FockH1Action.shiftNu (FockH1Action.cPair p q) (fun b => W2 b α) (Sum.inr k) =
        (∑ a : Fin q, (α (Sum.inr a, Sum.inr k) : ℚ)) - ∑ a : Fin p, (α (Sum.inl a, Sum.inr k) : ℚ) := by
      show W2 (Sum.inr k) α + FockH1Action.cPair p q = _
      rw [hL, sum_neg_sub_half_add_sum_add_half, FockH1Action.cPair]
      ring
    exact (abs_le_of _ _ _ (by exact Finset.sum_nonneg fun a _ => Nat.cast_nonneg _)
      (by exact Finset.sum_nonneg fun a _ => Nat.cast_nonneg _) hx).trans_eq (add_comm _ _)

theorem half1 (p q r s : ℕ) : ∀ d (μ : Ix p q → ℚ) P, P ∈ homog (Ix p q × Ix r s) d →
    IsHW (fockAct1 p q r s) μ P → degW (cPair r s) μ ≤ d := by
  intro d μ P hP hH
  obtain ⟨h0, hw⟩ := wt_of_isHW (FockH1Action.fockAct1 p q r s) μ P hH
  obtain ⟨α, hd, hμ⟩ := exists_monomial_weight (fun a => FockH1Action.fockAct1 p q r s (FockH1Action.Eab a a))
    (fun a β => W1 a β) (fun a β => fockAct1_monomial p q r s a β) μ d P hP h0 hw
  have hμ' : μ = fun b => W1 b α := funext hμ
  subst hμ'
  calc FockH1Action.degW (FockH1Action.cPair r s) (fun b => W1 b α)
      = ∑ a, |FockH1Action.shiftNu (FockH1Action.cPair r s) (fun b => W1 b α) a| := rfl
    _ ≤ ∑ a : FockH1Action.Ix p q, ∑ c : FockH1Action.Ix r s, (α (a, c) : ℚ) :=
        Finset.sum_le_sum fun a _ => shift1_le α a
    _ = ((∑ i, α i : ℕ) : ℚ) := by rw [Nat.cast_sum, Fintype.sum_prod_type]
    _ = d := by rw [hd]

theorem half2 (p q r s : ℕ) : ∀ d (μ : Ix r s → ℚ) P, P ∈ homog (Ix p q × Ix r s) d →
    IsHW (fockAct2 p q r s) μ P → degW (cPair p q) μ ≤ d := by
  intro d μ P hP hH
  obtain ⟨h0, hw⟩ := wt_of_isHW (FockH1Action.fockAct2 p q r s) μ P hH
  obtain ⟨α, hd, hμ⟩ := exists_monomial_weight (fun c => FockH1Action.fockAct2 p q r s (FockH1Action.Eab c c))
    (fun c β => W2 c β) (fun c β => fockAct2_monomial p q r s c β) μ d P hP h0 hw
  have hμ' : μ = fun b => W2 b α := funext hμ
  subst hμ'
  calc FockH1Action.degW (FockH1Action.cPair p q) (fun b => W2 b α)
      = ∑ c, |FockH1Action.shiftNu (FockH1Action.cPair p q) (fun b => W2 b α) c| := rfl
    _ ≤ ∑ c : FockH1Action.Ix r s, ∑ a : FockH1Action.Ix p q, (α (a, c) : ℚ) :=
        Finset.sum_le_sum fun c _ => shift2_le α c
    _ = ((∑ i, α i : ℕ) : ℚ) := by rw [Nat.cast_sum, Fintype.sum_prod_type, Finset.sum_comm]
    _ = d := by rw [hd]

theorem wtDeg : PI.FockDegreeTwoParts.WtDeg :=
  fun p q r s => ⟨half1 p q r s, half2 p q r s⟩

end PI.FockWtDegWork
