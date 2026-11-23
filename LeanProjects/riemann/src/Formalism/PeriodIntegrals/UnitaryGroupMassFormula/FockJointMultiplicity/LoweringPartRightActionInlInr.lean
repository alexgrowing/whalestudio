import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.JointMultOfSteps

noncomputable section

open Matrix FockH1Action

namespace PI.WFJM

private theorem omAct_eq_sum_smul_omE (p q r s : ℕ)
    (M : Matrix (FockH1Action.Ln p q r s) (FockH1Action.Ln p q r s) ℂ) :
    FockH1Action.omAct p q r s M = ∑ l, ∑ l', M l l' • FockH1Action.omE l l' := by
  first
  | (simp only [FockH1Action.omAct, LinearMap.sum_apply, LinearMap.smulRight_apply,
      Matrix.entryLinearMap_apply]; done)
  | simp [FockH1Action.omAct]

private theorem fockAct1_eq_omAct_kronecker_one (p q r s : ℕ) (Z : FockH1Action.Mat p q) :
    FockH1Action.fockAct1 p q r s Z =
      FockH1Action.omAct p q r s (Matrix.kroneckerMap (· * ·) Z (1 : FockH1Action.Mat r s)) := rfl

theorem fockAct1_eq (p q r s : ℕ) (Z : Mat p q) :
    fockAct1 p q r s Z = ∑ a : Ix p q, ∑ b : Ix p q, ∑ c : Ix r s,
      Z a b • omE (p := p) (q := q) (r := r) (s := s) (a, c) (b, c) := by
  rw [fockAct1_eq_omAct_kronecker_one, omAct_eq_sum_smul_omE]
  simp only [Fintype.sum_prod_type, Matrix.kroneckerMap_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  rw [Fintype.sum_eq_single c]
  · simp
  · intro d hd
    simp [Matrix.one_apply, Ne.symm hd]

private theorem fockAct2_eq_omAct_one_kronecker (p q r s : ℕ) (Y : FockH1Action.Mat r s) :
    FockH1Action.fockAct2 p q r s Y =
      FockH1Action.omAct p q r s (Matrix.kroneckerMap (· * ·) (1 : FockH1Action.Mat p q) Y) := rfl

theorem fockAct2_eq (p q r s : ℕ) (Y : Mat r s) :
    fockAct2 p q r s Y = ∑ a : Ix p q, ∑ c : Ix r s, ∑ d : Ix r s,
      Y c d • omE (p := p) (q := q) (r := r) (s := s) (a, c) (a, d) := by
  rw [fockAct2_eq_omAct_one_kronecker, omAct_eq_sum_smul_omE]
  simp only [Fintype.sum_prod_type, Matrix.kroneckerMap_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  rw [Fintype.sum_eq_single a]
  · simp
  · intro b hb
    simp [Matrix.one_apply, Ne.symm hb]

end PI.WFJM

namespace PI.WFJM

open MvPolynomial

def sgnL {p q r s : ℕ} (l : Ln p q r s) : ℂ := if linePos l then 1 else -1

theorem X_mul_pderiv_monomial {σ : Type*} (i : σ) (α : σ →₀ ℕ) (c : ℂ) :
    X i * pderiv i (monomial α c) = ((α i : ℕ) : ℂ) • monomial α c := by
  rw [pderiv_monomial]
  by_cases h : α i = 0
  · simp [h]
  · rw [X, monomial_mul, one_mul,
      add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h)),
      smul_monomial, smul_eq_mul, mul_comm c]

theorem pderiv_X_mul_monomial {σ : Type*} (i : σ) (α : σ →₀ ℕ) (c : ℂ) :
    pderiv i (X i * monomial α c) = (((α i : ℕ) : ℂ) + 1) • monomial α c := by
  classical
  have hX : pderiv i (X i : MvPolynomial σ ℂ) = 1 := by
    first
    | exact pderiv_X_self i
    | simp [pderiv_X]
  first
  | rw [Derivation.leibniz, hX, smul_eq_mul, smul_eq_mul, X_mul_pderiv_monomial, mul_one,
      add_smul, one_smul]
  | (simp only [Derivation.leibniz, hX, smul_eq_mul, X_mul_pderiv_monomial, mul_one]; module)

private theorem pderiv_toLinearMap_apply {σ : Type*} (i : σ) (P : MvPolynomial σ ℂ) :
    (pderiv i).toLinearMap P = pderiv i P := rfl

private theorem moduleEnd_mul_apply {M : Type*} [AddCommGroup M] [Module ℂ M]
    (f g : Module.End ℂ M) (x : M) : (f * g) x = f (g x) := rfl

private theorem moduleEnd_one_apply {M : Type*} [AddCommGroup M] [Module ℂ M] (x : M) :
    (1 : Module.End ℂ M) x = x := rfl

private theorem sgnL_eq_one_of_linePos {p q r s : ℕ} {l : FockH1Action.Ln p q r s}
    (h : FockH1Action.linePos l = true) : sgnL l = 1 := by
  simp [sgnL, h]

private theorem sgnL_eq_neg_one_of_not_linePos {p q r s : ℕ} {l : FockH1Action.Ln p q r s}
    (h : FockH1Action.linePos l = false) : sgnL l = -1 := by
  simp [sgnL, h]

private theorem raiB_eq_mulLeft_X_of_linePos {p q r s : ℕ} {l : FockH1Action.Ln p q r s}
    (h : FockH1Action.linePos l = true) : FockH1Action.raiB l = LinearMap.mulLeft ℂ (X l) := by
  rw [FockH1Action.raiB, if_pos h]

private theorem raiB_eq_neg_pderiv_of_not_linePos {p q r s : ℕ} {l : FockH1Action.Ln p q r s}
    (h : FockH1Action.linePos l = false) : FockH1Action.raiB l = -(pderiv l).toLinearMap := by
  rw [FockH1Action.raiB, if_neg (show ¬ (FockH1Action.linePos l = true) by simp [h])]

private theorem lowB_eq_pderiv_of_linePos {p q r s : ℕ} {l : FockH1Action.Ln p q r s}
    (h : FockH1Action.linePos l = true) : FockH1Action.lowB l = (pderiv l).toLinearMap := by
  rw [FockH1Action.lowB, if_pos h]

private theorem lowB_eq_mulLeft_X_of_not_linePos {p q r s : ℕ} {l : FockH1Action.Ln p q r s}
    (h : FockH1Action.linePos l = false) : FockH1Action.lowB l = LinearMap.mulLeft ℂ (X l) := by
  rw [FockH1Action.lowB, if_neg (show ¬ (FockH1Action.linePos l = true) by simp [h])]

theorem omE_self_monomial {p q r s : ℕ} (l : Ln p q r s) (α : Ln p q r s →₀ ℕ) (c : ℂ) :
    omE l l (monomial α c) = (sgnL l * (((α l : ℕ) : ℂ) + 1 / 2)) • monomial α c := by
  have h1 := X_mul_pderiv_monomial l α c
  have h2 := pderiv_X_mul_monomial l α c
  rw [FockH1Action.omE, if_pos rfl, LinearMap.add_apply, moduleEnd_mul_apply, LinearMap.smul_apply,
    moduleEnd_one_apply]
  cases hl : FockH1Action.linePos l
  · rw [raiB_eq_neg_pderiv_of_not_linePos hl, lowB_eq_mulLeft_X_of_not_linePos hl, sgnL_eq_neg_one_of_not_linePos hl, LinearMap.neg_apply,
      LinearMap.mulLeft_apply, pderiv_toLinearMap_apply, h2]
    first
    | module
    | (rw [← neg_smul, ← add_smul]; congr 1; ring)
  · rw [raiB_eq_mulLeft_X_of_linePos hl, lowB_eq_pderiv_of_linePos hl, sgnL_eq_one_of_linePos hl, pderiv_toLinearMap_apply,
      LinearMap.mulLeft_apply, h1]
    first
    | module
    | (rw [← add_smul]; congr 1; ring)

theorem omE_ne {p q r s : ℕ} {l l' : Ln p q r s} (h : l ≠ l') : omE l l' = raiB l * lowB l' := by
  rw [FockH1Action.omE, if_neg h, add_zero]

open PI.FJM

theorem fockAct1_Eab (p q r s : ℕ) (a b : Ix p q) :
    fockAct1 p q r s (Eab a b) = ∑ c : Ix r s, omE (p := p) (q := q) (r := r) (s := s) (a, c) (b, c) := by
  rw [fockAct1_eq, Fintype.sum_eq_single a, Fintype.sum_eq_single b]
  · simp [FockH1Action.Eab, Matrix.single_apply]
  · intro x hx
    simp [FockH1Action.Eab, Matrix.single_apply, Ne.symm hx]
  · intro x hx
    simp [FockH1Action.Eab, Matrix.single_apply, Ne.symm hx]

theorem fockAct2_Eab (p q r s : ℕ) (c d : Ix r s) :
    fockAct2 p q r s (Eab c d) = ∑ a : Ix p q, omE (p := p) (q := q) (r := r) (s := s) (a, c) (a, d) := by
  rw [fockAct2_eq]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_eq_single c, Fintype.sum_eq_single d]
  · simp [FockH1Action.Eab, Matrix.single_apply]
  · intro x hx
    simp [FockH1Action.Eab, Matrix.single_apply, Ne.symm hx]
  · intro x hx
    simp [FockH1Action.Eab, Matrix.single_apply, Ne.symm hx]

theorem leftOffDiagonalActionFormula : FormRaise1 := by
  intro p q r s a b hab
  rw [fockAct1_Eab, PI.FJM.rai1]
  refine Finset.sum_congr rfl fun c _ => omE_ne ?_
  intro h
  exact hab (congrArg Prod.fst h)

theorem rightOffDiagonalActionFormula : FormRaise2 := by
  intro p q r s c d hcd
  rw [fockAct2_Eab, PI.FJM.rai2]
  refine Finset.sum_congr rfl fun a _ => omE_ne ?_
  intro h
  exact hcd (congrArg Prod.snd h)

private theorem sgnL_inl_inl {p q r s : ℕ} (i : Fin p) (k : Fin r) :
    sgnL (p := p) (q := q) (r := r) (s := s) (Sum.inl i, Sum.inl k) = 1 :=
  sgnL_eq_one_of_linePos (by rfl)

private theorem sgnL_inl_inr {p q r s : ℕ} (i : Fin p) (k : Fin s) :
    sgnL (p := p) (q := q) (r := r) (s := s) (Sum.inl i, Sum.inr k) = -1 :=
  sgnL_eq_neg_one_of_not_linePos (by rfl)

private theorem sgnL_inr_inl {p q r s : ℕ} (i : Fin q) (k : Fin r) :
    sgnL (p := p) (q := q) (r := r) (s := s) (Sum.inr i, Sum.inl k) = -1 :=
  sgnL_eq_neg_one_of_not_linePos (by rfl)

private theorem sgnL_inr_inr {p q r s : ℕ} (i : Fin q) (k : Fin s) :
    sgnL (p := p) (q := q) (r := r) (s := s) (Sum.inr i, Sum.inr k) = 1 :=
  sgnL_eq_one_of_linePos (by rfl)

private theorem sgnL_mul_natCast {p q r s : ℕ} (l : FockH1Action.Ln p q r s) (n : ℕ) :
    sgnL l * (n : ℂ) =
      (((if FockH1Action.linePos l then (n : ℤ) else -(n : ℤ)) : ℤ) : ℂ) := by
  cases hl : FockH1Action.linePos l
  · rw [sgnL_eq_neg_one_of_not_linePos hl]
    simp
  · rw [sgnL_eq_one_of_linePos hl]
    simp

private theorem sum_sgnL_right_index_eq_two_mul_sh1 {p q r s : ℕ} (a : FockH1Action.Ix p q) :
    ∑ c : FockH1Action.Ix r s, sgnL (a, c) = ((2 * PI.FJM.sh1 p q r s a : ℚ) : ℂ) := by
  rcases a with i | j <;>
    simp only [Fintype.sum_sum_type, sgnL_inl_inl, sgnL_inl_inr, sgnL_inr_inl,
      sgnL_inr_inr, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      PI.FJM.sh1, Sum.elim_inl, Sum.elim_inr, FockH1Action.cPair] <;>
    push_cast <;> ring

private theorem sum_sgnL_mul_add_half_eq_wt1_add_sh1 {p q r s : ℕ} (a : FockH1Action.Ix p q)
    (m : FockH1Action.Ln p q r s →₀ ℕ) :
    ∑ c : FockH1Action.Ix r s, sgnL (a, c) * (((m (a, c) : ℕ) : ℂ) + 1 / 2) =
      (((PI.FJM.wt1 m a : ℚ) + PI.FJM.sh1 p q r s a : ℚ) : ℂ) := by
  have h1 := sum_sgnL_right_index_eq_two_mul_sh1 (r := r) (s := s) a
  have h2 : ∑ c : FockH1Action.Ix r s, sgnL (a, c) * ((m (a, c) : ℕ) : ℂ) =
      ((PI.FJM.wt1 m a : ℤ) : ℂ) := by
    rw [PI.FJM.wt1, Int.cast_sum]
    exact Finset.sum_congr rfl fun c _ => sgnL_mul_natCast _ _
  have h3 : ∑ c : FockH1Action.Ix r s, sgnL (a, c) * (((m (a, c) : ℕ) : ℂ) + 1 / 2) =
      ∑ c : FockH1Action.Ix r s, sgnL (a, c) * ((m (a, c) : ℕ) : ℂ) +
        (∑ c : FockH1Action.Ix r s, sgnL (a, c)) * (1 / 2) := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => mul_add _ _ _
  rw [h3, h2, h1]
  push_cast
  ring

private theorem fockAct1_Eab_diag_monomial {p q r s : ℕ} (a : FockH1Action.Ix p q)
    (m : FockH1Action.Ln p q r s →₀ ℕ) (b : ℂ) :
    FockH1Action.fockAct1 p q r s (FockH1Action.Eab a a) (monomial m b) =
      (((PI.FJM.wt1 m a : ℚ) + PI.FJM.sh1 p q r s a : ℚ) : ℂ) • monomial m b := by
  rw [fockAct1_Eab, LinearMap.sum_apply]
  simp only [omE_self_monomial]
  rw [← Finset.sum_smul, sum_sgnL_mul_add_half_eq_wt1_add_sh1]

theorem leftDiagonalActionFormula : FormWt1 := by
  intro p q r s a m
  exact fockAct1_Eab_diag_monomial a m 1

private theorem sum_sgnL_left_index_eq_two_mul_sh2 {p q r s : ℕ} (c : FockH1Action.Ix r s) :
    ∑ a : FockH1Action.Ix p q, sgnL (a, c) = ((2 * PI.FJM.sh2 p q r s c : ℚ) : ℂ) := by
  rcases c with k | l <;>
    simp only [Fintype.sum_sum_type, sgnL_inl_inl, sgnL_inl_inr, sgnL_inr_inl,
      sgnL_inr_inr, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      PI.FJM.sh2, Sum.elim_inl, Sum.elim_inr, FockH1Action.cPair] <;>
    push_cast <;> ring

private theorem sum_sgnL_mul_add_half_eq_wt2_add_sh2 {p q r s : ℕ} (c : FockH1Action.Ix r s)
    (m : FockH1Action.Ln p q r s →₀ ℕ) :
    ∑ a : FockH1Action.Ix p q, sgnL (a, c) * (((m (a, c) : ℕ) : ℂ) + 1 / 2) =
      (((PI.FJM.wt2 m c : ℚ) + PI.FJM.sh2 p q r s c : ℚ) : ℂ) := by
  have h1 := sum_sgnL_left_index_eq_two_mul_sh2 (p := p) (q := q) c
  have h2 : ∑ a : FockH1Action.Ix p q, sgnL (a, c) * ((m (a, c) : ℕ) : ℂ) =
      ((PI.FJM.wt2 m c : ℤ) : ℂ) := by
    rw [PI.FJM.wt2, Int.cast_sum]
    exact Finset.sum_congr rfl fun a _ => sgnL_mul_natCast _ _
  have h3 : ∑ a : FockH1Action.Ix p q, sgnL (a, c) * (((m (a, c) : ℕ) : ℂ) + 1 / 2) =
      ∑ a : FockH1Action.Ix p q, sgnL (a, c) * ((m (a, c) : ℕ) : ℂ) +
        (∑ a : FockH1Action.Ix p q, sgnL (a, c)) * (1 / 2) := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => mul_add _ _ _
  rw [h3, h2, h1]
  push_cast
  ring

private theorem fockAct2_Eab_diag_monomial {p q r s : ℕ} (c : FockH1Action.Ix r s)
    (m : FockH1Action.Ln p q r s →₀ ℕ) (b : ℂ) :
    FockH1Action.fockAct2 p q r s (FockH1Action.Eab c c) (monomial m b) =
      (((PI.FJM.wt2 m c : ℚ) + PI.FJM.sh2 p q r s c : ℚ) : ℂ) • monomial m b := by
  rw [fockAct2_Eab, LinearMap.sum_apply]
  simp only [omE_self_monomial]
  rw [← Finset.sum_smul, sum_sgnL_mul_add_half_eq_wt2_add_sh2]

theorem rightDiagonalActionFormula : FormWt2 := by
  intro p q r s c m
  exact fockAct2_Eab_diag_monomial c m 1

section Grade

open MvPolynomial

variable {σ : Type*}

private theorem isHomogeneous_X_one (k : σ) : (X k : MvPolynomial σ ℂ).IsHomogeneous 1 := by
  first
  | exact isHomogeneous_X ℂ k
  | exact isHomogeneous_X k

private theorem homogeneousComponent_monomial_of_isHomogeneous {v : σ →₀ ℕ} {b : ℂ} {N : ℕ}
    (h : (monomial v b).IsHomogeneous N) (e : ℕ) :
    homogeneousComponent e (monomial v b) = if e = N then monomial v b else 0 :=
  homogeneousComponent_of_mem ((mem_homogeneousSubmodule N _).mpr h)

private theorem homogeneousComponent_pderiv_monomial_eq_pderiv_succ (l : σ) (e : ℕ) (u : σ →₀ ℕ) (c : ℂ) :
    homogeneousComponent e (pderiv l (monomial u c)) =
      pderiv l (homogeneousComponent (e + 1) (monomial u c)) := by
  by_cases hu : u l = 0
  · have h0 : pderiv l (monomial u c) = 0 := by
      rw [pderiv_monomial, hu]
      simp
    rw [h0, map_zero, homogeneousComponent_monomial_of_isHomogeneous (isHomogeneous_monomial c rfl)]
    split_ifs <;> simp [h0]
  · have hle : Finsupp.single l 1 ≤ u :=
      Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hu)
    have hsplit : monomial u c = X l * monomial (u - Finsupp.single l 1) c := by
      rw [X, monomial_mul, one_mul, add_tsub_cancel_of_le hle]
    have hv := isHomogeneous_monomial (R := ℂ) (d := u - Finsupp.single l 1) c rfl
    have hU : (monomial u c).IsHomogeneous (1 + Finsupp.degree (u - Finsupp.single l 1)) := by
      rw [hsplit]
      exact (isHomogeneous_X_one l).mul hv
    rw [pderiv_monomial, homogeneousComponent_monomial_of_isHomogeneous (isHomogeneous_monomial _ rfl),
      homogeneousComponent_monomial_of_isHomogeneous hU]
    split_ifs <;> first | omega | rw [pderiv_monomial] | simp

theorem hc_pderiv (l : σ) (e : ℕ) (P : MvPolynomial σ ℂ) :
    homogeneousComponent e (pderiv l P) = pderiv l (homogeneousComponent (e + 1) P) := by
  induction P using MvPolynomial.induction_on' with
  | monomial u c => exact homogeneousComponent_pderiv_monomial_eq_pderiv_succ l e u c
  | add P Q hP hQ => simp only [map_add, hP, hQ]

theorem pderiv_comm (i j : σ) (P : MvPolynomial σ ℂ) :
    pderiv i (pderiv j P) = pderiv j (pderiv i P) := by
  classical
  have h : ⁅pderiv (R := ℂ) i, pderiv (R := ℂ) j⁆ = (0 : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) := by
    apply derivation_ext
    intro k
    rw [Derivation.commutator_apply, pderiv_X, pderiv_X]
    simp only [Pi.single_apply]
    split_ifs <;> simp
  have h2 : ⁅pderiv (R := ℂ) i, pderiv (R := ℂ) j⁆ P =
      (0 : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) P := by rw [h]
  rw [Derivation.commutator_apply] at h2
  have h3 : (0 : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) P = 0 := by simp
  exact sub_eq_zero.mp (h2.trans h3)

theorem hc_hc (m n : ℕ) (P : MvPolynomial σ ℂ) :
    homogeneousComponent m (homogeneousComponent n P) =
      if m = n then homogeneousComponent n P else 0 := by
  exact homogeneousComponent_of_mem (homogeneousComponent_mem n P)

theorem eq_zero_of_hc (x : MvPolynomial σ ℂ) (h : ∀ e, homogeneousComponent e x = 0) :
    x = 0 := by
  have hx : x = ∑ i ∈ Finset.range (x.totalDegree + 1), homogeneousComponent i x := by
    first
    | exact (sum_homogeneousComponent x).symm
    | exact sum_homogeneousComponent.symm
  rw [hx]
  exact Finset.sum_eq_zero fun i _ => h i

theorem sum_hc_of_le (P : MvPolynomial σ ℂ) (n : ℕ) (hn : P.totalDegree < n) :
    ∑ i ∈ Finset.range n, homogeneousComponent i P = P := by
  have hx : ∑ i ∈ Finset.range (P.totalDegree + 1), homogeneousComponent i P = P := by
    first
    | exact sum_homogeneousComponent P
    | exact sum_homogeneousComponent
  calc ∑ i ∈ Finset.range n, homogeneousComponent i P
      = ∑ i ∈ Finset.range (P.totalDegree + 1), homogeneousComponent i P := by
        symm
        apply Finset.sum_subset
        · intro i hi
          simp only [Finset.mem_range] at hi ⊢
          omega
        · intro i _ hi
          simp only [Finset.mem_range, not_lt] at hi
          exact homogeneousComponent_eq_zero i P (by omega)
    _ = P := hx

theorem minusPart_eq_sum (A : Module.End ℂ (MvPolynomial σ ℂ)) (P : MvPolynomial σ ℂ) :
    minusPart A P = ∑ d ∈ Finset.range (P.totalDegree + 1),
      homogeneousComponent d (A (homogeneousComponent (d + 2) P)) := by
  unfold FockH1Action.minusPart
  apply finsum_eq_sum_of_support_subset
  intro d hd
  rw [Function.mem_support] at hd
  rw [Finset.mem_coe, Finset.mem_range]
  by_contra hlt
  apply hd
  show homogeneousComponent d (A (homogeneousComponent (d + 2) P)) = 0
  rw [homogeneousComponent_eq_zero (d + 2) P (by omega), map_zero, map_zero]

theorem minusPart_add (A B : Module.End ℂ (MvPolynomial σ ℂ)) (P : MvPolynomial σ ℂ) :
    minusPart (A + B) P = minusPart A P + minusPart B P := by
  simp only [minusPart_eq_sum, LinearMap.add_apply, map_add, Finset.sum_add_distrib]

theorem minusPart_smul (c : ℂ) (A : Module.End ℂ (MvPolynomial σ ℂ)) (P : MvPolynomial σ ℂ) :
    minusPart (c • A) P = c • minusPart A P := by
  simp only [minusPart_eq_sum, LinearMap.smul_apply, map_smul, Finset.smul_sum]

theorem minusPart_sum {ι : Type*} (t : Finset ι) (A : ι → Module.End ℂ (MvPolynomial σ ℂ))
    (P : MvPolynomial σ ℂ) : minusPart (∑ i ∈ t, A i) P = ∑ i ∈ t, minusPart (A i) P := by
  simp only [minusPart_eq_sum, LinearMap.sum_apply, map_sum]
  exact Finset.sum_comm

theorem minusPart_raise (A : Module.End ℂ (MvPolynomial σ ℂ))
    (hA : ∀ (d : ℕ) (Q : MvPolynomial σ ℂ), Q ∈ homog σ d → A Q ∈ homog σ (d + 2))
    (P : MvPolynomial σ ℂ) : minusPart A P = 0 := by
  rw [minusPart_eq_sum]
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [homogeneousComponent_of_mem (hA (d + 2) _ (homogeneousComponent_mem (d + 2) P)),
    if_neg (by omega)]

private theorem homogeneousComponent_minusPart (A : Module.End ℂ (MvPolynomial σ ℂ))
    (P : MvPolynomial σ ℂ) (e : ℕ) :
    homogeneousComponent e (FockH1Action.minusPart A P) =
      homogeneousComponent e (A (homogeneousComponent (e + 2) P)) := by
  rw [minusPart_eq_sum, map_sum]
  simp only [hc_hc]
  first
  | rw [Finset.sum_ite_eq]
  | rw [Finset.sum_ite_eq']
  by_cases h : e ∈ Finset.range (P.totalDegree + 1)
  · rw [if_pos h]
  · rw [if_neg h]
    rw [Finset.mem_range, not_lt] at h
    rw [homogeneousComponent_eq_zero (e + 2) P (by omega), map_zero, map_zero]

theorem minusPart_lower (L : Module.End ℂ (MvPolynomial σ ℂ))
    (hL : ∀ (e : ℕ) (P : MvPolynomial σ ℂ),
      homogeneousComponent e (L P) = L (homogeneousComponent (e + 2) P))
    (P : MvPolynomial σ ℂ) : minusPart L P = L P := by
  rw [← sub_eq_zero]
  apply eq_zero_of_hc
  intro e
  rw [map_sub, homogeneousComponent_minusPart, hL, hL,
    hc_hc, if_pos rfl, sub_self]

theorem mulXX_homog (l l' : σ) (d : ℕ) (Q : MvPolynomial σ ℂ) (hQ : Q ∈ homog σ d) :
    ((LinearMap.mulLeft ℂ (X l) * LinearMap.mulLeft ℂ (X l') : Module.End ℂ (MvPolynomial σ ℂ)) Q) ∈
      homog σ (d + 2) := by
  have h := (isHomogeneous_X_one l).mul ((isHomogeneous_X_one l').mul ((mem_homogeneousSubmodule d Q).mp hQ))
  rw [show 1 + (1 + d) = d + 2 by omega] at h
  exact (mem_homogeneousSubmodule (d + 2) _).mpr h

end Grade

theorem hc_dd {p q r s : ℕ} (l l' : Ln p q r s) (e : ℕ) (P : Pol p q r s) :
    MvPolynomial.homogeneousComponent e (dd l l' P) = dd l l' (MvPolynomial.homogeneousComponent (e + 2) P) := by
  rw [show e + 2 = e + 1 + 1 by omega]
  simp only [PI.FJM.dd, moduleEnd_mul_apply, pderiv_toLinearMap_apply]
  rw [hc_pderiv, hc_pderiv]

theorem dd_comm {p q r s : ℕ} (l l' : Ln p q r s) : dd l l' = dd l' l := by
  apply LinearMap.ext
  intro P
  simp only [PI.FJM.dd, moduleEnd_mul_apply, pderiv_toLinearMap_apply]
  exact pderiv_comm l l' P

theorem ne_of_linePos {p q r s : ℕ} {l l' : Ln p q r s} (h : linePos l ≠ linePos l') : l ≠ l' := by
  rintro rfl
  exact h rfl

theorem minusPart_omE_pn {p q r s : ℕ} (l l' : Ln p q r s) (h : linePos l = true) (h' : linePos l' = false)
    (P : Pol p q r s) : minusPart (omE l l') P = 0 := by
  have hne : l ≠ l' := ne_of_linePos (by rw [h, h']; decide)
  rw [omE_ne hne, raiB_eq_mulLeft_X_of_linePos h, lowB_eq_mulLeft_X_of_not_linePos h']
  apply minusPart_raise
  intro d Q hQ
  exact mulXX_homog l l' d Q hQ

theorem minusPart_omE_np {p q r s : ℕ} (l l' : Ln p q r s) (h : linePos l = false) (h' : linePos l' = true)
    (P : Pol p q r s) : minusPart (omE l l') P = -(dd l l' P) := by
  have hne : l ≠ l' := ne_of_linePos (by rw [h, h']; decide)
  have hop : FockH1Action.omE l l' = -PI.FJM.dd l l' := by
    rw [omE_ne hne, raiB_eq_neg_pderiv_of_not_linePos h, lowB_eq_pderiv_of_linePos h', PI.FJM.dd, neg_mul]
  rw [hop]
  have hL : ∀ (e : ℕ) (Q : FockH1Action.Pol p q r s),
      MvPolynomial.homogeneousComponent e ((-PI.FJM.dd l l') Q) =
        (-PI.FJM.dd l l') (MvPolynomial.homogeneousComponent (e + 2) Q) := by
    intro e Q
    rw [LinearMap.neg_apply, LinearMap.neg_apply, map_neg, hc_dd]
  rw [minusPart_lower _ hL, LinearMap.neg_apply]

theorem minusPart_omE_np' {p q r s : ℕ} (l l' : Ln p q r s) (h : linePos l = false) (h' : linePos l' = true)
    (P : Pol p q r s) : minusPart (omE l l') P = -(dd l' l P) := by
  rw [minusPart_omE_np l l' h h' P, dd_comm]

section Lap

variable {p q r s : ℕ}

theorem loweringPart_leftAction_inl_inr (i : Fin p) (j : Fin q) (P : Pol p q r s) :
    minusPart (fockAct1 p q r s (Eab (Sum.inl i) (Sum.inr j))) P = -(lapA (r := r) (s := s) i j P) := by
  rw [fockAct1_Eab, minusPart_sum]
  have h1 : ∀ k : Fin r, FockH1Action.minusPart (FockH1Action.omE (p := p) (q := q) (r := r) (s := s)
      (Sum.inl i, Sum.inl k) (Sum.inr j, Sum.inl k)) P = 0 :=
    fun k => minusPart_omE_pn _ _ (by rfl) (by rfl) P
  have h2 : ∀ l : Fin s, FockH1Action.minusPart (FockH1Action.omE (p := p) (q := q) (r := r) (s := s)
      (Sum.inl i, Sum.inr l) (Sum.inr j, Sum.inr l)) P =
        -(PI.FJM.dd (Sum.inl i, Sum.inr l) (Sum.inr j, Sum.inr l) P) :=
    fun l => minusPart_omE_np _ _ (by rfl) (by rfl) P
  simp only [Fintype.sum_sum_type, h1, h2, Finset.sum_const_zero, zero_add, PI.FJM.lapA,
    LinearMap.sum_apply, Finset.sum_neg_distrib]

theorem loweringPart_leftAction_inr_inl (i : Fin p) (j : Fin q) (P : Pol p q r s) :
    minusPart (fockAct1 p q r s (Eab (Sum.inr j) (Sum.inl i))) P = -(lapB (r := r) (s := s) i j P) := by
  rw [fockAct1_Eab, minusPart_sum]
  have h1 : ∀ k : Fin r, FockH1Action.minusPart (FockH1Action.omE (p := p) (q := q) (r := r) (s := s)
      (Sum.inr j, Sum.inl k) (Sum.inl i, Sum.inl k)) P =
        -(PI.FJM.dd (Sum.inl i, Sum.inl k) (Sum.inr j, Sum.inl k) P) :=
    fun k => minusPart_omE_np' _ _ (by rfl) (by rfl) P
  have h2 : ∀ l : Fin s, FockH1Action.minusPart (FockH1Action.omE (p := p) (q := q) (r := r) (s := s)
      (Sum.inr j, Sum.inr l) (Sum.inl i, Sum.inr l)) P = 0 :=
    fun l => minusPart_omE_pn _ _ (by rfl) (by rfl) P
  simp only [Fintype.sum_sum_type, h1, h2, Finset.sum_const_zero, add_zero, PI.FJM.lapB,
    LinearMap.sum_apply, Finset.sum_neg_distrib]

theorem loweringPart_rightAction_inl_inr (k : Fin r) (l : Fin s) (P : Pol p q r s) :
    minusPart (fockAct2 p q r s (Eab (Sum.inl k) (Sum.inr l))) P = -(lapD (p := p) (q := q) k l P) := by
  rw [fockAct2_Eab, minusPart_sum]
  have h1 : ∀ i : Fin p, FockH1Action.minusPart (FockH1Action.omE (p := p) (q := q) (r := r) (s := s)
      (Sum.inl i, Sum.inl k) (Sum.inl i, Sum.inr l)) P = 0 :=
    fun i => minusPart_omE_pn _ _ (by rfl) (by rfl) P
  have h2 : ∀ j : Fin q, FockH1Action.minusPart (FockH1Action.omE (p := p) (q := q) (r := r) (s := s)
      (Sum.inr j, Sum.inl k) (Sum.inr j, Sum.inr l)) P =
        -(PI.FJM.dd (Sum.inr j, Sum.inl k) (Sum.inr j, Sum.inr l) P) :=
    fun j => minusPart_omE_np _ _ (by rfl) (by rfl) P
  simp only [Fintype.sum_sum_type, h1, h2, Finset.sum_const_zero, zero_add, PI.FJM.lapD,
    LinearMap.sum_apply, Finset.sum_neg_distrib]

theorem loweringPart_rightAction_inr_inl (k : Fin r) (l : Fin s) (P : Pol p q r s) :
    minusPart (fockAct2 p q r s (Eab (Sum.inr l) (Sum.inl k))) P = -(lapC (p := p) (q := q) k l P) := by
  rw [fockAct2_Eab, minusPart_sum]
  have h1 : ∀ i : Fin p, FockH1Action.minusPart (FockH1Action.omE (p := p) (q := q) (r := r) (s := s)
      (Sum.inl i, Sum.inr l) (Sum.inl i, Sum.inl k)) P =
        -(PI.FJM.dd (Sum.inl i, Sum.inl k) (Sum.inl i, Sum.inr l) P) :=
    fun i => minusPart_omE_np' _ _ (by rfl) (by rfl) P
  have h2 : ∀ j : Fin q, FockH1Action.minusPart (FockH1Action.omE (p := p) (q := q) (r := r) (s := s)
      (Sum.inr j, Sum.inr l) (Sum.inr j, Sum.inl k)) P = 0 :=
    fun j => minusPart_omE_pn _ _ (by rfl) (by rfl) P
  simp only [Fintype.sum_sum_type, h1, h2, Finset.sum_const_zero, add_zero, PI.FJM.lapC,
    LinearMap.sum_apply, Finset.sum_neg_distrib]

theorem fockAct1_expand (X : Mat p q) :
    fockAct1 p q r s X = ∑ a, ∑ b, X a b • fockAct1 p q r s (Eab a b) := by
  rw [fockAct1_eq]
  simp only [fockAct1_Eab, Finset.smul_sum]

theorem fockAct2_expand (Y : Mat r s) :
    fockAct2 p q r s Y = ∑ c, ∑ d, Y c d • fockAct2 p q r s (Eab c d) := by
  rw [fockAct2_eq]
  simp only [fockAct2_Eab, Finset.smul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_comm

theorem minusPart1_expand (X : Mat p q) (P : Pol p q r s) :
    minusPart (fockAct1 p q r s X) P = ∑ a, ∑ b, X a b • minusPart (fockAct1 p q r s (Eab a b)) P := by
  rw [fockAct1_expand (r := r) (s := s) X, minusPart_sum]
  simp only [minusPart_sum, minusPart_smul]

theorem minusPart2_expand (Y : Mat r s) (P : Pol p q r s) :
    minusPart (fockAct2 p q r s Y) P = ∑ c, ∑ d, Y c d • minusPart (fockAct2 p q r s (Eab c d)) P := by
  rw [fockAct2_expand (p := p) (q := q) Y, minusPart_sum]
  simp only [minusPart_sum, minusPart_smul]

theorem isPC_Eab {n m : ℕ} (a b : Ix n m) (h : ¬ sameBlock a b) : IsPC (Eab a b) := by
  intro a' b' h'
  rw [FockH1Action.Eab, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact h h'

end Lap

theorem jointHarmonicsIffLaplacians : FormJ := by
  intro p q r s P
  simp only [FockH1Action.Jset, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hL, hR⟩
    refine ⟨fun i j => ?_, fun i j => ?_, fun k l => ?_, fun k l => ?_⟩
    · have h := hL _ (isPC_Eab (Sum.inl i) (Sum.inr j)
        (by simp [FockH1Action.sameBlock]))
      rw [loweringPart_leftAction_inl_inr] at h
      exact neg_eq_zero.mp h
    · have h := hL _ (isPC_Eab (Sum.inr j) (Sum.inl i)
        (by simp [FockH1Action.sameBlock]))
      rw [loweringPart_leftAction_inr_inl] at h
      exact neg_eq_zero.mp h
    · have h := hR _ (isPC_Eab (Sum.inr l) (Sum.inl k)
        (by simp [FockH1Action.sameBlock]))
      rw [loweringPart_rightAction_inr_inl] at h
      exact neg_eq_zero.mp h
    · have h := hR _ (isPC_Eab (Sum.inl k) (Sum.inr l)
        (by simp [FockH1Action.sameBlock]))
      rw [loweringPart_rightAction_inl_inr] at h
      exact neg_eq_zero.mp h
  · rintro ⟨hA, hB, hC, hD⟩
    refine ⟨fun X hX => ?_, fun Y hY => ?_⟩
    · rw [minusPart1_expand]
      refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
      rcases a with i | j <;> rcases b with i' | j'
      · rw [hX (Sum.inl i) (Sum.inl i') (by simp [FockH1Action.sameBlock]), zero_smul]
      · rw [loweringPart_leftAction_inl_inr, hA, neg_zero, smul_zero]
      · rw [loweringPart_leftAction_inr_inl, hB, neg_zero, smul_zero]
      · rw [hX (Sum.inr j) (Sum.inr j') (by simp [FockH1Action.sameBlock]), zero_smul]
    · rw [minusPart2_expand]
      refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
      rcases c with k | l <;> rcases d with k' | l'
      · rw [hY (Sum.inl k) (Sum.inl k') (by simp [FockH1Action.sameBlock]), zero_smul]
      · rw [loweringPart_rightAction_inl_inr, hD, neg_zero, smul_zero]
      · rw [loweringPart_rightAction_inr_inl, hC, neg_zero, smul_zero]
      · rw [hY (Sum.inr l) (Sum.inr l') (by simp [FockH1Action.sameBlock]), zero_smul]

section HW

variable {p q r s : ℕ}

open MvPolynomial

theorem coeff_fockAct1_diag (a : Ix p q) (P : Pol p q r s) (m : Ln p q r s →₀ ℕ) :
    coeff m (fockAct1 p q r s (Eab a a) P) =
      (((wt1 m a : ℚ) + sh1 p q r s a : ℚ) : ℂ) * coeff m P := by
  induction P using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [fockAct1_Eab_diag_monomial, coeff_smul, smul_eq_mul, coeff_monomial]
    split_ifs with h
    · rw [h]
    · simp
  | add P Q hP hQ => simp only [map_add, coeff_add, hP, hQ, mul_add]

theorem coeff_fockAct2_diag (c : Ix r s) (P : Pol p q r s) (m : Ln p q r s →₀ ℕ) :
    coeff m (fockAct2 p q r s (Eab c c) P) =
      (((wt2 m c : ℚ) + sh2 p q r s c : ℚ) : ℂ) * coeff m P := by
  induction P using MvPolynomial.induction_on' with
  | monomial u b =>
    rw [fockAct2_Eab_diag_monomial, coeff_smul, smul_eq_mul, coeff_monomial]
    split_ifs with h
    · rw [h]
    · simp
  | add P Q hP hQ => simp only [map_add, coeff_add, hP, hQ, mul_add]

theorem mem_wtSub1 (μ : Ix p q → ℚ) (P : Pol p q r s) :
    P ∈ wtSub (fockAct1 p q r s) μ ↔ ∀ m ∈ P.support, ∀ a, (wt1 m a : ℚ) + sh1 p q r s a = μ a := by
  simp only [FockH1Action.wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  constructor
  · intro h m hm a
    have hc := congrArg (coeff m) (h a)
    rw [coeff_fockAct1_diag, coeff_smul, smul_eq_mul] at hc
    exact_mod_cast mul_right_cancel₀ (MvPolynomial.mem_support_iff.mp hm) hc
  · intro h a
    ext m
    rw [coeff_fockAct1_diag, coeff_smul, smul_eq_mul]
    by_cases hm : m ∈ P.support
    · rw [h m hm a]
    · have h0 : coeff m P = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
      rw [h0, mul_zero, mul_zero]

theorem mem_wtSub2 (μ : Ix r s → ℚ) (P : Pol p q r s) :
    P ∈ wtSub (fockAct2 p q r s) μ ↔ ∀ m ∈ P.support, ∀ c, (wt2 m c : ℚ) + sh2 p q r s c = μ c := by
  simp only [FockH1Action.wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  constructor
  · intro h m hm c
    have hc := congrArg (coeff m) (h c)
    rw [coeff_fockAct2_diag, coeff_smul, smul_eq_mul] at hc
    exact_mod_cast mul_right_cancel₀ (MvPolynomial.mem_support_iff.mp hm) hc
  · intro h c
    ext m
    rw [coeff_fockAct2_diag, coeff_smul, smul_eq_mul]
    by_cases hm : m ∈ P.support
    · rw [h m hm c]
    · have h0 : coeff m P = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
      rw [h0, mul_zero, mul_zero]

theorem ne_of_posC {n k : ℕ} {a b : Ix n k} (h : posC a b) : a ≠ b := by
  rintro rfl
  rcases a with i | i <;>
    first
    | exact lt_irrefl i h
    | simp [FockH1Action.posC] at h

theorem mem_hwSub1 (μ : Ix p q → ℚ) (P : Pol p q r s) :
    P ∈ hwSub (fockAct1 p q r s) μ ↔
      (∀ m ∈ P.support, ∀ a, (wt1 m a : ℚ) + sh1 p q r s a = μ a) ∧
        ∀ a b, posC a b → rai1 (r := r) (s := s) a b P = 0 := by
  rw [FockH1Action.hwSub, Submodule.mem_inf, mem_wtSub1]
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  refine and_congr Iff.rfl (forall_congr' fun a => forall_congr' fun b =>
    forall_congr' fun hab => ?_)
  rw [leftOffDiagonalActionFormula p q r s a b (ne_of_posC hab)]

theorem mem_hwSub2 (μ : Ix r s → ℚ) (P : Pol p q r s) :
    P ∈ hwSub (fockAct2 p q r s) μ ↔
      (∀ m ∈ P.support, ∀ c, (wt2 m c : ℚ) + sh2 p q r s c = μ c) ∧
        ∀ c d, posC c d → rai2 (p := p) (q := q) c d P = 0 := by
  rw [FockH1Action.hwSub, Submodule.mem_inf, mem_wtSub2]
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  refine and_congr Iff.rfl (forall_congr' fun c => forall_congr' fun d =>
    forall_congr' fun hcd => ?_)
  rw [rightOffDiagonalActionFormula p q r s c d (ne_of_posC hcd)]

end HW

end PI.WFJM

namespace PI.FJM

theorem jointHarmonicsIffLaplacians : FormJ := by
  exact PI.WFJM.jointHarmonicsIffLaplacians
theorem leftDiagonalActionFormula : FormWt1 := by
  exact PI.WFJM.leftDiagonalActionFormula
theorem rightDiagonalActionFormula : FormWt2 := by
  exact PI.WFJM.rightDiagonalActionFormula
theorem leftOffDiagonalActionFormula : FormRaise1 := by
  exact PI.WFJM.leftOffDiagonalActionFormula
theorem rightOffDiagonalActionFormula : FormRaise2 := by
  exact PI.WFJM.rightOffDiagonalActionFormula

end PI.FJM
