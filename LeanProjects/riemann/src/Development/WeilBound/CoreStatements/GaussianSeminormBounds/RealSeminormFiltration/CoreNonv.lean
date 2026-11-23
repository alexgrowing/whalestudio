import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreGraph
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreDelta
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreProj

noncomputable section

open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

section Dual

variable {p q : ℕ}

theorem epsB_mul (a c b : Ix p q) : epsB a c * epsB c b = epsB a b := by
  rcases a with a | a <;> rcases c with c | c <;> rcases b with b | b <;> simp [epsB, sameBlock]

theorem epsB_symm (a b : Ix p q) : epsB a b = epsB b a := by
  rcases a with a | a <;> rcases b with b | b <;> simp [epsB, sameBlock]

theorem epsB_self (a : Ix p q) : epsB a a = 1 := by
  rcases a with a | a <;> simp [epsB, sameBlock]

theorem epsB_conj (a b : Ix p q) : (starRingEnd ℂ) (epsB a b) = epsB a b := by
  unfold epsB
  split_ifs <;> simp

def thetaM (p q : ℕ) : Mat p q →ₗ[ℂ] Mat p q where
  toFun Z := Matrix.of fun a b => epsB a b * Z b a
  map_add' Z W := by
    ext a b
    simp [mul_add]
  map_smul' t Z := by
    ext a b
    simp [mul_left_comm]

theorem thetaM_mul (Z W : Mat p q) : thetaM p q (Z * W) = thetaM p q W * thetaM p q Z := by
  ext a b
  simp only [thetaM, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← epsB_mul a c b]
  ring

theorem thetaM_Eab (a b : Ix p q) : thetaM p q (Eab a b) = epsB a b • Eab b a := by
  ext i j
  simp only [thetaM, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply, Eab, Matrix.single_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases h1 : a = j <;> by_cases h2 : b = i
  · subst h1 h2
    simp [epsB_symm a b]
  all_goals simp [h1, h2]

theorem trace_Eab (a b : Ix p q) : (Eab a b).trace = if a = b then 1 else 0 := by
  simp [Eab, Matrix.trace, Matrix.single_apply, Matrix.diag]
  split_ifs with h
  · subst h
    simp [Finset.filter_eq]
  · rw [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro x - ⟨h1, h2⟩
    exact h (h1.trans h2.symm)

def dualAct {B : Type} [AddCommGroup B] [Module ℂ B] (ρ : Mat p q →ₗ[ℂ] Module.End ℂ B) (c : ℂ) :
    Mat p q →ₗ[ℂ] Module.End ℂ B :=
  (c • Matrix.traceLinearMap (Ix p q) ℂ ℂ).smulRight 1 - ρ ∘ₗ thetaM p q

theorem dualAct_eq {B : Type} [AddCommGroup B] [Module ℂ B] (ρ : Mat p q →ₗ[ℂ] Module.End ℂ B) (c : ℂ)
    (Z : Mat p q) : dualAct ρ c Z = (c * Z.trace) • (1 : Module.End ℂ B) - ρ (thetaM p q Z) := by
  simp [dualAct]

theorem dualAct_Eab {B : Type} [AddCommGroup B] [Module ℂ B] (ρ : Mat p q →ₗ[ℂ] Module.End ℂ B) (c : ℂ)
    (a b : Ix p q) (v : B) :
    dualAct ρ c (Eab a b) v = (if a = b then c else 0) • v - epsB a b • ρ (Eab b a) v := by
  rw [dualAct_eq, trace_Eab, thetaM_Eab]
  split_ifs <;> simp

theorem dualAct_lie {B : Type} [AddCommGroup B] [Module ℂ B] {ρ : Mat p q →ₗ[ℂ] Module.End ℂ B}
    (h : IsLie ρ) (c : ℂ) : IsLie (dualAct ρ c) := by
  intro X Y
  rw [dualAct_eq, dualAct_eq, dualAct_eq, map_sub, thetaM_mul, thetaM_mul, Matrix.trace_sub, Matrix.trace_mul_comm X Y, sub_self, mul_zero, zero_smul, zero_sub, map_sub, neg_sub, ← map_sub, ← h (thetaM p q X) (thetaM p q Y)]
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul, smul_sub]
  rw [mul_comm (c * Y.trace) (c * X.trace)]
  abel

theorem dualAct_adj {B : Type} [NormedAddCommGroup B] [InnerProductSpace ℂ B]
    {ρ : Mat p q →ₗ[ℂ] Module.End ℂ B} (h : AdjG ρ) (c0 : ℚ) : AdjG (dualAct ρ (c0 : ℂ)) := by
  intro a b u v
  rw [dualAct_Eab, dualAct_Eab, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_left, inner_smul_right, inner_smul_right, h, epsB_conj, mul_sub, ← mul_assoc, ← mul_assoc, epsB_mul, epsB_self, one_mul]
  by_cases hab : a = b
  · subst hab
    simp [epsB_self]
  · simp [hab, Ne.symm hab]

end Dual

section Conj

variable {p q r s : ℕ}

def cjP (P : Pol p q r s) : Pol p q r s := MvPolynomial.map (starRingEnd ℂ) P

theorem cjP_add (P Q : Pol p q r s) : cjP (P + Q) = cjP P + cjP Q := map_add _ _ _

theorem cjP_sub (P Q : Pol p q r s) : cjP (P - Q) = cjP P - cjP Q := map_sub _ _ _

theorem cjP_smul (t : ℂ) (P : Pol p q r s) : cjP (t • P) = (starRingEnd ℂ) t • cjP P := by
  simp [cjP, MvPolynomial.smul_eq_C_mul]

theorem cjP_lowB (l : Ln p q r s) (P : Pol p q r s) : cjP (lowB l P) = lowB l (cjP P) := by
  unfold lowB
  split_ifs <;> simp [cjP, MvPolynomial.pderiv_map]

theorem cjP_raiB (l : Ln p q r s) (P : Pol p q r s) : cjP (raiB l P) = raiB l (cjP P) := by
  unfold raiB
  split_ifs <;> simp [cjP, MvPolynomial.pderiv_map]

theorem cjP_omE (l l' : Ln p q r s) (P : Pol p q r s) : cjP (omE l l' P) = omE l l' (cjP P) := by
  unfold omE
  simp only [LinearMap.add_apply, Module.End.mul_apply, cjP_add, cjP_raiB, cjP_lowB]
  split_ifs
  · simp only [LinearMap.smul_apply, cjP_smul, Module.End.one_apply]
    congr 2
    rw [map_div₀, map_one, Complex.conj_ofNat]
  · simp [cjP]

theorem conj_first_action_comm (a b : Ix p q) (P : Pol p q r s) :
    cjP (fockAct1 p q r s (Eab a b) P) = fockAct1 p q r s (Eab a b) (cjP P) := by
  rw [PI.FHS.fockAct1_eq, PI.FHS.omAct_apply, PI.FHS.omAct_apply]
  show MvPolynomial.map _ _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun l' _ => ?_
  change cjP _ = _
  rw [cjP_smul, cjP_omE]
  congr 1
  simp only [Matrix.kroneckerMap_apply, Eab, Matrix.single_apply, Matrix.one_apply, map_mul]
  split_ifs <;> simp

theorem fockInner_sub_left' (P P' Q : Pol p q r s) :
    fockInner (P - P') Q = fockInner P Q - fockInner P' Q := by
  rw [sub_eq_add_neg, PI.FHS.fockInner_add_left, PI.FHS.fockInner_neg_left, sub_eq_add_neg]

end Conj

private theorem fockInner_cjP_fockAct1_thetaM_adjoint {p q r s : ℕ} (Z : Mat p q) (w v : Pol p q r s) :
    fockInner (cjP (fockAct1 p q r s (thetaM p q Z) w)) v = fockInner (cjP w) (fockAct1 p q r s Z v) := by
  induction Z using Matrix.induction_on' with
  | h_zero =>
    simp [cjP, PI.FHS.fockInner_zero_left, PI.FHS.fockInner_zero_right]
  | h_add A B hA hB =>
    rw [map_add, map_add, LinearMap.add_apply, cjP_add, PI.FHS.fockInner_add_left, hA, hB, map_add,
      LinearMap.add_apply, PI.FHS.fockInner_add_right]
  | h_std_basis i j t =>
    have hE : Matrix.single i j t = t • Eab i j := by
      simp [Eab, Matrix.smul_single]
    simp only [hE, map_smul, LinearMap.smul_apply, cjP_smul, PI.FHS.fockInner_smul_left,
      PI.FHS.fockInner_smul_right, Complex.conj_conj, thetaM_Eab, conj_first_action_comm, epsB_conj, fock_inner_adjoint_first]
    rw [← mul_assoc (epsB i j), epsB_mul, epsB_self, one_mul]

theorem nontrivial_of_pair {p q r s : ℕ} (c : ℂ) (c0 : ℚ) (hc : c = c0) (h : PairData p q r s c) :
    Nontrivial (ThC p q r s c) := by
  obtain ⟨lam, x, y, dx, hx0, hy0, hxh, hxw, hxl, hyw, hyl⟩ := h
  subst hc
  have hsb : ∀ a : Ix p q, sameBlock a a := by
    intro a
    rcases a with a | a <;> simp [sameBlock]
  have hsym : ∀ a b : Ix p q, sameBlock a b → sameBlock b a := by
    intro a b
    rcases a with a | a <;> rcases b with b | b <;> simp [sameBlock]
  have hlam : ∀ a, (starRingEnd ℂ) (lam a) = lam a := by
    intro a
    have h1 := fock_inner_adjoint_first a a x x
    rw [hxw a a (hsb a), if_pos rfl, epsB_self, one_mul, PI.FHS.fockInner_smul_left,
      PI.FHS.fockInner_smul_right] at h1
    have hne : fockInner x x ≠ 0 := fun h0 => hx0 (PI.FHS.fockInner_self_eq_zero h0)
    exact mul_right_cancel₀ hne h1
  set ρB := dualAct (fvAct1 p q 0 s) (c0 : ℂ) with hρB
  have hyw' : ∀ a b, sameBlock a b →
      ρB (Eab a b) (cjP y : FV p q 0 s) = (if a = b then lam a else 0) • (cjP y : FV p q 0 s) := by
    intro a b hab
    rw [hρB]
    refine (dualAct_Eab (fvAct1 p q 0 s) (c0 : ℂ) a b (cjP y)).trans ?_
    change (if a = b then (c0 : ℂ) else 0) • cjP y - epsB a b • fockAct1 p q 0 s (Eab b a) (cjP y) =
      (if a = b then lam a else 0) • cjP y
    rw [← conj_first_action_comm, hyw b a (hsym a b hab)]
    by_cases hab' : a = b
    · subst hab'
      rw [if_pos rfl, if_pos rfl, if_pos rfl, cjP_smul, epsB_self, one_smul, map_sub, hlam, map_ratCast,
        sub_smul]
      abel
    · rw [if_neg hab', if_neg hab', if_neg (Ne.symm hab'), zero_smul, zero_smul]
      simp [cjP]
  have hyl' : ∀ (i : Fin p) (j : Fin q), ρB (Eab (Sum.inr j) (Sum.inl i)) (cjP y : FV p q 0 s) = 0 := by
    intro i j
    rw [hρB]
    refine (dualAct_Eab (fvAct1 p q 0 s) (c0 : ℂ) _ _ (cjP y)).trans ?_
    change (if (Sum.inr j : Ix p q) = Sum.inl i then (c0 : ℂ) else 0) • cjP y -
      epsB (Sum.inr j) (Sum.inl i) • fockAct1 p q 0 s (Eab (Sum.inl i) (Sum.inr j)) (cjP y) = 0
    rw [← conj_first_action_comm, hyl i j, if_neg (by simp)]
    simp [cjP]
  obtain ⟨Φ, hΦ, hΦx⟩ := graph_map (fvAct1 p q r 0) ρB (lie1 p q r 0) (dualAct_lie (lie1 p q 0 s) _)
    (adj1 p q r 0) (dualAct_adj (adj1 p q 0 s) c0) lam x (cjP y) hx0 hxw hyw' hxl hyl' (proj_gen x dx hxh)
  obtain ⟨Ψ, hΨ1, hΨ2⟩ : ∃ Ψ : Pol p q r 0 →ₗ[ℂ] Pol p q 0 s,
      (∀ Z u, Ψ (fockAct1 p q r 0 Z u) = ((c0 : ℂ) * Z.trace) • Ψ u - fockAct1 p q 0 s (thetaM p q Z) (Ψ u)) ∧
      Ψ x = cjP y := by
    refine ⟨Φ, fun Z u => ?_, hΦx⟩
    have h1 := hΦ Z u
    rw [hρB, dualAct_eq, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at h1
    exact h1
  let b : Pol p q r 0 →ₗ[ℂ] Pol p q 0 s →ₗ[ℂ] ℂ :=
    LinearMap.mk₂ ℂ (fun u v => fockInner (cjP (Ψ u)) v)
      (by
        intro u u' v
        rw [map_add, cjP_add, PI.FHS.fockInner_add_left])
      (by
        intro t u v
        rw [map_smul, cjP_smul, PI.FHS.fockInner_smul_left, Complex.conj_conj]
        rfl)
      (by
        intro u v v'
        exact PI.FHS.fockInner_add_right _ _ _)
      (by
        intro t u v
        rw [PI.FHS.fockInner_smul_right]
        rfl)
  refine nontrivial_of_form (c0 : ℂ) b ?_ x y ?_
  · intro Z u v
    change fockInner (cjP (Ψ (fockAct1 p q r 0 Z u))) v + fockInner (cjP (Ψ u)) (fockAct1 p q 0 s Z v) =
      (c0 : ℂ) * Z.trace * fockInner (cjP (Ψ u)) v
    rw [hΨ1, cjP_sub, cjP_smul, fockInner_sub_left', PI.FHS.fockInner_smul_left, Complex.conj_conj,
      fockInner_cjP_fockAct1_thetaM_adjoint]
    ring
  · change fockInner (cjP (Ψ x)) y ≠ 0
    rw [hΨ2]
    intro h0
    apply hy0
    apply PI.FHS.fockInner_self_eq_zero
    simpa [cjP, MvPolynomial.map_map, MvPolynomial.map_id] using h0

end PositivityTheory.KReal

end
