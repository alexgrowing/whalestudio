import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.IsPolyMon

noncomputable section

namespace PI.WMI

open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace

def lowerInv_e (r : ℝ) : ℂ := Complex.exp ((r : ℂ) * Complex.I)

lemma lowerInv_e_mul_pow (r s : ℝ) (m : ℕ) :
    lowerInv_e r * lowerInv_e s ^ m = lowerInv_e (r + m * s) := by
  unfold lowerInv_e
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1; push_cast; ring

lemma lowerInv_conj_e (r : ℝ) : (starRingEnd ℂ) (lowerInv_e r) = lowerInv_e (-r) := by
  unfold lowerInv_e
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal]

lemma lowerInv_evM_affine {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℂ)
    (Q : MvPolynomial (Fin N × Fin N) ℂ) :
    ∃ p : Polynomial ℂ, ∀ c : ℂ, evM (A + c • B) Q = p.eval c := by
  induction Q using MvPolynomial.induction_on with
  | C r => exact ⟨Polynomial.C r, fun c => by simp [evM]⟩
  | add p q hp hq =>
    obtain ⟨p1, h1⟩ := hp
    obtain ⟨q1, h2⟩ := hq
    refine ⟨p1 + q1, fun c => ?_⟩
    have e : evM (A + c • B) (p + q) = evM (A + c • B) p + evM (A + c • B) q := by
      simp [evM]
    rw [e, h1, h2, Polynomial.eval_add]
  | mul_X p i hp =>
    obtain ⟨p1, h1⟩ := hp
    refine ⟨p1 * (Polynomial.C (A i.1 i.2) + Polynomial.C (B i.1 i.2) * Polynomial.X), fun c => ?_⟩
    have e : evM (A + c • B) (p * X i) = evM (A + c • B) p * (A i.1 i.2 + c * B i.1 i.2) := by
      simp [evM]
    rw [e, h1, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_C, Polynomial.eval_X]
    ring

lemma lowerInv_torus_mem {N : ℕ} (θ : Fin N → ℝ) : torus θ ∈ Kset (allPos N) := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, torus, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [Pi.star_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      Complex.norm_exp_ofReal_mul_I]
    simp
  · simp [Jm, allPos]

lemma lowerInv_torus_mul {N : ℕ} (θ φ : Fin N → ℝ) : torus θ * torus φ = torus (θ + φ) := by
  unfold torus
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [← Complex.exp_add]
  congr 1
  push_cast [Pi.add_apply]
  ring

lemma lowerInv_torus_zero {N : ℕ} : torus (0 : Fin N → ℝ) = 1 := by
  unfold torus
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  simp

lemma lowerInv_det_ne {N : ℕ} (θ : Fin N → ℝ) : (torus θ).det ≠ 0 := by
  unfold torus
  rw [Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => Complex.exp_ne_zero _

lemma lowerInv_comm {N : ℕ} {a b : Fin N} (hab : a < b) (θ : Fin N → ℝ) (c : ℂ) :
    (1 + Matrix.single b a c) * torus θ =
      torus θ * (1 + Matrix.single b a (c * lowerInv_e (θ a - θ b))) := by
  have key : Complex.exp ((θ b : ℂ) * Complex.I) * lowerInv_e (θ a - θ b) =
      Complex.exp ((θ a : ℂ) * Complex.I) := by
    unfold lowerInv_e
    rw [← Complex.exp_add]
    congr 1; push_cast; ring
  ext i j
  simp only [torus, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
  by_cases h : b = i ∧ a = j
  · obtain ⟨rfl, rfl⟩ := h
    simp only [and_self, if_true]
    rw [Matrix.one_apply_ne (ne_of_gt hab), ← key]; ring
  · simp only [if_neg h, add_zero]
    by_cases hij : i = j
    · subst hij; ring
    · rw [Matrix.one_apply_ne hij]; ring

section
variable {N : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)}

lemma lowerInv_inner_pres (hU : IsURepOn (Kset (allPos N)) σ) {g : Matrix (Fin N) (Fin N) ℂ}
    (hg : g ∈ Kset (allPos N)) (u w : H) : ⟪σ g u, σ g w⟫_ℂ = ⟪u, w⟫_ℂ := by
  let L : H →ₗᵢ[ℂ] H := { toLinearMap := (σ g).toLinearMap, norm_map' := fun v => hU.2.1 g hg v }
  exact L.inner_map_map u w

lemma lowerInv_adj (hU : IsURepOn (Kset (allPos N)) σ) (θ : Fin N → ℝ) (y w : H) :
    ⟪y, σ (torus θ) w⟫_ℂ = ⟪σ (torus (-θ)) y, w⟫_ℂ := by
  have h1 : σ (torus θ) (σ (torus (-θ)) y) = y := by
    have h := hU.1.2 (torus θ) (lowerInv_torus_mem θ) (torus (-θ)) (lowerInv_torus_mem (-θ))
    rw [lowerInv_torus_mul, add_neg_cancel, lowerInv_torus_zero, hU.1.1] at h
    have h' := congrArg (fun f : H →L[ℂ] H => f y) h
    simpa using h'.symm
  rw [← lowerInv_inner_pres hU (lowerInv_torus_mem θ) (σ (torus (-θ)) y) w, h1]

end

lemma lowerInv_not_cdom {N : ℕ} {Λ : Fin N → ℝ} {a b : Fin N} (hab : a < b) {m : ℕ} (hm : 1 ≤ m) :
    ¬ CDom (allPos N) (Λ + (m : ℝ) • root a b) Λ := by
  rintro ⟨cc, hcc, heq⟩
  let L : (Fin N → ℝ) →ₗ[ℝ] ℝ := ∑ x : Fin N, ((x : ℕ) : ℝ) • LinearMap.proj x
  have hL : ∀ v, L v = ∑ x : Fin N, ((x : ℕ) : ℝ) * v x := by
    intro v; simp [L, LinearMap.sum_apply]
  have hroot : ∀ x y : Fin N, L (root x y) = ((x : ℕ) : ℝ) - ((y : ℕ) : ℝ) := by
    intro x y
    rw [hL]
    simp [root, Pi.single_apply, mul_sub, Finset.sum_sub_distrib]
  have h1 := congrArg L heq
  simp only [map_sum, map_smul, hroot] at h1
  have lhs : L (Λ - (Λ + (m : ℝ) • root a b)) = (m : ℝ) * (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
    rw [sub_add_cancel_left, map_neg, map_smul, hroot, smul_eq_mul]; ring
  rw [lhs] at h1
  have hle : ∑ x, ∑ y, (cc x y : ℝ) • (((x : ℕ) : ℝ) - ((y : ℕ) : ℝ)) ≤ 0 :=
    Finset.sum_nonpos fun x _ => Finset.sum_nonpos fun y _ => by
      by_cases h : cc x y = 0
      · simp [h]
      · have hxy : (x : ℕ) < y := (hcc x y h).1
        rw [smul_eq_mul]
        apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
        rw [sub_nonpos]; exact_mod_cast hxy.le
  have hpos : 0 < (m : ℝ) * (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
    apply mul_pos (by exact_mod_cast hm)
    rw [sub_pos]; exact_mod_cast hab
  linarith

lemma lowerInv_coeff_scale (p q : Polynomial ℂ) (D u : ℂ) (h : ∀ c, q.eval c = D * p.eval (c * u))
    (m : ℕ) : q.coeff m = D * u ^ m * p.coeff m := by
  have hq : q = Polynomial.C D * p.comp (Polynomial.C u * Polynomial.X) := by
    apply Polynomial.funext
    intro c
    rw [h, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, mul_comm u c]
  rw [hq, Polynomial.coeff_C_mul, Polynomial.comp_C_mul_X_coeff]
  ring

theorem lower_triangular_invariance : LowerInv := by
  intro N Λ H _ _ σ S K P hU hKT hP hPσ v0 hv0 a b hab c x
  have : FiniteDimensional ℂ S := hKT.1
  have hex : ∀ y : S, ∃ p : Polynomial ℂ, ∀ c : ℂ,
      p.eval c = ⟪v0, P (1 + Matrix.single b a c) y⟫_ℂ := by
    intro y
    obtain ⟨Q, hQ⟩ := hP.poly y v0
    obtain ⟨p, hp⟩ := lowerInv_evM_affine 1 (Matrix.single b a 1) Q
    refine ⟨p, fun c => ?_⟩
    rw [← hp c, hQ, Matrix.smul_single, smul_eq_mul, mul_one]
  choose pp hpp using hex
  have hadd : ∀ y z : S, pp (y + z) = pp y + pp z := fun y z => Polynomial.funext fun c => by
    rw [Polynomial.eval_add, hpp, hpp, hpp, map_add, inner_add_right]
  have hsmul : ∀ (r : ℂ) (y : S), pp (r • y) = Polynomial.C r * pp y := fun r y =>
    Polynomial.funext fun c => by
      rw [Polynomial.eval_mul, Polynomial.eval_C, hpp, hpp, map_smul, inner_smul_right]
  let ψ : ℕ → S →ₗ[ℂ] ℂ := fun m =>
    { toFun := fun y => (pp y).coeff m
      map_add' := fun y z => by simp only [hadd, Polynomial.coeff_add]
      map_smul' := fun r y => by
        simp only [hsmul, Polynomial.coeff_C_mul, smul_eq_mul, RingHom.id_apply] }
  have hψ_apply : ∀ m (y : S), ψ m y = (pp y).coeff m := fun _ _ => rfl
  have hstab : ∀ θ (y : S), σ (torus θ) (y : H) ∈ S := fun θ y =>
    hKT.2.1 _ (lowerInv_torus_mem θ) _ y.2

  have hv0eig : ∀ (θ : Fin N → ℝ) (w : H),
      ⟪(v0 : H), σ (torus θ) w⟫_ℂ = lowerInv_e (∑ i, Λ i * θ i) * ⟪(v0 : H), w⟫_ℂ := by
    intro θ w
    have hw : σ (torus (-θ)) (v0 : H) =
        Complex.exp (((∑ i, Λ i * (-θ) i : ℝ) : ℂ) * Complex.I) • (v0 : H) :=
      hv0 (-θ) (lowerInv_torus_mem (-θ))
    rw [lowerInv_adj hU θ, hw, inner_smul_left]
    have := lowerInv_conj_e (∑ i, Λ i * (-θ) i)
    unfold lowerInv_e at this ⊢
    rw [this]
    congr 3
    simp [Finset.sum_neg_distrib]
  have hv0P : ∀ θ (y : S), ⟪v0, P (torus θ) y⟫_ℂ =
      (torus θ).det ^ K * lowerInv_e (∑ i, Λ i * θ i) * ⟪v0, y⟫_ℂ := by
    intro θ y
    rw [Submodule.coe_inner, hPσ _ (lowerInv_torus_mem θ), inner_smul_right, hv0eig,
      Submodule.coe_inner, mul_assoc]
  have hrel : ∀ θ (y : S) (c : ℂ), (pp (P (torus θ) y)).eval c =
      ((torus θ).det ^ K * lowerInv_e (∑ i, Λ i * θ i)) *
        (pp y).eval (c * lowerInv_e (θ a - θ b)) := by
    intro θ y c
    rw [hpp, hpp, ← LinearMap.comp_apply, ← hP.mul, lowerInv_comm hab, hP.mul, LinearMap.comp_apply,
      hv0P]
  have hψ : ∀ m, 1 ≤ m → ψ m = 0 := by
    intro m hm
    let y : S := (InnerProductSpace.toDual ℂ S).symm (LinearMap.toContinuousLinearMap (ψ m))
    have hyx : ∀ z : S, ⟪y, z⟫_ℂ = ψ m z := fun z => by
      rw [InnerProductSpace.toDual_symm_apply]; rfl
    have hsc : ∀ θ (z : S), ψ m (P (torus θ) z) =
        (torus θ).det ^ K * lowerInv_e (∑ i, Λ i * θ i) * lowerInv_e (θ a - θ b) ^ m * ψ m z :=
      fun θ z => by
        rw [hψ_apply, hψ_apply, lowerInv_coeff_scale _ _ _ _ (hrel θ z) m]
    have hwt : IsWtOn (Kset (allPos N)) σ (Λ + (m : ℝ) • root a b) (y : H) := by
      intro θ _
      show σ (torus θ) (y : H) = _
      have key : ∀ z : S, ⟪σ (torus θ) (y : H), (z : H)⟫_ℂ =
          lowerInv_e (∑ i, Λ i * (-θ) i) * lowerInv_e ((-θ) a - (-θ) b) ^ m * ⟪(y : H), (z : H)⟫_ℂ := by
        intro z
        have h1 := hsc (-θ) z
        rw [← hyx, ← hyx, Submodule.coe_inner, Submodule.coe_inner, hPσ _ (lowerInv_torus_mem _),
          inner_smul_right, lowerInv_adj hU, neg_neg, mul_assoc ((torus (-θ)).det ^ K),
          mul_assoc ((torus (-θ)).det ^ K)] at h1
        exact mul_left_cancel₀ (pow_ne_zero _ (lowerInv_det_ne (-θ))) h1
      have hE : lowerInv_e (∑ i, Λ i * (-θ) i) * lowerInv_e ((-θ) a - (-θ) b) ^ m =
          (starRingEnd ℂ) (Complex.exp (((∑ i, (Λ + (m : ℝ) • root a b) i * θ i : ℝ) : ℂ) *
            Complex.I)) := by
        rw [lowerInv_e_mul_pow]
        have := lowerInv_conj_e (∑ i, (Λ + (m : ℝ) • root a b) i * θ i)
        unfold lowerInv_e at this ⊢
        rw [this]
        congr 3
        simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, root, Pi.sub_apply,
          add_mul, Finset.sum_add_distrib, mul_sub, sub_mul, Finset.sum_sub_distrib, Pi.single_apply,
          mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq',
          Finset.mem_univ, if_true, mul_neg, Finset.sum_neg_distrib]
        ring
      set ev := Complex.exp (((∑ i, (Λ + (m : ℝ) • root a b) i * θ i : ℝ) : ℂ) * Complex.I)
      let w : S := ⟨σ (torus θ) (y : H), hstab θ y⟩ - ev • y
      have hw0 : ∀ z : S, ⟪w, z⟫_ℂ = 0 := by
        intro z
        rw [inner_sub_left, inner_smul_left, Submodule.coe_inner, Submodule.coe_inner]
        show ⟪σ (torus θ) (y : H), (z : H)⟫_ℂ - _ = 0
        rw [key, hE, sub_self]
      have hw : w = 0 := inner_self_eq_zero.mp (hw0 w)
      have := congrArg (fun u : S => (u : H)) hw
      simp only [w, Submodule.coe_sub, Submodule.coe_smul, ZeroMemClass.coe_zero] at this
      exact sub_eq_zero.mp this
    by_contra hne
    have hy0 : (y : H) ≠ 0 := by
      intro h0
      apply hne
      ext z
      rw [← hyx, Submodule.coe_inner, h0, inner_zero_left]
      rfl
    exact lowerInv_not_cdom hab hm (hKT.2.2.2.2 _ (y : H) y.2 hy0 hwt)
  have hconst : pp x = Polynomial.C ((pp x).coeff 0) := by
    ext m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [Polynomial.coeff_C, if_neg (by omega)]
      have := LinearMap.congr_fun (hψ m hm) x
      rw [hψ_apply] at this
      simpa using this
  have h0 := hpp x 0
  rw [Matrix.single_zero, add_zero, hP.one, LinearMap.id_apply] at h0
  rw [← hpp, hconst, Polynomial.eval_C]
  rw [hconst, Polynomial.eval_C] at h0
  exact h0

end PI.WMI
