import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLActs
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsBoundPolyMulExp

noncomputable section

open scoped SchwartzMap LineDeriv
open MeasureTheory Complex

namespace PositivityTheory.RL.Fock

section Gauss

open scoped Nat

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_iteratedFDeriv_id_le_one_add (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (id : E → E) x‖ ≤ 1 + ‖x‖ := by
  rcases j with _ | n
  · rw [norm_iteratedFDeriv_zero]; simp
  · rw [← norm_iteratedFDeriv_fderiv,
      show fderiv ℝ (id : E → E) = fun _ => ContinuousLinearMap.id ℝ E from funext fun _ => fderiv_id]
    rcases n with _ | n
    · rw [norm_iteratedFDeriv_zero]
      exact (ContinuousLinearMap.norm_id_le).trans (by linarith [norm_nonneg x])
    · rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]
      simp only [Pi.zero_apply, norm_zero]
      positivity

theorem norm_iteratedFDeriv_diag_le (B : E →L[ℝ] E →L[ℝ] ℝ) (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => B y y) x‖ ≤ ‖B‖ * (2 ^ n * (1 + ‖x‖) ^ 2) := by
  have h := B.norm_iteratedFDeriv_le_of_bilinear (f := id) (g := id) (N := (n : WithTop ℕ∞))
    contDiff_id contDiff_id x le_rfl
  simp only [id] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  calc ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : E => y) x‖ *
        ‖iteratedFDeriv ℝ (n - i) (fun y : E => y) x‖
      ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (1 + ‖x‖) ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [mul_assoc, sq]
        gcongr
        · exact norm_iteratedFDeriv_id_le_one_add i x
        · exact norm_iteratedFDeriv_id_le_one_add (n - i) x
    _ = 2 ^ n * (1 + ‖x‖) ^ 2 := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose n

theorem norm_iteratedFDeriv_rexp (i : ℕ) (y : ℝ) : ‖iteratedFDeriv ℝ i Real.exp y‖ = Real.exp y := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have h := congrFun (iteratedDeriv_exp_const_mul i 1) y
  simp only [one_mul, one_pow] at h
  rw [show (fun s => Real.exp s) = Real.exp from rfl] at h
  rw [h, Real.norm_eq_abs, abs_of_pos (Real.exp_pos y)]

theorem exists_bound_poly_mul_exp (c : ℝ) (hc : 0 < c) (N : ℕ) :
    ∃ C, ∀ r : ℝ, 0 ≤ r → (1 + r) ^ N * Real.exp (-(c * r ^ 2)) ≤ C :=
  _root_.UpperTheory.Reformulated.B.Rc4.exists_bound_poly_mul_exp c hc N

theorem exists_coercive [FiniteDimensional ℝ E] (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ x, x ≠ 0 → B x x < 0) :
    ∃ c > 0, ∀ x, B x x ≤ -(c * ‖x‖ ^ 2) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · refine ⟨1, one_pos, fun x => ?_⟩
    rw [Subsingleton.elim x 0]; simp
  · have hcont : Continuous fun y : E => B y y := (B.continuous.clm_apply continuous_id)
    obtain ⟨x0, hx0, hmax⟩ := (isCompact_sphere (0 : E) 1).exists_isMaxOn
      (NormedSpace.sphere_nonempty.2 zero_le_one) hcont.continuousOn
    have hx0n : ‖x0‖ = 1 := by simpa using hx0
    have hx0ne : x0 ≠ 0 := by intro h; rw [h, norm_zero] at hx0n; exact zero_ne_one hx0n
    refine ⟨-(B x0 x0), by linarith [hB x0 hx0ne], fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx; simp
    · have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
      set u : E := ‖x‖⁻¹ • x with hu
      have hun : u ∈ Metric.sphere (0 : E) 1 := by
        rw [mem_sphere_zero_iff_norm, hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hxn.ne']
      have hxu : x = ‖x‖ • u := by rw [hu, smul_smul, mul_inv_cancel₀ hxn.ne', one_smul]
      have h1 : B u u ≤ B x0 x0 := hmax hun
      have h2 : B x x = ‖x‖ ^ 2 * B u u := by
        conv_lhs => rw [hxu]
        simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]; ring
      rw [h2]
      nlinarith [sq_nonneg ‖x‖]

theorem exists_schwartz_exp_diag [FiniteDimensional ℝ E] (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ x, x ≠ 0 → B x x < 0) :
    ∃ f : SchwartzMap E ℂ, ∀ x, f x = ((Real.exp (B x x) : ℝ) : ℂ) := by
  obtain ⟨c, hc, hBc⟩ := exists_coercive B hB
  have hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : E => B y y) := B.contDiff.clm_apply contDiff_id
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Real.exp ∘ fun y : E => B y y) := Real.contDiff_exp.comp hq
  refine ⟨⟨Complex.ofRealLI ∘ (Real.exp ∘ fun y : E => B y y),
    Complex.ofRealLI.toContinuousLinearMap.contDiff.comp hg, ?_⟩, fun x => rfl⟩
  intro k n
  obtain ⟨C, hC⟩ := exists_bound_poly_mul_exp c hc (k + 2 * n)
  refine ⟨n ! * (2 * (‖B‖ + 1)) ^ n * C, fun x => ?_⟩
  have hn : ((n : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  rw [LinearIsometry.norm_iteratedFDeriv_comp_left _ hg.contDiffAt hn]
  have hfb := norm_iteratedFDeriv_comp_le (g := Real.exp) (f := fun y : E => B y y)
    Real.contDiff_exp hq hn x (C := Real.exp (B x x)) (D := 2 * (‖B‖ + 1) * (1 + ‖x‖) ^ 2)
    (fun i _ => (norm_iteratedFDeriv_rexp i _).le) (fun i hi _ => by
      have hB0 := norm_nonneg B
      have hx0 := norm_nonneg x
      have a1 : ‖B‖ ≤ (‖B‖ + 1) ^ i :=
        le_trans (by linarith) (le_self_pow₀ (by linarith) (by omega))
      have a2 : (1 + ‖x‖) ^ 2 ≤ ((1 + ‖x‖) ^ 2) ^ i :=
        le_self_pow₀ (by nlinarith) (by omega)
      calc ‖iteratedFDeriv ℝ i (fun y : E => B y y) x‖ ≤ ‖B‖ * (2 ^ i * (1 + ‖x‖) ^ 2) :=
            norm_iteratedFDeriv_diag_le B i x
        _ = 2 ^ i * ‖B‖ * (1 + ‖x‖) ^ 2 := by ring
        _ ≤ 2 ^ i * (‖B‖ + 1) ^ i * ((1 + ‖x‖) ^ 2) ^ i := by gcongr
        _ = (2 * (‖B‖ + 1) * (1 + ‖x‖) ^ 2) ^ i := by rw [mul_pow, mul_pow])
  have hx0 := norm_nonneg x
  have hB0 := norm_nonneg B
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (Real.exp ∘ fun y : E => B y y) x‖
      ≤ (1 + ‖x‖) ^ k * (n ! * Real.exp (-(c * ‖x‖ ^ 2)) * (2 * (‖B‖ + 1) * (1 + ‖x‖) ^ 2) ^ n) := by
        gcongr
        · linarith
        · exact hfb.trans (by gcongr; exact hBc x)
    _ = n ! * (2 * (‖B‖ + 1)) ^ n * ((1 + ‖x‖) ^ (k + 2 * n) * Real.exp (-(c * ‖x‖ ^ 2))) := by
        rw [show (2 * (‖B‖ + 1) * (1 + ‖x‖) ^ 2) ^ n = (2 * (‖B‖ + 1)) ^ n * (1 + ‖x‖) ^ (2 * n) by
          rw [mul_pow, pow_mul], pow_add]; ring
    _ ≤ n ! * (2 * (‖B‖ + 1)) ^ n * C := by gcongr; exact hC ‖x‖ hx0

theorem cos_temperate : Real.cos.HasTemperateGrowth :=
  ⟨Real.contDiff_cos, fun n => ⟨0, 1, fun t => by
    simpa [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using Real.abs_iteratedDeriv_cos_le_one n t⟩⟩

theorem sin_temperate : Real.sin.HasTemperateGrowth :=
  ⟨Real.contDiff_sin, fun n => ⟨0, 1, fun t => by
    simpa [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using Real.abs_iteratedDeriv_sin_le_one n t⟩⟩

theorem cis_temperate : Function.HasTemperateGrowth (fun t : ℝ => cexp (I * t)) := by
  have e : (fun t : ℝ => cexp (I * t)) = (ofReal ∘ Real.cos) + (ofReal ∘ Real.sin) * fun _ => I := by
    funext t
    simp [mul_comm I, exp_mul_I]
  rw [e]
  exact (Function.Complex.hasTemperateGrowth_ofReal.comp cos_temperate).add
    ((Function.Complex.hasTemperateGrowth_ofReal.comp sin_temperate).mul (Function.HasTemperateGrowth.const I))

theorem exists_schwartz_cexp [FiniteDimensional ℝ E] (B B' : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ x, x ≠ 0 → B x x < 0) :
    ∃ f : SchwartzMap E ℂ, ∀ x, f x = cexp ((B x x : ℝ) + I * (B' x x : ℝ)) := by
  obtain ⟨f, hf⟩ := exists_schwartz_exp_diag B hB
  have hq : (fun x => B' x x).HasTemperateGrowth := by
    have := B'.bilinear_hasTemperateGrowth (Function.HasTemperateGrowth.id (E := E)) (Function.HasTemperateGrowth.id (E := E))
    exact this
  have ht : (fun x => cexp (I * (B' x x : ℝ))).HasTemperateGrowth := cis_temperate.comp hq
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun x => cexp (I * (B' x x : ℝ))) f, fun x => ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply_apply ht, hf, Complex.exp_add, ofReal_exp, smul_eq_mul, mul_comm]

end Gauss

section Alg

open MvPolynomial

variable {L : Type} {S : Type} [AddCommGroup S] [Module ℂ S]

theorem eq_zero_of_stable (K : Submodule ℂ (MvPolynomial L ℂ)) (hK : ∀ l, ∀ P ∈ K, pderiv l P ∈ K)
    (hC : ∀ a : ℂ, C a ∈ K → a = 0) (n : ℕ) : ∀ P ∈ K, (∀ α, coeff α P ≠ 0 → α.degree < n) → P = 0 := by
  classical
  induction n with
  | zero => exact fun P _ h => MvPolynomial.ext _ _ fun α => by simpa using h α
  | succ n ih =>
    intro P hP h
    have h1 : ∀ l, pderiv l P = 0 := fun l => ih _ (hK l P hP) fun α hα => by
      rw [coeff_pderiv] at hα
      have := h _ (left_ne_zero_of_mul hα)
      simp only [map_add, Finsupp.degree_single] at this
      omega
    have h2 : P = C (coeff 0 P) := by
      refine MvPolynomial.ext _ _ fun α => ?_
      rw [coeff_C]
      split_ifs with h0
      · rw [h0]
      · obtain ⟨l, hl⟩ := Finsupp.ne_iff.1 (Ne.symm h0)
        have h3 := congrArg (coeff (α - Finsupp.single l 1)) (h1 l)
        rw [coeff_pderiv, Finsupp.sub_add_single_one_cancel hl, coeff_zero] at h3
        exact (mul_eq_zero.1 h3).resolve_right (Nat.cast_add_one_ne_zero _)
    rw [h2] at hP
    rw [h2, hC _ hP, map_zero]

theorem exists_fock [DecidableEq L] (Z d : L → Module.End ℂ S) (hZ : ∀ l l', Z l * Z l' = Z l' * Z l)
    (hd : ∀ l l', d l * Z l' = Z l' * d l + if l = l' then 1 else 0) (G : S) (hG : G ≠ 0) (h0 : ∀ l, d l G = 0) :
    ∃ φ : MvPolynomial L ℂ →ₗ[ℂ] S, Function.Injective φ ∧ (∀ l P, φ (X l * P) = Z l (φ P)) ∧
      ∀ l P, φ (pderiv l P) = d l (φ P) := by
  have hc : ∀ a ∈ Set.range Z, ∀ b ∈ Set.range Z, a * b = b * a := by
    rintro _ ⟨l, rfl⟩ _ ⟨l', rfl⟩
    exact hZ l l'
  letI : CommRing (Algebra.adjoin ℂ (Set.range Z)) := Algebra.adjoinCommRingOfComm ℂ hc
  let e : MvPolynomial L ℂ →ₐ[ℂ] Module.End ℂ S := (Algebra.adjoin ℂ (Set.range Z)).val.comp
    (aeval fun l => (⟨Z l, Algebra.subset_adjoin ⟨l, rfl⟩⟩ : Algebra.adjoin ℂ (Set.range Z)))
  have he : ∀ l, e (X l) = Z l := fun l => by simp [e]
  let φ : MvPolynomial L ℂ →ₗ[ℂ] S := (LinearMap.applyₗ G).comp e.toLinearMap
  have hφ : ∀ P, φ P = e P G := fun P => rfl
  have hX : ∀ l P, φ (X l * P) = Z l (φ P) := fun l P => by rw [hφ, hφ, map_mul, he]; rfl
  have hCa : ∀ a : ℂ, φ (C a) = a • G := fun a => by
    rw [hφ, ← algebraMap_eq, AlgHom.commutes]; rfl
  have hp : ∀ l P, φ (pderiv l P) = d l (φ P) := fun l P => by
    induction P using MvPolynomial.induction_on with
    | C a => rw [pderiv_C, map_zero, hCa, map_smul, h0, smul_zero]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p j hp =>
      rw [mul_comm p, hX, pderiv_mul, map_add, hX, hp, ← Module.End.mul_apply (d l), hd, add_comm]
      by_cases h : l = j
      · subst h; simp
      · simp [h, pderiv_X_of_ne (Ne.symm h)]
  refine ⟨φ, ?_, hX, hp⟩
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro P hP
  refine eq_zero_of_stable (LinearMap.ker φ) (fun l P hP => ?_) (fun a ha => ?_) (P.totalDegree + 1) P hP fun α hα => ?_
  · rw [LinearMap.mem_ker] at hP ⊢
    rw [hp, hP, map_zero]
  · rw [LinearMap.mem_ker, hCa] at ha
    exact (smul_eq_zero.1 ha).resolve_right hG
  · exact Nat.lt_succ_of_le (le_totalDegree (mem_support_iff.2 hα))

def hop [Fintype L] (c : L → ℂ) : Module.End ℂ (MvPolynomial L ℂ) :=
  ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) • ∑ l, (c l • LinearMap.mulLeft ℂ (X l) - star (c l) • (pderiv l).toLinearMap)

theorem hop_one [Fintype L] (c : L → ℂ) : hop (I • c) 1 = I • hop c 1 := by
  simp [hop, LinearMap.sum_apply, Finset.smul_sum, smul_smul, mul_left_comm]

end Alg

section Tens

open MvPolynomial
open scoped TensorProduct

variable (W N : Type) [Fintype W] [DecidableEq W]

def iota : (⨂[ℂ] _ : W, MvPolynomial N ℂ) →ₐ[ℂ] MvPolynomial (W × N) ℂ :=
  PiTensorProduct.liftAlgHom ((MultilinearMap.mkPiAlgebra ℂ W (MvPolynomial (W × N) ℂ)).compLinearMap
    fun w => (rename (Prod.mk w)).toLinearMap) (by simp) (fun x y => by simp [Finset.prod_mul_distrib])

variable {W N}

theorem iota_tprod (P : W → MvPolynomial N ℂ) : iota W N (PiTensorProduct.tprod ℂ P) = ∏ w, rename (Prod.mk w) (P w) := by
  exact (PiTensorProduct.lift.tprod P).trans (by simp)

theorem iota_update (P : W → MvPolynomial N ℂ) (w : W) (p : MvPolynomial N ℂ) :
    iota W N (PiTensorProduct.tprod ℂ (Function.update P w p)) =
      rename (Prod.mk w) p * ∏ w' ∈ Finset.univ.erase w, rename (Prod.mk w') (P w') := by
  rw [iota_tprod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ w), Function.update_self]
  congr 1
  exact Finset.prod_congr rfl fun w' hw' => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hw')]

theorem iota_injective : Function.Injective (iota W N) := by
  let j : MvPolynomial (W × N) ℂ →ₐ[ℂ] (⨂[ℂ] _ : W, MvPolynomial N ℂ) :=
    aeval fun p => PiTensorProduct.singleAlgHom (R := ℂ) (A := fun _ : W => MvPolynomial N ℂ) p.1 (X p.2)
  have h : j.comp (iota W N) = AlgHom.id _ _ := by
    refine PiTensorProduct.algHom_ext fun w => MvPolynomial.algHom_ext fun l => ?_
    have : iota W N (PiTensorProduct.singleAlgHom (R := ℂ) (A := fun _ : W => MvPolynomial N ℂ) w (X l)) = X (w, l) := by
      rw [PiTensorProduct.singleAlgHom_apply, MonoidHom.mulSingle_apply, Pi.mulSingle, iota_update]
      simp
    simp only [AlgHom.comp_apply, this, AlgHom.id_apply, j, aeval_X]
  exact Function.LeftInverse.injective (g := j) fun T => AlgHom.congr_fun h T

theorem pderiv_rename_ne {w w' : W} (h : w' ≠ w) (l : N) (p : MvPolynomial N ℂ) :
    pderiv (w, l) (rename (Prod.mk w') p) = 0 := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
    rw [map_mul, pderiv_mul, hp, rename_X, pderiv_X_of_ne (fun e => h (congrArg Prod.fst e))]
    simp

theorem pderiv_rest (P : W → MvPolynomial N ℂ) (w : W) (l : N) :
    pderiv (w, l) (∏ w' ∈ Finset.univ.erase w, rename (Prod.mk w') (P w')) = 0 := by
  refine Finset.prod_induction _ (fun q => pderiv (w, l) q = 0) (fun a b ha hb => ?_) pderiv_one fun w' hw' =>
    pderiv_rename_ne (Finset.ne_of_mem_erase hw') l _
  rw [pderiv_mul, ha, hb]
  simp

theorem iota_hop [Fintype N] (P : W → MvPolynomial N ℂ) (c : W × N → ℂ) :
    ∑ w, iota W N (PiTensorProduct.tprod ℂ (Function.update P w (hop (fun l => c (w, l)) (P w)))) =
      hop c (iota W N (PiTensorProduct.tprod ℂ P)) := by
  have h : ∀ w, iota W N (PiTensorProduct.tprod ℂ P) =
      rename (Prod.mk w) (P w) * ∏ w' ∈ Finset.univ.erase w, rename (Prod.mk w') (P w') := fun w => by
    rw [← iota_update, Function.update_eq_self]
  simp only [iota_update, hop, LinearMap.smul_apply, LinearMap.sum_apply, Fintype.sum_prod_type, map_smul, map_sum,
    smul_mul_assoc, Finset.sum_mul, ← Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun l _ => ?_
  rw [h w]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe, map_sub, map_smul,
    map_mul, rename_X, pderiv_mul, pderiv_rest, pderiv_rename (Prod.mk_right_injective w), sub_mul, smul_mul_assoc,
    mul_assoc, mul_zero, add_zero]

end Tens

structure Heis (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (L : Type) [Fintype L] where
  v : (L → ℂ) →ₗ[ℝ] V
  lam : (L → ℂ) →ₗ[ℝ] (V →L[ℝ] ℝ)
  D : (L → ℂ) → (𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ))
  hD : ∀ c f x, D c f x = fderiv ℝ f x (v c) - 2 * Real.pi * I * (lam c x : ℝ) * f x
  form : ∀ c c', lam c' (v c) - lam c (v c') = -2 * (∑ l, c l * star (c' l)).im
  dim : Module.finrank ℝ V ≤ Module.finrank ℝ (LinearMap.ker v)

namespace Heis

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {L : Type} [Fintype L] (H : Heis V L)

theorem D_add (c c' : L → ℂ) (f : 𝓢(V, ℂ)) : H.D (c + c') f = H.D c f + H.D c' f := by
  ext x
  simp only [SchwartzMap.add_apply, H.hD, map_add, ContinuousLinearMap.add_apply]
  push_cast
  ring

theorem D_smul (t : ℝ) (c : L → ℂ) (f : 𝓢(V, ℂ)) : H.D (t • c) f = (t : ℂ) • H.D c f := by
  ext x
  simp only [SchwartzMap.smul_apply, H.hD, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, real_smul]
  push_cast
  ring

def Dl : (L → ℂ) →ₗ[ℝ] Module.End ℂ 𝓢(V, ℂ) where
  toFun c := (H.D c).toLinearMap
  map_add' c c' := LinearMap.ext fun f => H.D_add c c' f
  map_smul' t c := LinearMap.ext fun f => by
    simp only [ContinuousLinearMap.coe_coe, H.D_smul, RingHom.id_apply, LinearMap.smul_apply]
    exact algebraMap_smul ℂ t _

theorem fderiv_D (c : L → ℂ) (f : 𝓢(V, ℂ)) (x y : V) :
    fderiv ℝ (H.D c f) x y = fderiv ℝ (fderiv ℝ f) x y (H.v c) -
      2 * Real.pi * I * ((H.lam c y : ℝ) * f x + (H.lam c x : ℝ) * fderiv ℝ f x y) := by
  have e : (H.D c f : V → ℂ) = fun x => fderiv ℝ f x (H.v c) - 2 * Real.pi * I * (((H.lam c x : ℝ) : ℂ) * f x) := by
    funext x; rw [H.hD]; ring
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((f.smooth 2).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  have h1 : HasFDerivAt (fun x => fderiv ℝ f x (H.v c)) ((fderiv ℝ (fderiv ℝ f) x).flip (H.v c)) x := by
    simpa using hd.hasFDerivAt.clm_apply (hasFDerivAt_const (H.v c) x)
  have h2 : HasFDerivAt (fun x => ((H.lam c x : ℝ) : ℂ)) (ofRealCLM.comp (H.lam c)) x :=
    (ofRealCLM.comp (H.lam c)).hasFDerivAt
  have h3 := h1.fun_sub ((h2.fun_mul (f.hasFDerivAt x)).const_mul (2 * Real.pi * I))
  rw [e, h3.fderiv]
  simp
  ring

theorem ccr (c c' : L → ℂ) (f : 𝓢(V, ℂ)) :
    H.D c (H.D c' f) = H.D c' (H.D c f) + (4 * Real.pi * I * (∑ l, c l * star (c' l)).im) • f := by
  ext x
  have hs : fderiv ℝ (fderiv ℝ f) x (H.v c) (H.v c') = fderiv ℝ (fderiv ℝ f) x (H.v c') (H.v c) :=
    ((f.smooth 2).contDiffAt.isSymmSndFDerivAt (by simp)).eq _ _
  have hf := congrArg (fun t : ℝ => (t : ℂ)) (H.form c c')
  simp only [ofReal_sub, ofReal_mul, ofReal_neg, ofReal_ofNat] at hf
  rw [SchwartzMap.add_apply, SchwartzMap.smul_apply, H.hD c, H.hD c' (H.D c f), fderiv_D, fderiv_D, H.hD, H.hD, hs, smul_eq_mul]
  linear_combination (-2 * Real.pi * I * f x) * hf

theorem sum_self_im (c : L → ℂ) : (∑ l, c l * star ((I • c) l)).im = -∑ l, normSq (c l) := by
  rw [im_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [normSq_apply]

theorem sum_normSq_pos {c : L → ℂ} (hc : c ≠ 0) : 0 < ∑ l, normSq (c l) := by
  obtain ⟨l, hl⟩ := Function.ne_iff.1 hc
  exact Finset.sum_pos' (fun _ _ => normSq_nonneg _) ⟨l, Finset.mem_univ _, normSq_pos.2 hl⟩

section L2

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]

def sq2 : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := (ContinuousLinearMap.mul ℝ ℂ).comp (conjCLE : ℂ →L[ℝ] ℂ)

theorem sq2_apply (a b : ℂ) : sq2 a b = star a * b := rfl

theorem integrable_ip (f g : 𝓢(V, ℂ)) : Integrable (fun x => star (f x) * g x) μ :=
  (SchwartzMap.bilinLeftCLM sq2 g.hasTemperateGrowth f).integrable

theorem skew (c : L → ℂ) (f g : 𝓢(V, ℂ)) :
    ∫ x, star (f x) * H.D c g x ∂μ = -∫ x, star (H.D c f x) * g x ∂μ := by
  have h1 := SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left (μ := μ) f g sq2 (H.v c)
  simp only [sq2_apply] at h1
  have h2 : ∀ x, star (f x) * H.D c g x + star (H.D c f x) * g x =
      star (f x) * (∂_{H.v c} g : 𝓢(V, ℂ)) x + star ((∂_{H.v c} f : 𝓢(V, ℂ)) x) * g x := fun x => by
    simp only [H.hD, SchwartzMap.lineDerivOp_apply_eq_fderiv, star_sub, star_mul', star_def, conj_ofReal, conj_I, map_ofNat]
    ring
  rw [eq_neg_iff_add_eq_zero, ← integral_add (integrable_ip μ _ _) (integrable_ip μ _ _)] at h1 ⊢
  simp only [h2, h1]

theorem ip_self (f : 𝓢(V, ℂ)) : ∫ x, star (f x) * f x ∂μ = ((∫ x, normSq (f x) ∂μ : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  congr 1
  funext x
  rw [normSq_eq_conj_mul_self, star_def]

theorem eq_zero_of_ip (f : 𝓢(V, ℂ)) (h : ∫ x, normSq (f x) ∂μ ≤ 0) : f = 0 := by
  have hi : Integrable (fun x => normSq (f x)) μ := by
    refine (integrable_ip μ f f).re.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [normSq_apply]
  have hc : Continuous fun x => normSq (f x) := continuous_normSq.comp f.continuous
  by_contra hne
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hne (SchwartzMap.ext hh)
  have := integral_pos_of_integrable_nonneg_nonzero (μ := μ) hc hi (fun x => normSq_nonneg _) (normSq_pos.2 hx).ne'
  linarith

end L2

variable [FiniteDimensional ℝ V]

theorem eq_zero_of_neg {c : L → ℂ} (hc : c ≠ 0) {f : 𝓢(V, ℂ)} (h : H.D (I • c) f = (-I) • H.D c f) : f = 0 := by
  borelize V
  let μ : Measure V := Measure.addHaar
  have h1 := congrArg (fun g : 𝓢(V, ℂ) => ∫ x, star (f x) * g x ∂μ) (H.ccr c (I • c) f)
  simp only [SchwartzMap.add_apply, mul_add] at h1
  rw [integral_add (integrable_ip μ _ _) (integrable_ip μ _ _), H.skew μ c f, H.skew μ (I • c) f, h, sum_self_im] at h1
  have k1 : ∀ (z : ℂ) (g : 𝓢(V, ℂ)), ∫ x, star (g x) * (z • g) x ∂μ = z * ((∫ x, normSq (g x) ∂μ : ℝ) : ℂ) := fun z g => by
    rw [← ip_self, ← integral_const_mul]
    congr 1; funext x; rw [smul_apply, smul_eq_mul]; ring
  have k2 : ∀ (g : 𝓢(V, ℂ)), ∫ x, star (((-I) • g) x) * g x ∂μ = I * ((∫ x, normSq (g x) ∂μ : ℝ) : ℂ) := fun g => by
    rw [← ip_self, ← integral_const_mul]
    congr 1; funext x; simp; ring
  rw [k1, k1, k2] at h1
  refine eq_zero_of_ip μ f ?_
  have hp := sum_normSq_pos hc
  have hn : 0 ≤ ∫ x, normSq (H.D c f x) ∂μ := integral_nonneg fun x => normSq_nonneg _
  have h2 := congrArg im h1
  simp at h2
  have := Real.pi_pos
  by_contra hh
  push Not at hh
  have : 0 < Real.pi * (∑ l, normSq (c l)) * ∫ x, normSq (f x) ∂μ := by positivity
  nlinarith

end Heis

namespace Heis

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {L : Type} [Fintype L] (H : Heis V L) [FiniteDimensional ℝ V]

def Vac (f : 𝓢(V, ℂ)) : Prop := ∀ c, H.D (I • c) f = I • H.D c f

def mulI (L : Type) : (L → ℂ) →ₗ[ℝ] (L → ℂ) := (I • LinearMap.id : (L → ℂ) →ₗ[ℂ] (L → ℂ)).restrictScalars ℝ

theorem lam_neg {k : L → ℂ} (h0 : H.v k = 0) (hk : k ≠ 0) : H.lam k (H.v (I • k)) < 0 := by
  have h := H.form k (I • k)
  rw [h0, map_zero, sum_self_im] at h
  linarith [sum_normSq_pos hk]

theorem exists_sec : ∃ s : V →L[ℝ] (L → ℂ), (∀ y, H.v (s y) = 0) ∧ (∀ y, H.v (I • s y) = y) ∧
    ∀ k, H.v k = 0 → s (H.v (I • k)) = k := by
  let T : LinearMap.ker H.v →ₗ[ℝ] V := (H.v.comp (mulI L)).comp (LinearMap.ker H.v).subtype
  have hT : ∀ k, T k = H.v (I • k.1) := fun k => rfl
  have hi : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro k hk
    by_contra hne
    have := H.lam_neg k.2 (fun e => hne (Subtype.ext e))
    rw [← hT, hk, map_zero] at this
    exact lt_irrefl _ this
  have hd : Module.finrank ℝ (LinearMap.ker H.v) = Module.finrank ℝ V :=
    le_antisymm (LinearMap.finrank_le_finrank_of_injective hi) H.dim
  let e := LinearMap.linearEquivOfInjective T hi hd
  refine ⟨LinearMap.toContinuousLinearMap ((LinearMap.ker H.v).subtype.comp e.symm.toLinearMap),
    fun y => (e.symm y).2, fun y => e.apply_symm_apply y, fun k hk => ?_⟩
  exact congrArg Subtype.val (e.symm_apply_apply ⟨k, hk⟩)

variable {H}

theorem vac_iff {s : V →L[ℝ] (L → ℂ)} (h0 : ∀ y, H.v (s y) = 0) (h1 : ∀ y, H.v (I • s y) = y)
    (h2 : ∀ k, H.v k = 0 → s (H.v (I • k)) = k) (f : 𝓢(V, ℂ)) :
    H.Vac f ↔ ∀ x y, fderiv ℝ f x y = 2 * Real.pi * ((H.lam (s y) x : ℝ) + I * (H.lam (I • s y) x : ℝ)) * f x := by
  constructor
  · intro h x y
    have e := congrArg (fun g : 𝓢(V, ℂ) => g x) (h (s y))
    simp only [smul_apply, H.hD, h0, h1, map_zero, smul_eq_mul] at e
    linear_combination e + (-2 * Real.pi * (H.lam (s y) x : ℝ) * f x) * I_mul_I
  · intro h c
    ext x
    have hII : ∀ k : L → ℂ, I • I • k = -k := fun k => by rw [smul_smul, I_mul_I, neg_one_smul]
    have e1 : s (H.v (I • c)) = c - I • s (H.v c) := by
      rw [← h2 (c - I • s (H.v c)) (by rw [map_sub, h1, sub_self]), smul_sub, hII, map_sub, map_neg, h0]
      simp
    simp only [smul_apply, H.hD, h, e1, smul_sub, hII, map_sub, map_neg, sub_apply, neg_apply, smul_eq_mul]
    push_cast
    linear_combination (2 * Real.pi * f x * ((H.lam c x : ℝ) - (H.lam (I • s (H.v c)) x : ℝ))) * I_mul_I

variable (H)

theorem exists_vac : ∃ G : 𝓢(V, ℂ), G ≠ 0 ∧ H.Vac G ∧ ∀ f, H.Vac f → ∃ z : ℂ, f = z • G := by
  obtain ⟨s, h0, h1, h2⟩ := H.exists_sec
  let B : V →L[ℝ] V →L[ℝ] ℝ := Real.pi • (LinearMap.toContinuousLinearMap H.lam).comp s
  let B' : V →L[ℝ] V →L[ℝ] ℝ := Real.pi • (LinearMap.toContinuousLinearMap (H.lam.comp (mulI L))).comp s
  have hB : ∀ x y, B x y = Real.pi * H.lam (s x) y := fun x y => rfl
  have hB' : ∀ x y, B' x y = Real.pi * H.lam (I • s x) y := fun x y => rfl
  have s1 : ∀ x y, H.lam (s x) y = H.lam (s y) x := fun x y => by
    have a := H.form (I • s y) (s x)
    have b := H.form (I • s x) (s y)
    rw [h0, map_zero, h1, sub_zero] at a b
    rw [a, b, im_sum, im_sum]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    simp
    ring
  have s2 : ∀ x y, H.lam (I • s x) y = H.lam (I • s y) x := fun x y => by
    have a := H.form (I • s y) (I • s x)
    have b := H.form (s y) (s x)
    rw [h1, h1] at a
    rw [h0, h0, map_zero, map_zero, sub_zero] at b
    rw [← sub_eq_zero, a, b, im_sum, im_sum]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    simp
  obtain ⟨G, hG⟩ := exists_schwartz_cexp B B' fun x hx => by
    have hs : s x ≠ 0 := fun e => hx (by rw [← h1 x, e, smul_zero, map_zero])
    have := H.lam_neg (h0 x) hs
    rw [h1] at this
    rw [hB]
    exact mul_neg_of_pos_of_neg Real.pi_pos this
  have hq : ∀ x, ∃ q : V →L[ℝ] ℂ, HasFDerivAt (fun x => ((B x x : ℝ) : ℂ) + I * (B' x x : ℝ)) q x ∧
      ∀ y, q y = 2 * Real.pi * ((H.lam (s y) x : ℝ) + I * (H.lam (I • s y) x : ℝ)) := fun x => by
    have a := ofRealCLM.hasFDerivAt.comp x (B.hasFDerivAt.clm_apply (hasFDerivAt_id x))
    have b := ofRealCLM.hasFDerivAt.comp x (B'.hasFDerivAt.clm_apply (hasFDerivAt_id x))
    refine ⟨_, a.fun_add (b.const_mul I), fun y => ?_⟩
    simp [hB, hB', s1 x y, s2 x y]
    ring
  have hGf : (G : V → ℂ) = fun x => cexp (((B x x : ℝ) : ℂ) + I * (B' x x : ℝ)) := funext hG
  refine ⟨G, fun e => ?_, (vac_iff h0 h1 h2 G).2 fun x y => ?_, fun f hf => ?_⟩
  · have := hG 0
    rw [e] at this
    exact Complex.exp_ne_zero _ this.symm
  · obtain ⟨q, a, b⟩ := hq x
    rw [hGf, a.cexp.fderiv, ← b]
    simp [mul_comm]
  · rw [vac_iff h0 h1 h2] at hf
    have hd : ∀ x, HasFDerivAt (fun x => f x * cexp (-(((B x x : ℝ) : ℂ) + I * (B' x x : ℝ)))) (0 : V →L[ℝ] ℂ) x := fun x => by
      obtain ⟨q, a, b⟩ := hq x
      refine ((f.hasFDerivAt x).fun_mul a.fun_neg.cexp).congr_fderiv ?_
      ext y
      simp [hf, ← b]
      ring
    have hc := is_const_of_fderiv_eq_zero (𝕜 := ℝ) (fun x => (hd x).differentiableAt) (fun x => (hd x).fderiv)
    refine ⟨f 0 * cexp (-(((B 0 0 : ℝ) : ℂ) + I * (B' 0 0 : ℝ))), ?_⟩
    ext x
    rw [smul_apply, hG, ← hc x 0, smul_eq_mul, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

theorem vac_unique {f g : 𝓢(V, ℂ)} (hf : H.Vac f) (hg : H.Vac g) (h0 : g ≠ 0) : ∃ z : ℂ, f = z • g := by
  obtain ⟨G, -, -, h⟩ := H.exists_vac
  obtain ⟨a, rfl⟩ := h f hf
  obtain ⟨b, rfl⟩ := h g hg
  have hb : b ≠ 0 := fun e => h0 (by rw [e, zero_smul])
  exact ⟨a / b, by rw [smul_smul, div_mul_cancel₀ _ hb]⟩

theorem exists_fockMap : ∃ φ : MvPolynomial L ℂ →ₗ[ℂ] 𝓢(V, ℂ), Function.Injective φ ∧ ∀ c P, H.D c (φ P) = φ (hop c P) := by
  classical
  obtain ⟨G, hG, hv, -⟩ := H.exists_vac
  set r : ℂ := ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) with hr
  have hr2 : r * r = 2 * Real.pi := by
    rw [hr, ← ofReal_mul, Real.mul_self_sqrt (by positivity)]; push_cast; ring
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hr0 : r ≠ 0 := fun e => by rw [e, mul_zero] at hr2; exact mul_ne_zero two_ne_zero hpi hr2.symm
  let a : L → Module.End ℂ 𝓢(V, ℂ) := fun l => H.Dl (Pi.single l 1)
  let b : L → Module.End ℂ 𝓢(V, ℂ) := fun l => H.Dl (I • Pi.single l 1)
  have hc : ∀ c c', H.Dl c * H.Dl c' = H.Dl c' * H.Dl c + (4 * Real.pi * I * (∑ l, c l * star (c' l)).im : ℂ) • 1 :=
    fun c c' => LinearMap.ext fun f => H.ccr c c' f
  have haa : ∀ l l', a l * a l' = a l' * a l := fun l l' => by
    rw [hc]; by_cases h : l = l' <;> simp [Pi.single_apply, h, @eq_comm _ l' l, a]
  have hbb : ∀ l l', b l * b l' = b l' * b l := fun l l' => by
    rw [hc]; by_cases h : l = l' <;> simp [Pi.single_apply, h, @eq_comm _ l' l, b]
  have hab : ∀ l l', a l * b l' = b l' * a l + (-4 * Real.pi * I * if l = l' then 1 else 0 : ℂ) • 1 := fun l l' => by
    rw [hc]; by_cases h : l = l' <;> simp [Pi.single_apply, h, @eq_comm _ l' l, a, b]
  have hba : ∀ l l', b l * a l' = a l' * b l + (4 * Real.pi * I * if l = l' then 1 else 0 : ℂ) • 1 := fun l l' => by
    rw [hc]; by_cases h : l = l' <;> simp [Pi.single_apply, h, @eq_comm _ l' l, a, b]
  obtain ⟨φ, h1, h2, h3⟩ := exists_fock (fun l => (2 * r)⁻¹ • (a l - I • b l)) (fun l => (2 * r)⁻¹ • (-a l - I • b l))
    (fun l l' => by
      simp only [smul_mul_smul_comm, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm]
      rw [haa l l', hbb l l', hab l l', hba l l']
      module)
    (fun l l' => by
      have e : (if l = l' then 1 else 0 : Module.End ℂ 𝓢(V, ℂ)) =
          ((2 * r)⁻¹ * (2 * r)⁻¹ * (-8 * Real.pi * (I * I) * if l = l' then 1 else 0)) • 1 := by
        rw [I_mul_I]
        split_ifs
        · rw [show (2 * r)⁻¹ * (2 * r)⁻¹ * (-8 * Real.pi * -1 * 1) = 1 by
            field_simp; linear_combination (-4) * hr2, one_smul]
        · simp
      rw [e]
      simp only [smul_mul_smul_comm, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, neg_mul, mul_neg]
      rw [haa l l', hbb l l', hab l l', hba l l']
      module)
    G hG (fun l => by
      have e : b l G = I • a l G := hv _
      simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.neg_apply, e, smul_smul, I_mul_I]
      simp)
  refine ⟨φ, h1, fun c P => ?_⟩
  have e : c = ∑ l, ((c l).re • (Pi.single l 1 : L → ℂ) + (c l).im • I • (Pi.single l 1 : L → ℂ)) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply, Finset.sum_add_distrib]
  have e2 : H.Dl c = ∑ l, (((c l).re : ℂ) • a l + ((c l).im : ℂ) • b l) := by
    conv_lhs => rw [e]
    simp only [map_sum, map_add, map_smul, coe_smul, a, b]
  change H.Dl c (φ P) = _
  rw [e2]
  simp only [hop, ← hr, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.sub_apply, LinearMap.add_apply, map_smul, map_sum,
    map_sub, LinearMap.mulLeft_apply, Derivation.coeFn_coe, h2, h3, Finset.smul_sum, LinearMap.neg_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  have e3 : c l = (c l).re + (c l).im * I := (re_add_im _).symm
  have e4 : star (c l) = (c l).re - (c l).im * I := by apply Complex.ext <;> simp
  have e5 : r * (2 * r)⁻¹ = 1 / 2 := by field_simp
  generalize ((c l).re : ℂ) = x, ((c l).im : ℂ) = y at e3 e4 ⊢
  rw [e4, e3]
  match_scalars
  · linear_combination (-2 * x) * e5
  · linear_combination (-2 * y) * e5 + (2 * y * r * (2 * r)⁻¹) * I_mul_I

end Heis

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

section Frame

variable {R S : ℕ} {β : Type} [Fintype β] [DecidableEq β]

theorem Jm_eq : Jm R S = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) fun _ => -1) := by
  have h : Jm R S = Matrix.fromBlocks 1 0 0 (-1) := rfl
  rw [h, ← Matrix.fromBlocks_diagonal, Matrix.diagonal_one, ← Matrix.diagonal_neg, Matrix.diagonal_one]

theorem Jm_mul_self : Jm R S * Jm R S = 1 := by
  rw [Jm_eq, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  rcases a with a | a <;> simp

theorem map_star_mul {l m n : Type} [Fintype m] (A : Matrix l m ℂ) (B : Matrix m n ℂ) :
    (A * B).map star = A.map star * B.map star := Matrix.map_mul (f := starRingEnd ℂ)

theorem frame_inv {M : Matrix β β ℂ} {C : Matrix β (Ix R S) ℂ} (h : IsFrame M C) :
    ∃ C' : Matrix (Ix R S) β ℂ, C * C' = 1 ∧ C' * C = 1 := by
  obtain ⟨h1, C', h2⟩ := h
  refine ⟨C', h2, ?_⟩
  have h3 : (M * C.map star * Jm R S)ᵀ * C = 1 := by
    have : Cᵀ * (M * C.map star * Jm R S) = 1 := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Jm_mul_self]
    rw [← Matrix.transpose_one, ← this, Matrix.transpose_mul Cᵀ, Matrix.transpose_transpose]
  have h4 : C' = (M * C.map star * Jm R S)ᵀ := by
    rw [← Matrix.one_mul C', ← h3, Matrix.mul_assoc, h2, Matrix.mul_one]
  rw [h4, h3]

end Frame

section Adele

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_moved {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ β : E, σ β ≠ β := by
  by_contra hne
  push Not at hne
  have := h.2.1
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
  rw [ComplexEmbedding.isReal_iff]
  ext y
  have := h.2.2.2 τ y
  rw [hne y] at this
  simpa using this.symm

theorem im_ne_zero {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {β : E} (hβ : σ β ≠ β) (τ : E →+* ℂ) : (τ β).im ≠ 0 := by
  intro h0
  apply hβ
  apply τ.injective
  rw [h.2.2.2 τ β]
  exact Complex.conj_eq_iff_im.2 h0

theorem exists_basis {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {β : E} (hβ : σ β ≠ β) :
    ∃ B : Module.Basis (Fin 2) F E, B 0 = 1 ∧ B 1 = β := by
  have hfin : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [h.2.2.1]; omega)
  have hli : LinearIndependent F ![(1 : E), β] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      by_contra ht
      apply hβ
      have e : β = algebraMap F E (-(s / t)) := by
        have ht' : algebraMap F E t ≠ 0 := by simpa using ht
        rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
        rw [map_neg, map_div₀]
        field_simp
        linear_combination hst
      rw [e, AlgHom.commutes]
    subst ht
    simpa using hst
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by simp [h.2.2.1]), ?_, ?_⟩ <;> simp

omit [NumberField E] in
theorem eq_add_tmul (B : Module.Basis (Fin 2) F E) (x : AF F ⊗[F] E) :
    x = (Algebra.TensorProduct.basis (AF F) B).repr x 0 ⊗ₜ[F] B 0 +
      (Algebra.TensorProduct.basis (AF F) B).repr x 1 ⊗ₜ[F] B 1 := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (AF F) B).sum_repr x]
  simp [Fin.sum_univ_two, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']

omit [NumberField E] in
theorem piInf_tmul {w : InfinitePlace F} (τ : EmbOver E w) (a : AF F) (y : E) :
    piInf τ (a ⊗ₜ[F] y) = InfinitePlace.Completion.extensionEmbedding w (a.1 w) * τ.1 y := rfl

omit [NumberField F] in
theorem im_extension (hF : IsTotallyReal F) (w : InfinitePlace F) (z : w.Completion) :
    (InfinitePlace.Completion.extensionEmbedding w z).im = 0 := by
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w) z]
  exact Complex.ofReal_im _

theorem piInf_cA {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (z : AE F E) :
    piInf τ (cA σ z) = star (piInf τ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb, star_add]
  | tmul a e =>
    show piInf τ (a ⊗ₜ[F] σ e) = _
    rw [piInf_tmul, piInf_tmul, h.2.2.2, star_mul']
    congr 1
    exact (Complex.conj_eq_iff_im.2 (im_extension h.1 w _)).symm

theorem eq_zero_of_piInf {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (x : AE F E)
    (hx : At (evI F) x) (hinf : ∀ w, piInf (τ w) x = 0) : x = 0 := by
  obtain ⟨β, hβ⟩ := exists_moved h
  obtain ⟨B, hB0, hB1⟩ := exists_basis h hβ
  have hdec := eq_add_tmul B x
  set C := Algebra.TensorProduct.basis (AF F) B with hC
  have hu : pairA F 0 1 • x = 0 := hx _ (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))
  have hfin : ∀ i, (C.repr x i).2 = 0 := fun i => by
    have h1 : C.repr (pairA F 0 1 • x) i = 0 := by rw [hu]; simp
    rw [map_smul] at h1
    have h2 : pairA F 0 1 * C.repr x i = 0 := h1
    have h3 := congrArg (sndA F) h2
    rw [map_mul, map_zero] at h3
    exact (one_mul _).symm.trans h3
  have hre : ∀ w i, (C.repr x i).1 w = 0 := fun w => by
    have e := hinf w
    rw [hdec, map_add, piInf_tmul, piInf_tmul, hB0, hB1, map_one, mul_one] at e
    have hi := congrArg Complex.im e
    have him := im_ne_zero h hβ (τ w).1
    set p := InfinitePlace.Completion.extensionEmbedding w ((C.repr x 0).1 w) with hp
    set q := InfinitePlace.Completion.extensionEmbedding w ((C.repr x 1).1 w) with hq
    have hpi : p.im = 0 := im_extension h.1 w _
    have hqi : q.im = 0 := im_extension h.1 w _
    simp only [Complex.add_im, Complex.mul_im, Complex.zero_im, hpi, hqi, zero_mul, add_zero, zero_add] at hi
    have hq0 : q.re = 0 := (mul_eq_zero.1 hi).resolve_right him
    have hq1 : q = 0 := Complex.ext hq0 hqi
    rw [hq1, zero_mul, add_zero] at e
    have inj := (InfinitePlace.Completion.extensionEmbedding w).injective
    intro i
    fin_cases i
    · show (C.repr x 0).1 w = 0
      exact inj (e.trans (map_zero _).symm)
    · show (C.repr x 1).1 w = 0
      exact inj (hq1.trans (map_zero _).symm)
  have hz : C.repr x = 0 := by
    ext i
    show C.repr x i = 0
    exact Prod.ext (funext fun w => hre w i) (hfin i)
  simpa using hz

def ofInf (c : ∀ w : InfinitePlace F, w.Completion) : AF F := ((c : Ainf F), (0 : Af F))

theorem continuous_ofInf : Continuous (ofInf (F := F)) := continuous_id.prodMk continuous_const

theorem mul_ofInf (u : AF F) (hu : evI F u = 0) (c : ∀ w : InfinitePlace F, w.Completion) : u * ofInf c = 0 := by
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  refine Prod.ext ?_ ?_
  · change u.1 * _ = 0
    rw [h1, zero_mul]
  · change u.2 * 0 = 0
    rw [mul_zero]

theorem exists_section {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    ∃ s : (InfinitePlace F → ℂ) → AE F E, Continuous s ∧ ∀ z, At (evI F) (s z) ∧ ∀ w, piInf (τ w) (s z) = z w := by
  have hF := h.1
  obtain ⟨β, hβ⟩ := exists_moved h
  have him : ∀ w, ((τ w).1 β).im ≠ 0 := fun w => im_ne_zero h hβ _
  let e : ∀ w : InfinitePlace F, w.Completion ≃ᵢ ℝ := fun w =>
    InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)
  have he : ∀ w a, InfinitePlace.Completion.extensionEmbedding w a = ((e w a : ℝ) : ℂ) := fun w a =>
    (InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w) a).symm
  let s : (InfinitePlace F → ℂ) → InfinitePlace F → ℝ := fun z w => (z w).im / ((τ w).1 β).im
  let r : (InfinitePlace F → ℂ) → InfinitePlace F → ℝ := fun z w => (z w).re - s z w * ((τ w).1 β).re
  have hs : ∀ w, Continuous fun z => s z w := fun w => by fun_prop
  have hr : ∀ w, Continuous fun z => r z w := fun w => by fun_prop
  refine ⟨fun z => ofInf (fun w => (e w).symm (r z w)) • ((1 : AF F) ⊗ₜ[F] (1 : E)) +
    ofInf (fun w => (e w).symm (s z w)) • ((1 : AF F) ⊗ₜ[F] β), ?_, fun z => ⟨?_, fun w => ?_⟩⟩
  · have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
    have : ContinuousSMul (AF F) (AE F E) := inferInstance
    have c1 : Continuous fun z => ofInf (fun w => (e w).symm (r z w)) :=
      continuous_ofInf.comp (continuous_pi fun w => (e w).symm.continuous.comp (hr w))
    have c2 : Continuous fun z => ofInf (fun w => (e w).symm (s z w)) :=
      continuous_ofInf.comp (continuous_pi fun w => (e w).symm.continuous.comp (hs w))
    exact (c1.smul (continuous_const (y := ((1 : AF F) ⊗ₜ[F] (1 : E) : AE F E)))).add
      (c2.smul (continuous_const (y := ((1 : AF F) ⊗ₜ[F] β : AE F E))))
  · intro u hu
    rw [smul_add, smul_smul, smul_smul, mul_ofInf u hu, mul_ofInf u hu, zero_smul, zero_smul, add_zero]
  · have hc : ∀ (c : ∀ w : InfinitePlace F, w.Completion) (y : E),
        piInf (τ w) (ofInf c • ((1 : AF F) ⊗ₜ[F] y)) = ((e w (c w) : ℝ) : ℂ) * (τ w).1 y := fun c y => by
      rw [← he, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rfl
    rw [map_add, hc, hc]
    simp only [(e w).apply_symm_apply, map_one, mul_one]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, r]; ring
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, s]
      have := him w
      field_simp
      ring

end Adele

section Trace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem emb_evI (a : AF F) {w : InfinitePlace F} (hw : w.IsReal) :
    InfinitePlace.Completion.extensionEmbedding w (a.1 w) = (((evI F a).1 ⟨w, hw⟩ : ℝ) : ℂ) :=
  (InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw _).symm

theorem trace_pi {ι : Type} [Fintype ι] [DecidableEq ι] (y : ι → ℝ) : Algebra.trace ℝ (ι → ℝ) y = ∑ i, y i := by
  rw [Algebra.trace_eq_matrix_trace (Pi.basisFun ℝ ι), Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Algebra.leftMulMatrix_eq_repr_mul]

theorem trace_mixed (hF : IsTotallyReal F) (a : AF F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F a) =
      ∑ w, (InfinitePlace.Completion.extensionEmbedding w (a.1 w)).re := by
  have : IsEmpty {w : InfinitePlace F // w.IsComplex} :=
    ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.2 w.2 (IsTotallyReal.isReal w.1)⟩
  rw [Algebra.trace_prod_apply, Subsingleton.elim (evI F a).2 0, map_zero, add_zero, trace_pi]
  refine Fintype.sum_equiv (Equiv.subtypeUnivEquiv fun w => IsTotallyReal.isReal w) _ _ fun w => ?_
  rw [Equiv.subtypeUnivEquiv_apply, emb_evI a w.2, ofReal_re]

theorem trace_AE {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (z : AE F E) :
    algebraMap (AF F) (AE F E) (Algebra.trace (AF F) (AE F E) z) = z + cA σ z := by
  obtain ⟨β, hβ⟩ := exists_moved h
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [h.2.2.2, h.2.2.2, star_star]
  have hξ : σ (β - σ β) = -(β - σ β) := by rw [map_sub, hσ, neg_sub]
  set ξ := β - σ β with hξ'
  have h0 : ξ ≠ 0 := sub_ne_zero.2 hβ.symm
  obtain ⟨B, hB0, hB1⟩ := exists_basis h (β := ξ) (by
    rw [hξ]; intro e; exact h0 (by linear_combination (-1 / 2) * e))
  let C := Algebra.TensorProduct.basis (AF F) B
  have q : IsQuad (cA σ) ((1 : AF F) ⊗ₜ[F] ξ) :=
    ⟨(Ne.isUnit h0).map (inclR (F := F) (AF F)), by
      change (1 : AF F) ⊗ₜ[F] σ ξ = _
      rw [hξ, TensorProduct.tmul_neg], C, by simp [C, hB0, Algebra.TensorProduct.one_def], by simp [C, hB1]⟩
  generalize (1 : AF F) ⊗ₜ[F] ξ = η at q
  obtain ⟨x, y, rfl⟩ := q.exists_eq z
  obtain ⟨d, hd⟩ := q.exists_of_fixed (z := η * η) (by rw [map_mul, q.anti, neg_mul_neg])
  obtain ⟨b, h0, h1⟩ := q.basis
  have e0 : (algebraMap (AF F) (AE F E) x + algebraMap (AF F) (AE F E) y * η) * b 0 = x • b 0 + y • b 1 := by
    rw [h0, h1, Algebra.smul_def, Algebra.smul_def]; ring
  have e1 : (algebraMap (AF F) (AE F E) x + algebraMap (AF F) (AE F E) y * η) * b 1 = (y * d) • b 0 + x • b 1 := by
    rw [h0, h1, Algebra.smul_def, Algebra.smul_def, map_mul, ← hd]; ring
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, e0, e1]
  rw [map_add (cA σ), map_mul (cA σ), AlgHom.commutes, AlgHom.commutes, q.anti]
  simp only [map_add, map_smul, Module.Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (zero_ne_one' (Fin 2)), Finsupp.single_eq_of_ne (zero_ne_one' (Fin 2)).symm, smul_eq_mul, mul_one, mul_zero,
    add_zero, zero_add]
  ring

theorem piInf_algebraMap {w : InfinitePlace F} (τ : EmbOver E w) (a : AF F) :
    piInf τ (algebraMap (AF F) (AE F E) a) = InfinitePlace.Completion.extensionEmbedding w (a.1 w) := by
  change piInf τ (a ⊗ₜ[F] 1) = _
  rw [piInf_tmul, map_one, mul_one]

theorem trace_trace {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (z : AE F E) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (Algebra.trace (AF F) (AE F E) z)) =
      ∑ w, 2 * (piInf (τ w) z).re := by
  rw [trace_mixed h.1]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← piInf_algebraMap (τ w), trace_AE h, map_add, piInf_cA h]
  simp [two_mul]

theorem evI_add (a b : AF F) : evI F (a + b) = evI F a + evI F b := map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) _ _

theorem evI_mul (a b : AF F) : evI F (a * b) = evI F a * evI F b := map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) _ _

variable (F) in

def evIh : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

theorem evIh_apply (a : AF F) : evIh F a = evI F a := rfl

theorem evI_realAd (t : ℝ) : evI F (realAd F t) = algebraMap ℝ _ t :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _

theorem piInf_realAd (hF : IsTotallyReal F) {w : InfinitePlace F} (τ : EmbOver E w) (t : ℝ) (z : AE F E) :
    piInf τ (realAd F t • z) = t * piInf τ z := by
  rw [Algebra.smul_def, map_mul, piInf_algebraMap, emb_evI _ (IsTotallyReal.isReal w), evI_realAd]
  rfl

end Trace

section Twist

variable {P Q R S : ℕ} {W : Type}

def tw1 (c : Matrix (Ix P Q) (Ix R S) ℂ) (l : Ln P Q R S) : ℂ := if linePos l then c l.1 l.2 else star (c l.1 l.2)

def tw (c : W → Matrix (Ix P Q) (Ix R S) ℂ) (p : W × Ln P Q R S) : ℂ := tw1 (c p.1) p.2

def untw (z : W × Ln P Q R S → ℂ) (w : W) : Matrix (Ix P Q) (Ix R S) ℂ :=
  Matrix.of fun i k => if linePos (p := P) (q := Q) (r := R) (s := S) (i, k) then z (w, i, k) else star (z (w, i, k))

theorem tw_untw (z : W × Ln P Q R S → ℂ) : tw (untw z) = z := by
  funext ⟨w, i, k⟩
  simp only [tw, tw1, untw, Matrix.of_apply]
  split_ifs <;> simp

theorem untw_tw (c : W → Matrix (Ix P Q) (Ix R S) ℂ) : untw (tw c) = c := by
  ext w i k
  simp only [tw, tw1, untw, Matrix.of_apply]
  split_ifs <;> simp

theorem untw_add (z z' : W × Ln P Q R S → ℂ) (w : W) : untw (z + z') w = untw z w + untw z' w := by
  ext i k
  simp only [untw, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

theorem untw_smul (t : ℝ) (z : W × Ln P Q R S → ℂ) (w : W) : untw (t • z) w = (t : ℂ) • untw z w := by
  ext i k
  simp only [untw, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply]
  split_ifs <;> simp

theorem heisOp_eq (c : Matrix (Ix P Q) (Ix R S) ℂ) : heisOp c = hop (tw1 c) := by
  rw [heisOp, hop]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rcases l with ⟨i | i, k | k⟩ <;> simp [tw1, raiB, lowB, linePos, lineSign] <;> abel

theorem tw_J (e : W → ℤˣ) (c : W → Matrix (Ix P Q) (Ix R S) ℂ) (p : W × Ln P Q R S) :
    tw (fun w => (((e w : ℤ) : ℂ) * I) • (Jm P Q * c w * Jm R S)) p = ((e p.1 : ℤ) : ℂ) * I * tw c p := by
  rcases p with ⟨w, i | i, k | k⟩ <;> simp [tw, tw1, linePos, Jm_eq, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem trace_J (c c' : Matrix (Ix P Q) (Ix R S) ℂ) :
    (cᵀ * Jm P Q * c'.map star * (Jm R S)ᵀ).trace.im = (∑ l, tw1 c l * star (tw1 c' l)).im := by
  rw [Fintype.sum_prod_type_right, Matrix.trace, im_sum, im_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Jm_eq, Jm_eq, Matrix.diagonal_transpose, Matrix.diag_apply, Matrix.mul_diagonal, Matrix.mul_apply, Finset.sum_mul,
    im_sum, im_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_diagonal]
  rcases i with i | i <;> rcases k with k | k <;> simp [tw1, linePos] <;> ring

theorem herm_frame {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {MA : Matrix α α ℂ} {MB : Matrix β β ℂ}
    {a b : ℂ} (hab : a * b = I) {A : Matrix α (Ix P Q) ℂ} {C : Matrix β (Ix R S) ℂ} (hA : IsFrame (a • MA) A)
    (hC : IsFrame (b • MB) C) (c c' : Matrix (Ix P Q) (Ix R S) ℂ) :
    (∑ i, ∑ j, ∑ k, ∑ l, (A * c * Cᵀ) i j * MA i k * MB j l * star ((A * c' * Cᵀ) k l)).re =
      (∑ l, tw1 c l * star (tw1 c' l)).im := by
  have e1 : ∀ u u' : Matrix α β ℂ, ∑ i, ∑ j, ∑ k, ∑ l, u i j * MA i k * MB j l * star (u' k l) =
      (uᵀ * MA * u'.map star * MBᵀ).trace := fun u u' => by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => by ring
  have e2 : I * ((A * c * Cᵀ)ᵀ * MA * (A * c' * Cᵀ).map star * MBᵀ).trace = (cᵀ * Jm P Q * c'.map star * (Jm R S)ᵀ).trace := by
    rw [← hA.1, ← hC.1, ← hab]
    simp only [map_star_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.transpose_smul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc, Matrix.transpose_map]
    rw [Matrix.trace_mul_comm C]
    simp only [Matrix.mul_assoc]
    ring
  rw [e1, ← trace_J, ← e2]
  simp

end Twist

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] {P Q R S : ℕ}

variable (F κ) in

def trB : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) :=
  (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := κ → mixedEmbedding.mixedSpace F) (F' := ℝ)).toLinearMap.comp
    (LinearMap.mk₂ ℝ (fun y x => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * y i))
      (fun y y' x => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add])
      (fun t y x => by simp only [Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_smul])
      (fun y x x' => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, map_add])
      (fun t y x => by simp only [Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum, map_smul]))

theorem trB_apply (y x : κ → mixedEmbedding.mixedSpace F) :
    trB F κ y x = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * y i) := rfl

theorem exists_lift (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) :
    ∃ U : (InfinitePlace F × Ln P Q R S → ℂ) → Matrix α β (AE F E), (∀ z, At (evI F) (U z)) ∧
      (∀ z w, (U z).map (piInf (τ w)) = A w * untw z w * (C w)ᵀ) ∧
      ∀ u z, At (evI F) u → (∀ w, u.map (piInf (τ w)) = A w * untw z w * (C w)ᵀ) → U z = u := by
  obtain ⟨s, -, hs⟩ := exists_section h τ
  let U : (InfinitePlace F × Ln P Q R S → ℂ) → Matrix α β (AE F E) := fun z =>
    Matrix.of fun i j => s fun w => (A w * untw z w * (C w)ᵀ) i j
  have h1 : ∀ z, At (evI F) (U z) := fun z a ha => by
    ext i j
    exact (hs _).1 a ha
  have h2 : ∀ z w, (U z).map (piInf (τ w)) = A w * untw z w * (C w)ᵀ := fun z w => by
    ext i j
    exact (hs _).2 w
  refine ⟨U, h1, h2, fun u z hu hc => ?_⟩
  ext i j
  refine sub_eq_zero.1 (eq_zero_of_piInf h τ _ (fun a ha => ?_) fun w => ?_)
  · rw [smul_sub, sub_eq_zero]
    exact (congrFun (congrFun (h1 z a ha) i) j).trans (congrFun (congrFun (hu a ha) i) j).symm
  · rw [map_sub, sub_eq_zero]
    exact congrFun (congrFun ((h2 z w).trans (hc w).symm) i) j

theorem exists_heis (hD : DerEx) {ψ : AddChar (AF F) ℂ} {τ : ∀ w : InfinitePlace F, EmbOver E w} {JA : Matrix α α (AE F E)}
    {JB : Matrix β β (AE F E)} (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) {a b : ℂ}
    {A : InfinitePlace F → Matrix α (Ix P Q) ℂ} {C : InfinitePlace F → Matrix β (Ix R S) ℂ} (h : IsCMExt F E σ) (hψ : IsStd ψ)
    (hfr : Framed τ JA JB a b A C) :
    ∃ H : Heis (κ → mixedEmbedding.mixedSpace F) (InfinitePlace F × Ln P Q R S),
      (∀ c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ, ∃ u : Matrix α β (AE F E), At (evI F) u ∧
        ∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) ∧
      ∀ u : Matrix α β (AE F E), At (evI F) u → ∀ c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ,
        (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) →
          ∀ f, SD (fun t => d.rho ψ (realAd F t • u)) f (H.D (tw c) f) := by
  obtain ⟨D, hD⟩ := hD F E σ α β κ ψ JA JB d hψ
  obtain ⟨U, h1, h2, h3⟩ := exists_lift (α := α) (β := β) h τ A C
  have hadd : ∀ z z', U (z + z') = U z + U z' := fun z z' => h3 _ _
    (fun a ha => by rw [smul_add, h1 z a ha, h1 z' a ha, add_zero]) fun w => by
      rw [Matrix.map_add _ (map_add _), h2, h2, untw_add, Matrix.mul_add, Matrix.add_mul]
  have hsmul : ∀ (t : ℝ) z, U (t • z) = realAd F t • U z := fun t z => h3 _ _
    (fun a ha => by rw [smul_comm, h1 z a ha, smul_zero]) fun w => by
      rw [untw_smul, Matrix.mul_smul, Matrix.smul_mul, ← h2]
      ext i j
      exact piInf_realAd h.1 (τ w) t _
  let v : (InfinitePlace F × Ln P Q R S → ℂ) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
    { toFun := fun z i => evI F ((d.e (U z)).1 i)
      map_add' := fun z z' => by
        funext i
        rw [hadd, map_add]
        exact evI_add _ _
      map_smul' := fun t z => by
        funext i
        rw [hsmul, map_smul]
        refine (evI_mul _ _).trans ?_
        rw [evI_realAd, ← Algebra.smul_def]
        rfl }
  let y : (InfinitePlace F × Ln P Q R S → ℂ) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
    { toFun := fun z i => evI F ((d.e (U z)).2 i)
      map_add' := fun z z' => by
        funext i
        rw [hadd, map_add]
        exact evI_add _ _
      map_smul' := fun t z => by
        funext i
        rw [hsmul, map_smul]
        refine (evI_mul _ _).trans ?_
        rw [evI_realAd, ← Algebra.smul_def]
        rfl }
  have hform : ∀ c c', trB F κ (y c') (v c) - trB F κ (y c) (v c') = -2 * (∑ l, c l * star (c' l)).im := fun c c' => by
    have e1 : trB F κ (y c') (v c) - trB F κ (y c) (v c') =
        Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (symp (R := AF F) (cA σ) (-1) JA JB (U c) (U c'))) := by
      rw [d.form, ← evIh_apply, trB_apply, trB_apply, ← map_sub]
      simp only [dotProduct, map_sub, map_sum, map_mul, evIh_apply]
      rfl
    rw [e1, symp, trace_trace h τ, Fintype.sum_prod_type, im_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    have e2 := herm_frame (MA := JA.map (piInf (τ w))) (MB := JB.map (piInf (τ w))) hfr.1 (hfr.2.1 w) (hfr.2.2 w)
      (untw c w) (untw c' w)
    have e3 : ∀ (z : InfinitePlace F × Ln P Q R S → ℂ) l, tw1 (untw z w) l = z (w, l) := fun z l =>
      congrFun (tw_untw z) (w, l)
    simp only [e3, ← h2, Matrix.map_apply] at e2
    rw [← e2, hTens, neg_one_mul, map_neg, neg_re]
    simp only [map_sum, map_mul, piInf_cA h]
    ring
  have hdim : Module.finrank ℝ (κ → mixedEmbedding.mixedSpace F) ≤ Module.finrank ℝ (LinearMap.ker v) := by
    refine LinearMap.finrank_le_finrank_of_surjective (f := y.comp (LinearMap.ker v).subtype) fun y0 => ?_
    choose A' hA' using fun w => (hfr.2.1 w).2
    choose C' hC' using fun w => (hfr.2.2 w).2
    let yt : κ → AF F := fun i => ofInf ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y0 i))
    let u : Matrix α β (AE F E) := d.e.symm (0, yt)
    have hu : At (evI F) u := fun a ha => by
      rw [← map_smul, ← map_zero d.e.symm]
      congr 1
      refine Prod.ext (smul_zero _) (funext fun i => mul_ofInf a ha _)
    have hz : U (tw fun w => A' w * u.map (piInf (τ w)) * (C' w)ᵀ) = u := h3 _ _ hu fun w => by
      rw [untw_tw, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hA', Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, hC',
        Matrix.transpose_one, Matrix.mul_one]
    refine ⟨⟨tw fun w => A' w * u.map (piInf (τ w)) * (C' w)ᵀ, ?_⟩, ?_⟩
    · funext i
      change evI F ((d.e (U _)).1 i) = 0
      rw [hz, LinearEquiv.apply_symm_apply]
      exact map_zero (evIh F)
    · funext i
      change evI F ((d.e (U (tw fun w => A' w * u.map (piInf (τ w)) * (C' w)ᵀ))).2 i) = _
      rw [hz, LinearEquiv.apply_symm_apply]
      exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _
  refine ⟨⟨v, (trB F κ).comp y, fun z => D (U z), fun z f x => (hD _ (h1 z) f).2 x, hform, hdim⟩, fun c => ?_,
    fun u hu c hc f => ?_⟩
  · exact ⟨U (tw c), h1 _, fun w => by rw [h2, untw_tw]⟩
  · have e : U (tw c) = u := h3 _ _ hu fun w => by rw [untw_tw, hc]
    change SD _ f (D (U (tw c)) f)
    rw [e]
    exact (hD u hu f).1

theorem iota_sumPl (c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) (T : Tens F P Q R S) :
    iota (InfinitePlace F) (Ln P Q R S) (sumPl (fun w => heisOp (c w)) T) =
      hop (tw c) (iota (InfinitePlace F) (Ln P Q R S) T) := by
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r p =>
    rw [map_smul, map_smul, map_smul, map_smul, ← iota_hop, sumPl, LinearMap.sum_apply, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [atPl, PiTensorProduct.map_tprod, heisOp_eq]
    congr 2
    funext w'
    by_cases h : w' = w
    · subst h
      rw [Function.update_self, Function.update_self]
      rfl
    · rw [Function.update_of_ne h, Function.update_of_ne h]
      rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end Main

end Fock

open scoped TensorProduct Matrix Classical
open Fock NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

theorem fockEx : GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.FockEx := by
  intro hD F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C h hψ hfr
  obtain ⟨H, -, hH⟩ := exists_heis hD d h hψ hfr
  obtain ⟨φ, h1, h2⟩ := H.exists_fockMap
  refine ⟨φ.comp (iota (InfinitePlace F) (Ln P Q R S)).toLinearMap, h1.comp iota_injective, fun u hu c hc T => ?_⟩
  have e := hH u hu c hc (φ (iota (InfinitePlace F) (Ln P Q R S) T))
  rw [h2, ← iota_sumPl] at e
  exact e

theorem vacLine : GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.VacLine := by
  intro hD F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ h hψ hfr hΦ f₀ ε hf
  obtain ⟨H, hU, hH⟩ := exists_heis hD d h hψ hfr
  have hI : ∀ c T, H.D (tw c) (Φ T) = Φ (sumPl (fun w => heisOp (c w)) T) := fun c T => by
    obtain ⟨u, hu, hc⟩ := hU c
    exact (actsLaws F κ _ _ _).2.2.2.2 _ (hH u hu c hc _) (hΦ.2 u hu c hc T)
  have h1 : iota (InfinitePlace F) (Ln P Q R S) (PiTensorProduct.tprod ℂ fun _ => 1) = 1 := by simp [iota_tprod]
  have hG : H.Vac (Φ (PiTensorProduct.tprod ℂ fun _ => 1)) := fun z => by
    rw [← tw_untw (I • z), hI, ← tw_untw z, hI, ← map_smul, tw_untw]
    congr 1
    apply iota_injective
    rw [map_smul, iota_sumPl, iota_sumPl, tw_untw, tw_untw, h1, hop_one]
  have hG0 : Φ (PiTensorProduct.tprod ℂ fun _ => 1) ≠ 0 := fun e => by
    rw [hΦ.1 (e.trans (map_zero Φ).symm), map_zero] at h1
    exact zero_ne_one h1
  have hε : ∀ z : InfinitePlace F × Ln P Q R S → ℂ,
      H.D (fun p => ((ε p.1 : ℤ) : ℂ) * I * z p) f₀ = I • H.D z f₀ := fun z => by
    obtain ⟨u, hu, hc⟩ := hU (untw z)
    obtain ⟨u', hu', hc'⟩ := hU fun w => (((ε w : ℤ) : ℂ) * I) • (Jm P Q * untw z w * Jm R S)
    have e := hf u u' hu hu' _ hc hc' _ _ (hH u hu _ hc f₀) (hH u' hu' _ hc' f₀)
    rw [funext (tw_J ε (untw z)), tw_untw] at e
    exact e
  by_cases hp : ∀ p : InfinitePlace F × Ln P Q R S, ε p.1 = 1
  · refine H.vac_unique (fun z => ?_) hG hG0
    rw [← hε]
    congr 2
    funext p
    simp [hp p]
  · push Not at hp
    obtain ⟨p, hp⟩ := hp
    have hm : ε p.1 = -1 := (Int.units_eq_one_or _).resolve_left hp
    refine ⟨0, (H.eq_zero_of_neg (c := Pi.single p 1) (by simp) ?_).trans (zero_smul _ _).symm⟩
    have e : (fun q => ((ε q.1 : ℤ) : ℂ) * I * (Pi.single p 1 : InfinitePlace F × Ln P Q R S → ℂ) q) =
        (-1 : ℝ) • I • (Pi.single p 1 : InfinitePlace F × Ln P Q R S → ℂ) := by
      funext q
      by_cases hq : q = p
      · subst hq; simp [hm]
      · simp [hq]
    have e2 := hε (Pi.single p 1)
    rw [e, H.D_smul] at e2
    rw [neg_smul, ← e2]
    simp

end PositivityTheory.RL

end
