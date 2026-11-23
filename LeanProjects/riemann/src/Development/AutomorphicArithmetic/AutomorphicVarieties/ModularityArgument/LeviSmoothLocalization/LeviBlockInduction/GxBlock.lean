import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.LeviBlockInduction.GxDefs

noncomputable section

open MeasureTheory Polynomial GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Parabolic
open GroundTheory.Automorphic.GodementJacquet
open scoped NNReal Classical ValuativeRel

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

open UpperTheory.V.Z.Gam

private def LF (f : ℂ → ℂ) : Prop := ∃ (P : ℂ[X]) (N : ℕ), ∀ x : ℂ, x ≠ 0 → f x = P.eval x / x ^ N

private theorem LF.add {f g : ℂ → ℂ} (hf : LF f) (hg : LF g) : LF fun x => f x + g x := by
  obtain ⟨P, N, h⟩ := hf
  obtain ⟨Q, M, h'⟩ := hg
  refine ⟨P * X ^ M + Q * X ^ N, N + M, fun x hx => ?_⟩
  simp only [h x hx, h' x hx, eval_add, eval_mul, eval_pow, eval_X]
  field_simp
  ring

private theorem LF.mul {f g : ℂ → ℂ} (hf : LF f) (hg : LF g) : LF fun x => f x * g x := by
  obtain ⟨P, N, h⟩ := hf
  obtain ⟨Q, M, h'⟩ := hg
  refine ⟨P * Q, N + M, fun x hx => ?_⟩
  simp only [h x hx, h' x hx, eval_mul]
  field_simp
  ring

private theorem LF.mono (c : ℂ) (k : ℤ) : LF fun x => c * x ^ k := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · exact ⟨C c * X ^ n, 0, fun x _ => by simp⟩
  · exact ⟨C c, n, fun x _ => by simp [div_eq_mul_inv]⟩

private theorem LF.mono' (κ c : ℂ) (k : ℤ) : LF fun x => c * (κ / x) ^ k := by
  obtain ⟨P, N, h⟩ := LF.mono (c * κ ^ k) (-k)
  refine ⟨P, N, fun x hx => ?_⟩
  rw [← h x hx]
  simp only [div_zpow, zpow_neg]
  ring

private theorem LF.sum {ι : Type} (S : Finset ι) {f : ι → ℂ → ℂ} (h : ∀ i, LF (f i)) : LF fun x => ∑ i ∈ S, f i x := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0, 0, fun x _ => by simp⟩
  | insert a s ha ih => simpa only [Finset.sum_insert ha] using (h a).add ih

private theorem LF.poly (κ : ℂ) (P : ℂ[X]) : LF fun x => P.eval (κ / x) := by
  simp only [eval_eq_sum_range]
  exact LF.sum _ fun i => by simpa using LF.mono' κ (P.coeff i) (i : ℤ)

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

private theorem rat_eq {γ : RatFunc ℂ} {a b : ℂ → ℂ} (h : RatFE F γ a b) {P Q P' Q' : ℂ[X]} {t t' : ℝ}
    (ha : ∀ s : ℂ, t < s.re → Q.eval (qs F s) ≠ 0 ∧ a s = P.eval (qs F s) / Q.eval (qs F s))
    (hb : ∀ s : ℂ, s.re < t' → Q'.eval (qs F s) ≠ 0 ∧ b s = P'.eval (qs F s) / Q'.eval (qs F s)) :
    algebraMap ℂ[X] (RatFunc ℂ) P' / algebraMap ℂ[X] (RatFunc ℂ) Q' =
      γ * (algebraMap ℂ[X] (RatFunc ℂ) P / algebraMap ℂ[X] (RatFunc ℂ) Q) := by
  obtain ⟨R, s₁, h₁, h₂⟩ := h
  have hR : R = algebraMap ℂ[X] (RatFunc ℂ) P / algebraMap ℂ[X] (RatFunc ℂ) Q :=
    eq_of_eval_qs_eq_right (F := F) (s₁ := max s₁ t) fun s hs => by
      rw [max_lt_iff] at hs
      rw [← h₁ s hs.1, eval_div_algebraMap _ _ (ha s hs.2).1, (ha s hs.2).2]
  rw [← hR]
  exact eq_of_eval_qs_eq_left (F := F) (s₁ := min (-s₁) t') fun s hs => by
    rw [lt_min_iff] at hs
    rw [← h₂ s hs.1, eval_div_algebraMap _ _ (hb s hs.2).1, (hb s hs.2).2]

private theorem core {γ : RatFunc ℂ} {a b a' b' f f' : ℂ → ℂ} (h : RatFE F γ a b) (h' : RatFE F γ a' b')
    {D D' : ℂ[X]} (hD : D ≠ 0) (hD' : D' ≠ 0) {c c' : ℂ} (hc : c ≠ 0) (hc' : c' ≠ 0) {i : ℕ} (hf : LF f) (hf' : LF f') {t t' : ℝ}
    (ha : ∀ s : ℂ, t < s.re → D.eval (qs F s) ≠ 0 ∧ a s = c / D.eval (qs F s) ∧ a' s = f' (qs F s) / D.eval (qs F s))
    (hb : ∀ s : ℂ, s.re < t' → D'.eval (qs F s) ≠ 0 ∧ b s = f (qs F s) / D'.eval (qs F s) ∧
      b' s = c' * qs F s ^ i / D'.eval (qs F s)) :
    ∃ (r : ℂ) (j : ℤ), r ≠ 0 ∧
      γ = RatFunc.C r * RatFunc.X ^ j * algebraMap ℂ[X] (RatFunc ℂ) D / algebraMap ℂ[X] (RatFunc ℂ) D' := by
  obtain ⟨P, N, hP⟩ := hf
  obtain ⟨P', N', hP'⟩ := hf'
  have e1 := rat_eq h (P := C c) (Q := D) (P' := P) (Q' := X ^ N * D') (t := t) (t' := t')
    (fun s hs => ⟨(ha s hs).1, by rw [(ha s hs).2.1, eval_C]⟩)
    (fun s hs => ⟨by simp [(hb s hs).1, qs_ne_zero], by
      rw [(hb s hs).2.1, hP _ (qs_ne_zero s), div_div]; simp⟩)
  have e2 := rat_eq h' (P := P') (Q := X ^ N' * D) (P' := C c' * X ^ i) (Q' := D') (t := t) (t' := t')
    (fun s hs => ⟨by simp [(ha s hs).1, qs_ne_zero], by
      rw [(ha s hs).2.2, hP' _ (qs_ne_zero s), div_div]; simp⟩)
    (fun s hs => ⟨(hb s hs).1, by rw [(hb s hs).2.2]; simp⟩)
  simp only [map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C] at e1 e2
  have n1 := RatFunc.algebraMap_ne_zero hD
  have n2 := RatFunc.algebraMap_ne_zero hD'
  have nX : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
  have nc : (RatFunc.C c : RatFunc ℂ) ≠ 0 := by simpa using hc
  have nc' : (RatFunc.C c' : RatFunc ℂ) ≠ 0 := by simpa using hc'
  set d := algebraMap ℂ[X] (RatFunc ℂ) D
  set d' := algebraMap ℂ[X] (RatFunc ℂ) D'
  have hγ : γ ≠ 0 := by
    rintro rfl
    rw [zero_mul] at e2
    exact div_ne_zero (mul_ne_zero nc' (pow_ne_zero _ nX)) n2 e2
  have m1 : γ * d' / d ∈ laurentSubalgebra := by
    have : γ * d' / d = RatFunc.C c⁻¹ * (algebraMap ℂ[X] (RatFunc ℂ) P / RatFunc.X ^ N) := by
      rw [map_inv₀]
      field_simp at e1 ⊢
      linear_combination -e1
    rw [this]
    exact mul_mem (C_mem_laurentSubalgebra _) (mem_laurentSubalgebra_iff.2 ⟨P, N, rfl⟩)
  have m2 : (γ * d' / d)⁻¹ ∈ laurentSubalgebra := by
    have : (γ * d' / d)⁻¹ = RatFunc.C c'⁻¹ * (algebraMap ℂ[X] (RatFunc ℂ) P' / RatFunc.X ^ (N' + i)) := by
      rw [map_inv₀, pow_add]
      field_simp at e2 ⊢
      linear_combination e2
    rw [this]
    exact mul_mem (C_mem_laurentSubalgebra _) (mem_laurentSubalgebra_iff.2 ⟨P', N' + i, rfl⟩)
  obtain ⟨r, k, l, hr, he⟩ := exists_eq_C_mul_X_pow_of_mem m1 m2 (div_ne_zero (mul_ne_zero hγ n2) n1)
  simp only [map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C] at he
  refine ⟨r, (k : ℤ) - l, hr, ?_⟩
  rw [zpow_sub₀ nX, zpow_natCast, zpow_natCast]
  field_simp at he ⊢
  linear_combination he

private theorem blockB_ind {m : ℕ} [MeasurableSpace (GL (Fin m) F)] [BorelSpace (GL (Fin m) F)] {H : Type} [Group H]
    {W : Type} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (GL (Fin m) F × H) W}
    (μ : Measure (GL (Fin m) F)) {r : ℕ} {K' : Subgroup H} {v : W}
    (hv : v ∈ fixedVectors σ ((congruenceSubgroup F m r).prod K')) (ℓ : Module.Dual ℂ W) (s : ℂ) :
    blockB μ σ (indGL (congruenceSubgroup F m r : Set (GL (Fin m) F))) v ℓ s =
      μ.real (congruenceSubgroup F m r : Set (GL (Fin m) F)) * ℓ v := by
  have hdet : ∀ g ∈ congruenceSubgroup F m r, detPow g (m - s) = 1 := fun g hg =>
    detPow_of_mem_integralGL (congruenceSubgroup_le F m r hg) _
  have hfix : ∀ g ∈ congruenceSubgroup F m r, σ (g⁻¹, 1) v = v := fun g hg =>
    mem_fixedVectors.1 hv _ (Subgroup.mem_prod.2 ⟨inv_mem hg, K'.one_mem⟩)
  simp only [blockB, mul_assoc]
  rw [integral_indGL_mul μ (isOpen_congruenceSubgroup F m r).measurableSet (x₀ := 1)
    (fun g hg => by rw [hdet g hg, hdet 1 (one_mem _), hfix g hg, hfix 1 (one_mem _)]),
    hdet 1 (one_mem _), one_mul, hfix 1 (one_mem _)]

theorem gxBlock_of (hL : LdLaurent) (hM : LdMean) (hT : LdTate) : GxBlock := by
  intro F _ _ _ _ _ _ m _ _ _ μ _ H _ _ _ _ _ _ _ W _ _ σ hσ hirr α hα0 hα hsupp ψ hψ hψ1 γ hFE
  obtain ⟨v₀, hv₀ne⟩ := exists_ne_zero_of_isIrreducible (ρ := σ)
  obtain ⟨r₀, K₀', hK₀'c, hK₀'o, hv₀⟩ := exists_fixed_prod₀ hσ.1 v₀
  obtain ⟨ℓ₀, hℓ₀, hℓ₀v₀⟩ : ∃ ℓ₀ ∈ smoothVectors (Representation.dual σ), ℓ₀ v₀ ≠ 0 := by
    set 𝕂₀ := (congruenceSubgroup F m r₀).prod K₀'
    have h𝕂₀c : IsCompact (𝕂₀ : Set (GL (Fin m) F × H)) := by
      rw [Subgroup.coe_prod]; exact (isCompact_congruenceSubgroup F m r₀).prod hK₀'c
    have h𝕂₀o : IsOpen (𝕂₀ : Set (GL (Fin m) F × H)) := by
      rw [Subgroup.coe_prod]; exact (isOpen_congruenceSubgroup F m r₀).prod hK₀'o
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ (fixedVectors σ 𝕂₀), φ ⟨v₀, hv₀⟩ ≠ 0 := by
      by_contra h
      push Not at h
      exact hv₀ne (congrArg Subtype.val ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 h))
    set ef := fixedContragredientEquiv hσ.1 h𝕂₀c h𝕂₀o with hef
    refine ⟨_, ((ef.symm φ : fixedVectors (contragredient σ) 𝕂₀) : smoothVectors (Representation.dual σ)).2, ?_⟩
    have h := congrArg (fun f : Module.Dual ℂ (fixedVectors σ 𝕂₀) => f ⟨v₀, hv₀⟩) (ef.apply_symm_apply φ)
    rw [hef, fixedContragredientEquiv_apply, restrictFixed_apply] at h
    rw [hef, h]
    exact hφ
  have hcc := isCentralCoeff_coeff hσ.1 hα0 hα hsupp v₀ hℓ₀
  set t : ℝ := Real.logb (LocalField.residueCard F) ‖α‖ / m
  have hR : ∀ s : ℂ, t < s.re → ‖α * qs F s ^ m‖ < 1 := fun s hs => norm_mul_qs_pow_lt_one hα0 hs
  have hLft : ∀ s : ℂ, s.re < t + m → ‖α⁻¹ * qs F ((m : ℂ) - s) ^ m‖ < 1 := fun s hs =>
    norm_inv_mul_qs_sub_lt_one hα0 (lt_norm_mul_qs_pow hα0 hs)
  split_ifs with hu
  · obtain ⟨rfl, hu⟩ := hu
    obtain ⟨Φ, hΦ, r, hr, hZ⟩ := hT F μ
    obtain ⟨Φ', hΦ', hF⟩ := exists_localMatrixFourier_eq hψ hψ1 hΦ
    have h1 : σ ((1 : GL (Fin 1) F), (1 : H)) = 1 := hu 1 (one_mem _)
    have hA := hZ α _ hcc (fun g hg => by simp only [hu g hg, h1])
    have hB := hZ α⁻¹ _ hcc.inv (fun g hg => by simp only [hu _ (inv_mem hg), inv_one, h1])
    obtain ⟨P, N, hP⟩ := hcc.inv.exists_eq_div_zeta μ (hΦ.localMatrixFourier hψ hψ1)
    obtain ⟨P', N', hP'⟩ := hcc.exists_eq_div_zeta μ hΦ'
    set q : ℂ := ((LocalField.residueCard F : ℕ) : ℂ) with hq
    have hq0 : q ≠ 0 := Nat.cast_ne_zero.2 LocalField.residueCard_ne_zero
    have hne : ∀ z : ℂ, ‖z‖ < 1 → 1 - z ≠ 0 := fun z hz h => by
      rw [← sub_eq_zero.1 h, norm_one] at hz; exact lt_irrefl _ hz
    have hD : (1 - C α * X : ℂ[X]).eval 0 = 1 := by simp
    have hD' : ((1 - C α * X : ℂ[X]).comp (C q * X)).eval 0 = 1 := by simp
    have hy : ∀ s : ℂ, qs F (((1 : ℕ) : ℂ) - s) = q⁻¹ / qs F s := fun s => by
      rw [Nat.cast_one]; exact qs_one_sub s
    have hFE' := hFE Φ' hΦ' v₀ ℓ₀ hℓ₀
    rw [hF] at hFE'
    obtain ⟨c, j, hc, hγ⟩ := core (hFE Φ hΦ v₀ ℓ₀ hℓ₀) hFE' (D := 1 - C α * X) (D' := (1 - C α * X).comp (C q * X))
      (fun h => by rw [h] at hD; simp at hD) (fun h => by rw [h] at hD'; simp at hD')
      (c := r * ℓ₀ v₀) (c' := -(α * q) * (r * ℓ₀ v₀)) (mul_ne_zero hr hℓ₀v₀)
      (mul_ne_zero (neg_ne_zero.2 (mul_ne_zero hα0 hq0)) (mul_ne_zero hr hℓ₀v₀)) (i := 1)
      (((LF.poly q⁻¹ P).mul (LF.mono' q⁻¹ 1 (-(N : ℤ)))).mul (LF.mono (-(α * q)) 1))
      (f' := fun x => P'.eval x / x ^ N') ⟨P', N', fun _ _ => rfl⟩ (t := t) (t' := t + (1 : ℕ))
      (fun s hs => by
        have h2 := hne _ (hR s hs)
        refine ⟨by simpa using h2, ?_, ?_⟩
        · rw [blockA, hA s (hR s hs), h1]; simp
        · rw [blockA, hP' s (hR s hs), div_div]; simp)
      (fun s hs => by
        have h2 := hne _ (hLft s hs)
        have hx := qs_ne_zero (F := F) s
        have h3 : 1 - α * (q * qs F s) ≠ 0 := by
          intro h
          apply h2
          rw [hy]
          field_simp
          linear_combination -h
        have h4 : 1 - α⁻¹ * (q⁻¹ / qs F s) = (1 - α * (q * qs F s)) / (-(α * q) * qs F s) := by
          field_simp
          ring
        refine ⟨by simpa using h3, ?_, ?_⟩
        · rw [blockB, hP _ (hLft s hs), hy, pow_one, h4]
          simp only [sub_comp, one_comp, mul_comp, C_comp, X_comp, eval_sub, eval_one, eval_mul, eval_C, eval_X,
            zpow_neg, zpow_natCast, zpow_one]
          field_simp
        · rw [blockB, hB _ (hLft s hs), hy, h4, inv_one, h1]
          simp only [sub_comp, one_comp, mul_comp, C_comp, X_comp, eval_sub, eval_one, eval_mul, eval_C, eval_X,
            Module.End.one_apply]
          field_simp)
    exact ⟨c, j, hc, hγ⟩
  · have hm := hM F m μ H W σ hσ hirr α hα0 hα hsupp hu v₀ ℓ₀ hℓ₀
    have he₀ := isSchwartzBruhat_indGL (isCompact_congruenceSubgroup F m r₀) (isOpen_congruenceSubgroup F m r₀)
    obtain ⟨Φ', hΦ', hF⟩ := exists_localMatrixFourier_eq hψ hψ1 he₀
    obtain ⟨S, a, hS⟩ := hL F m μ α⁻¹ _ hcc.inv (fun k => (hm k).2) _ (he₀.localMatrixFourier hψ hψ1)
    obtain ⟨S', a', hS'⟩ := hL F m μ α _ hcc (fun k => (hm k).1) _ hΦ'
    have hA₀ : ((μ.real (congruenceSubgroup F m r₀ : Set (GL (Fin m) F)) : ℝ) : ℂ) * ℓ₀ v₀ ≠ 0 := by
      refine mul_ne_zero ?_ hℓ₀v₀
      have : μ.real (congruenceSubgroup F m r₀ : Set (GL (Fin m) F)) ≠ 0 := by
        rw [measureReal_ne_zero_iff ((isCompact_congruenceSubgroup F m r₀).measure_lt_top.ne)]
        exact ((isOpen_congruenceSubgroup F m r₀).measure_pos μ ⟨1, one_mem _⟩).ne'
      exact_mod_cast this
    have hFE' := hFE Φ' hΦ' v₀ ℓ₀ hℓ₀
    rw [hF] at hFE'
    obtain ⟨c, j, hc, hγ⟩ := core (hFE _ he₀ v₀ ℓ₀ hℓ₀) hFE' (D := 1) (D' := 1) one_ne_zero one_ne_zero hA₀ hA₀ (i := 0)
      (LF.sum S fun k => LF.mono' (qs F (m : ℂ)) (a k) k) (LF.sum S' fun k => LF.mono (a' k) k) (t := t) (t' := t + m)
      (fun s hs => ⟨by simp, by rw [blockA_indGL μ hv₀]; simp, by rw [blockA, hS' s (hR s hs)]; simp⟩)
      (fun s hs => ⟨by simp, by rw [blockB, hS _ (hLft s hs), qs_natCast_sub]; simp, by rw [blockB_ind μ hv₀]; simp⟩)
    exact ⟨c, j, hc, by simpa using hγ⟩

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
