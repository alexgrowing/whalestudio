import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.NormEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Descent
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IsFixMapIff

namespace UpperTheory.V.Z.Sym.Loc.OE

open IsLocalRing QuadraticAlgebra Matrix UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ : K}

theorem int_star (L : IsLoc O Δ) {x : Lsq K Δ} (h : IsInt O x) : IsInt O (star x) := by
  obtain ⟨ε, s, hs0, hΔ⟩ := L.even
  exact (descent O K Δ L s⁻¹ ε (by rw [hΔ]; field_simp) x).2 h

theorem multiple (L : IsLoc O Δ) {I : Type} (t : Finset I) (f : I → Lsq K Δ) : ∃ a : O, a ≠ 0 ∧ ∀ i ∈ t, IsInt O (a • f i) := by
  obtain ⟨u, s, hs0, hΔ⟩ := L.even
  have hs2 : Δ * s⁻¹ ^ 2 = algebraMap O K ↑u := by
    rw [hΔ]
    field_simp
  have hdes := descent O K Δ L s⁻¹ u hs2
  haveI := L.frac
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O)
    (t ×ˢ (Finset.univ : Finset Bool)) (fun p : I × Bool => if p.2 then (f p.1).im * s else (f p.1).re)
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, fun i hi => ?_⟩
  refine (hdes _).1.2 ⟨?_, ?_⟩
  · obtain ⟨r, hr⟩ := hb (i, false) (Finset.mem_product.2 ⟨hi, Finset.mem_univ _⟩)
    refine ⟨r, ?_⟩
    simp only [Bool.false_eq_true, if_false] at hr
    rw [re_smul]
    exact hr
  · obtain ⟨r, hr⟩ := hb (i, true) (Finset.mem_product.2 ⟨hi, Finset.mem_univ _⟩)
    refine ⟨r, ?_⟩
    simp only [if_true] at hr
    rw [im_smul]
    change algebraMap O K r = (b : O) • ((f i).im * s) at hr
    rw [hr, Algebra.smul_def, Algebra.smul_def]
    field_simp

def B (x y : Fin 3 → Lsq K Δ) : Lsq K Δ := ∑ i, x i * star (y i)

theorem B_star (x y : Fin 3 → Lsq K Δ) : star (B x y) = B y x := by simp [B, mul_comm]

theorem B_smul_left (r : Lsq K Δ) (x y : Fin 3 → Lsq K Δ) : B (r • x) y = r * B x y := by simp [B, Finset.mul_sum, mul_assoc]

theorem B_smul_right (r : Lsq K Δ) (x y : Fin 3 → Lsq K Δ) : B x (r • y) = star r * B x y := by
  simp only [B, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_mul']
  ring

theorem B_add_left (x x' y : Fin 3 → Lsq K Δ) : B (x + x') y = B x y + B x' y := by simp [B, add_mul, Finset.sum_add_distrib]

theorem B_add_right (x y y' : Fin 3 → Lsq K Δ) : B x (y + y') = B x y + B x y' := by simp [B, mul_add, Finset.sum_add_distrib]

theorem B_sub_left (x x' y : Fin 3 → Lsq K Δ) : B (x - x') y = B x y - B x' y := by simp [B, sub_mul, Finset.sum_sub_distrib]

private theorem eventually_abs_le_half_add_of_doubling_bounds (x : Fin 3 → Lsq K Δ) : B x 0 = 0 := by
  simp [B]

private theorem v_sub_one_add_le_v_pow_l_sub_one (L : IsLoc O Δ) (M : Submodule O (Fin 3 → Lsq K Δ))
    (hd : ∀ y, y ∈ M ↔ ∀ x ∈ M, IsInt O (B x y)) {c : Lsq K Δ} (hc : IsInt O c)
    {y : Fin 3 → Lsq K Δ} (hy : y ∈ M) : c • y ∈ M :=
  (hd _).2 fun x hx => by
    rw [B_smul_right]
    exact IsIntegral.mul (int_star L hc) ((hd y).1 hy x hx)

private theorem step_lemma_3 (L : IsLoc O Δ) (z : Lsq K Δ) (hz : IsInt O z) (hs : star z = z) :
    ∃ r : O, z = algebraMap O (Lsq K Δ) r := by
  obtain ⟨u, t, ht0, hΔ⟩ := L.even
  have hs2 : Δ * t⁻¹ ^ 2 = algebraMap O K ↑u := by
    rw [hΔ]
    field_simp
  obtain ⟨⟨r, hr⟩, -⟩ := (descent O K Δ L t⁻¹ u hs2 z).1.1 hz
  obtain ⟨v, hv⟩ := L.two
  have h2 : (2 : K) ≠ 0 := by
    have : algebraMap O K (v : O) ≠ 0 := by
      simpa using (Units.map (algebraMap O K).toMonoidHom v).ne_zero
    rwa [hv, map_ofNat] at this
  have e0 : (star z).im = z.im := by rw [hs]
  have e1 : (star z).im = -z.im := by simp
  have h' : (2 : K) * z.im = 0 := by
    have := e1.symm.trans e0
    linear_combination -this
  have him : z.im = 0 := (mul_eq_zero.1 h').resolve_left h2
  refine ⟨r, ?_⟩
  rw [IsScalarTower.algebraMap_apply O K (Lsq K Δ)]
  ext
  · rw [QuadraticAlgebra.algebraMap_re, hr]
  · rw [QuadraticAlgebra.algebraMap_im, him]

private theorem sq_enorm_le_two_lintegral_add_two_lintegral_fderiv (L : IsLoc O Δ) {ϖ : O} (hϖ : Irreducible ϖ) (x : K)
    (h : ∀ k : ℕ, (algebraMap O K ϖ)⁻¹ ^ k * x ∈ (algebraMap O K).range) : x = 0 := by
  haveI := L.frac
  have hinj := IsFractionRing.injective O K
  have hϖ0 : algebraMap O K ϖ ≠ 0 := fun h0 => hϖ.ne_zero (hinj (by rw [h0, map_zero]))
  obtain ⟨r, hr⟩ := h 0
  simp only [pow_zero, one_mul] at hr
  have hmem : ∀ k : ℕ, r ∈ (maximalIdeal O) ^ k := by
    intro k
    obtain ⟨rk, hrk⟩ := h k
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    refine ⟨rk, hinj ?_⟩
    rw [map_mul, map_pow, hrk, hr, inv_pow, mul_comm _ x, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hϖ0), mul_one]
  have hr0 : r ∈ ⨅ k : ℕ, (maximalIdeal O) ^ k := (Submodule.mem_iInf _).2 hmem
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal O).ne_top, Ideal.mem_bot] at hr0
  rw [← hr, hr0, map_zero]

private theorem vv_pow_smul_mem_of_sen_eq_zero (L : IsLoc O Δ) {ϖ : O} (hϖ : Irreducible ϖ) (z : Lsq K Δ)
    (h : ∀ k : ℕ, IsInt O (algebraMap K (Lsq K Δ) ((algebraMap O K ϖ)⁻¹ ^ k) * z)) : z = 0 := by
  obtain ⟨u, t, ht0, hΔ⟩ := L.even
  have hs2 : Δ * t⁻¹ ^ 2 = algebraMap O K ↑u := by
    rw [hΔ]
    field_simp
  have hdes := descent O K Δ L t⁻¹ u hs2
  have hre : z.re = 0 := sq_enorm_le_two_lintegral_add_two_lintegral_fderiv L hϖ z.re fun k => by
    have := ((hdes _).1.1 (h k)).1
    simpa using this
  have him : z.im * t = 0 := by
    refine sq_enorm_le_two_lintegral_add_two_lintegral_fderiv L hϖ (z.im * t) fun k => ?_
    obtain ⟨b, hb⟩ := ((hdes _).1.1 (h k)).2
    refine ⟨b, ?_⟩
    simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im,
      zero_mul, mul_zero, add_zero, zero_add] at hb
    rw [← mul_assoc, hb]
    field_simp
  ext
  · simpa using hre
  · simpa [ht0] using him

private theorem exists_smul_isInt_of_fg (L : IsLoc O Δ) (M : Submodule O (Fin 3 → Lsq K Δ)) (hfg : M.FG) :
    ∃ α : O, α ≠ 0 ∧ ∀ m ∈ M, ∀ j, IsInt O (α • m j) := by
  classical
  obtain ⟨S, hS⟩ := hfg
  obtain ⟨α, hα, hαS⟩ := multiple L (S ×ˢ (Finset.univ : Finset (Fin 3))) (fun p => p.1 p.2)
  refine ⟨α, hα, fun m hm => ?_⟩
  rw [← hS] at hm
  induction hm using Submodule.span_induction with
  | mem x hx => exact fun j => hαS (x, j) (Finset.mem_product.2 ⟨Finset.mem_coe.1 hx, Finset.mem_univ _⟩)
  | zero =>
    intro j
    simp only [Pi.zero_apply, smul_zero]
    exact isIntegral_zero
  | add x y _ _ hx hy =>
    intro j
    simp only [Pi.add_apply, smul_add]
    exact IsIntegral.add (hx j) (hy j)
  | smul r x _ hx =>
    intro j
    simp only [Pi.smul_apply]
    rw [smul_comm, Algebra.smul_def]
    exact IsIntegral.mul isIntegral_algebraMap (hx j)

private theorem exists_basis_size_reduce_column (a b : Fin 3 → Lsq K Δ)
    (h : ∀ j k : Fin 3, (if j = k then (1 : Lsq K Δ) else 0) = star (a j) * a k + star (b j) * b k) :
    False := by
  let A : Matrix (Fin 3) (Fin 3) (Lsq K Δ) := Matrix.of fun j i => ![star (a j), star (b j), 0] i
  let C : Matrix (Fin 3) (Fin 3) (Lsq K Δ) := Matrix.of fun i k => ![a k, b k, 0] i
  have hAC : (1 : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) = A * C := by
    refine Matrix.ext fun j k => ?_
    rw [Matrix.one_apply, h j k]
    simp [A, C, Matrix.mul_apply, Fin.sum_univ_three]
  have hA : A.det = 0 := Matrix.det_eq_zero_of_column_eq_zero 2 fun j => by simp [A]
  have := congrArg Matrix.det hAC
  rw [Matrix.det_one, Matrix.det_mul, hA, zero_mul] at this
  exact one_ne_zero this

theorem step (L : IsLoc O Δ) (M : Submodule O (Fin 3 → Lsq K Δ)) (hfg : M.FG) (hd : ∀ y, y ∈ M ↔ ∀ x ∈ M, IsInt O (B x y))
    {a b : Fin 3 → Lsq K Δ} (ha : a ∈ M) (hb : b ∈ M) (ha' : a = 0 ∨ B a a = 1) (hb' : b = 0 ∨ B b b = 1) (hab : B a b = 0) :
    ∃ e ∈ M, B e e = 1 ∧ B e a = 0 ∧ B e b = 0 := by
  classical
  obtain ⟨u, t, ht0, hΔ⟩ := L.even
  have hs2 : Δ * t⁻¹ ^ 2 = algebraMap O K ↑u := by
    rw [hΔ]
    field_simp
  have hdes := descent O K Δ L t⁻¹ u hs2
  obtain ⟨v, hv⟩ := L.two
  haveI := L.frac
  have hinj := IsFractionRing.injective O K
  obtain ⟨w, hwdef⟩ : ∃ w : Lsq K Δ, w = ⟨0, t⁻¹⟩ := ⟨_, rfl⟩
  obtain ⟨U, hUdef⟩ : ∃ U : Lsq K Δ, U = algebraMap O (Lsq K Δ) ↑u := ⟨_, rfl⟩
  obtain ⟨hh, hhdef⟩ : ∃ hh : Lsq K Δ, hh = algebraMap O (Lsq K Δ) ↑v⁻¹ := ⟨_, rfl⟩
  obtain ⟨e, edef⟩ : ∃ e : Lsq K Δ, e = algebraMap O (Lsq K Δ) ↑u⁻¹ := ⟨_, rfl⟩
  have hww : w * w = U := by
    rw [hUdef, IsScalarTower.algebraMap_apply O K (Lsq K Δ), ← hs2]
    have : algebraMap K (Lsq K Δ) (Δ * t⁻¹ ^ 2) = ⟨Δ * t⁻¹ ^ 2, 0⟩ := by
      ext
      · exact QuadraticAlgebra.algebraMap_re _
      · exact QuadraticAlgebra.algebraMap_im _
    rw [this, hwdef]
    ext <;> simp <;> ring
  have hsw : star w = -w := by
    rw [hwdef]
    ext <;> simp
  have hh2 : hh * 2 = 1 := by
    rw [hhdef, ← map_ofNat (algebraMap O (Lsq K Δ)) 2, ← hv, ← map_mul, Units.inv_mul, map_one]
  have heu : e * U = 1 := by
    rw [edef, hUdef, ← map_mul, Units.inv_mul, map_one]
  have iw : IsIntegral O w := by
    refine (hdes w).1.2 ⟨?_, 1, ?_⟩
    · rw [hwdef]
      exact ⟨0, map_zero _⟩
    · rw [hwdef]
      simp
  have ih : IsIntegral O hh := by
    rw [hhdef]
    exact isIntegral_algebraMap
  have ie : IsIntegral O e := by
    rw [edef]
    exact isIntegral_algebraMap
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖ0 : algebraMap O K ϖ ≠ 0 := fun h0 => hϖ.ne_zero (hinj (by rw [h0, map_zero]))
  obtain ⟨c, hcdef⟩ : ∃ c : Lsq K Δ, c = algebraMap K (Lsq K Δ) (algebraMap O K ϖ)⁻¹ := ⟨_, rfl⟩
  have hcs : star c = c := by
    rw [hcdef]
    ext <;> simp
  have hcϖ : c * algebraMap O (Lsq K Δ) ϖ = 1 := by
    rw [hcdef, IsScalarTower.algebraMap_apply O K (Lsq K Δ), ← map_mul, inv_mul_cancel₀ hϖ0, map_one]
  have hstarO : ∀ r : O, star (algebraMap O (Lsq K Δ) r) = algebraMap O (Lsq K Δ) r := by
    intro r
    rw [IsScalarTower.algebraMap_apply O K (Lsq K Δ)]
    ext <;> simp
  have hBba : B b a = 0 := by rw [← B_star, hab, star_zero]
  have hPa : ∀ x, B (x - B x a • a - B x b • b) a = 0 := by
    intro x
    rw [B_sub_left, B_sub_left, B_smul_left, B_smul_left, hBba, mul_zero, sub_zero]
    rcases ha' with h | h
    · subst h
      simp [eventually_abs_le_half_add_of_doubling_bounds]
    · rw [h, mul_one, sub_self]
  have hPb : ∀ x, B (x - B x a • a - B x b • b) b = 0 := by
    intro x
    rw [B_sub_left, B_sub_left, B_smul_left, B_smul_left, hab, mul_zero, sub_zero]
    rcases hb' with h | h
    · subst h
      simp [eventually_abs_le_half_add_of_doubling_bounds]
    · rw [h, mul_one, sub_self]
  have hPM : ∀ x ∈ M, x - B x a • a - B x b • b ∈ M := fun x hx =>
    M.sub_mem (M.sub_mem hx (v_sub_one_add_le_v_pow_l_sub_one L M hd ((hd a).1 ha x hx) ha)) (v_sub_one_add_le_v_pow_l_sub_one L M hd ((hd b).1 hb x hx) hb)
  have hBP : ∀ x y, B y a = 0 → B y b = 0 → B (x - B x a • a - B x b • b) y = B x y := by
    intro x y hya hyb
    rw [B_sub_left, B_sub_left, B_smul_left, B_smul_left, ← B_star y a, ← B_star y b, hya, hyb, star_zero,
      mul_zero, mul_zero, sub_zero, sub_zero]
  by_contra hcon
  push_neg at hcon
  have hq : ∀ y ∈ M, B y a = 0 → B y b = 0 → IsInt O (c * B y y) := by
    intro y hy hya hyb
    obtain ⟨r, hr⟩ := step_lemma_3 L (B y y) ((hd y).1 hy y hy) (B_star y y)
    by_cases hru : IsUnit r
    · exfalso
      obtain ⟨ν, hνi, hνn⟩ := normEx O K Δ L hru.unit⁻¹
      have hνν : ν * star ν = algebraMap O (Lsq K Δ) ↑hru.unit⁻¹ := by
        have : ν * star ν = algebraMap K (Lsq K Δ) (QuadraticAlgebra.norm ν) := by
          ext <;> simp [QuadraticAlgebra.norm] <;> ring
        rw [this, hνn, ← IsScalarTower.algebraMap_apply]
      refine hcon (ν • y) (v_sub_one_add_le_v_pow_l_sub_one L M hd hνi hy) ?_ ?_ ?_
      · rw [B_smul_left, B_smul_right, hr, ← mul_assoc, hνν, ← map_mul, hru.val_inv_mul, map_one]
      · rw [B_smul_left, hya, mul_zero]
      · rw [B_smul_left, hyb, mul_zero]
    · have hrm : r ∈ maximalIdeal O := (IsLocalRing.mem_maximalIdeal r).2 hru
      rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hrm
      obtain ⟨r', hr'⟩ := hrm
      have : c * B y y = algebraMap O (Lsq K Δ) r' := by
        rw [hr, ← hr', map_mul, mul_left_comm, hcϖ, mul_one]
      rw [this]
      exact isIntegral_algebraMap
  have hpol : ∀ y ∈ M, ∀ z ∈ M, B y a = 0 → B y b = 0 → B z a = 0 → B z b = 0 → IsInt O (c * B y z) := by
    intro y hy z hz hya hyb hza hzb
    have hγ : ∀ γ : Lsq K Δ, IsInt O γ → IsInt O (c * (star γ * B y z + γ * star (B y z))) := by
      intro γ hγ
      have hm : y + γ • z ∈ M := M.add_mem hy (v_sub_one_add_le_v_pow_l_sub_one L M hd hγ hz)
      have h1 := hq (y + γ • z) hm (by rw [B_add_left, B_smul_left, hya, hza, mul_zero, add_zero])
        (by rw [B_add_left, B_smul_left, hyb, hzb, mul_zero, add_zero])
      have h2 := hq y hy hya hyb
      have h3 := hq z hz hza hzb
      have hexp : B (y + γ • z) (y + γ • z)
          = B y y + (star γ * B y z + γ * star (B y z)) + γ * star γ * B z z := by
        simp only [B_add_left, B_add_right, B_smul_left, B_smul_right]
        rw [← B_star y z]
        ring
      have hid : c * (star γ * B y z + γ * star (B y z))
          = c * B (y + γ • z) (y + γ • z) - c * B y y - γ * star γ * (c * B z z) := by
        rw [hexp]
        ring
      rw [hid]
      exact IsIntegral.sub (IsIntegral.sub h1 h2) (IsIntegral.mul (IsIntegral.mul hγ (int_star L hγ)) h3)
    have e1 := hγ 1 isIntegral_one
    have e2 := hγ w iw
    rw [star_one, one_mul, one_mul] at e1
    rw [hsw] at e2
    have hid : c * B y z = hh * (c * (B y z + star (B y z)))
        - hh * e * w * (c * (-w * B y z + w * star (B y z))) := by
      linear_combination -(c * B y z) * hh2 - hh * e * c * (B y z - star (B y z)) * hww
        - hh * c * (B y z - star (B y z)) * heu
    rw [hid]
    exact IsIntegral.sub (IsIntegral.mul ih e1) (IsIntegral.mul (IsIntegral.mul (IsIntegral.mul ih ie) iw) e2)
  have hcN : ∀ y ∈ M, B y a = 0 → B y b = 0 → c • y ∈ M := by
    intro y hy hya hyb
    refine (hd _).2 fun x hx => ?_
    rw [B_smul_right, hcs, ← hBP x y hya hyb]
    exact hpol _ (hPM x hx) y hy (hPa x) (hPb x) hya hyb
  have hpow : ∀ y ∈ M, B y a = 0 → B y b = 0 → ∀ k : ℕ, c ^ k • y ∈ M := by
    intro y hy hya hyb k
    induction k with
    | zero => simpa using hy
    | succ k ihk =>
      rw [pow_succ', mul_smul]
      exact hcN _ ihk (by rw [B_smul_left, hya, mul_zero]) (by rw [B_smul_left, hyb, mul_zero])
  obtain ⟨α, hα0, hαM⟩ := exists_smul_isInt_of_fg L M hfg
  have hαK : algebraMap O K α ≠ 0 := fun h0 => hα0 (hinj (by rw [h0, map_zero]))
  have hαL : IsUnit (algebraMap O (Lsq K Δ) α) := by
    rw [IsScalarTower.algebraMap_apply O K (Lsq K Δ)]
    exact (isUnit_iff_ne_zero.2 hαK).map _
  have hzero : ∀ y ∈ M, B y a = 0 → B y b = 0 → y = 0 := by
    intro y hy hya hyb
    funext j
    have key := vv_pow_smul_mem_of_sen_eq_zero L hϖ (α • y j) fun k => by
      have h1 := hαM _ (hpow y hy hya hyb k) j
      rw [map_pow, ← hcdef]
      convert h1 using 1
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Algebra.smul_def, Algebra.smul_def]
      ring
    rw [Algebra.smul_def] at key
    exact hαL.mul_right_eq_zero.1 key
  have hE : ∀ j : Fin 3, Pi.single j (algebraMap O (Lsq K Δ) α) ∈ M := by
    intro j
    refine (hd _).2 fun x hx => ?_
    have hB : B x (Pi.single j (algebraMap O (Lsq K Δ) α)) = α • x j := by
      have h1 : B x (Pi.single j (algebraMap O (Lsq K Δ) α)) = x j * star (algebraMap O (Lsq K Δ) α) := by
        unfold B
        rw [Finset.sum_eq_single j (fun i _ hij => by rw [Pi.single_eq_of_ne hij, star_zero, mul_zero])
          (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same]
      rw [h1, hstarO, Algebra.smul_def, mul_comm]
    rw [hB]
    exact hαM x hx j
  have hrel : ∀ j k : Fin 3, (if j = k then (1 : Lsq K Δ) else 0) = star (a j) * a k + star (b j) * b k := by
    intro j k
    have h0 := hzero _ (hPM _ (hE j)) (hPa _) (hPb _)
    have hk := congrFun h0 k
    have hBEa : B (Pi.single j (algebraMap O (Lsq K Δ) α)) a = algebraMap O (Lsq K Δ) α * star (a j) := by
      simp [B, Pi.single_apply]
    have hBEb : B (Pi.single j (algebraMap O (Lsq K Δ) α)) b = algebraMap O (Lsq K Δ) α * star (b j) := by
      simp [B, Pi.single_apply]
    rw [hBEa, hBEb] at hk
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hk
    apply hαL.mul_left_cancel
    by_cases hjk : j = k
    · subst hjk
      rw [Pi.single_eq_same] at hk
      rw [if_pos rfl]
      linear_combination hk
    · rw [Pi.single_eq_of_ne (Ne.symm hjk)] at hk
      rw [if_neg hjk]
      linear_combination hk
  exact exists_basis_size_reduce_column a b hrel

theorem ortho (L : IsLoc O Δ) (M : Submodule O (Fin 3 → Lsq K Δ)) (hfg : M.FG) (hd : ∀ y, y ∈ M ↔ ∀ x ∈ M, IsInt O (B x y)) :
    ∃ g : U3 Δ, ∀ x, x ∈ M ↔ ∀ i, IsInt O ((((g⁻¹ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ x) i) := by
  classical
  obtain ⟨e1, h1M, h11, -, -⟩ := step L M hfg hd M.zero_mem M.zero_mem (Or.inl rfl) (Or.inl rfl) (eventually_abs_le_half_add_of_doubling_bounds 0)
  obtain ⟨e2, h2M, h22, h21, -⟩ := step L M hfg hd h1M M.zero_mem (Or.inr h11) (Or.inl rfl) (eventually_abs_le_half_add_of_doubling_bounds e1)
  have h12 : B e1 e2 = 0 := by rw [← B_star, h21, star_zero]
  obtain ⟨e3, h3M, h33, h31, h32⟩ := step L M hfg hd h1M h2M (Or.inr h11) (Or.inr h22) h12
  have h13 : B e1 e3 = 0 := by rw [← B_star, h31, star_zero]
  have h23 : B e2 e3 = 0 := by rw [← B_star, h32, star_zero]
  let E : Fin 3 → (Fin 3 → Lsq K Δ) := ![e1, e2, e3]
  have hEM : ∀ j, E j ∈ M := by
    intro j
    fin_cases j
    · exact h1M
    · exact h2M
    · exact h3M
  have hEB : ∀ j k, B (E k) (E j) = if j = k then 1 else 0 := by
    intro j k
    fin_cases j <;> fin_cases k <;> simp [E, h11, h22, h33, h12, h13, h23, h21, h31, h32]
  let G : Matrix (Fin 3) (Fin 3) (Lsq K Δ) := Matrix.of fun i j => E j i
  have hGG : star G * G = 1 := by
    refine Matrix.ext fun j k => ?_
    rw [Matrix.one_apply, ← hEB j k]
    simp only [Matrix.mul_apply, Matrix.star_apply, G, Matrix.of_apply, B]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hmem : G ∈ unitaryGroup (Fin 3) (Lsq K Δ) := Matrix.mem_unitaryGroup_iff'.2 hGG
  let g : U3 Δ := ⟨G, hmem⟩
  refine ⟨g, fun x => ?_⟩
  have hinv : ((g⁻¹ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) = star G := by
    rfl
  have hcoord : ∀ i, (((g⁻¹ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ x) i = B x (E i) := by
    intro i
    rw [hinv]
    simp only [Matrix.mulVec, dotProduct, Matrix.star_apply, G, Matrix.of_apply, B]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  simp only [hcoord]
  constructor
  · intro hx i
    exact (hd (E i)).1 (hEM i) x hx
  · intro hx
    have hGG' : G * star G = 1 := mul_eq_one_comm.1 hGG
    have hx' : x = ∑ j, B x (E j) • E j := by
      have h0 : x = G *ᵥ (star G *ᵥ x) := by rw [Matrix.mulVec_mulVec, hGG', Matrix.one_mulVec]
      conv_lhs => rw [h0]
      funext k
      simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, G, Matrix.of_apply,
        Matrix.star_apply, B]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_comm]
      congr 1
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    rw [hx']
    exact M.sum_mem fun j _ => v_sub_one_add_le_v_pow_l_sub_one L M hd (hx j) (hEM j)

end UpperTheory.V.Z.Sym.Loc.OE
