import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.CintIdx

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc Matrix

namespace UpperTheory.V.Z.Sym.Loc

private theorem cyc {O : Type} [CommRing O] [IsLocalRing O] (B : Matrix (Fin 2) (Fin 2) O) (τ : O)
    (htr : B.trace = τ) (hdet : B.det = 1) (hu : IsUnit (τ ^ 2 - 4)) :
    ∃ g : GL (Fin 2) O, B * (g : Matrix (Fin 2) (Fin 2) O) = (g : Matrix (Fin 2) (Fin 2) O) * !![0, -1; 1, τ] := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, B = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two B⟩
  rw [Matrix.trace_fin_two_of] at htr
  rw [Matrix.det_fin_two_of] at hdet
  subst htr
  have mk : ∀ (g : Matrix (Fin 2) (Fin 2) O), IsUnit g.det →
      !![a, b; c, d] * g = g * !![0, -1; 1, a + d] →
      ∃ g : GL (Fin 2) O, !![a, b; c, d] * (g : Matrix (Fin 2) (Fin 2) O) = (g : Matrix (Fin 2) (Fin 2) O) * !![0, -1; 1, a + d] :=
    fun g hg h => ⟨GeneralLinearGroup.mk'' g hg, h⟩
  by_cases hc : IsUnit c
  · refine mk !![1, a; 0, c] (by simpa [Matrix.det_fin_two_of] using hc) ?_
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | linear_combination -hdet | linear_combination hdet
  by_cases hb : IsUnit b
  · refine mk !![0, b; 1, d] (by simpa [Matrix.det_fin_two_of] using hb) ?_
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | linear_combination -hdet | linear_combination hdet
  have hm : ∀ x : O, ¬ IsUnit x → x ∈ IsLocalRing.maximalIdeal O := fun x hx => hx
  have hdet' : IsUnit (c + d - a - b) := by
    by_contra hn
    have h1 := hm _ hn
    have h2 : a - d ∈ IsLocalRing.maximalIdeal O := by
      have : a - d = (c - b) - (c + d - a - b) := by ring
      rw [this]
      exact Ideal.sub_mem _ (Ideal.sub_mem _ (hm _ hc) (hm _ hb)) h1
    have h3 : (a + d) ^ 2 - 4 ∈ IsLocalRing.maximalIdeal O := by
      have : (a + d) ^ 2 - 4 = (a - d) * (a - d) + 4 * b * c := by linear_combination 4 * hdet
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h2) (Ideal.mul_mem_left _ _ (hm _ hc))
    exact h3 hu
  refine mk !![1, a + b; 1, c + d] (by rw [Matrix.det_fin_two_of]; convert hdet' using 1; ring) ?_
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination -hdet | linear_combination hdet

section

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ τ : K}

private theorem j_eq (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K) (x : Etau K τ) :
    j x = x.re • (1 : Matrix (Fin 2) (Fin 2) K) + x.im • j ω := by
  conv_lhs => rw [show x = algebraMap K (Etau K τ) x.re + x.im • ω by ext <;> simp]
  rw [map_add, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one]

private theorem j_det_one (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K) (ht : (j ω).trace = τ) :
    (j ω).det = 1 := by
  have h : j ω * j ω = (-1 : K) • 1 + τ • j ω := by
    rw [← map_mul, omega_mul_omega_eq_add, map_add, map_smul, map_smul, map_one]
  have h00 := congrFun (congrFun h 0) 0
  rw [Matrix.trace_fin_two] at ht
  rw [Matrix.det_fin_two]
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00
  linear_combination -h00 + (j ω 0 0) * ht

private theorem j_tr (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K) (ht : (j ω).trace = τ) (x : Etau K τ) :
    (j x).trace = QuadraticAlgebra.trace x := by
  rw [j_eq, QuadraticAlgebra.trace_def]
  rw [Matrix.trace_fin_two] at ht ⊢
  simp
  linear_combination x.im * ht

private theorem j_det (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K) (ht : (j ω).trace = τ) (x : Etau K τ) :
    (j x).det = QuadraticAlgebra.norm x := by
  have hd := j_det_one j ht
  rw [j_eq, QuadraticAlgebra.norm_def]
  rw [Matrix.trace_fin_two] at ht
  rw [Matrix.det_fin_two] at hd ⊢
  simp
  linear_combination (x.im ^ 2) * hd + (x.re * x.im) * ht

private theorem coe_jU (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K) (z : (Etau K τ)ˣ) :
    ((jU j z : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = j z := rfl

private theorem coe_map' (g : GL (Fin 2) O) :
    ((Matrix.GeneralLinearGroup.map (algebraMap O K) g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (g : Matrix (Fin 2) (Fin 2) O).map (algebraMap O K) := rfl

private theorem coe_scal (s : Kˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) s : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (s : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext a b
  by_cases h : a = b <;> simp [Matrix.GeneralLinearGroup.scalar, Matrix.one_apply, h]

private theorem lift_mat (A : Matrix (Fin 2) (Fin 2) K) (h : ∀ s t, A s t ∈ (algebraMap O K).range) :
    ∃ A₀ : Matrix (Fin 2) (Fin 2) O, A₀.map (algebraMap O K) = A := by
  choose f hf using h
  exact ⟨Matrix.of f, by ext s t; exact hf s t⟩

private theorem mem_KG (hinj : Function.Injective (algebraMap O K)) (x : GL (Fin 2) K)
    (h : ∀ s t, (x : Matrix (Fin 2) (Fin 2) K) s t ∈ (algebraMap O K).range)
    (hd : ∃ u : Oˣ, algebraMap O K u = (x : Matrix (Fin 2) (Fin 2) K).det) : x ∈ KG O K := by
  obtain ⟨A₀, hA⟩ := lift_mat (O := O) _ h
  obtain ⟨u, hu⟩ := hd
  have hdet : A₀.det = u := hinj (by
    rw [hu, ← hA, RingHom.map_det]; rfl)
  exact ⟨Matrix.GeneralLinearGroup.mk'' A₀ (hdet ▸ u.isUnit), Units.ext hA⟩

private theorem mem_ZK {g : GL (Fin 2) K} :
    g ∈ ZK O K ↔ ∃ s : Kˣ, ∃ k ∈ KG O K, g = Matrix.GeneralLinearGroup.scalar (Fin 2) s * k := by
  constructor
  · intro hg
    haveI : (Matrix.GeneralLinearGroup.scalar (Fin 2) : Kˣ →* GL (Fin 2) K).range.Normal := ⟨by
      rintro _ ⟨s, rfl⟩ x
      refine ⟨s, ?_⟩
      have comm : x * Matrix.GeneralLinearGroup.scalar (Fin 2) s = Matrix.GeneralLinearGroup.scalar (Fin 2) s * x :=
        Units.ext (by rw [Units.val_mul, Units.val_mul, coe_scal]; simp)
      rw [comm]; simp⟩
    have := (Subgroup.normal_mul (Matrix.GeneralLinearGroup.scalar (Fin 2) : Kˣ →* GL (Fin 2) K).range (KG O K))
    have hg' : g ∈ ((ZK O K : Subgroup _) : Set (GL (Fin 2) K)) := hg
    rw [ZK, this] at hg'
    obtain ⟨_, ⟨s, rfl⟩, k, hk, rfl⟩ := Set.mem_mul.1 hg'
    exact ⟨s, k, hk, rfl⟩
  · rintro ⟨s, k, hk, rfl⟩
    exact mul_mem (Subgroup.mem_sup_left ⟨s, rfl⟩) (Subgroup.mem_sup_right hk)

private theorem quo_norm (z : (Etau K τ)ˣ) (s : K) (hs : s ≠ 0) (w : Etau K τ) (hzw : (z : Etau K τ) = s • w) :
    quo z * algebraMap K (Etau K τ) (QuadraticAlgebra.norm w) = w ^ 2 := by
  have h1 : star (z : Etau K τ) * star ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) = 1 := by
    rw [← star_mul]; simp
  have h2 : star (z : Etau K τ) = algebraMap K (Etau K τ) s * star w := by
    rw [hzw]; ext <;> simp <;> ring
  have hz' : (z : Etau K τ) = algebraMap K (Etau K τ) s * w := by rw [hzw, Algebra.smul_def]
  have h3 : s • (quo z * algebraMap K (Etau K τ) (QuadraticAlgebra.norm w)) = s • w ^ 2 := by
    rw [algebraMap_norm_eq_mul_star, quo, Algebra.smul_def, Algebra.smul_def]
    calc _ = (z : Etau K τ) * w * ((algebraMap K (Etau K τ) s * star w) * star ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ)) := by ring
      _ = (z : Etau K τ) * w := by rw [← h2, h1, mul_one]
      _ = _ := by rw [hz']; ring
  have := congrArg (fun x => s⁻¹ • x) h3
  simpa [smul_smul, inv_mul_cancel₀ hs] using this

private theorem isInt_w (w : Etau K τ) (a n : O) (ha : QuadraticAlgebra.trace w = algebraMap O K a)
    (hn : QuadraticAlgebra.norm w = algebraMap O K n) : IsIntegral O w := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C a * Polynomial.X + Polynomial.C n, by monicity!, ?_⟩
  have := sq_sub_trace_smul_add_norm_eq_zero w
  rw [ha, hn, Algebra.smul_def] at this
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C]
  rw [IsScalarTower.algebraMap_apply O K (Etau K τ) a, IsScalarTower.algebraMap_apply O K (Etau K τ) n]
  exact this

private theorem quo_int (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K) (ht : (j ω).trace = τ)
    (z : (Etau K τ)ˣ) (hz : jU j z ∈ ZK O K) : IsIntegral O (quo z) := by
  obtain ⟨s, k, ⟨k₀, rfl⟩, e⟩ := mem_ZK.1 hz
  set w : Etau K τ := ((s⁻¹ : Kˣ) : K) • (z : Etau K τ) with hw
  have hjz : j z = (s : K) • (k₀ : Matrix (Fin 2) (Fin 2) O).map (algebraMap O K) := by
    have := congrArg Units.val e
    rw [Units.val_mul, coe_scal, coe_jU, coe_map'] at this
    rw [this]; simp
  have hjw : j w = (k₀ : Matrix (Fin 2) (Fin 2) O).map (algebraMap O K) := by
    rw [hw, map_smul, hjz, smul_smul]; simp
  have h1 : QuadraticAlgebra.trace w = algebraMap O K (k₀ : Matrix (Fin 2) (Fin 2) O).trace := by
    rw [← j_tr j ht, hjw, Matrix.trace_fin_two, Matrix.trace_fin_two]; simp
  have h2 : QuadraticAlgebra.norm w = algebraMap O K (k₀ : Matrix (Fin 2) (Fin 2) O).det := by
    rw [← j_det j ht, hjw, RingHom.map_det]; rfl
  have hwi := isInt_w (O := O) w _ _ h1 h2
  obtain ⟨n, hn⟩ := Matrix.isUnits_det_units k₀
  have hzw : (z : Etau K τ) = (s : K) • w := by rw [hw, smul_smul]; simp
  have h3 := quo_norm z s s.ne_zero w hzw
  rw [h2, ← hn] at h3
  have h4 : quo z = algebraMap O (Etau K τ) ((n⁻¹ : Oˣ) : O) * w ^ 2 := by
    rw [← h3, ← IsScalarTower.algebraMap_apply O K (Etau K τ), mul_comm, mul_assoc, ← map_mul]
    simp
  rw [h4]
  exact isIntegral_algebraMap.mul (hwi.pow 2)

private theorem tr_int (h : IsLoc O Δ) {x : Etau K τ} (hx : IsIntegral O x) :
    ∃ c : O, algebraMap O K c = QuadraticAlgebra.trace x := by
  haveI := h.frac
  have hinj : Function.Injective (IsScalarTower.toAlgHom O K (Etau K τ)) := algebraMap_injective
  exact IsIntegrallyClosed.isIntegral_iff.1 ((isIntegral_algHom_iff _ hinj).1 (by
    change IsIntegral O (algebraMap K (Etau K τ) _)
    rw [algebraMap_trace_eq_add_star]; exact hx.add (isIntegral_star_quad hx)))

private theorem prim (h : IsLoc O Δ) (x y : K) (hxy : ¬ (x = 0 ∧ y = 0)) :
    ∃ (s : K) (a b : O), s ≠ 0 ∧ x = s * algebraMap O K a ∧ y = s * algebraMap O K b ∧ (a = 1 ∨ b = 1) := by
  haveI := h.frac
  by_cases hx : x = 0
  · have hy : y ≠ 0 := fun hy => hxy ⟨hx, hy⟩
    exact ⟨y, 0, 1, hy, by simp [hx], by simp, Or.inr rfl⟩
  rcases ValuationRing.isInteger_or_isInteger O (y / x) with ⟨b, hb⟩ | ⟨a, ha⟩
  · refine ⟨x, 1, b, hx, by simp, ?_, Or.inl rfl⟩
    rw [show algebraMap O K b = y / x from hb]; field_simp
  · have ha' : algebraMap O K a = x / y := by rw [show algebraMap O K a = (y / x)⁻¹ from ha, inv_div]
    by_cases hy : y = 0
    · refine ⟨x, 1, 0, hx, by simp, by simp [hy], Or.inl rfl⟩
    · refine ⟨y, a, 1, hy, ?_, by simp, Or.inr rfl⟩
      rw [ha']; field_simp

private theorem ent_j (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K)
    (hent : ∀ s t, j ω s t ∈ (algebraMap O K).range) (x : Etau K τ)
    (h1 : x.re ∈ (algebraMap O K).range) (h2 : x.im ∈ (algebraMap O K).range) (s t : Fin 2) :
    j x s t ∈ (algebraMap O K).range := by
  rw [j_eq, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
  refine add_mem (mul_mem h1 ?_) (mul_mem h2 (hent s t))
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

private theorem cint_zk (h : IsLoc O Δ) (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K) (ht : (j ω).trace = τ)
    (hent : ∀ s t, j ω s t ∈ (algebraMap O K).range) (τ₀ : O) (hτ₀ : algebraMap O K τ₀ = τ)
    (hu : IsUnit (τ₀ ^ 2 - 4)) (z : (Etau K τ)ˣ) (hz : z ∈ Cint O τ) : jU j z ∈ ZK O K := by
  haveI := h.frac
  have hinj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have hz0 : ¬ ((z : Etau K τ).re = 0 ∧ (z : Etau K τ).im = 0) := fun h0 =>
    z.ne_zero (QuadraticAlgebra.ext h0.1 h0.2)
  obtain ⟨s, a, b, hs, ha, hb, hab⟩ := prim h _ _ hz0
  set w : Etau K τ := ⟨algebraMap O K a, algebraMap O K b⟩ with hw
  have hzw : (z : Etau K τ) = s • w := by ext <;> simp [hw, ha, hb]
  set n : O := a * a + τ₀ * a * b + b * b with hn
  set t : O := 2 * a + τ₀ * b with htdef
  have hnw : QuadraticAlgebra.norm w = algebraMap O K n := by
    simp [hw, hn, QuadraticAlgebra.norm_def, hτ₀]
  have htw : QuadraticAlgebra.trace w = algebraMap O K t := by
    simp [hw, htdef, QuadraticAlgebra.trace_def, hτ₀, map_ofNat]
  obtain ⟨c, hc⟩ := tr_int h hz.1
  have key : (c + 2) * n = t * t := hinj (by
    have h1 := quo_norm z s hs w hzw
    have h2 := congrArg QuadraticAlgebra.trace h1
    rw [mul_comm, ← Algebra.smul_def, map_smul, sq_eq_trace_smul_sub_norm, map_sub, map_smul,
      QuadraticAlgebra.trace_algebraMap, smul_eq_mul, smul_eq_mul, ← hc, htw, hnw] at h2
    simp only [map_mul, map_add, map_ofNat]
    linear_combination h2)
  have hm : ∀ x : O, ¬ IsUnit x → x ∈ IsLocalRing.maximalIdeal O := fun x hx => hx
  have hnu : IsUnit n := by
    by_contra hn'
    have hnm := hm _ hn'
    have ht2 : t * t ∈ IsLocalRing.maximalIdeal O := key ▸ Ideal.mul_mem_left _ _ hnm
    have htm : t ∈ IsLocalRing.maximalIdeal O := by
      rcases (IsLocalRing.maximalIdeal.isMaximal O).isPrime.mem_or_mem ht2 with h' | h' <;> exact h'
    have hb2 : (τ₀ ^ 2 - 4) * (b * b) ∈ IsLocalRing.maximalIdeal O := by
      have : (τ₀ ^ 2 - 4) * (b * b) = t * t - 4 * n := by rw [hn, htdef]; ring
      rw [this]
      exact Ideal.sub_mem _ ht2 (Ideal.mul_mem_left _ _ hnm)
    have hbb : b * b ∈ IsLocalRing.maximalIdeal O := by
      rcases (IsLocalRing.maximalIdeal.isMaximal O).isPrime.mem_or_mem hb2 with h' | h'
      · exact absurd hu h'
      · exact h'
    have hbm : b ∈ IsLocalRing.maximalIdeal O := by
      rcases (IsLocalRing.maximalIdeal.isMaximal O).isPrime.mem_or_mem hbb with h' | h' <;> exact h'
    have h2a : 2 * a ∈ IsLocalRing.maximalIdeal O := by
      have : 2 * a = t - τ₀ * b := by rw [htdef]; ring
      rw [this]
      exact Ideal.sub_mem _ htm (Ideal.mul_mem_left _ _ hbm)
    have ham : a ∈ IsLocalRing.maximalIdeal O := by
      rcases (IsLocalRing.maximalIdeal.isMaximal O).isPrime.mem_or_mem h2a with h' | h'
      · exact absurd h.two h'
      · exact h'
    rcases hab with rfl | rfl
    · exact ham isUnit_one
    · exact hbm isUnit_one
  let s' : Kˣ := Units.mk0 s hs
  have hW : (((Matrix.GeneralLinearGroup.scalar (Fin 2) s')⁻¹ * jU j z : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = j w := by
    rw [← map_inv, Units.val_mul, coe_scal, coe_jU, hzw, map_smul]
    simp [s', smul_smul, hs]
  refine mem_ZK.2 ⟨s', (Matrix.GeneralLinearGroup.scalar (Fin 2) s')⁻¹ * jU j z, ?_, (mul_inv_cancel_left _ _).symm⟩
  refine mem_KG hinj _ ?_ ?_
  · rw [hW]
    exact ent_j j hent w ⟨a, rfl⟩ ⟨b, rfl⟩
  · rw [hW, j_det j ht, hnw]
    obtain ⟨u, hu'⟩ := hnu
    exact ⟨u, by rw [hu']⟩

private theorem comm_C {τ : K} (M : Matrix (Fin 2) (Fin 2) K)
    (h : (!![0, -1; 1, τ] : Matrix (Fin 2) (Fin 2) K) * M = M * !![0, -1; 1, τ]) :
    M = M 0 0 • (1 : Matrix (Fin 2) (Fin 2) K) + M 1 0 • (!![0, -1; 1, τ] : Matrix (Fin 2) (Fin 2) K) := by
  have h00 := congrFun (congrFun h 0) 0
  have h10 := congrFun (congrFun h 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h10
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination -h00
  · linear_combination -h10

private theorem orbit_imp (h : IsLoc O Δ) (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K) (ht : (j ω).trace = τ)
    (hent : ∀ s t, j ω s t ∈ (algebraMap O K).range) (τ₀ : O) (hτ₀ : algebraMap O K τ₀ = τ)
    (hu : IsUnit (τ₀ ^ 2 - 4)) (e : O) (z : (Etau K τ)ˣ)
    (hze : (z : Etau K τ) = algebraMap K (Etau K τ) (algebraMap O K e) + ω)
    (hν : ∃ v : Oˣ, algebraMap O K v = QuadraticAlgebra.norm (z : Etau K τ)) (y : GL (Fin 2) K)
    (hy : y⁻¹ * jU j z * y ∈ ZK O K) : ∃ t, ∃ k ∈ ZK O K, y = jU j t * k := by
  haveI := h.frac
  have hinj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  obtain ⟨s, k, ⟨k₀, rfl⟩, E⟩ := mem_ZK.1 hy
  obtain ⟨v, hv⟩ := hν
  set A := j ω with hA
  set Y : Matrix (Fin 2) (Fin 2) K := (y : Matrix (Fin 2) (Fin 2) K) with hY
  set Yi : Matrix (Fin 2) (Fin 2) K := ((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) with hYi
  have hYiY : Yi * Y = 1 := by rw [hYi, hY, ← Units.val_mul]; simp
  have hYYi : Y * Yi = 1 := by rw [hYi, hY, ← Units.val_mul]; simp
  have hconjdet : ∀ M : Matrix (Fin 2) (Fin 2) K, (Yi * M * Y).det = M.det := fun M => by
    have := congrArg Matrix.det hYiY
    rw [Matrix.det_mul, Matrix.det_one] at this
    rw [Matrix.det_mul, Matrix.det_mul]
    linear_combination M.det * this
  have hconjtr : ∀ M : Matrix (Fin 2) (Fin 2) K, (Yi * M * Y).trace = M.trace := fun M => by
    rw [Matrix.trace_mul_comm, ← mul_assoc, hYYi, one_mul]
  have hE : Yi * j z * Y = (s : K) • (k₀ : Matrix (Fin 2) (Fin 2) O).map (algebraMap O K) := by
    have := congrArg Units.val E
    rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_scal, coe_jU, coe_map'] at this
    rw [this]; simp

  obtain ⟨n, hn⟩ := Matrix.isUnits_det_units k₀
  have hs2 : (s : K) ^ 2 = algebraMap O K (v * ((n⁻¹ : Oˣ) : O)) := by
    have h1 : (Yi * j z * Y).det = QuadraticAlgebra.norm (z : Etau K τ) := by
      rw [hconjdet, j_det j ht]
    rw [hE, Matrix.det_smul, ← hv] at h1
    have h2 : ((k₀ : Matrix (Fin 2) (Fin 2) O).map (algebraMap O K)).det = algebraMap O K n := by
      rw [hn, RingHom.map_det]; rfl
    rw [h2] at h1
    have h3 : algebraMap O K (n : O) * algebraMap O K ((n⁻¹ : Oˣ) : O) = 1 := by
      rw [← map_mul]; simp
    rw [map_mul]
    simp only [Fintype.card_fin] at h1
    linear_combination (algebraMap O K ((n⁻¹ : Oˣ) : O)) * h1 - (s : K) ^ 2 * h3
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : O, algebraMap O K s₀ = s :=
    IsIntegrallyClosed.isIntegral_iff.1 (IsIntegral.of_pow two_pos (by rw [hs2]; exact isIntegral_algebraMap))

  obtain ⟨A₀, hA₀⟩ := lift_mat (O := O) A hent
  let B₀ : Matrix (Fin 2) (Fin 2) O := s₀ • (k₀ : Matrix (Fin 2) (Fin 2) O) - e • 1
  have hB₀ : B₀.map (algebraMap O K) = Yi * A * Y := by
    have h1 : j z = algebraMap O K e • (1 : Matrix (Fin 2) (Fin 2) K) + A := by
      rw [hze, map_add, AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
    have h2 : Yi * j z * Y = algebraMap O K e • (1 : Matrix (Fin 2) (Fin 2) K) + Yi * A * Y := by
      rw [h1, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, hYiY]
    have h3 : Yi * A * Y = (s : K) • (k₀ : Matrix (Fin 2) (Fin 2) O).map (algebraMap O K) - algebraMap O K e • (1 : Matrix (Fin 2) (Fin 2) K) := by
      rw [← hE, h2]; abel
    rw [h3, ← hs₀]
    ext a b
    simp only [B₀, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, map_sub, smul_eq_mul, map_mul, Matrix.one_apply]
    split_ifs <;> simp
  have tr_map : ∀ M : Matrix (Fin 2) (Fin 2) O, (M.map (algebraMap O K)).trace = algebraMap O K M.trace := fun M => by
    simp [Matrix.trace_fin_two]
  have det_map : ∀ M : Matrix (Fin 2) (Fin 2) O, (M.map (algebraMap O K)).det = algebraMap O K M.det := fun M => by
    rw [RingHom.map_det]; rfl
  have hAt : A₀.trace = τ₀ := hinj (by rw [← tr_map, hA₀, hτ₀, ht])
  have hAd : A₀.det = 1 := hinj (by rw [← det_map, hA₀, map_one, hA, j_det_one j ht])
  have hBt : B₀.trace = τ₀ := hinj (by rw [← tr_map, hB₀, hconjtr, hτ₀, ht])
  have hBd : B₀.det = 1 := hinj (by rw [← det_map, hB₀, hconjdet, map_one, hA, j_det_one j ht])
  obtain ⟨g, hg⟩ := cyc A₀ τ₀ hAt hAd hu
  obtain ⟨g', hg'⟩ := cyc B₀ τ₀ hBt hBd hu

  set C : Matrix (Fin 2) (Fin 2) K := !![0, -1; 1, τ] with hC
  have hCmap : (!![0, -1; 1, τ₀] : Matrix (Fin 2) (Fin 2) O).map (algebraMap O K) = C := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [hC, hτ₀]
  let G : GL (Fin 2) K := Matrix.GeneralLinearGroup.map (algebraMap O K) g
  let G' : GL (Fin 2) K := Matrix.GeneralLinearGroup.map (algebraMap O K) g'
  have hAG : A * (G : Matrix (Fin 2) (Fin 2) K) = G * C := by
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) O => M.map (algebraMap O K)) hg
    simp only [Matrix.map_mul, hA₀, hCmap] at this
    exact this
  have hBG : (Yi * A * Y) * (G' : Matrix (Fin 2) (Fin 2) K) = G' * C := by
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) O => M.map (algebraMap O K)) hg'
    simp only [Matrix.map_mul, hB₀, hCmap] at this
    exact this
  set Gm : Matrix (Fin 2) (Fin 2) K := (G : Matrix (Fin 2) (Fin 2) K) with hGm
  set Gi : Matrix (Fin 2) (Fin 2) K := ((G⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) with hGi
  set Gp : Matrix (Fin 2) (Fin 2) K := (G' : Matrix (Fin 2) (Fin 2) K) with hGp
  have hGiG : Gi * Gm = 1 := by rw [hGi, hGm, ← Units.val_mul]; simp
  have hGGi : Gm * Gi = 1 := by rw [hGi, hGm, ← Units.val_mul]; simp
  have hCG : C = Gi * (A * Gm) := by rw [hAG, ← mul_assoc, hGiG, one_mul]
  have hYA : Y * (Gp * C) = A * (Y * Gp) := by
    rw [← hBG]
    simp only [mul_assoc]
    rw [← mul_assoc Y Yi, hYYi, one_mul]
  have hcomm : C * (Gi * (Y * Gp)) = (Gi * (Y * Gp)) * C := by
    calc C * (Gi * (Y * Gp)) = Gi * (A * (Y * Gp)) := by
          conv_lhs => rw [hCG]
          simp only [mul_assoc]
          rw [← mul_assoc Gm Gi, hGGi, one_mul]
      _ = (Gi * (Y * Gp)) * C := by rw [← hYA]; simp only [mul_assoc]
  have hM := comm_C _ hcomm
  set a := (Gi * (Y * Gp)) 0 0
  set c := (Gi * (Y * Gp)) 1 0
  let T : GL (Fin 2) K := y * G' * G⁻¹
  have hT : (T : Matrix (Fin 2) (Fin 2) K) = j ⟨a, c⟩ := by
    have h1 : (T : Matrix (Fin 2) (Fin 2) K) = Gm * (Gi * (Y * Gp)) * Gi := by
      rw [← mul_assoc Gm, hGGi, one_mul]; rfl
    rw [h1, hM, j_eq]
    have h2 : Gm * C * Gi = A := by rw [← hAG, mul_assoc, hGGi, mul_one]
    rw [mul_add, add_mul, mul_smul_comm, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, mul_one, hGGi, h2]
  have hTu : IsUnit (⟨a, c⟩ : Etau K τ) := by
    rw [isUnit_iff_norm_isUnit, ← j_det j ht, ← hT]
    exact Matrix.isUnits_det_units T
  obtain ⟨t, htt⟩ := hTu
  refine ⟨t, G * G'⁻¹, Subgroup.mem_sup_right (mul_mem ⟨g, rfl⟩ (inv_mem ⟨g', rfl⟩)), ?_⟩
  have : jU j t = T := Units.ext (by rw [coe_jU, htt, hT])
  rw [this]
  simp [T, mul_assoc]

end

theorem oneG : OneG := by
  intro O K _ _ _ _ _ Δ τ h j ht hent ⟨u, hu⟩
  haveI := h.frac
  have hinj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  obtain ⟨τ₀, hτ₀⟩ : τ ∈ (algebraMap O K).range := by
    rw [← ht, Matrix.trace_fin_two]
    exact add_mem (hent 0 0) (hent 1 1)
  have hu₀ : IsUnit (τ₀ ^ 2 - 4) := by
    have : (u : O) = τ₀ ^ 2 - 4 := hinj (by rw [hu, ← hτ₀]; simp [map_ofNat])
    exact this ▸ u.isUnit
  have h2u : IsUnit (2 + τ₀) := isUnit_of_mul_isUnit_left (y := τ₀ - 2) (by convert hu₀ using 1; ring)
  refine ⟨?_, ?_⟩
  · ext z
    constructor
    · intro hz
      refine ⟨quo_int j ht z hz, quo_int j ht z⁻¹ ?_⟩
      have : jU j z⁻¹ = (jU j z)⁻¹ := map_inv _ _
      rw [this]
      exact inv_mem hz
    · exact cint_zk h j ht hent τ₀ hτ₀ hu₀ z
  · intro z hz
    have hdata : ∃ e : O, (z : Etau K τ) = algebraMap K (Etau K τ) (algebraMap O K e) + ω ∧
        ∃ v : Oˣ, algebraMap O K v = QuadraticAlgebra.norm (z : Etau K τ) := by
      rcases hz with hz | hz
      · refine ⟨0, by simp [hz], 1, ?_⟩
        rw [hz]; simp [QuadraticAlgebra.norm_def]
      · obtain ⟨v, hv⟩ := h2u
        refine ⟨1, by simp [hz], v, ?_⟩
        rw [hz, hv]
        simp [QuadraticAlgebra.norm_def, hτ₀, map_ofNat]
        ring
    obtain ⟨e, hze, hν⟩ := hdata
    have hKG : jU j z ∈ KG O K := by
      refine mem_KG hinj _ ?_ ?_
      · rw [coe_jU]
        exact ent_j j hent _ (by rw [hze]; simp) (by rw [hze]; simp)
      · rw [coe_jU, j_det j ht]; exact hν
    refine ⟨hKG, fun y => ⟨orbit_imp h j ht hent τ₀ hτ₀ hu₀ e z hze hν y, ?_⟩⟩
    rintro ⟨t, k, hk, rfl⟩
    have hc : (jU j t)⁻¹ * jU j z * jU j t = jU j z := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      rw [mul_comm, mul_inv_cancel_left]
    have : (jU j t * k)⁻¹ * jU j z * (jU j t * k) = k⁻¹ * jU j z * k := by
      conv_rhs => rw [← hc]
      simp only [_root_.mul_inv_rev, mul_assoc]
    rw [this]
    exact mul_mem (mul_mem (inv_mem hk) (Subgroup.mem_sup_right hKG)) hk

end UpperTheory.V.Z.Sym.Loc
