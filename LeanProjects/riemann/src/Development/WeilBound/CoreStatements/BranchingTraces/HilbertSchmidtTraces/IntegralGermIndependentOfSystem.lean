import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HeBranching

noncomputable section

open MeasureTheory Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants Formalism.L2.Theta GlobalTheory.SmVec GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods GlobalTheory.CompanionTheory.PairingAnalysis
open scoped InnerProductSpace

namespace PositivityTheory.UnitaryDecomposition.X4

def PwSt : Prop := ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ] [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B] (σ : Γ → (A →L[ℂ] A)) (ρ : Γ → (B →L[ℂ] B)) (d : ℝ), IsU σ → IsU ρ → IsFd ν σ d → ∀ w₀ : A, ‖w₀‖ = 1 → Integrable (fun g => ⟪w₀, σ g w₀⟫_ℂ) ν → ∀ i : A →L[ℂ] B, IsIsoMap σ ρ i → (∀ j : A →L[ℂ] B, IsMap σ ρ j → ∃ c : ℂ, j = c • i) → (∀ x : Γ, ∫ g, star ⟪w₀, σ g w₀⟫_ℂ * star ⟪w₀, σ (g⁻¹ * x) w₀⟫_ℂ ∂ν = ((d⁻¹ : ℝ) : ℂ) * star ⟪w₀, σ x w₀⟫_ℂ) ∧ ∀ a b : B, ∫ g, star ⟪w₀, σ g w₀⟫_ℂ * ⟪b, ρ g a⟫_ℂ ∂ν = ((d⁻¹ : ℝ) : ℂ) * (⟪b, i w₀⟫_ℂ * ⟪i w₀, a⟫_ℂ)

def IntegralGermIndependentOfSystem : Prop := ∀ {n r : ℕ} {ε : Fin n → Bool} {ε' : Fin r → Bool} (ι : UJ ε' →* UJ ε) (z : Fin n → ℂ), IsStdStab ε ε' ι z → ∀ {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B] (π : Matrix (Fin n) (Fin n) ℂ → (A →L[ℂ] A)) (σ : Matrix (Fin r) (Fin r) ℂ → (B →L[ℂ] B)) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (ν : Measure (UJ ε')) [ν.IsHaarMeasure] (dπ dσ : ℝ), IsU (onU ε π) → IsU (onU ε' σ) → IsFd μ (onU ε π) dπ → IsFd ν (onU ε' σ) dσ → ∀ i : B →L[ℂ] A, IsIsoMap (onU ε' σ) (res ι π) i → ∀ (v₀ : A) (w : B), ‖v₀‖ = 1 → ‖w‖ = 1 → ∀ Y₁ K D : ℝ, 1 ≤ Y₁ → 0 < K → ∫⁻ g, ENNReal.ofReal (nsq (umat g⁻¹ *ᵥ z) * ‖⟪i w, π (umat g) v₀⟫_ℂ‖ ^ 2) ∂μ ≤ ENNReal.ofReal (Y₁ / 2) * ∫⁻ g, ENNReal.ofReal (‖⟪i w, π (umat g) v₀⟫_ℂ‖ ^ 2) ∂μ → ENNReal.ofReal dπ * μ {g | hs (umat g) ≤ 64 * n * ((n : ℝ) + Y₁) ^ 2} ≤ ENNReal.ofReal K → 1 / dσ ≤ D * ν.real (ball ε' 1) → ∃ g₀ : UJ ε, hs (umat g₀) ≤ 64 * n * ((n : ℝ) + Y₁) ^ 2 ∧ 1 ≤ 4 * D * K * ‖ContinuousLinearMap.adjoint i (π (umat g₀) v₀)‖ ^ 2

def EmbSt : Prop := (∀ {n : ℕ} (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool) (e : Fin n ⊕ Unit ≃ Fin (n + 1)), Fits ε ε' e → ∃ ι : UJ ε' →* UJ ε, (∀ h, umat (ι h) = emb e (um h)) ∧ IsStdStab ε ε' ι (Pi.single (zi e) 1) ∧ ∀ h : Matrix (Fin n) (Fin n) ℂ, incl e * h * (incl e)ᴴ + vecMulVec (Pi.single (zi e) (1 : ℂ)) (star (Pi.single (zi e) (1 : ℂ) : Fin (n + 1) → ℂ)) = emb e h) ∧ (∀ {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) (j : Fin m), nsq (g *ᵥ Pi.single j 1) = colSq g j) ∧ (∀ {m : ℕ} (ε : Fin m → Bool) {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] (π : Matrix (Fin m) (Fin m) ℂ → (A →L[ℂ] A)), IsURepOn (UJset ε) π → IsU (onU ε π)) ∧ ∀ {m : ℕ} (ε : Fin m → Bool) (lam : Fin m → ℝ) {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] (π : Matrix (Fin m) (Fin m) ℂ → (A →L[ℂ] A)) (μ : Measure (UJ ε)), μ.IsHaarMeasure → IsHCParam lam → IsDS ε lam π → μ.IsMulRightInvariant ∧ (∃ d, IsFdeg μ π d ∧ IsFd μ (onU ε π) d) ∧ ∃ v ∈ lowKSub ε lam π, ‖v‖ = 1

theorem num_C {n : ℕ} {x : ℝ} (hn : 1 ≤ n) (hx : 3 ≤ x) (hnx : (n : ℝ) ≤ x) :
    Real.exp (6 * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.log n + 12 * ((n + 1 : ℕ) : ℝ) ^ 2) * (n : ℝ) ^ (12 * (n + 1) ^ 2) ≤
      x ^ (30 * (n + 1) ^ 2) := by
  have h0 : (0 : ℝ) < n := by exact_mod_cast hn
  have he : Real.exp 1 ≤ x := (Real.exp_one_lt_d9.le.trans (by norm_num)).trans hx
  have e1 : Real.exp (6 * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.log n + 12 * ((n + 1 : ℕ) : ℝ) ^ 2) =
      (n : ℝ) ^ (6 * (n + 1) ^ 2) * Real.exp 1 ^ (12 * (n + 1) ^ 2) := by
    rw [Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_log (pow_pos h0 (6 * (n + 1) ^ 2)), Real.log_pow]
    push_cast
    rw [mul_one]
  rw [e1, show 30 * (n + 1) ^ 2 = 6 * (n + 1) ^ 2 + 12 * (n + 1) ^ 2 + 12 * (n + 1) ^ 2 by ring, pow_add x, pow_add x]
  gcongr

theorem num_D {n : ℕ} {x : ℝ} (hx : 16 ≤ x) (hnx : (n : ℝ) ≤ x) :
    (x ^ (30 * (n + 1) ^ 2)) ^ 2 * (2 * (16 * (n : ℝ) ^ 2) ^ (2 * n ^ 2)) ≤ x ^ (67 * (n + 1) ^ 2) := by
  have h1 : (1 : ℝ) ≤ x := by linarith
  have h2 : 16 * (n : ℝ) ^ 2 ≤ x ^ 3 := by
    rw [pow_succ' x 2]; gcongr
  calc _ ≤ (x ^ (30 * (n + 1) ^ 2)) ^ 2 * (x * (x ^ 3) ^ (2 * n ^ 2)) := by gcongr; linarith
    _ = x ^ (60 * (n + 1) ^ 2 + 1 + 6 * n ^ 2) := by rw [← pow_mul, ← pow_mul, ← pow_succ', ← pow_add]; congr 1; ring
    _ ≤ _ := pow_le_pow_right₀ h1 (by
      have a1 : n ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have a2 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega)

theorem num_Y {N : ℕ} {x : ℝ} (hN : 1 ≤ N) (hx : 9 ≤ x) (hnx : (N : ℝ) ≤ x) :
    64 * (N : ℝ) * ((N : ℝ) + 2 * x ^ (8 * N)) ^ 2 ≤ x ^ (20 * N) := by
  have h1 : (1 : ℝ) ≤ x := by linarith
  have h2 : (N : ℝ) ≤ x ^ (8 * N) := hnx.trans (le_self_pow₀ h1 (by omega))
  calc _ ≤ x ^ 2 * x * (3 * x ^ (8 * N)) ^ 2 := by gcongr <;> nlinarith
    _ = 9 * x ^ (16 * N + 3) := by ring
    _ ≤ x * x ^ (16 * N + 3) := by gcongr
    _ = x ^ (16 * N + 4) := by ring
    _ ≤ _ := pow_le_pow_right₀ h1 (by omega)

theorem num_V {N : ℕ} {B x : ℝ} (hN : 3 ≤ N) (hB : 2 ≤ B) (hx : x = 8 * N * B) :
    (4 * N * (Real.sqrt N + 1) * x ^ (10 * N) / ((100 * N * (B + 1)) ^ 2)⁻¹) ^ (2 * N ^ 2) ≤ x ^ (24 * N ^ 3) := by
  have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hx1 : 25 ≤ x := by rw [hx]; nlinarith
  have a1 : 4 * (N : ℝ) ≤ x := by rw [hx]; nlinarith
  have a2 : Real.sqrt N + 1 ≤ x := by
    have : Real.sqrt N ≤ N := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
    linarith
  have a3 : 100 * N * (B + 1) ≤ x ^ 2 := by
    have : 100 * N * (B + 1) ≤ 25 * x := by rw [hx]; nlinarith
    nlinarith
  rw [div_inv_eq_mul]
  calc _ ≤ (x * x * x ^ (10 * N) * (x ^ 2) ^ 2) ^ (2 * N ^ 2) := by gcongr
    _ = x ^ ((10 * N + 6) * (2 * N ^ 2)) := by rw [pow_mul x (10 * N + 6)]; congr 1; ring
    _ ≤ _ := pow_le_pow_right₀ (by linarith) (by nlinarith [Nat.mul_le_mul_right (N ^ 2) hN])

set_option maxHeartbeats 1600000 in
theorem big_of (hpw : PwSt) (hg0 : IntegralGermIndependentOfSystem) (hem : EmbSt) : Moment → Analysis → BigProj := by
  rintro hM ⟨hVol, hDec, hInt, -, hDUp, -⟩ n ε lam ε' mu B e H H' _ _ _ _ _ _ π σ ν hν hF hP hπ hσ i hi1 hi2 hi3 v hv hv1
  obtain ⟨hE1, hE2, hE3, hE4⟩ := hem
  obtain ⟨ι, hι, hstab, -⟩ := hE1 ε ε' e hF
  have hn2 := hP.two
  have hN2 : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hN3 : (3 : ℝ) ≤ (n : ℝ) + 1 := by linarith
  obtain ⟨a0, ha0⟩ := hP.neg
  have hB : 2 ≤ B := by
    have h1 := hP.gap (zi e) a0 (by rw [ha0, show ε (zi e) = true from hF.1]; simp)
    have h2 := (abs_sub _ _).trans (add_le_add (hP.bd (zi e)) (hP.bd a0))
    have h3 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 3 := one_le_pow₀ (by linarith)
    linarith
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = 8 * ((n : ℝ) + 1) * B := ⟨_, rfl⟩
  rw [← hx]
  have hxN : (n : ℝ) + 1 ≤ x := by rw [hx]; nlinarith
  have hx16 : 16 ≤ x := by rw [hx]; nlinarith
  have hx0 : 0 < x := by linarith
  obtain ⟨hR', ⟨dσ, -, hdσ⟩, w, hw, hw1⟩ := hE4 ε' mu σ ν hν hP.hc' hσ
  obtain ⟨-, ⟨dπ, hdπ', hdπ⟩, -⟩ := hE4 ε lam π (muG ε) inferInstance hP.hc hπ
  have hUσ := hE3 ε' σ hσ.2.2.1
  have hUπ := hE3 ε π hπ.2.2.1
  have hres : ∀ h, res ι π h = π (emb e (um h)) := fun h => congrArg π (hι h)
  have hcm : Continuous fun g : UJ ε' => ⟪w, σ (um g) w⟫_ℂ := continuous_const.inner (hUσ.cont w)
  have hdec : ∀ g : UJ ε', ‖⟪w, σ (um g) w⟫_ℂ‖ ≤ x ^ (30 * (n + 1) ^ 2) * hs (um g) ^ (-(6 * ((n + 1 : ℕ) : ℝ) ^ 2)) := by
    intro g
    have h := hDec n (n + 1) ε' mu H' σ (by omega) (by omega) hP.hc' hσ (by exact_mod_cast hP.gap') w hw hw1 1 n
      (by simp [hs, um, Matrix.one_apply, apply_ite]) g
    have h1 : σ (um (1 : UJ ε')) w = w := DFunLike.congr_fun hUσ.one w
    rw [h1] at h
    refine h.trans (mul_le_mul_of_nonneg_right (num_C (by omega) (by linarith) (by linarith)) ?_)
    exact Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) _
  have hm := (hInt n ε' ν hν (by omega) _ _ _ hcm (by push_cast; nlinarith) hdec).1
  have hD : 1 / dσ ≤ x ^ (67 * (n + 1) ^ 2) * ν.real (ball ε' 1) := by
    have h := (hInt n ε' ν hν (by omega) (fun g => ⟪w, σ (um g) w⟫_ℂ * star ⟪w, σ (um g) w⟫_ℂ) ((x ^ (30 * (n + 1) ^ 2)) ^ 2)
      (12 * ((n + 1 : ℕ) : ℝ) ^ 2) (hcm.mul hcm.star) (by push_cast; nlinarith) fun g => by
        have h0 : 0 ≤ hs (um g) := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
        rw [norm_mul, norm_star, ← sq, show -(12 * ((n + 1 : ℕ) : ℝ) ^ 2) = -(6 * ((n + 1 : ℕ) : ℝ) ^ 2) * (2 : ℕ) by
          push_cast; ring, Real.rpow_mul_natCast h0, ← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hdec g) 2).2
    have h2 := congrArg norm (hdσ.2 w w w w).2
    rw [inner_self_eq_norm_sq_to_K, hw1, norm_div, Complex.norm_real, Real.norm_of_nonneg hdσ.1.le] at h2
    simp only [Complex.coe_algebraMap, Complex.ofReal_one, one_pow, mul_one, norm_one] at h2
    rw [← h2]
    exact ((norm_integral_le_integral_norm _).trans h).trans
      (mul_le_mul_of_nonneg_right (num_D hx16 (by linarith)) measureReal_nonneg)
  have hiso : IsIsoMap (onU ε' σ) (res ι π) i := ⟨fun g y => by rw [hres]; exact hi2 g y, hi1⟩
  have hUr : IsU (res ι π) :=
    ⟨by rw [res, map_one]; exact hUπ.one, fun a b => by rw [res, map_mul]; exact hUπ.mul _ _, fun g => hUπ.norm (ι g), fun y => by
      have hc : Continuous fun h : UJ ε' => emb e (um h) := by
        have h1 : Continuous fun h : UJ ε' => um h := Units.continuous_val.comp continuous_subtype_val
        refine continuous_matrix fun a b => ?_
        obtain ⟨a, rfl⟩ := e.surjective a
        obtain ⟨b, rfl⟩ := e.surjective b
        rcases a with a | a <;> rcases b with b | b <;> simp [emb]
        · exact h1.matrix_elem a b
        all_goals exact continuous_const
      simp only [hres]
      exact (hπ.2.2.1.2.2 y).comp_continuous hc fun h => hι h ▸ (ι h).2⟩
  obtain ⟨hc1, hc2⟩ := hpw ν (onU ε' σ) (res ι π) dσ hUσ hUr hdσ w hw1 hm i hiso
    fun j hj => hi3 j fun h y => by rw [← hres]; exact hj h y
  have haa : ContinuousLinearMap.adjoint (ContinuousLinearMap.adjoint i) = i := ContinuousLinearMap.adjoint_adjoint i
  have hadj : ∀ {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {ρ : UJ ε' → K →L[ℂ] K}, IsU ρ → ∀ g a b,
      ⟪a, ρ g b⟫_ℂ = ⟪ρ g⁻¹ a, b⟫_ℂ := fun {K} _ _ {ρ} hρ g a b => by
    have ha : a = ρ g (ρ g⁻¹ a) := by
      rw [← ContinuousLinearMap.mul_apply, ← hρ.mul, mul_inv_cancel, hρ.one]; rfl
    conv_lhs => rw [ha]
    exact (LinearIsometry.mk (ρ g : K →ₗ[ℂ] K) (hρ.norm g)).inner_map_map _ b
  have hI : Intertw ε' e π σ (ContinuousLinearMap.adjoint i) := by
    refine ⟨?_, fun h y => ext_inner_left ℂ fun u => ?_⟩
    · rw [LinearIsometryEquiv.norm_map]
      exact i.opNorm_le_bound zero_le_one fun y => by rw [hi1, one_mul]
    · rw [ContinuousLinearMap.adjoint_inner_right, ← hres, hadj hUr, ← hiso.1, ← ContinuousLinearMap.adjoint_inner_right]
      exact (hadj hUσ h u _).symm
  have hmom := hM n ε lam ε' mu B e H H' π σ ν hν hF hP hπ hσ (ContinuousLinearMap.adjoint i) w dσ⁻¹ hI hw1
    (by rw [haa, hi1, hw1]) (inv_pos.2 hdσ.1) hm hc1 (fun a b => by
      rw [haa, ← hc2 a b]; simp only [hres]; rfl) v hv hv1
  rw [haa, ← hx] at hmom
  have hY := num_Y (N := n + 1) (x := x) (by omega) (by linarith) (by push_cast; exact hxN)
  have hone : (1 : ℝ) ≤ x ^ (8 * (n + 1)) := one_le_pow₀ (by linarith)
  obtain ⟨g₀, hg1, hg2⟩ := hg0 ι _ hstab π σ (muG ε) ν dπ dσ hUπ hUσ hdπ hdσ i hiso v w hv1 hw1 (2 * x ^ (8 * (n + 1)))
    (4 * x ^ (24 * (n + 1) ^ 3)) (x ^ (67 * (n + 1) ^ 2)) (by linarith) (by positivity)
    (by simp only [hE2]; rw [mul_div_cancel_left₀ _ two_ne_zero]; exact hmom)
    (by
      have hδ : (1 : ℝ) ≤ (100 * ((n + 1 : ℕ) : ℝ) * (B + 1)) ^ 2 := one_le_pow₀ (by push_cast; nlinarith)
      have h1 := hVol (n + 1) ε (muG ε) inferInstance (by omega) ((100 * ((n + 1 : ℕ) : ℝ) * (B + 1)) ^ 2)⁻¹ (x ^ (10 * (n + 1)))
        (inv_pos.2 (by linarith)) ((inv_le_one_of_one_le₀ hδ).trans one_le_two) (by positivity)
      have h2 := hDUp (n + 1) ε lam B H π (muG ε) dπ inferInstance (by omega) hP.hc hπ hP.bd (fun a b hab => le_trans (by
        push_cast
        have : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 3 := by positivity
        linarith) (hP.gap a b hab)) hdπ'
      have h3 := ENNReal.ofReal_le_ofReal (num_V (N := n + 1) (B := B) (x := x) (by omega) hB (by push_cast; exact hx))
      calc _ ≤ ENNReal.ofReal dπ * (ENNReal.ofReal (x ^ (24 * (n + 1) ^ 3)) * muG ε (ball ε _)) := by
            refine mul_le_mul_right ((measure_mono fun g hg => ?_).trans (h1.trans (mul_le_mul_left h3 _))) _
            exact le_trans (le_trans hg hY) (by rw [← pow_mul]; exact le_of_eq (by congr 1; ring))
        _ = ENNReal.ofReal (x ^ (24 * (n + 1) ^ 3)) * (ENNReal.ofReal dπ * muG ε (ball ε _)) := mul_left_comm _ _ _
        _ ≤ ENNReal.ofReal (x ^ (24 * (n + 1) ^ 3)) * 4 := mul_le_mul_right h2 _
        _ = _ := by rw [ENNReal.ofReal_mul (by norm_num), mul_comm, ENNReal.ofReal_ofNat])
    hD
  refine ⟨g₀, hg1.trans hY, ?_⟩
  obtain ⟨p, hp⟩ : ∃ p, p = ‖ContinuousLinearMap.adjoint i (π (umat g₀) v)‖ := ⟨_, rfl⟩
  have hp0 : 0 ≤ p := hp ▸ norm_nonneg _
  rw [← hp] at hg2
  refine le_of_le_of_eq ?_ hp
  have h1 : 4 * x ^ (67 * (n + 1) ^ 2) * (4 * x ^ (24 * (n + 1) ^ 3)) ≤ (x ^ (100 * (n + 1) ^ 3)) ^ 2 := by
    calc _ = 16 * x ^ (67 * (n + 1) ^ 2 + 24 * (n + 1) ^ 3) := by rw [pow_add x]; ring
      _ ≤ x * x ^ (67 * (n + 1) ^ 2 + 24 * (n + 1) ^ 3) := by gcongr
      _ ≤ _ := by
        rw [← pow_succ', ← pow_mul]
        refine pow_le_pow_right₀ (by linarith) ?_
        have a1 : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
        have a2 : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
        omega
  have h2 : 1 ≤ x ^ (100 * (n + 1) ^ 3) * p := by
    refine (one_le_sq_iff₀ (mul_nonneg (pow_pos hx0 _).le hp0)).1 ?_
    rw [mul_pow]
    exact hg2.trans (mul_le_mul_of_nonneg_right h1 (sq_nonneg _))
  rw [Real.exp_neg, show 100 * ((n : ℝ) + 1) ^ 3 * Real.log x = Real.log (x ^ (100 * (n + 1) ^ 3)) by
    rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity), inv_le_iff_one_le_mul₀' (by positivity)]
  exact h2

end PositivityTheory.UnitaryDecomposition.X4
