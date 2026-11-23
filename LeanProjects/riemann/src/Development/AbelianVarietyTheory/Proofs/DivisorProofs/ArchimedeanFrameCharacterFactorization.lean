import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieElementsGenerateOneParamLines
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGrpDataMapHaar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarDecompositionIndefiniteUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteUnitaryCharacterMaximalCompactDetPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteUnitaryCharacterEqOneCayleyRotationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfCayleyTwoIZpowEqOneForallStatement
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section
namespace GlobalTheory.RealLift.CharTrace
open scoped Matrix
open GlobalTheory.RealLift.OneParam

variable {R S : ℕ}

theorem jm_eq : Jm R S = Matrix.fromBlocks 1 0 0 (-1) := rfl

theorem jm_conjTranspose : (Jm R S)ᴴ = Jm R S := by
  rw [jm_eq, Matrix.fromBlocks_conjTranspose]; simp

theorem ne_zero_add (x : ℝ) : (1 + 2 * Complex.I * x : ℂ) ≠ 0 := fun h => by
  have := congrArg Complex.re h; simp at this

theorem ne_zero_sub (x : ℝ) : (1 - 2 * Complex.I * x : ℂ) ≠ 0 := fun h => by
  have := congrArg Complex.re h; simp at this

theorem star_zeta (x : ℝ) : star ((1 + 2 * Complex.I * x) / (1 - 2 * Complex.I * x)) =
    (1 - 2 * Complex.I * x) / (1 + 2 * Complex.I * x) := by
  rw [star_div₀]; congr 1 <;> simp [Complex.ext_iff]

theorem diag_unit {m : Type} [Fintype m] [DecidableEq m] (i0 : m) (z : ℂ) (hz : star z * z = 1) :
    (Matrix.diagonal (Function.update (1 : m → ℂ) i0 z))ᴴ * Matrix.diagonal (Function.update 1 i0 z) = 1 := by
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext i
  by_cases hi : i = i0
  · subst hi; simpa using hz
  · simp [Function.update_of_ne hi]

theorem det_diag {m : Type} [Fintype m] [DecidableEq m] (i0 : m) (z : ℂ) :
    (Matrix.diagonal (Function.update (1 : m → ℂ) i0 z)).det = z := by
  rw [Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ _)]; simp

theorem charUpq : ∀ (R S : ℕ) (χ : Mat R S → ℂ),
    (∀ g h : Mat R S, gᴴ * Jm R S * g = Jm R S → hᴴ * Jm R S * h = Jm R S → χ (g * h) = χ g * χ h) →
    ContinuousOn χ {g : Mat R S | gᴴ * Jm R S * g = Jm R S} →
    (∀ g : Mat R S, gᴴ * Jm R S * g = Jm R S → χ g ≠ 0) →
    ∃ n : ℤ, ∀ g : Mat R S, gᴴ * Jm R S * g = Jm R S → χ g = g.det ^ n := by
  intro R S χ hmul hc hne
  obtain ⟨x, y, hxy⟩ := GlobalTheory.T.indefiniteUnitaryCharacter_maximalCompact_det_pow R S χ hmul hc hne
  have hJJ : Jm R S * Jm R S = 1 := jm_mul_self
  have h1 : χ 1 = 1 := by
    have e := hmul 1 1 (by simp) (by simp)
    rw [mul_one] at e
    exact mul_left_cancel₀ (hne 1 (by simp)) (e.symm.trans (mul_one _).symm)
  have hJU : (Jm R S)ᴴ * Jm R S * Jm R S = Jm R S := by rw [jm_conjTranspose, hJJ, Matrix.one_mul]
  have hχJ : χ (Jm R S) * χ (Jm R S) = 1 := by rw [← hmul _ _ hJU hJU, hJJ, h1]
  have memm : ∀ {g h : Mat R S}, gᴴ * Jm R S * g = Jm R S → hᴴ * Jm R S * h = Jm R S →
      (g * h)ᴴ * Jm R S * (g * h) = Jm R S := fun {g h} hg hh => by
    calc (g * h)ᴴ * Jm R S * (g * h) = hᴴ * (gᴴ * Jm R S * g) * h := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Jm R S := by rw [hg, hh]
  have blk : ∀ k : Mat R S, kᴴ * Jm R S * k = Jm R S → Jm R S * k = k * Jm R S →
      ∃ (a : Matrix (Fin R) (Fin R) ℂ) (d : Matrix (Fin S) (Fin S) ℂ), aᴴ * a = 1 ∧ dᴴ * d = 1 ∧
        k = Matrix.fromBlocks a 0 0 d := by
    intro k hkG hkJ
    obtain ⟨a, b, b', d, hmm⟩ : ∃ a b b' d, k = Matrix.fromBlocks a b b' d :=
      ⟨_, _, _, _, (Matrix.fromBlocks_toBlocks k).symm⟩
    subst hmm
    rw [jm_eq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at hkJ
    obtain ⟨-, e1, e2, -⟩ := hkJ
    simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_one, add_zero, zero_add] at e1 e2
    have hb : b = 0 := by
      ext i j
      have : b i j = - b i j := congrFun (congrFun e1 i) j
      show b i j = 0
      linear_combination this / 2
    have hb' : b' = 0 := by
      ext i j
      have : - b' i j = b' i j := congrFun (congrFun e2 i) j
      show b' i j = 0
      linear_combination -this / 2
    subst hb hb'
    rw [jm_eq] at hkG
    have := hkG
    simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply] at this
    exact ⟨a, d, this.1, this.2, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n : ℤ, ∀ (a : Matrix (Fin R) (Fin R) ℂ) (d : Matrix (Fin S) (Fin S) ℂ),
      a.det ^ x * d.det ^ y = (a.det * d.det) ^ n := by
    rcases Nat.eq_zero_or_pos R with hR | hR
    · subst hR; exact ⟨y, fun a d => by simp [Matrix.det_isEmpty]⟩
    rcases Nat.eq_zero_or_pos S with hS | hS
    · subst hS; exact ⟨x, fun a d => by simp [Matrix.det_isEmpty]⟩
    have hxy' : x = y := by
      have h0 := GlobalTheory.T.eq_zero_of_cayley_two_I_zpow_eq_one_forall (x - y) (fun t => by
        have e := GlobalTheory.T.indefiniteUnitaryCharacter_eq_one_cayleyRotation R S χ hmul hc hne ⟨0, hR⟩ ⟨0, hS⟩ t
        have hu1 := diag_unit (⟨0, hR⟩ : Fin R) ((1 + 2 * Complex.I * t) / (1 - 2 * Complex.I * t)) (by
          rw [star_zeta]; field_simp [ne_zero_add t, ne_zero_sub t])
        have hu2 := diag_unit (⟨0, hS⟩ : Fin S) ((1 - 2 * Complex.I * t) / (1 + 2 * Complex.I * t)) (by
          rw [star_div₀]
          have e1 : star (1 - 2 * Complex.I * t) = 1 + 2 * Complex.I * t := by simp [Complex.ext_iff]
          have e2 : star (1 + 2 * Complex.I * t) = 1 - 2 * Complex.I * t := by simp [Complex.ext_iff]
          rw [e1, e2]; field_simp [ne_zero_add t, ne_zero_sub t])
        rw [hxy _ _ hu1 hu2, det_diag, det_diag] at e
        have hz : ((1 + 2 * Complex.I * t) / (1 - 2 * Complex.I * t)) ≠ 0 :=
          div_ne_zero (ne_zero_add t) (ne_zero_sub t)
        have einv : (1 - 2 * Complex.I * t) / (1 + 2 * Complex.I * t) = ((1 + 2 * Complex.I * t) / (1 - 2 * Complex.I * t))⁻¹ := by
          rw [inv_div]
        rw [einv, inv_zpow', ← zpow_add₀ hz] at e
        rw [sub_eq_add_neg]; exact e)
      omega
    subst hxy'
    exact ⟨x, fun a d => (mul_zpow _ _ _).symm⟩
  refine ⟨n, fun g hg => ?_⟩
  obtain ⟨k, q, hk1, hk2, hq1, hq2, rfl⟩ := GlobalTheory.T.exists_polar_decomposition_indefiniteUnitary R S g hg
  have hq : χ q * χ q = 1 := by
    have hJq : (Jm R S * q)ᴴ * Jm R S * (Jm R S * q) = Jm R S := memm hJU hq1
    have hJqJ := memm hJq hJU
    have e : χ (Jm R S * q * Jm R S * q) = χ (Jm R S) * χ q * χ (Jm R S) * χ q := by
      rw [hmul _ _ hJqJ hq1, hmul _ _ hJq hJU, hmul _ _ hJU hq1]
    rw [hq2, h1] at e
    calc χ q * χ q = (χ (Jm R S) * χ (Jm R S)) * (χ q * χ q) := by rw [hχJ, one_mul]
      _ = 1 := by rw [e]; ring
  have hdq : q.det * q.det = 1 := by
    have e := congrArg Matrix.det hq2
    have eJ := congrArg Matrix.det hJJ
    simp only [Matrix.det_mul, Matrix.det_one] at e eJ
    calc q.det * q.det = (Jm R S).det * (Jm R S).det * (q.det * q.det) := by rw [eJ, one_mul]
      _ = 1 := by rw [← e]; ring
  obtain ⟨a, d, ha, hd, rfl⟩ := blk k hk1 hk2
  rw [hmul _ _ (memm hk1 hq1) hq1, hmul _ _ hk1 hq1, mul_assoc, hq, mul_one, hxy a d ha hd, hn a d,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, mul_assoc, hdq, mul_one]

theorem jm_map_star : (Jm R S).map star = Jm R S := by
  ext a b; rcases a with i | i <;> rcases b with j | j <;>
    simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks, Matrix.one_apply] <;> split_ifs <;> simp

theorem form_iff (h : Mat R S) : hᴴ * Jm R S * h = Jm R S ↔ hᵀ * Jm R S * h.map star = Jm R S := by
  have e1 : (hᴴ).map star = hᵀ := by ext i j; simp [Matrix.conjTranspose_apply]
  have e2 : (hᵀ).map star = hᴴ := by ext i j; simp [Matrix.conjTranspose_apply]
  have e3 : (h.map star).map star = h := by ext i j; simp
  constructor
  · intro hh
    have := congrArg (fun X => X.map star) hh
    simp only [map_star_mul, jm_map_star, e1] at this
    exact this
  · intro hh
    have := congrArg (fun X => X.map star) hh
    simp only [map_star_mul, jm_map_star, e2, e3] at this
    exact this

theorem mem_mul {g h : Mat R S} (hg : gᴴ * Jm R S * g = Jm R S) (hh : hᴴ * Jm R S * h = Jm R S) :
    (g * h)ᴴ * Jm R S * (g * h) = Jm R S := by
  calc (g * h)ᴴ * Jm R S * (g * h) = hᴴ * (gᴴ * Jm R S * g) * h := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Jm R S := by rw [hg, hh]

theorem mem_one : (1 : Mat R S)ᴴ * Jm R S * 1 = Jm R S := by simp

theorem prod_char {ι : Type} [Fintype ι] [DecidableEq ι] (χ : (ι → Mat R S) → ℂ)
    (hmul : ∀ g h : ι → Mat R S, (∀ w, (g w)ᴴ * Jm R S * g w = Jm R S) → (∀ w, (h w)ᴴ * Jm R S * h w = Jm R S) →
      χ (g * h) = χ g * χ h)
    (hc : ContinuousOn χ {g | ∀ w, (g w)ᴴ * Jm R S * g w = Jm R S})
    (hne : ∀ g : ι → Mat R S, (∀ w, (g w)ᴴ * Jm R S * g w = Jm R S) → χ g ≠ 0) :
    ∃ n : ι → ℤ, ∀ g : ι → Mat R S, (∀ w, (g w)ᴴ * Jm R S * g w = Jm R S) → χ g = ∏ w, (g w).det ^ n w := by
  have upd : ∀ w (a : Mat R S), aᴴ * Jm R S * a = Jm R S → ∀ v,
      (Function.update (1 : ι → Mat R S) w a v)ᴴ * Jm R S * Function.update (1 : ι → Mat R S) w a v = Jm R S := by
    intro w a ha v
    by_cases hv : v = w
    · subst hv; simpa using ha
    · rw [Function.update_of_ne hv]; exact mem_one
  have key : ∀ w, ∃ n : ℤ, ∀ a : Mat R S, aᴴ * Jm R S * a = Jm R S →
      χ (Function.update (1 : ι → Mat R S) w a) = a.det ^ n := by
    intro w
    refine charUpq R S (fun a => χ (Function.update (1 : ι → Mat R S) w a)) ?_ ?_ ?_
    · intro a b ha hb
      have e : Function.update (1 : ι → Mat R S) w (a * b) =
          Function.update (1 : ι → Mat R S) w a * Function.update (1 : ι → Mat R S) w b := by
        funext v
        by_cases hv : v = w
        · subst hv; simp
        · simp [Function.update_of_ne hv]
      rw [e]
      exact hmul _ _ (upd w a ha) (upd w b hb)
    · exact hc.comp (show Continuous (Function.update (1 : ι → Mat R S) w) from continuous_const.update w continuous_id).continuousOn
        fun a ha => upd w a ha
    · intro a ha; exact hne _ (upd w a ha)
  choose n hn using key
  refine ⟨n, fun g hg => ?_⟩
  have h1 : χ 1 = 1 := by
    have e := hmul 1 1 (fun _ => mem_one) (fun _ => mem_one)
    rw [mul_one] at e
    have hz := hne 1 (fun _ => mem_one)
    exact mul_left_cancel₀ hz (e.symm.trans (mul_one _).symm)
  have pc : ∀ (s : Finset ι) v, (s.piecewise g 1 v)ᴴ * Jm R S * s.piecewise g 1 v = Jm R S := by
    intro s v
    by_cases hv : v ∈ s
    · rw [Finset.piecewise_eq_of_mem _ _ _ hv]; exact hg v
    · rw [Finset.piecewise_eq_of_notMem _ _ _ hv]; exact mem_one
  have ind : ∀ s : Finset ι, χ (s.piecewise g 1) = ∏ w ∈ s, (g w).det ^ n w := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using h1
    | insert a s ha ih =>
      have e : (insert a s).piecewise g 1 = Function.update (1 : ι → Mat R S) a (g a) * s.piecewise g 1 := by
        funext v
        by_cases hv : v = a
        · subst hv; simp [Finset.piecewise, ha]
        · simp [Finset.piecewise, hv, Function.update_of_ne hv]
      rw [e, hmul _ _ (upd a (g a) (hg a)) (pc s), hn a (g a) (hg a), ih, Finset.prod_insert ha]
  simpa using ind Finset.univ

theorem conj_unit {β : Type} [Fintype β] [DecidableEq β] {N : Matrix β β ℂ} {C : Matrix β (Ix R S) ℂ}
    {C' : Matrix (Ix R S) β ℂ} (hF : Cᵀ * N * C.map star = Jm R S) (hR : C * C' = 1) {h : Mat R S}
    (hh : hᵀ * Jm R S * h.map star = Jm R S) :
    (C * h * C')ᵀ * N * (C * h * C').map star = N := by
  calc (C * h * C')ᵀ * N * (C * h * C').map star
        = C'ᵀ * (hᵀ * (Cᵀ * N * C.map star) * h.map star) * C'.map star := by
          rw [map_star_mul, map_star_mul, Matrix.transpose_mul, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = C'ᵀ * (Cᵀ * N * C.map star) * C'.map star := by rw [hF, hh, ← hF]
      _ = (C * C')ᵀ * N * (C * C').map star := by
          rw [map_star_mul, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = N := by
          rw [hR, Matrix.transpose_one, Matrix.one_mul, Matrix.map_one _ (by simp) (by simp), Matrix.mul_one]

theorem deriv_char : GlobalTheory.FunPr.Hypotheses₂ →
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type) [Fintype β]
    [DecidableEq β] (R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (AE F E)) (b : ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ), IsCMExt F E σ → (∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) →
    ∀ ν : UG (cA σ) J → ℂ,
      (∀ g h : UG (cA σ) J, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → At (evI F) ((h.1 : Matrix β β (AE F E)) - 1) →
        ν (g * h) = ν g * ν h) →
      ContinuousOn ν {g : UG (cA σ) J | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)} →
      (∀ g : UG (cA σ) J, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → ν g ≠ 0) →
      ∃ k : InfinitePlace F → ℂ, ∀ γ ∈ RLines σ J, ∀ Y, IsGen τ C γ Y →
        HasDerivAt (fun t : ℝ => ν (γ (Multiplicative.ofAdd t))) (∑ w, k w * (Y w).trace) 0 := by
  intro _ F E _ _ _ _ _ σ β _ _ R S τ J b C hCM hC ν hmul hcont hne
  have := hCM.1
  obtain ⟨ξ, hξ⟩ := exists_moved hCM
  have hξ' : ∀ w, ((τ w).1 ξ).im ≠ 0 := fun w => im_ne_zero hCM hξ (τ w).1
  choose C' hC' using fun w => (hC w).2
  have hL : ∀ w, C' w * C w = 1 := fun w => frame_inv (hC w).1 (hC' w)
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  set U : Set (InfinitePlace F → Mat R S) := {h | ∀ w, (h w)ᴴ * Jm R S * h w = Jm R S} with hU
  set Λ : (InfinitePlace F → Mat R S) → Matrix β β (AE F E) :=
    fun h => 1 + liftM τ ξ (fun w => C w * h w * C' w - 1) with hΛ
  have Λπ : ∀ h w, (Λ h).map (piInf (τ w)) = C w * h w * C' w := fun h w => by
    rw [hΛ, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), OneParam.liftM_map τ hξ', add_sub_cancel]
  have Λat : ∀ h, At (evI F) (Λ h - 1) := fun h => by
    rw [hΛ, add_sub_cancel_left]
    exact at_liftM τ ξ _
  have Λmul : ∀ h h', Λ (h * h') = Λ h * Λ h' := fun h h' => by
    refine (eq_of_at hCM τ ?_ fun w => ?_).symm
    · have e : Λ h * Λ h' - Λ (h * h') = (Λ h - 1) * Λ h' + (Λ h' - 1) - (Λ (h * h') - 1) := by noncomm_ring
      rw [e]
      exact at_sub (at_add (at_mul_right (Λat h) _) (Λat h')) (Λat _)
    · rw [Matrix.map_mul, Λπ, Λπ, Λπ, Pi.mul_apply]
      calc C w * h w * C' w * (C w * h' w * C' w) = C w * h w * (C' w * C w) * h' w * C' w := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hL, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have Λone : Λ 1 = 1 := eq_of_at hCM τ (Λat 1) fun w => by
    rw [Λπ, Pi.one_apply, Matrix.mul_one, hC' w, Matrix.map_one _ (map_zero _) (map_one _)]
  have ΛU : ∀ h ∈ U, (Λ h)ᵀ * J * (Λ h).map (cA σ) = J := fun h hh => by
    refine eq_of_at hCM τ ?_ fun w => ?_
    · have e : (Λ h)ᵀ * J * (Λ h).map (cA σ) - J =
          (Λ h - 1)ᵀ * J * (Λ h).map (cA σ) + J * (Λ h - 1).map (cA σ) := by
        have e1 : (Λ h - 1).map (cA σ) = (Λ h).map (cA σ) - 1 := by
          rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
        rw [e1, Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul,
          Matrix.mul_sub, Matrix.mul_one]
        abel
      rw [e]
      exact at_add (at_mul_right (at_mul_right (at_transpose (Λat h)) _) _)
        (at_mul_left (at_map_cA σ (Λat h)) _)
    · have hc : ((Λ h).map (cA σ)).map (piInf (τ w)) = (C w * h w * C' w).map star := by
        rw [← Λπ h w, Matrix.map_map, Matrix.map_map]
        congr 1
        funext z
        exact piInf_cA hCM (τ w) z
      rw [Matrix.map_mul, Matrix.map_mul, hc, Matrix.transpose_map, Λπ]
      by_cases hb : b = 0
      · haveI := isEmpty_of_zero (hb ▸ (hC w).1) (hC' w)
        ext i
        exact isEmptyElim i
      · have h1 := conj_unit (hC w).1 (hC' w) ((form_iff (h w)).1 (hh w))
        rw [Matrix.mul_smul, Matrix.smul_mul] at h1
        exact smul_right_injective _ hb h1
  set hinv : (InfinitePlace F → Mat R S) → InfinitePlace F → Mat R S :=
    fun h w => Jm R S * (h w)ᴴ * Jm R S with hhinv
  have inv_mul : ∀ h ∈ U, hinv h * h = 1 := fun h hh => by
    funext w
    rw [Pi.mul_apply, hhinv, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ (Jm R S) (h w), hh w,
      jm_mul_self, Pi.one_apply]
  have mul_inv : ∀ h ∈ U, h * hinv h = 1 := fun h hh => by
    funext w
    have := congrFun (inv_mul h hh) w
    rw [Pi.mul_apply, Pi.one_apply] at this ⊢
    exact mul_eq_one_comm.1 this
  have Λinv1 : ∀ h ∈ U, Λ h * Λ (hinv h) = 1 := fun h hh => by rw [← Λmul, mul_inv h hh, Λone]
  have Λinv2 : ∀ h ∈ U, Λ (hinv h) * Λ h = 1 := fun h hh => by rw [← Λmul, inv_mul h hh, Λone]
  let G : U → UG (cA σ) J := fun h => ⟨⟨Λ h, Λ (hinv h), Λinv1 h h.2, Λinv2 h h.2⟩, ΛU h h.2⟩
  have LevelValuationRings : ∀ h, At (evI F) (((G h).1 : Matrix β β (AE F E)) - 1) := fun h => Λat h
  have Gmul : ∀ h h' : U, ∀ hm : (h : InfinitePlace F → Mat R S) * h' ∈ U, G ⟨_, hm⟩ = G h * G h' :=
    fun h h' hm => Subtype.ext (Units.ext (Λmul h h'))
  have Λc : Continuous Λ := continuous_const.add ((continuous_liftM τ ξ).comp (continuous_pi fun w =>
    (((continuous_const.matrix_mul (continuous_apply w)).matrix_mul continuous_const).sub continuous_const)))
  have hinvc : Continuous hinv := continuous_pi fun w =>
    (continuous_const.matrix_mul (continuous_apply w).matrix_conjTranspose).matrix_mul continuous_const
  have Gc : Continuous G := by
    have hu : Continuous fun h : U => ((G h).1 : GL β (AE F E)) :=
      Units.continuous_iff.2 ⟨Λc.comp continuous_subtype_val, (Λc.comp hinvc).comp continuous_subtype_val⟩
    exact hu.subtype_mk _
  classical
  let χ : (InfinitePlace F → Mat R S) → ℂ := fun h => if hh : h ∈ U then ν (G ⟨h, hh⟩) else 0
  have χG : ∀ h : U, χ h = ν (G h) := fun h => by simp only [χ, dif_pos h.2]
  have memU : ∀ h h' : InfinitePlace F → Mat R S, h ∈ U → h' ∈ U → h * h' ∈ U := fun h h' hh hh' w =>
    mem_mul (hh w) (hh' w)
  obtain ⟨n, hn⟩ := prod_char (R := R) (S := S) χ
    (fun g h hg hh => by
      rw [χG ⟨g, hg⟩, χG ⟨h, hh⟩, χG ⟨g * h, memU g h hg hh⟩, Gmul ⟨g, hg⟩ ⟨h, hh⟩]
      exact hmul _ _ (LevelValuationRings _) (LevelValuationRings _))
    (by
      rw [continuousOn_iff_continuous_restrict]
      convert hcont.comp_continuous Gc LevelValuationRings using 1
      funext h
      exact χG h)
    (fun g hg => by rw [χG ⟨g, hg⟩]; exact hne _ (LevelValuationRings _))
  refine ⟨fun w => (n w : ℂ), fun γ hγ Y hY => ?_⟩
  set e : ℝ → InfinitePlace F → Mat R S := fun t w => NormedSpace.exp (t • Y w) with he
  have hγw : ∀ t w, ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf (τ w)) = C w * e t w * C' w :=
    fun t w => by
      rw [he]; simp only
      rw [← hY t w, Matrix.mul_assoc, hC' w, Matrix.mul_one]
  have heU : ∀ t, e t ∈ U := fun t w => by
    rw [form_iff]
    set g := ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf (τ w)) with hg
    have hgU : gᵀ * (b • J.map (piInf (τ w))) * g.map star = b • J.map (piInf (τ w)) := by
      have hu : ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E))ᵀ * J *
          ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (cA σ) = J := (γ (Multiplicative.ofAdd t)).2
      have := congrArg (fun X => X.map (piInf (τ w))) hu
      simp only [Matrix.map_mul, Matrix.transpose_map] at this
      have hc : (((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (cA σ)).map (piInf (τ w)) = g.map star := by
        rw [hg, Matrix.map_map, Matrix.map_map]
        congr 1
        funext z
        exact piInf_cA hCM (τ w) z
      rw [hc] at this
      rw [Matrix.mul_smul, Matrix.smul_mul, this]
    have hee : e t w = C' w * g * C w := by
      rw [hg, hγw, Matrix.mul_assoc, Matrix.mul_assoc, hL, Matrix.mul_one, ← Matrix.mul_assoc, hL, Matrix.one_mul]
    have t1 : (C' w)ᵀ * (C w)ᵀ = 1 := by rw [← Matrix.transpose_mul, hC' w, Matrix.transpose_one]
    have t2 : (C w).map star * (C' w).map star = 1 := by
      rw [← map_star_mul, hC' w]; exact Matrix.map_one _ (star_zero _) (star_one _)
    rw [hee, ← (hC w).1]
    calc (C' w * g * C w)ᵀ * ((C w)ᵀ * (b • J.map (piInf (τ w))) * (C w).map star) * (C' w * g * C w).map star
        = (C w)ᵀ * (gᵀ * (((C' w)ᵀ * (C w)ᵀ) * (b • J.map (piInf (τ w))) * ((C w).map star * (C' w).map star)) *
            g.map star) * (C w).map star := by
          rw [map_star_mul, map_star_mul, Matrix.transpose_mul, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = (C w)ᵀ * (b • J.map (piInf (τ w))) * (C w).map star := by
          rw [t1, t2, Matrix.one_mul, Matrix.mul_one, hgU]
  have hγe : ∀ t, γ (Multiplicative.ofAdd t) = G ⟨e t, heU t⟩ := fun t => by
    refine Subtype.ext (Units.ext (eq_of_at hCM τ ?_ fun w => ?_))
    · have e1 : ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)) - Λ (e t) =
          (((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)) - 1) - (Λ (e t) - 1) := by abel
      show At (evI F) (((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)) - Λ (e t))
      rw [e1]
      exact at_sub (hγ.2 _) (Λat _)
    · show ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf (τ w)) = (Λ (e t)).map (piInf (τ w))
      rw [hγw, Λπ]
  have hval : ∀ t : ℝ, ν (γ (Multiplicative.ofAdd t)) =
      Complex.exp ((t : ℂ) * ∑ w, (n w : ℂ) * (Y w).trace) := fun t => by
    rw [hγe t, ← χG, hn _ (heU t), Finset.mul_sum, Complex.exp_sum]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [he]; simp only
    rw [GlobalTheory.DetSqrtCover.det_exp, ← Complex.exp_int_mul, Matrix.trace_smul]
    congr 1
    simp only [Complex.real_smul]
    ring
  have hd : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * ∑ w, (n w : ℂ) * (Y w).trace))
      (∑ w, (n w : ℂ) * (Y w).trace) 0 := by
    have h0 := ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const (∑ w, (n w : ℂ) * (Y w).trace)).cexp
    simpa using h0
  exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall hval)

end GlobalTheory.RealLift.CharTrace
