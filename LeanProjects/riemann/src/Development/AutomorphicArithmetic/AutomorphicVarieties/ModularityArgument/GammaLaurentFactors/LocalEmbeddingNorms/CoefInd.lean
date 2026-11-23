import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.HodgeTateFromSandwich

noncomputable section

open GroundTheory.Automorphic GroundTheory.Automorphic.GodementJacquet
open Matrix GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Parabolic MeasureTheory GroundTheory.Automorphic.Measures
  GroundTheory.Automorphic.GJMatrix
open scoped NNReal ENNReal Pointwise

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

private theorem UpperTheory.V.Z.Gam.induced_matrix_coefficients {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]
    {n : ℕ} [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) F) V} (hπ : IsSmooth π) {β : Fin n → ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (levi F n β) W} (hσs : IsSmooth σ)
    (ι : Representation.IntertwiningMap π (parabolicInd F n β σ))
    (hι : Function.Injective ι) (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] {ψ : AddChar F Circle}
    (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {γ : RatFunc ℂ} (hγ : InducedFE F σ μ ψ γ) : IsGammaFactor F π μ ψ γ := by
  classical
  intro Φ hΦ v ℓ hℓ
  have : μ.IsInvInvariant := ⟨inv_eq_self_GL F n μ⟩

  obtain ⟨m₀, hm₀⟩ := hΦ.exists_congruence_invariant
  obtain ⟨m₁, -, hm₁⟩ := (hasBasis_nhds_one F n).mem_iff.1
    ((hπ v).mem_nhds (one_mem (stabilizerOf π v)))
  obtain ⟨m₂, -, hm₂⟩ := (hasBasis_nhds_one F n).mem_iff.1
    ((mem_smoothVectors.1 hℓ).mem_nhds (one_mem (stabilizerOf (Representation.dual π) ℓ)))
  set m := max m₀ (max m₁ m₂) with hmdef
  set K := congruenceSubgroup F n m with hKdef
  have hKc : IsCompact (K : Set (GL (Fin n) F)) := isCompact_congruenceSubgroup F n m
  have hKo : IsOpen (K : Set (GL (Fin n) F)) := isOpen_congruenceSubgroup F n m
  have hK0 : ∀ k ∈ K, k ∈ integralGL F n := fun k hk => congruenceSubgroup_le F n m hk
  have hvK : ∀ k ∈ K, π k v = v := fun k hk =>
    hm₁ (congruenceSubgroup_antitone F n (le_max_of_le_right (le_max_left m₁ m₂)) hk)
  have hℓK : ∀ k ∈ K, ∀ x, ℓ (π k x) = ℓ x := mem_fixedVectors_dual.1 fun k hk =>
    hm₂ (congruenceSubgroup_antitone F n (le_max_of_le_right (le_max_right m₁ m₂)) hk)
  have hΦK : ∀ k ∈ K, ∀ X, Φ ((k : Matrix (Fin n) (Fin n) F) * X) = Φ X ∧
      Φ (X * (k : Matrix (Fin n) (Fin n) F)) = Φ X := fun k hk =>
    hm₀ k (congruenceSubgroup_antitone F n (le_max_left _ _) hk)

  obtain ⟨lam, hlamK, hlam⟩ := exists_extend_dual hπ (isSmooth_parabolicInd σ) ι hι hKc hKo hℓK
  obtain ⟨R, hR₀, hR⟩ := exists_reps_congruenceSubgroup F n m
  obtain ⟨ℓx, hℓxK, hdec⟩ := exists_eval_decomposition hσs hR₀ hR lam
  set φ : parabolicIndSpace F n β σ := ι v with hφdef
  have hφK : φ ∈ fixedVectors (parabolicInd F n β σ) K := fun k hk => by
    rw [hφdef, ← ι.isIntertwining, hvK k hk]
  have hf : ∀ g, matrixCoeff π v ℓ g = lam (parabolicInd F n β σ g φ) := fun g => by
    rw [matrixCoeff, ← hlam, hφdef, ι.isIntertwining]
  have hℓxs : ∀ x, ℓx x ∈ smoothVectors (Representation.dual σ) := fun x =>
    mem_smoothVectors_of_mem_fixedVectors (isOpen_subgroupOf_levi hKo) (hℓxK x)

  set Φx : GL (Fin n) F → Matrix (Fin n) (Fin n) F → ℂ := fun x X =>
    Φ (((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * X) with hΦxdef
  have hΦx : ∀ x, IsSchwartzBruhat (Φx x) := fun x => hΦ.comp_mul_left x⁻¹
  have hJ := fun x : GL (Fin n) F =>
    hγ (Φx x) (hΦx x) (φ : GL (Fin n) F → W) φ.2 (ℓx x) (hℓxs x)
  choose hJA hJB hJR using hJ
  choose sA hsA using hJA
  choose sB hsB using hJB
  set SA : ℝ := ∑ x ∈ R, |sA x| with hSA
  have hSAx : ∀ x ∈ R, sA x ≤ SA := fun x hx =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun x => |sA x|)
      (fun _ _ => abs_nonneg _) hx)
  set SB : ℝ := -∑ x ∈ R, |sB x| with hSB
  have hSBx : ∀ x ∈ R, SB ≤ sB x := fun x hx => by
    have h1 := Finset.single_le_sum (f := fun x => |sB x|) (fun _ _ => abs_nonneg _) hx
    have h2 := neg_abs_le (sB x)
    linarith

  obtain ⟨r, A, -, hA⟩ := hΦ.exists_invariant
  have hAdec : ∀ s : ℂ, SA < s.re →
      Integrable (fun g : GL (Fin n) F => (Φ (g : Matrix (Fin n) (Fin n) F) * detPow g (s + ((n : ℂ) - 1) / 2)) *
        lam (parabolicInd F n β σ g φ)) μ ∧
      ∫ g : GL (Fin n) F, (Φ (g : Matrix (Fin n) (Fin n) F) * detPow g (s + ((n : ℂ) - 1) / 2)) *
        lam (parabolicInd F n β σ g φ) ∂μ =
        ∑ x ∈ R, ∫ g : GL (Fin n) F, (Φ (g : Matrix (Fin n) (Fin n) F) * detPow g (s + ((n : ℂ) - 1) / 2)) *
          ℓx x ((φ : GL (Fin n) F → W) (x * g)) ∂μ := by
    intro s hs
    refine integrable_and_integral_mul_coeff_eq μ hKc hKo hK0 hlamK hφK hdec
      (H := fun g : GL (Fin n) F => Φ (g : Matrix (Fin n) (Fin n) F) * detPow g (s + ((n : ℂ) - 1) / 2))
      (fun k hk g => ?_) (fun k hk g => ?_) (fun j => ?_) (fun x hx => ?_)
    · rw [Units.val_mul, (hΦK k hk _).1, detPow_mul, detPow_of_mem_integralGL (hK0 k hk), one_mul]
    · rw [Units.val_mul, (hΦK k hk _).2, detPow_mul, detPow_of_mem_integralGL (hK0 k hk), mul_one]
    · refine HasCompactSupport.intro (isCompact_shell F n A j) fun g hg => ?_
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]
      split_ifs with hj
      · by_contra hne
        exact hg ⟨hA _ (left_ne_zero_of_mul hne), hj⟩
      · rfl
    · refine ((hsA x s (lt_of_le_of_lt (hSAx x hx) hs)).comp_mul_left x).congr
        (Filter.Eventually.of_forall fun g => ?_)
      simp only [Φx]
      rw [Units.val_mul, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mul, detPow_mul, detPow_of_mem_integralGL (hR₀ x hx), one_mul]

  have hΦh : IsSchwartzBruhat (localMatrixFourier ψ Φ) := hΦ.localMatrixFourier hψ hψ1
  have hΦhK := localMatrixFourier_invariant ψ hK0 hΦK
  obtain ⟨r', A', -, hA'⟩ := hΦh.exists_invariant
  have hBdec : ∀ s : ℂ, s.re < SB →
      Integrable (fun g : GL (Fin n) F =>
        (localMatrixFourier ψ Φ ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          detPow g⁻¹ (1 - s + ((n : ℂ) - 1) / 2)) * lam (parabolicInd F n β σ g φ)) μ ∧
      ∫ g : GL (Fin n) F, (localMatrixFourier ψ Φ ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          detPow g⁻¹ (1 - s + ((n : ℂ) - 1) / 2)) * lam (parabolicInd F n β σ g φ) ∂μ =
        ∑ x ∈ R, ∫ g : GL (Fin n) F,
          (localMatrixFourier ψ Φ ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
            detPow g⁻¹ (1 - s + ((n : ℂ) - 1) / 2)) * ℓx x ((φ : GL (Fin n) F → W) (x * g)) ∂μ := by
    intro s hs
    refine integrable_and_integral_mul_coeff_eq μ hKc hKo hK0 hlamK hφK hdec
      (H := fun g : GL (Fin n) F =>
        localMatrixFourier ψ Φ ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          detPow g⁻¹ (1 - s + ((n : ℂ) - 1) / 2))
      (fun k hk g => ?_) (fun k hk g => ?_) (fun j => ?_) (fun x hx => ?_)
    · rw [_root_.mul_inv_rev, Units.val_mul, (hΦhK k⁻¹ (inv_mem hk) _).2, detPow_mul,
        detPow_of_mem_integralGL (hK0 _ (inv_mem hk)), mul_one]
    · rw [_root_.mul_inv_rev, Units.val_mul, (hΦhK k⁻¹ (inv_mem hk) _).1, detPow_mul,
        detPow_of_mem_integralGL (hK0 _ (inv_mem hk)), one_mul]
    · refine HasCompactSupport.intro ((isCompact_shell F n A' (-j)).image continuous_inv)
        fun g hg => ?_
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]
      split_ifs with hj
      · by_contra hne
        exact hg ⟨g⁻¹, ⟨hA' _ (left_ne_zero_of_mul hne), by rw [ordDet_inv, hj]⟩, inv_inv g⟩
      · rfl
    · refine (((hsB x s (lt_of_lt_of_le hs (hSBx x hx))).comp_inv).comp_mul_left x).congr
        (Filter.Eventually.of_forall fun g => ?_)
      simp only [Φx]
      rw [inv_inv, _root_.mul_inv_rev, Units.val_mul, localMatrixFourier_inv_mul ψ (hR₀ x hx),
        Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one,
        detPow_mul, detPow_of_mem_integralGL (inv_mem (hR₀ x hx)), mul_one]

  have hsumFE := RatFE.sum (F := F) (γ := γ) R (fun x _ => hJR x)
  refine hsumFE.congr ⟨SA, fun s hs => ?_⟩ ⟨SB, fun s hs => ?_⟩
  · have e1 : zetaIntegral μ Φ (matrixCoeff π v ℓ) s = ∫ g : GL (Fin n) F,
        (Φ (g : Matrix (Fin n) (Fin n) F) * detPow g (s + ((n : ℂ) - 1) / 2)) *
          lam (parabolicInd F n β σ g φ) ∂μ := by
      rw [zetaIntegral]
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      simp only
      rw [hf g]
      ring
    rw [e1, (hAdec s hs).2]
    refine Finset.sum_congr rfl fun x hx => ?_
    calc ∫ g : GL (Fin n) F, (Φ (g : Matrix (Fin n) (Fin n) F) *
          detPow g (s + ((n : ℂ) - 1) / 2)) * ℓx x ((φ : GL (Fin n) F → W) (x * g)) ∂μ
        = ∫ g : GL (Fin n) F, (fun g : GL (Fin n) F => Φx x (g : Matrix (Fin n) (Fin n) F) *
            detPow g (s + ((n : ℂ) - 1) / 2) * ℓx x ((φ : GL (Fin n) F → W) g)) (x * g) ∂μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
          simp only [Φx]
          rw [Units.val_mul, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
            Matrix.one_mul, detPow_mul, detPow_of_mem_integralGL (hR₀ x hx), one_mul]
      _ = _ := integral_mul_left_eq_self (μ := μ) (fun g : GL (Fin n) F =>
          Φx x (g : Matrix (Fin n) (Fin n) F) * detPow g (s + ((n : ℂ) - 1) / 2) *
            ℓx x ((φ : GL (Fin n) F → W) g)) x
  · have e1 : zetaIntegral μ (localMatrixFourier ψ Φ) (fun g => matrixCoeff π v ℓ g⁻¹) (1 - s) =
        ∫ g : GL (Fin n) F, (fun g : GL (Fin n) F =>
          (localMatrixFourier ψ Φ ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
            detPow g⁻¹ (1 - s + ((n : ℂ) - 1) / 2)) * lam (parabolicInd F n β σ g φ)) g⁻¹ ∂μ := by
      rw [zetaIntegral]
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      simp only [inv_inv]
      rw [hf g⁻¹]
      ring
    rw [e1, integral_inv_eq_self (fun g : GL (Fin n) F =>
      (localMatrixFourier ψ Φ ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        detPow g⁻¹ (1 - s + ((n : ℂ) - 1) / 2)) * lam (parabolicInd F n β σ g φ)) μ,
      (hBdec s hs).2]
    refine Finset.sum_congr rfl fun x hx => ?_
    set Bx : GL (Fin n) F → ℂ := fun g => localMatrixFourier ψ (Φx x) (g : Matrix (Fin n) (Fin n) F) *
      detPow g (1 - s + ((n : ℂ) - 1) / 2) * ℓx x ((φ : GL (Fin n) F → W) g⁻¹) with hBx
    calc ∫ g : GL (Fin n) F,
          (localMatrixFourier ψ Φ ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
            detPow g⁻¹ (1 - s + ((n : ℂ) - 1) / 2)) * ℓx x ((φ : GL (Fin n) F → W) (x * g)) ∂μ
        = ∫ g : GL (Fin n) F, (fun g => Bx g⁻¹) (x * g) ∂μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
          simp only [Bx, Φx]
          rw [inv_inv, _root_.mul_inv_rev, Units.val_mul, localMatrixFourier_inv_mul ψ (hR₀ x hx),
            Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one,
            detPow_mul, detPow_of_mem_integralGL (inv_mem (hR₀ x hx)), mul_one]
      _ = ∫ g : GL (Fin n) F, Bx g⁻¹ ∂μ :=
          integral_mul_left_eq_self (μ := μ) (fun g : GL (Fin n) F => Bx g⁻¹) x
      _ = ∫ g : GL (Fin n) F, Bx g ∂μ := integral_inv_eq_self Bx μ

theorem UpperTheory.V.Z.Gam.coefInd :
    UpperTheory.V.Z.Gam.CoefInd := by
  intro F _ _ _ _ _ _ n _ _ V _ _ π hπ β W _ _ σ hσ ι hι μ _ ψ hψ hψ1 γ hγ
  exact UpperTheory.V.Z.Gam.induced_matrix_coefficients hπ hσ ι hι μ hψ hψ1 hγ
