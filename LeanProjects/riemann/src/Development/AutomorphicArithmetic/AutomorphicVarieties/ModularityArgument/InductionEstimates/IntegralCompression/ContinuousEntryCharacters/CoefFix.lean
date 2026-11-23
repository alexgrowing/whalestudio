import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.LongWeylSwapsBlockDiagonal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.CoefIdem

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

private theorem fixOf (μ : Measure U4) (hμ : Haar4 μ) (ψ : U4 → ℂ) (hψ : Continuous ψ) (ι : U2 → U4) (hι : Continuous ι)
    (n : ℕ) (q : ℤ)
    (hin : ∀ k, ∫ m, KT.psi n q n m * ψ ((ι m)⁻¹ * k) ∂μK = ((KT.normSqInt n q : ℝ) : ℂ) * ψ k)
    (Φ : U4 → ℂ) (hΦ : Continuous Φ) (hfix : RFix μ (eOf μ ψ) Φ) (g : U4) :
    ∫ m, T n q m * Φ (g * ι m) ∂μK = Φ g := by
  haveI := hμ.prob
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hcpt, -⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.u4
  have hN : ((KT.normSqInt n q : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (KT.normSqInt_pos n q).ne'
  have hec : Continuous (eOf μ ψ) := by
    unfold eOf
    exact continuous_const.mul (Complex.continuous_conj.comp hψ)
  have hTc : Continuous (T n q) := by
    unfold T
    exact continuous_const.mul (KT.continuous_conj_psi n q n)
  have hA : ∀ m, Φ (g * ι m) = ∫ k, eOf μ ψ ((ι m)⁻¹ * k) * Φ (g * k) ∂μ := by
    intro m
    rw [← hfix (g * ι m)]
    have h := (hμ.left (ι m)).integral_comp (Homeomorph.mulLeft (ι m)).measurableEmbedding
      (fun k => eOf μ ψ ((ι m)⁻¹ * k) * Φ (g * k))
    rw [← h]
    congr 1; funext k
    simp only [inv_mul_cancel_left, mul_assoc]
  have hint : Integrable (Function.uncurry fun m k => T n q m * (eOf μ ψ ((ι m)⁻¹ * k) * Φ (g * k))) (μK.prod μ) := by
    have hcont : Continuous (Function.uncurry fun m k => T n q m * (eOf μ ψ ((ι m)⁻¹ * k) * Φ (g * k))) := by
      unfold Function.uncurry
      refine (hTc.comp continuous_fst).mul ((hec.comp ?_).mul (hΦ.comp (continuous_const.mul continuous_snd)))
      exact ((hι.comp continuous_fst).inv).mul continuous_snd
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hB : ∀ k, ∫ m, T n q m * eOf μ ψ ((ι m)⁻¹ * k) ∂μK = eOf μ ψ k := by
    intro k
    have h := congrArg conj (hin k)
    rw [← integral_conj] at h
    have e : ∀ m, T n q m * eOf μ ψ ((ι m)⁻¹ * k) = (((KT.normSqInt n q : ℝ) : ℂ)⁻¹ * ((∫ h, ‖ψ h‖ ^ 2 ∂μ : ℝ) : ℂ)⁻¹) *
        conj (KT.psi n q n m * ψ ((ι m)⁻¹ * k)) := by
      intro m
      simp only [T, eOf, map_mul]
      ring
    simp only [e]
    rw [integral_const_mul, h, map_mul, Complex.conj_ofReal, eOf]
    field_simp
  calc ∫ m, T n q m * Φ (g * ι m) ∂μK
      = ∫ m, ∫ k, T n q m * (eOf μ ψ ((ι m)⁻¹ * k) * Φ (g * k)) ∂μ ∂μK := by
        congr 1; funext m
        rw [hA m, integral_const_mul]
    _ = ∫ k, ∫ m, T n q m * (eOf μ ψ ((ι m)⁻¹ * k) * Φ (g * k)) ∂μK ∂μ := integral_integral_swap hint
    _ = ∫ k, eOf μ ψ k * Φ (g * k) ∂μ := by
        congr 1; funext k
        rw [← hB k, ← integral_mul_const]
        congr 1; funext m
        ring
    _ = Φ g := hfix g

private theorem innerOf (ψ : U4 → ℂ) (ι : U2 → U4) (hι : Continuous ι) (n : ℕ) (q : ℤ)
    {J : Type} [Fintype J] (j₀ : J) (a b : J → U4 → ℂ) (hc : ∀ j, Continuous (a j) ∧ Continuous (b j))
    (hexp : ∀ h k, ψ (h * k) = ∑ j, a j h * b j k) (ha : a j₀ = ψ) (hb : b j₀ = ψ)
    (hz : ∀ j, j ≠ j₀ → ∫ m, KT.psi n q n m * a j (ι m)⁻¹ ∂μK = 0)
    (hres : ∀ m, ψ (ι m)⁻¹ = conj (KT.psi n q n m)) (k : U4) :
    ∫ m, KT.psi n q n m * ψ ((ι m)⁻¹ * k) ∂μK = ((KT.normSqInt n q : ℝ) : ℂ) * ψ k := by
  have hci : ∀ j, Integrable (fun m => KT.psi n q n m * a j (ι m)⁻¹) μK := fun j =>
    KT.integrable_of_continuous ((KT.continuous_psi n q n).mul ((hc j).1.comp hι.inv))
  have h1 : ∀ m, KT.psi n q n m * ψ ((ι m)⁻¹ * k) = ∑ j, (KT.psi n q n m * a j (ι m)⁻¹) * b j k := by
    intro m
    rw [hexp, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [h1]
  rw [integral_finset_sum _ fun j _ => (hci j).mul_const _]
  simp only [integral_mul_const]
  rw [Finset.sum_eq_single j₀ (fun j _ hj => by rw [hz j hj, zero_mul]) (fun h => absurd (Finset.mem_univ _) h), ha, hb]
  congr 1
  rw [← KT.integral_conj_psi_self n q]
  congr 1; funext m
  rw [hres, mul_comm]

private theorem vanish (a₀ : U4 → ℂ) (ν μ₀ : Fin (2 + 2) → ℤ) (ι : U2 → U4) (n : ℕ) (q : ℤ) (D D' : ℝ → ℝ → Fin (2 + 2) → ℝ)
    (hr : ∀ θ h, a₀ (h * dg θ) = chi ν θ * a₀ h) (hl : ∀ θ h, a₀ (dg θ * h) = chi μ₀ θ * a₀ h)
    (hmul : ∀ x y, ι (x * y) = ι x * ι y) (hD : ∀ s t, ι (tC s t) = dg (D s t))
    (hD' : ∀ s t m, dg (D' s t) * ι m = ι m * dg (D' s t))
    (hψ : ∀ s t m, KT.psi n q n (tC s t * m) = chi μ₀ (D s t) * KT.psi n q n m)
    (hsplit : (∀ s t, chi ν (D s t) = chi μ₀ (D s t)) → (∀ s t, chi ν (D' s t) = chi μ₀ (D' s t)) → ν = μ₀)
    (hne : ν ≠ μ₀) : ∫ m, KT.psi n q n m * a₀ (ι m)⁻¹ ∂μK = 0 := by
  by_contra hI
  refine hne (hsplit (fun s t => ?_) fun s t => ?_)
  · apply mul_right_cancel₀ hI
    conv_lhs => rw [← integral_mul_left_K _ (tC s t)]
    rw [← integral_const_mul, ← integral_const_mul]
    congr 1; funext m
    have e : a₀ (ι m)⁻¹ = chi ν (D s t) * a₀ (ι (tC s t * m))⁻¹ := by
      rw [← hr, hmul, hD, _root_.mul_inv_rev, inv_mul_cancel_right]
    rw [hψ, e]
    ring
  · have hx : ∃ m, a₀ (ι m)⁻¹ ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hI (by simp [hcon])
    obtain ⟨m, hm⟩ := hx
    apply mul_right_cancel₀ hm
    have hcomm : Commute (dg (D' s t)) (ι m)⁻¹ := (show Commute (dg (D' s t)) (ι m) from hD' s t m).inv_right
    rw [← hr, ← hl, hcomm.eq]

private theorem chi_add (ν : Fin (2 + 2) → ℤ) (θ θ' : Fin (2 + 2) → ℝ) : chi ν (θ + θ') = chi ν θ * chi ν θ' := by
  simp only [chi]
  rw [← Complex.exp_add, ← mul_add, ← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply]
  push_cast
  ring

private theorem chi_split (hchi : ∀ ν ν' : Fin (2 + 2) → ℤ, (∀ θ, chi ν θ = chi ν' θ) → ν = ν') (ν ν' : Fin (2 + 2) → ℤ)
    (h1 : ∀ s t : ℝ, chi ν ![s, t, 0, 0] = chi ν' ![s, t, 0, 0])
    (h2 : ∀ s t : ℝ, chi ν ![0, 0, s, t] = chi ν' ![0, 0, s, t]) : ν = ν' := by
  refine hchi _ _ fun θ => ?_
  have e : θ = ![θ 0, θ 1, 0, 0] + ![0, 0, θ 2, θ 3] := by
    funext i; fin_cases i <;> simp
  rw [e, chi_add, chi_add, h1, h2]

private theorem chi_wt₁ (n : ℕ) (q : ℤ) (n' : ℕ) (q' : ℤ) (s t : ℝ) :
    chi (wt n q n' q') ![s, t, 0, 0] = Complex.exp (Complex.I * ((((n : ℝ) + q) * s + ((n : ℝ) - n + q) * t : ℝ) : ℂ)) := by
  rw [chi]
  congr 2
  have := Fin.sum_univ_four (fun i : Fin 4 => ((wt n q n' q' i : ℤ) : ℂ) * (((![s, t, 0, 0] : Fin 4 → ℝ) i : ℝ) : ℂ))
  refine this.trans ?_
  simp [wt]

private theorem chi_wt₂ (n : ℕ) (q : ℤ) (n' : ℕ) (q' : ℤ) (s t : ℝ) :
    chi (wt n q n' q') ![0, 0, s, t] = Complex.exp (Complex.I * ((((n' : ℝ) + q') * s + ((n' : ℝ) - n' + q') * t : ℝ) : ℂ)) := by
  rw [chi]
  congr 2
  have := Fin.sum_univ_four (fun i : Fin 4 => ((wt n q n' q' i : ℤ) : ℂ) * (((![0, 0, s, t] : Fin 4 → ℝ) i : ℝ) : ℂ))
  refine this.trans ?_
  simp [wt]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.coefFix :
    ∀ (μ : Measure U4) ψ n q n' q', Haar4 μ → μ.IsOpenPosMeasure → Coef ψ n q n' q' → ∀ Φ : U4 → ℂ, Continuous Φ → RFix μ (eOf μ ψ) Φ → ∀ g,
      ∫ m, T n q m * Φ (g * bd m 1) ∂μK = Φ g ∧ ∫ m, T n' q' m * Φ (g * bd 1 m) ∂μK = Φ g := by
  intro μ ψ n q n' q' hH hO hC Φ hΦ hfix g
  obtain ⟨hψc, -, -, -⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.coefIdem μ ψ n q n' q' hH hO hC
  obtain ⟨-, hmul, -, hinv, hcont, -, -, -, hdg, -, hchi, -, -⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.u4
  obtain ⟨J, _, j₀, a, b, ν, hc, hexp, ha, hb, -, hw, -, hne⟩ := hC.exp
  have ht0 : tC 0 0 = 1 := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [tC]
  have h1 : ∀ s t : ℝ, bd (tC s t) 1 = dg ![s, t, 0, 0] := fun s t => by rw [hdg, ht0]
  have h2 : ∀ s t : ℝ, bd 1 (tC s t) = dg ![0, 0, s, t] := fun s t => by rw [hdg, ht0]
  have hι₁ : Continuous fun m : U2 => bd m 1 := hcont.comp (continuous_id.prodMk continuous_const)
  have hι₂ : Continuous fun m : U2 => bd 1 m := hcont.comp (continuous_const.prodMk continuous_id)
  constructor
  · refine fixOf μ hH ψ hψc (fun m => bd m 1) hι₁ n q
      (fun k => innerOf ψ (fun m => bd m 1) hι₁ n q j₀ a b hc hexp ha hb (fun j hj => ?_) (fun m => ?_) k)
      Φ hΦ hfix g
    · refine vanish (a j) (ν j) (wt n q n' q') (fun m => bd m 1) n q (fun s t => ![s, t, 0, 0]) (fun s t => ![0, 0, s, t])
        (fun θ h => (hw j θ h).1) (fun θ h => (hw j θ h).2.1) (fun x y => ?_) h1 (fun s t m => ?_) (fun s t m => ?_)
        (chi_split hchi _ _) (hne j hj)
      · simp only [hmul, mul_one]
      · simp only [← h2, hmul, mul_one, one_mul]
      · rw [KT.psi_tC_mul n q le_rfl, chi_wt₁]
    · simp only [hinv, hC.res, inv_one, KT.psi_one, mul_one, KT.psi_self_inv]
  · refine fixOf μ hH ψ hψc (fun m => bd 1 m) hι₂ n' q'
      (fun k => innerOf ψ (fun m => bd 1 m) hι₂ n' q' j₀ a b hc hexp ha hb (fun j hj => ?_) (fun m => ?_) k)
      Φ hΦ hfix g
    · refine vanish (a j) (ν j) (wt n q n' q') (fun m => bd 1 m) n' q' (fun s t => ![0, 0, s, t]) (fun s t => ![s, t, 0, 0])
        (fun θ h => (hw j θ h).1) (fun θ h => (hw j θ h).2.1) (fun x y => ?_) h2 (fun s t m => ?_) (fun s t m => ?_)
        (fun e₂ e₁ => chi_split hchi _ _ e₁ e₂) (hne j hj)
      · simp only [hmul, mul_one]
      · simp only [← h1, hmul, mul_one, one_mul]
      · rw [KT.psi_tC_mul n' q' le_rfl, chi_wt₂]
    · simp only [hinv, hC.res, inv_one, KT.psi_one, one_mul, KT.psi_self_inv]
