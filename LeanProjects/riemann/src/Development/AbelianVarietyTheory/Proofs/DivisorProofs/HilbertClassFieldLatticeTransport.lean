import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmCurveTorsionTransportSecondPeriod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartEqOneOfLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModFMulPosPrincipal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticFieldExistsSqrtNegDiscrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealNormEqFiniteIdeleModuleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteIdeleModuleExistsRatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModFFiniteIdeleUpToExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCMTypeOfEmbeddingsCardEqFinrankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormGaloisConjHeckeCharacterFinitePartEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricSumCoordinateIsAlgebraicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjToricPeriodCoordinateSumOverClassesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquidistributedIdealClassesOfHilbertClassFieldJStatement

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn coordIn_div)
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.TransportProof
theorem exists_sq_eq_neg : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (h2 : Module.finrank ℚ K = 2) (hd : discr K = -(d : ℤ)), ∃ δ : K, δ ^ 2 = -(d : K) := GlobalTheory.T.quadraticField_exists_sqrt_neg_discr

theorem nrm_eq_modF : ∀ {K : Type} [Field K] [NumberField K] (t : (Af K)ˣ) (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (h : IsInvIdealOf t 𝔞), nrm 𝔞 = modF t := GlobalTheory.T.fractionalIdealNorm_eq_finiteIdeleModule

theorem modF_rat : ∀ {E : Type} [Field E] [NumberField E] (y : (Af E)ˣ), ∃ q : ℚ, modF y = q := GlobalTheory.T.finiteIdele_module_exists_rat

theorem modF_upIdele : ∀ {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (t : (Af K)ˣ), modF (upIdele K E t) = modF t ^ Module.finrank K E := GlobalTheory.T.modF_finiteIdeleUpToExtension

theorem card_eq_finrank : ∀ {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [IsCMField E] [Algebra K E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hφ : IsCMType φ) (h2 : Module.finrank ℚ K = 2), Fintype.card I = Module.finrank K E := GlobalTheory.T.isCMTypeOfEmbeddings_card_eq_finrank

theorem norm_conj_finPart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hφ : IsCMType φ) (s : ℕ) (κ : I → ℕ) (c : Ideal (OF E)) (hc : c ≠ ⊥) (χ : HChar E) (hχ : HasInf χ φ (fun i => (κ i : ℤ) + s)) (hu : ∀ u ∈ hatOUnits c, finPart χ u = 1) (σ : ℂ ≃+* ℂ) (y : (Af E)ˣ), ‖σ (finPart χ y : ℂ)‖ = 1 := GlobalTheory.T.norm_galois_conj_heckeCharacter_finitePart_eq_one

theorem algebraic_coordIn_toric : ∀ (hA : LatAlg) {K : Type} [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (h2 : Module.finrank ℚ K = 2) (hd : 0 < d) (hδ : δ ^ 2 = -(d : K)) (Λ₀ : PeriodPair) (Ω₀ : ℂ) (hΛ : IsLatOf ι 1 Λ₀) (hΩ : Ω₀ ^ 12 = latDisc Λ₀) {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra K E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hE : UnramFin E) (hφ : IsCMType φ) (hφK : ∀ i, (φ i).comp (algebraMap K E) = ι) (s : ℕ) (hs : 1 ≤ s) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (h𝔣 : IsBaseCond 𝔣) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E) (T : ℂ) (hV : IsValSum φ s κ 𝔣 Q χ T), IsAlgebraic ℚ (coordIn E d s κ Ω₀ T) := GlobalTheory.T.toricSum_coordinate_isAlgebraic

theorem conj_coordIn_toric : ∀ (hC : LatConj) {K : Type} [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (h2 : Module.finrank ℚ K = 2) (hd : 0 < d) (hδ : δ ^ 2 = -(d : K)) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ) (hΩ : Ω₀ ^ 12 = latDisc Λ₀) (hT : TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁) {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra K E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hE : UnramFin E) (hφ : IsCMType φ) (hφK : ∀ i, (φ i).comp (algebraMap K E) = ι) (s : ℕ) (hs : 1 ≤ s) (κ κ' : I → ℕ) (hκ' : IsConjWt φ g κ κ') (𝔣 : Ideal (OF E)) (h𝔣 : IsBaseCond 𝔣) (Q : Finset (HeightOneSpectrum (OF E))) (χ χ' : HChar E) (T T' : ℂ) (hV : IsValSum φ s κ 𝔣 Q χ T) (hV' : IsConjSum φ s κ' 𝔣 Q g χ χ' T'), g (coordIn E d s κ Ω₀ T) = coordIn E d s κ Ω₁ ((((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ * (lamF s χ' (upIdele K E t))⁻¹ * T') := GlobalTheory.T.conj_toricPeriodCoordinate_sum_over_classes

theorem equidistributed_of_j : ∀ (hH : GlobalTheory.Published.HilbertClassFieldJ) {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (h2 : Module.finrank ℚ K = 2) (φK : K →+* ℂ) (ΛK : PeriodPair) (hΛ : IsLatOf φK 1 ΛK) (𝔞 : (ℂ ≃+* ℂ) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (h𝔞 : ∀ σ : ℂ ≃+* ℂ, Fixes φK σ → ∃ Λ : PeriodPair, IsLatOf φK (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) Λ ∧ jLat Λ = σ (jLat ΛK)), Equidistributed φK (jLat ΛK) 𝔞 := GlobalTheory.T.equidistributed_idealClasses_of_hilbertClassFieldJ

theorem isTotallyComplex_of_discr_neg {K : Type} [Field K] [NumberField K] (h2 : Module.finrank ℚ K = 2)
    (h : discr K < 0) : IsTotallyComplex K := by
  have hs := sign_discr K
  rw [Int.sign_eq_neg_one_of_neg h] at hs
  have hr := InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [h2] at hr
  have hc : InfinitePlace.nrComplexPlaces K = 1 := by
    rcases Nat.even_or_odd (InfinitePlace.nrComplexPlaces K) with he | ho
    · rw [he.neg_one_pow] at hs; norm_num at hs
    · obtain ⟨k, hk⟩ := ho; omega
  exact nrRealPlaces_eq_zero_iff.1 (by omega)

theorem disc_j_of_torsTransport {K : Type} [Field K] [NumberField K] {ι : K →+* ℂ} {g : ℂ ≃+* ℂ} {t : (Af K)ˣ}
    {Λ₀ Λ₁ : PeriodPair} {Ω₀ Ω₁ : ℂ} (hT : TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁) (hΩ : Ω₀ ^ 12 = latDisc Λ₀) :
    Ω₁ ^ 12 = latDisc Λ₁ ∧ jLat Λ₁ = g (jLat Λ₀) := by
  obtain ⟨h0, h1, -, -, -, ha, hb, -⟩ := hT
  have e0 : (Λ₀.g₂ / Ω₀ ^ 4) ^ 3 - 27 * (Λ₀.g₃ / Ω₀ ^ 6) ^ 2 = 1 := by
    have : latDisc Λ₀ / Ω₀ ^ 12 = 1 := by rw [← hΩ, div_self (pow_ne_zero _ h0)]
    rw [← this, latDisc]; field_simp
  have e1 : (Λ₁.g₂ / Ω₁ ^ 4) ^ 3 - 27 * (Λ₁.g₃ / Ω₁ ^ 6) ^ 2 = 1 := by
    rw [← ha, ← hb]
    have := congrArg g e0
    simpa [map_sub, map_pow, map_mul, map_ofNat] using this
  have hD : Ω₁ ^ 12 = latDisc Λ₁ := by
    rw [latDisc]; field_simp at e1; linear_combination -e1
  refine ⟨hD, ?_⟩
  have j0 : jLat Λ₀ = 1728 * (Λ₀.g₂ / Ω₀ ^ 4) ^ 3 := by
    rw [jLat, ← hΩ]; field_simp
  have j1 : jLat Λ₁ = 1728 * (Λ₁.g₂ / Ω₁ ^ 4) ^ 3 := by
    rw [jLat, ← hD]; field_simp
  rw [j0, j1, map_mul, map_pow, ha, map_ofNat]

theorem condQ_ne_bot {E : Type} [Field E] [NumberField E] {𝔣 : Ideal (OF E)} (h𝔣 : IsBaseCond 𝔣)
    (Q : Finset (HeightOneSpectrum (OF E))) : condQ 𝔣 Q ≠ ⊥ := by
  unfold condQ
  rw [← Ideal.zero_eq_bot]
  refine mul_ne_zero h𝔣.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)

theorem norm_lamF_conj_up {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [IsCMField E]
    [Algebra K E] {I : Type} [Fintype I] (h2 : Module.finrank ℚ K = 2) (φ : I → E →+* ℂ) (hE : UnramFin E)
    (hφ : IsCMType φ) (s : ℕ) (κ κ' : I → ℕ) (𝔣 : Ideal (OF E)) (h𝔣 : IsBaseCond 𝔣)
    (Q : Finset (HeightOneSpectrum (OF E))) (hQ : IsFinSetSplitPlacesCoprimeConductor 𝔣 Q) (χ χ' : HChar E) (hχ : IsValChar φ s κ 𝔣 Q χ)
    (σ : ℂ ≃+* ℂ) (hc : IsConjChar φ s κ' σ χ χ') (t : (Af K)ˣ) :
    ‖lamF s χ' (upIdele K E t)‖ = modF t ^ (s * Fintype.card I) := by
  have hu := GlobalTheory.CMVal.OrderUnits.finPart_eq_one E I φ hφ s κ 𝔣 Q χ hE h𝔣 hQ hχ
  have h1 := norm_conj_finPart φ hφ s κ (condQ 𝔣 Q) (condQ_ne_bot h𝔣 Q) χ hχ.2.2.1 hu σ (upIdele K E t)
  obtain ⟨q, hq⟩ := modF_rat (upIdele K E t)
  have hpos := GlobalTheory.CMVal.IdeleModule.modF_pos (upIdele K E t)
  rw [hc.1, lamF, map_mul, norm_mul, h1, one_mul]
  have e : (((modF (upIdele K E t)) ^ s : ℝ) : ℂ) = ((q ^ s : ℚ) : ℂ) := by rw [hq]; push_cast; rfl
  rw [e, map_ratCast, ← e]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pow_pos hpos _), modF_upIdele, ← card_eq_finrank φ hφ h2,
    ← pow_mul, mul_comm]

theorem beta_eq_coordIn_pow (E : Type) [Field E] [NumberField E] {I : Type} [Fintype I] (d s : ℕ) (κ : I → ℕ)
    (Ω T : ℂ) (Λ : PeriodPair) (h : Ω ^ 12 = latDisc Λ) : beta E d s κ Λ T = coordIn E d s κ Ω T ^ 12 := by
  rw [beta_eq, coordIn, div_pow, ← h, ← pow_mul, ← pow_mul, mul_comm 12]

theorem transportFor_of (hA : LatAlg) (hC : LatConj) {K : Type} [Field K] [NumberField K] (d : ℕ) (hd : 0 < d)
    (δ : K) (hδ : δ ^ 2 = -(d : K)) (h2 : Module.finrank ℚ K = 2) (φK : K →+* ℂ) (ΛK : PeriodPair)
    (hΛ : IsLatOf φK 1 ΛK) (Ω₀ : ℂ) (hΩ₀ : Ω₀ ^ 12 = latDisc ΛK) (hΩ₀0 : Ω₀ ≠ 0)
    (t : (ℂ ≃+* ℂ) → (Af K)ˣ) (𝔞 : (ℂ ≃+* ℂ) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (Λ : (ℂ ≃+* ℂ) → PeriodPair)
    (Ω : (ℂ ≃+* ℂ) → ℂ)
    (hT : ∀ σ, Fixes φK σ →
      TorsTransport φK σ (t σ) ΛK (Λ σ) Ω₀ (Ω σ) ∧ IsInvIdealOf (t σ) (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K))
    (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (hE : UnramFin E)
    (I : Type) [Fintype I] (φ : I → E →+* ℂ) (hφ : IsCMType φ) (hφK : ∀ i, (φ i).comp (algebraMap K E) = φK)
    (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (hs : 1 ≤ s) (h𝔣 : IsBaseCond 𝔣) :
    TransportFor d φK ΛK t 𝔞 Λ φ s κ 𝔣 := by
  have hC0 : (C0 E d (2 * s) κ : ℂ) ≠ 0 := by exact_mod_cast (cmValueConst_pos E hd (by omega) κ).ne'
  have conj : ∀ σ, Fixes φK σ → ∀ κ', IsConjWt φ σ κ κ' → ∀ Q χ T χ' T', IsValSum φ s κ 𝔣 Q χ T →
      IsConjSum φ s κ' 𝔣 Q σ χ χ' T' →
      σ (coordIn E d s κ Ω₀ T) = coordIn E d s κ (Ω σ) ((((nrm (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^
        (∑ i, κ i))⁻¹ * (lamF s χ' (upIdele K E (t σ)))⁻¹ * T') := by
    intro σ hσ κ' hκ' Q χ T χ' T' hV hV'
    rw [nrm_eq_modF _ _ (hT σ hσ).2]
    exact conj_coordIn_toric hC d δ φK h2 hd hδ σ (t σ) ΛK (Λ σ) Ω₀ (Ω σ) hΩ₀ (hT σ hσ).1 φ hE hφ hφK s hs
      κ κ' hκ' 𝔣 h𝔣 Q χ χ' T T' hV hV'
  refine ⟨fun Q χ T hV => ⟨?_, fun σ hσ κ' hκ' χ' T' hV' => ?_⟩,
    fun Q₁ Q₂ χ₁ χ₂ T₁ T₂ hV₁ hV₂ hT₂ => ⟨?_, fun σ hσ κ' hκ' χ₁' χ₂' T₁' T₂' hV₁' hV₂' => ?_⟩⟩
  · rw [beta_eq_coordIn_pow E d s κ Ω₀ T ΛK hΩ₀]
    exact (algebraic_coordIn_toric hA d δ φK h2 hd hδ ΛK Ω₀ hΛ hΩ₀ φ hE hφ hφK s hs κ 𝔣 h𝔣 Q χ T hV).pow 12
  · have hD := (disc_j_of_torsTransport (hT σ hσ).1 hΩ₀).1
    set N := nrm (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) with hN
    have hN0 : N ≠ 0 := nrm_ne_zero _
    have hNpos : 0 < N := lt_of_le_of_ne (by rw [hN, nrm]; exact_mod_cast FractionalIdeal.absNorm_nonneg _) hN0.symm
    have e : σ (beta E d s κ ΛK T) = beta E d s κ (Λ σ)
        ((((N : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ * (lamF s χ' (upIdele K E (t σ)))⁻¹ * T') := by
      rw [beta_eq_coordIn_pow E d s κ Ω₀ T ΛK hΩ₀, map_pow, conj σ hσ κ' hκ' Q χ T χ' T' hV hV',
        beta_eq_coordIn_pow E d s κ (Ω σ) _ (Λ σ) hD]
    have hl := norm_lamF_conj_up h2 φ hE hφ s κ κ' 𝔣 h𝔣 Q hV.1 χ χ' hV.2.1 σ hV'.1 (t σ)
    rw [← nrm_eq_modF _ _ (hT σ hσ).2, ← hN] at hl
    refine ⟨by rw [e, beta_eq]; ring, ?_⟩
    rw [e, beta_eq, norm_div, norm_pow, norm_mul, norm_mul, norm_mul, norm_inv, norm_inv, hl, norm_pow, norm_pow,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hNpos,
      abs_of_pos (cmValueConst_pos E hd (by omega) κ)]
    have hDn : ‖latDisc (Λ σ)‖ ≠ 0 := norm_ne_zero_iff.2 (latDisc_ne_zero _)
    field_simp
    ring
  · rw [← coordIn_div E hd hs κ hΩ₀0 T₁ T₂, div_eq_mul_inv]
    exact (algebraic_coordIn_toric hA d δ φK h2 hd hδ ΛK Ω₀ hΛ hΩ₀ φ hE hφ hφK s hs κ 𝔣 h𝔣 Q₁ χ₁ T₁ hV₁).mul
      (algebraic_coordIn_toric hA d δ φK h2 hd hδ ΛK Ω₀ hΛ hΩ₀ φ hE hφ hφK s hs κ 𝔣 h𝔣 Q₂ χ₂ T₂ hV₂).inv
  · have hΩσ : Ω σ ≠ 0 := (hT σ hσ).1.2.1
    set m : ℂ := (((nrm (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ (∑ i, κ i)) with hm
    have hm0 : m ≠ 0 := pow_ne_zero _ (by exact_mod_cast nrm_ne_zero _)
    have c1 := conj σ hσ κ' hκ' Q₁ χ₁ T₁ χ₁' T₁' hV₁ hV₁'
    have c2 := conj σ hσ κ' hκ' Q₂ χ₂ T₂ χ₂' T₂' hV₂ hV₂'
    have hc2 : coordIn E d s κ Ω₀ T₂ ≠ 0 := by
      rw [coordIn]; exact div_ne_zero (mul_ne_zero hC0 hT₂) (pow_ne_zero _ hΩ₀0)
    have hT2' : T₂' ≠ 0 := by
      rintro rfl
      have := (map_ne_zero σ).2 hc2
      rw [c2, mul_zero, coordIn, mul_zero, zero_div] at this
      exact this rfl
    refine ⟨hT2', ?_⟩
    rw [← coordIn_div E hd hs κ hΩ₀0 T₁ T₂, map_div₀, c1, c2, coordIn_div E hd hs κ hΩσ, mul_assoc, mul_assoc,
      mul_div_mul_left _ _ (inv_ne_zero hm0)]

theorem transport_of (hH : GlobalTheory.Published.HilbertClassFieldJ) (hA : LatAlg) (hC : LatConj) : Transport := by
  intro K _ _ d hd h2 hdisc φK ΛK hΛ
  have hTC : IsTotallyComplex K := isTotallyComplex_of_discr_neg h2 (by rw [hdisc]; omega)
  obtain ⟨δ, hδ⟩ := exists_sq_eq_neg K d h2 hdisc
  obtain ⟨Ω₀, hΩ₀⟩ := IsAlgClosed.exists_pow_nat_eq (latDisc ΛK) (by norm_num : 0 < 12)
  have hΩ₀0 : Ω₀ ≠ 0 := by rintro rfl; exact latDisc_ne_zero ΛK (by rw [← hΩ₀]; norm_num)
  have key : ∀ σ : ℂ ≃+* ℂ, Fixes φK σ → ∃ (t : (Af K)ˣ) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (Λ : PeriodPair) (Ω : ℂ),
      TorsTransport φK σ t ΛK Λ Ω₀ Ω ∧ IsInvIdealOf t (𝔞 : FractionalIdeal (𝓞 K)⁰ K) ∧
        IsLatOf φK (𝔞 : FractionalIdeal (𝓞 K)⁰ K) Λ := by
    intro σ hσ
    letI : Algebra K ℂ := φK.toAlgebra
    obtain ⟨X, hX, ξ, hξ, hTr⟩ := GlobalTheory.LatVal.CurveTransport.exists_curve_torsTransport h2 φK ΛK Ω₀ hΛ hΩ₀0
    haveI := hX
    let σK : ℂ ≃ₐ[K] ℂ := AlgEquiv.ofRingEquiv (f := σ) hσ
    obtain ⟨t, ht⟩ := GlobalTheory.EllipticCM.exists_transports h2 σK one_ne_zero hξ
    obtain ⟨Λ₁, Ω₁, h1⟩ := hTr σK t ht
    obtain ⟨𝔞, h𝔞t, h𝔞Λ⟩ := h1.2.2.2.2.1
    have h𝔞0 : 𝔞 ≠ 0 := by
      rintro rfl
      have hm : Λ₁.ω₁ ∈ (Λ₁.lattice : Set ℂ) := PeriodPair.ω₁_mem_lattice Λ₁
      rw [h𝔞Λ] at hm
      obtain ⟨x, hx, hx'⟩ := hm
      have hx0 : x = 0 := by simpa using hx
      rw [hx0, map_zero] at hx'
      exact (by simpa using Λ₁.indep.ne_zero 0 : Λ₁.ω₁ ≠ 0) hx'.symm
    exact ⟨t, Units.mk0 𝔞 h𝔞0, Λ₁, Ω₁, h1, h𝔞t, h𝔞Λ⟩
  haveI : Nonempty PeriodPair := ⟨ΛK⟩
  choose! t 𝔞 Λ Ω hT using key
  refine ⟨t, 𝔞, Λ, fun σ hσ => ⟨(hT σ hσ).2.1, (hT σ hσ).2.2, (disc_j_of_torsTransport (hT σ hσ).1 hΩ₀).2⟩,
    equidistributed_of_j hH h2 φK ΛK hΛ 𝔞
      (fun σ hσ => ⟨Λ σ, (hT σ hσ).2.2, (disc_j_of_torsTransport (hT σ hσ).1 hΩ₀).2⟩), ?_⟩
  intro E _ _ _ _ _ hE I _ φ hcard hφ hφK s κ 𝔣 hs hκ h𝔣
  exact transportFor_of hA hC d (by omega) δ hδ h2 φK ΛK hΛ Ω₀ hΩ₀ hΩ₀0 t 𝔞 Λ Ω
    (fun σ hσ => ⟨(hT σ hσ).1, (hT σ hσ).2.1⟩) E hE I φ hφ hφK s κ 𝔣 hs h𝔣

end GlobalTheory.TransportProof
