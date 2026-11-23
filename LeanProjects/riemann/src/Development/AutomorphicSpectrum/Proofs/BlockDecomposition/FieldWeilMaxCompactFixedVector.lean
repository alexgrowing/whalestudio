import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.REALTH
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticUniformizerOrder
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLFactorHalfNeZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsQuadCharUnramified
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsStdChEOfOrdUnif
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnstatedLocalWeilLemma

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th Ad3.K.GL2LocalData
open GlobalTheory.CompanionTheory.SphTheta GlobalTheory.CompanionTheory.NormGauss
open GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.RwKF

section One
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem intInd_congr {x y : K} (h : modulus x = modulus y) : intInd x = intInd y := by
  unfold intInd
  simp only [← modulus_le_one_iff, h]

theorem modulus_eq_one_of_mem {x : K} (h0 : x ≠ 0) (hx : x ∈ 𝒪[K]) (hi : x⁻¹ ∈ 𝒪[K]) : modulus x = 1 := by
  refine le_antisymm (modulus_le_one_iff.2 hx) ?_
  have h := modulus_le_one_iff.2 hi
  rw [modulus_inv] at h
  exact (inv_le_one₀ (modulus_pos h0)).1 h

theorem indicator_eq_intInd : Set.indicator {x : K | x ∈ 𝒪[K]} (1 : K → ℂ) = intInd := by
  funext x
  by_cases h : x ∈ 𝒪[K]
  · rw [intInd_of_mem h, Set.indicator_of_mem (show x ∈ {x : K | x ∈ 𝒪[K]} from h)]
    rfl
  · rw [intInd_of_not_mem h, Set.indicator_of_notMem (show x ∉ {x : K | x ∈ 𝒪[K]} from h)]

end One

section Two
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E]

theorem ord_unif_of_card (hd : Module.finrank F E = 2) (hres : residueCard E = residueCard F ^ 2) :
    ord (algebraMap F E (unifUnit F : F)) = 1 := by
  have h := card_residueField_eq_pow_residueDegree F E
  have hf : residueDegree F E = 2 :=
    Nat.pow_right_injective (one_lt_residueCard (K := F)) (h.symm.trans hres)
  have he := ramificationIndex_mul_residueDegree F E
  rw [hf, hd] at he
  have he1 : ramificationIndex F E = 1 := by omega
  rw [ord_algebraMap, he1, ord_unif]
  simp

end Two

section Three
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
  {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [Fact (Module.finrank F E = 2)]

theorem modulus_sigma (σ : E ≃ₐ[F] E) (x : E) : modulus (σ x) = modulus x := by
  rw [← modulus_norm (K := F) (σ x), ← modulus_norm (K := F) x, Algebra.norm_eq_of_algEquiv]

theorem modulus_map_one {e : F} (he : modulus e = 1) : modulus (algebraMap F E e) = 1 := by
  rw [← modulus_norm (K := F), norm_algebraMap_eq_sq, pow_two, modulus_mul, he, one_mul]

theorem intInd_sigma_mul (σ : E ≃ₐ[F] E) {e : F} (he : modulus e = 1) (z : E) :
    intInd (σ z * algebraMap F E e) = intInd z :=
  intInd_congr (by rw [modulus_mul, modulus_sigma, modulus_map_one he, mul_one])

theorem norm_y (σ : E ≃ₐ[F] E) (c : F) (z : E) :
    Algebra.norm F (σ z * algebraMap F E c⁻¹) = Algebra.norm F z * c⁻¹ ^ 2 := by
  rw [map_mul, Algebra.norm_eq_of_algEquiv, norm_algebraMap_eq_sq]

variable [MeasurableSpace E] [BorelSpace E]

theorem rW_ne (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μ : Measure E) (a b d : F) {c : F} (hc : c ≠ 0) (z : E) :
    Ad3.K.GL2LocalData.rW χ σ μ 1 a b c d intInd z = nsg E (-c) * (((modulus c : ℝ)⁻¹ : ℝ) : ℂ) *
      ((χ (a * Algebra.norm F z / c) : ℂ) *
        ∫ u : E, (χ (d / c * Algebra.norm F u
          - Algebra.trace F E ((σ z * algebraMap F E c⁻¹) * u)) : ℂ) * intInd u ∂μ) := by
  unfold Ad3.K.GL2LocalData.rW
  rw [if_neg hc, one_mul]
  congr 1
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have ht : Algebra.trace F E (σ z * algebraMap F E c⁻¹ * u) = c⁻¹ * Algebra.trace F E (σ z * u) := by
    rw [show σ z * algebraMap F E c⁻¹ * u = c⁻¹ • (σ z * u) by rw [Algebra.smul_def]; ring,
      map_smul, smul_eq_mul]
  have harg : (a * Algebra.norm F z + d * Algebra.norm F u - Algebra.trace F E (σ z * u)) / c =
      a * Algebra.norm F z / c + (d / c * Algebra.norm F u
        - Algebra.trace F E (σ z * algebraMap F E c⁻¹ * u)) := by
    rw [ht]
    field_simp
    ring
  beta_reduce
  rw [harg, AddChar.map_add_eq_mul, Circle.coe_mul, mul_assoc]

theorem rW_fix_zero {χ : AddChar F Circle} (hχ : IsStd χ) (σ : E ≃ₐ[F] E) (μ : Measure E)
    (hu : ∀ ε : F, modulus ε = 1 → nsg E ε = 1) {a b d : F} (ha : a ∈ 𝒪[F]) (hb : b ∈ 𝒪[F]) (hd : d ∈ 𝒪[F])
    (hdet : a * d = 1) (z : E) : Ad3.K.GL2LocalData.rW χ σ μ 1 a b 0 d intInd z = intInd z := by
  have ha0 : a ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  have hinv : a⁻¹ = d := (eq_inv_of_mul_eq_one_right hdet).symm
  have ha1 : modulus a = 1 := modulus_eq_one_of_mem ha0 ha (hinv ▸ hd)
  have hI : intInd (algebraMap F E a * z) = intInd z :=
    intInd_congr (by rw [modulus_mul, modulus_map_one ha1, one_mul])
  unfold Ad3.K.GL2LocalData.rW
  rw [if_pos rfl, hu a ha1, ha1, hI]
  by_cases hz : z ∈ 𝒪[E]
  · rw [char_int hχ (mul_mem (mul_mem ha hb) (norm_mem hz))]
    simp
  · simp [intInd_of_not_mem hz]

theorem rW_fix_big {χ : AddChar F Circle} (hχ : IsStd χ) (σ : E ≃ₐ[F] E) (μ : Measure E)
    (hu : ∀ ε : F, modulus ε = 1 → nsg E ε = 1)
    (hint : ∀ (δ : F) (y : E), δ ∈ 𝒪[F] →
      ∫ u : E, (χ (δ * Algebra.norm F u - Algebra.trace F E (y * u)) : ℂ) * intInd u ∂μ = intInd y)
    {a b c d : F} (ha : a ∈ 𝒪[F]) (hb : b ∈ 𝒪[F]) (hcO : c ∈ 𝒪[F])
    (hdet : a * d - b * c = 1) (hc : c ≠ 0) (hδ : d / c ∈ 𝒪[F]) (z : E) :
    Ad3.K.GL2LocalData.rW χ σ μ 1 a b c d intInd z = intInd z := by
  have hci : c⁻¹ = a * (d / c) - b := by
    field_simp
    linear_combination -hdet
  have hciO : c⁻¹ ∈ 𝒪[F] := by
    rw [hci]
    exact sub_mem (mul_mem ha hδ) hb
  have hc1 : modulus c = 1 := modulus_eq_one_of_mem hc hcO hciO
  have hc1' : modulus c⁻¹ = 1 := by rw [modulus_inv, hc1, inv_one]
  have hnc : nsg E (-c) = 1 := hu _ (modulus_eq_one_of_mem (neg_ne_zero.2 hc) (neg_mem hcO)
    (by rw [inv_neg]; exact neg_mem hciO))
  rw [rW_ne χ σ μ a b d hc z, hint _ _ hδ, hnc, hc1, intInd_sigma_mul σ hc1' z]
  by_cases hz : z ∈ 𝒪[E]
  · rw [show a * Algebra.norm F z / c = a * Algebra.norm F z * c⁻¹ from div_eq_mul_inv _ _,
      char_int hχ (mul_mem (mul_mem ha (norm_mem hz)) hciO)]
    simp
  · simp [intInd_of_not_mem hz]

theorem rW_fix_small {χ : AddChar F Circle} (hχ : IsStd χ) (σ : E ≃ₐ[F] E) (μ : Measure E)
    (hm : ∀ x y : F, x ≠ 0 → y ≠ 0 → nsg E (x * y) = nsg E x * nsg E y)
    (hu : ∀ ε : F, modulus ε = 1 → nsg E ε = 1)
    (hint : ∀ (δ : F) (y : E), δ ∉ 𝒪[F] →
      ∫ u : E, (χ (δ * Algebra.norm F u - Algebra.trace F E (y * u)) : ℂ) * intInd u ∂μ
        = nsg E δ * (((modulus δ : ℝ)⁻¹ : ℝ) : ℂ) * (χ (-(Algebra.norm F y) / δ) : ℂ)
          * intInd (y * algebraMap F E δ⁻¹))
    {a b c d : F} (ha : a ∈ 𝒪[F]) (hb : b ∈ 𝒪[F]) (hdO : d ∈ 𝒪[F])
    (hdet : a * d - b * c = 1) (hc : c ≠ 0) (hδ : d / c ∉ 𝒪[F]) (z : E) :
    Ad3.K.GL2LocalData.rW χ σ μ 1 a b c d intInd z = intInd z := by
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hδ (by simp [zero_mem])
  have hδ1 : 1 < modulus (d / c) := not_le.1 (fun h => hδ (modulus_le_one_iff.1 h))
  have hcd : c / d ∈ 𝒪[F] := by
    refine modulus_le_one_iff.1 ?_
    rw [← inv_div, modulus_inv]
    exact (inv_lt_one_of_one_lt₀ hδ1).le
  have hdi : d⁻¹ = a - b * (c / d) := by
    field_simp
    linear_combination -hdet
  have hdiO : d⁻¹ ∈ 𝒪[F] := by
    rw [hdi]
    exact sub_mem ha (mul_mem hb hcd)
  have hd1 : modulus d = 1 := modulus_eq_one_of_mem hd0 hdO hdiO
  have hd1' : modulus d⁻¹ = 1 := by rw [modulus_inv, hd1, inv_one]
  have hnd : nsg E (-d) = 1 := hu _ (modulus_eq_one_of_mem (neg_ne_zero.2 hd0) (neg_mem hdO)
    (by rw [inv_neg]; exact neg_mem hdiO))
  have hnsg : nsg E (-c) * nsg E (d / c) = 1 := by
    rw [← hm _ _ (neg_ne_zero.2 hc) (div_ne_zero hd0 hc), ← hnd]
    congr 1
    field_simp
  have hcr : (modulus c : ℝ) ≠ 0 := by exact_mod_cast modulus_ne_zero hc
  have hmod : (((modulus c : ℝ)⁻¹ : ℝ) : ℂ) * (((modulus (d / c) : ℝ)⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, div_eq_mul_inv, modulus_mul, modulus_inv, hd1]
    push_cast
    field_simp
    simp [hc]
  have hy : σ z * algebraMap F E c⁻¹ * algebraMap F E (d / c)⁻¹ = σ z * algebraMap F E d⁻¹ := by
    rw [mul_assoc, ← map_mul]
    congr 2
    field_simp
  rw [rW_ne χ σ μ a b d hc z, hint _ _ hδ, hy, intInd_sigma_mul σ hd1' z]
  by_cases hz : z ∈ 𝒪[E]
  · have hχ2 : (χ (a * Algebra.norm F z / c) : ℂ) *
        (χ (-(Algebra.norm F (σ z * algebraMap F E c⁻¹)) / (d / c)) : ℂ) = 1 := by
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, norm_y]
      have harg : a * Algebra.norm F z / c + -(Algebra.norm F z * c⁻¹ ^ 2) / (d / c) =
          b * d⁻¹ * Algebra.norm F z := by
        field_simp
        linear_combination (Algebra.norm F z) * hdet
      rw [harg, char_int hχ (mul_mem (mul_mem hb hdiO) (norm_mem hz))]
      simp
    calc _ = (nsg E (-c) * nsg E (d / c)) * ((((modulus c : ℝ)⁻¹ : ℝ) : ℂ) * (((modulus (d / c) : ℝ)⁻¹ : ℝ) : ℂ)) *
          ((χ (a * Algebra.norm F z / c) : ℂ) *
            (χ (-(Algebra.norm F (σ z * algebraMap F E c⁻¹)) / (d / c)) : ℂ)) * intInd z := by ring
      _ = intInd z := by rw [hnsg, hmod, hχ2]; ring
  · simp [intInd_of_not_mem hz]

end Three

theorem rwkf : RWKF := by
  intro F _ _ _ _ _ _ _ χ hcχ hχ1 E _ _ _ _ _ _ _ hfin hcont σ _ η hη hcond hres k hdet hk
  haveI : ValuativeExtension F E := GlobalTheory.CompanionTheory.WeilSB.valuativeExtension_of_continuous hcont
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hfin
  haveI : Fact (Module.finrank F E = 2) := ⟨hfin⟩
  haveI : Algebra.IsSeparable F E := inferInstance
  have h1 := ord_unif_of_card (F := F) (E := E) hfin hres
  have hχ : IsStd χ := ⟨hcχ, hχ1, hcond⟩
  have hχE := isStd_chE_of_ord_unif F E hfin hcont h1 χ hχ
  obtain ⟨η', hv', hu', hs', hn1⟩ := UnramQuad.exists_quadChar_unramified F E hfin hcont h1
  have hηe : η = η' := by
    ext a
    rw [hη, hv']
  subst hηe
  have hlam := GlobalTheory.CompanionTheory.LamUnr.lamE_eq_one F E χ η hχ hχE hu' hs'
  have hg := gauss_main F E hfin hcont h1 χ η hχ hχE ⟨hv', hu', hs', hn1⟩
  have hm : ∀ x y : F, x ≠ 0 → y ≠ 0 → nsg E (x * y) = nsg E x * nsg E y := by
    intro x y hx hy
    have h := hv' (Units.mk0 x hx * Units.mk0 y hy)
    rw [map_mul, Units.val_mul, hv', hv'] at h
    simpa using h.symm
  have hu : ∀ ε : F, modulus ε = 1 → nsg E ε = 1 := by
    intro ε hε
    have hε0 : ε ≠ 0 := by
      rintro rfl
      simp at hε
    have hmem : Units.mk0 ε hε0 ∈ unitFiltrationUnits F 0 :=
      mem_unitFiltrationUnits_zero_iff_ord.2 ((modulus_eq_one_iff hε0).1 hε)
    have h2 : η (Units.mk0 ε hε0) = 1 := hu' hmem
    have h3 := hv' (Units.mk0 ε hε0)
    rw [h2, Units.val_mk0] at h3
    simpa using h3.symm
  rw [indicator_eq_intInd]
  funext z
  have hdet' : k 0 0 * k 1 1 - k 0 1 * k 1 0 = 1 := by rwa [Matrix.det_fin_two] at hdet
  show Ad3.K.GL2LocalData.rW χ σ (muE E χ) (lamE E χ η) (k 0 0) (k 0 1) (k 1 0) (k 1 1) intInd z = intInd z
  rw [hlam]
  by_cases hc : k 1 0 = 0
  · rw [hc]
    rw [hc, mul_zero, sub_zero] at hdet'
    exact rW_fix_zero hχ σ _ hu (hk 0 0) (hk 0 1) (hk 1 1) hdet' z
  by_cases hδ : k 1 1 / k 1 0 ∈ 𝒪[F]
  · exact rW_fix_big hχ σ _ hu (fun δ y h => (hg δ y).1 h) (hk 0 0) (hk 0 1) (hk 1 0) hdet' hc hδ z
  · exact rW_fix_small hχ σ _ hm hu (fun δ y h => (hg δ y).2 h) (hk 0 0) (hk 0 1) (hk 1 1) hdet' hc hδ z

end GlobalTheory.CompanionTheory.RwKF
