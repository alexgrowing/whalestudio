import Mathlib
import GroundTheory.AutomorphicForms.MacdonaldWhittaker

noncomputable section

namespace GroundTheory.Automorphic

namespace Spherical

open MeasureTheory Matrix GLnLocal Iwasawa HeckeAlgebra AddMonoidAlgebra Finset
open scoped ValuativeRel Pointwise

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

local notation "π" => (GLnLocal.uniformizer F : F)

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

theorem integrable_hecke_mul {f : GL (Fin n) F → ℂ}
    (hf : ∀ g, ∀ k ∈ integralGL F n, f (g * k) = f g) (h : SphericalHecke μ (F := F) (n := n))
    (g : GL (Fin n) F) :
    Integrable (fun x => (h : HeckeAlgebra μ) x * f (g * x)) μ := by
  refine Continuous.integrable_of_hasCompactSupport ?_ (h : HeckeAlgebra μ).mem.2.mul_right
  exact (h : HeckeAlgebra μ).mem.1.continuous.mul
    ((continuous_of_mul_right_invariant hf).comp (continuous_mul_left g))

theorem integral_one_mul {f : GL (Fin n) F → ℂ}
    (hf : ∀ g, ∀ k ∈ integralGL F n, f (g * k) = f g) (g : GL (Fin n) F) :
    ∫ x, ((1 : SphericalHecke μ (F := F) (n := n)) : HeckeAlgebra μ) x * f (g * x) ∂μ = f g := by
  have hK : (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2
      (measureReal_compactOpen_pos μ (isCompact_integralGL F n) (isOpen_integralGL F n)).ne'
  have : (fun x => ((1 : SphericalHecke μ (F := F) (n := n)) : HeckeAlgebra μ) x * f (g * x)) =
      (integralGL F n : Set (GL (Fin n) F)).indicator
        (fun _ => (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ)⁻¹ * f g) := by
    funext x
    rw [HeckeAlgebraLevel.val_one, idem_apply]
    by_cases hx : x ∈ integralGL F n
    · rw [Set.indicator_of_mem (show x ∈ (integralGL F n : Set (GL (Fin n) F)) from hx),
        Set.indicator_of_mem (show x ∈ (integralGL F n : Set (GL (Fin n) F)) from hx), hf g x hx]
    · rw [Set.indicator_of_notMem (show x ∉ (integralGL F n : Set (GL (Fin n) F)) from hx),
        Set.indicator_of_notMem (show x ∉ (integralGL F n : Set (GL (Fin n) F)) from hx), zero_mul]
  rw [this, integral_indicator (isOpen_integralGL F n).measurableSet, setIntegral_const,
    Complex.real_smul, ← mul_assoc, mul_inv_cancel₀ hK, one_mul]

theorem integral_mul_mul_eigen (z : Fin n → ℂˣ) {f : GL (Fin n) F → ℂ}
    (hf : ∀ g, ∀ k ∈ integralGL F n, f (g * k) = f g) {h₁ h₂ : SphericalHecke μ (F := F) (n := n)}
    (hh₁ : ∀ g, ∫ x, (h₁ : HeckeAlgebra μ) x * f (g * x) ∂μ = evalAt z (satakeTransform μ h₁) * f g)
    (hh₂ : ∀ g, ∫ x, (h₂ : HeckeAlgebra μ) x * f (g * x) ∂μ = evalAt z (satakeTransform μ h₂) * f g)
    (g : GL (Fin n) F) :
    ∫ x, ((h₁ * h₂ : SphericalHecke μ (F := F) (n := n)) : HeckeAlgebra μ) x * f (g * x) ∂μ =
      evalAt z (satakeTransform μ (h₁ * h₂)) * f g := by
  rw [map_mul, map_mul]
  have hconv : ∀ x, (((h₁ * h₂ : SphericalHecke μ (F := F) (n := n)) : HeckeAlgebra μ) x) =
      ∫ y, (h₁ : HeckeAlgebra μ) y * (h₂ : HeckeAlgebra μ) (y⁻¹ * x) ∂μ := by
    intro x
    rw [HeckeAlgebraLevel.val_mul, HeckeAlgebra.coe_mul]
    rfl
  simp only [hconv, ← integral_mul_const]
  set B := tsupport ((h₁ : HeckeAlgebra μ) : GL (Fin n) F → ℂ)
  set C := tsupport ((h₂ : HeckeAlgebra μ) : GL (Fin n) F → ℂ)
  have hB : IsCompact B := (h₁ : HeckeAlgebra μ).mem.2
  have hC : IsCompact C := (h₂ : HeckeAlgebra μ).mem.2
  have hswap := integral_integral_swap_of_coset μ (integralOpen F n) (isCompact_integralGL F n)
    (hB.mul hC) hB (F := fun x y => (h₁ : HeckeAlgebra μ) y * (h₂ : HeckeAlgebra μ) (y⁻¹ * x) *
      f (g * x))
    (by
      intro x y hxy
      have hy : y ∈ B := subset_tsupport _ (left_ne_zero_of_mul (left_ne_zero_of_mul hxy))
      have hx : y⁻¹ * x ∈ C := subset_tsupport _ (right_ne_zero_of_mul (left_ne_zero_of_mul hxy))
      exact ⟨Set.mem_mul.2 ⟨y, hy, y⁻¹ * x, hx, by group⟩, hy⟩)
    (by
      intro x y k hk
      rw [← mul_assoc, (HeckeAlgebraLevel.val_mem _ _ h₂ k hk _).2, ← mul_assoc, hf _ k hk])
    (by
      intro x y k hk
      rw [(HeckeAlgebraLevel.val_mem _ _ h₁ k hk y).2, _root_.mul_inv_rev,
        show k⁻¹ * y⁻¹ * x = k⁻¹ * (y⁻¹ * x) from mul_assoc _ _ _,
        HeckeAlgebraLevel.apply_mul_left _ _ h₂ ((integralGL F n).inv_mem hk)])
  rw [hswap]
  have hinner : ∀ y, ∫ x, (h₁ : HeckeAlgebra μ) y * (h₂ : HeckeAlgebra μ) (y⁻¹ * x) * f (g * x) ∂μ =
      (h₁ : HeckeAlgebra μ) y * f (g * y) * evalAt z (satakeTransform μ h₂) := by
    intro y
    have e := integral_mul_left_eq_self (μ := μ)
      (fun x => (h₁ : HeckeAlgebra μ) y * (h₂ : HeckeAlgebra μ) (y⁻¹ * x) * f (g * x)) y
    simp only [inv_mul_cancel_left] at e
    rw [← e]
    have hpt : ∀ x, (h₁ : HeckeAlgebra μ) y * (h₂ : HeckeAlgebra μ) x * f (g * (y * x)) =
        (h₁ : HeckeAlgebra μ) y * ((h₂ : HeckeAlgebra μ) x * f ((g * y) * x)) := by
      intro x
      rw [mul_assoc g y x]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul, hh₂ (g * y)]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hinner), integral_mul_const, hh₁ g]
  ring

variable (μ) in

def eigenSubalgebra (z : Fin n → ℂˣ) (f : GL (Fin n) F → ℂ)
    (hf : ∀ g, ∀ k ∈ integralGL F n, f (g * k) = f g) :
    Subalgebra ℂ (SphericalHecke μ (F := F) (n := n)) where
  carrier := {h | ∀ g, ∫ x, (h : HeckeAlgebra μ) x * f (g * x) ∂μ =
    evalAt z (satakeTransform μ h) * f g}
  mul_mem' {h₁ h₂} hh₁ hh₂ g := integral_mul_mul_eigen z hf hh₁ hh₂ g
  one_mem' g := by
    simp only [Set.mem_setOf_eq, map_one, one_mul]
    exact integral_one_mul hf g
  add_mem' {h₁ h₂} hh₁ hh₂ g := by
    simp only [HeckeAlgebraLevel.val_add, HeckeAlgebra.coe_add, Pi.add_apply, add_mul]
    rw [integral_add (integrable_hecke_mul hf h₁ g) (integrable_hecke_mul hf h₂ g), hh₁, hh₂,
      map_add, map_add, add_mul]
  zero_mem' g := by
    simp [HeckeAlgebraLevel.val_zero]
  algebraMap_mem' c g := by
    rw [Algebra.algebraMap_eq_smul_one, HeckeAlgebraLevel.val_smul, HeckeAlgebra.coe_smul, map_smul,
      map_smul, smul_eq_mul, map_one, map_one, mul_one]
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [integral_const_mul, integral_one_mul hf g]

omit [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] in
theorem polyEmb_esymm (k : ℕ) : polyEmb n (MvPolynomial.esymm (Fin n) ℂ k) = esymmL n k := by
  rw [MvPolynomial.esymm, map_sum, esymmL]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_prod]
  simp only [polyEmb_X, monomial]
  rw [AddMonoidAlgebra.prod_single, Finset.prod_const_one, sum_single_one]

omit [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] in
theorem esymmL_eq_zero {k : ℕ} (hk : n < k) : esymmL n k = 0 := by
  rw [esymmL, Finset.powersetCard_eq_empty.2 (by simpa using hk), Finset.sum_empty]

omit [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] in
theorem sum_rho_coeff : ∑ i : Fin n, ((n : ℤ) - 1 - 2 * (i : ℕ)) = 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (n : ℤ) - 1 - 2 * (i : ℤ)) n, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, ← Finset.mul_sum]
  have h := Finset.sum_range_id_mul_two n
  have h' : (∑ i ∈ Finset.range n, (i : ℤ)) * 2 = (n : ℤ) * ((n : ℤ) - 1) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp
    · have : (((∑ i ∈ Finset.range n, i) * 2 : ℕ) : ℤ) = ((n * (n - 1) : ℕ) : ℤ) := by rw [h]
      push_cast [Nat.cast_sub hn] at this
      linarith
  simp only [nsmul_eq_mul]
  linarith

omit [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] in

theorem halfModulus_const (c : ℤ) : halfModulus F (fun _ : Fin n => c) = 1 := by
  rw [halfModulus_eq, rhoPair]
  simp only [mul_comm _ c, ← Finset.mul_sum, sum_rho_coeff, mul_zero, neg_zero, zpow_zero]

theorem satakeTransform_minusculeHecke {k : ℕ} (hk : k ≤ n) :
    satakeTransform μ (minusculeHecke μ k) =
      ((μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) * sqrtQ F ^ (k * (n - k))) • esymmL n k := by
  refine eq_of_forall_evalAt fun w => ?_
  rw [evalAt_satakeTransform_minusculeHecke w hk, map_smul, smul_eq_mul]

theorem satakeTransform_centralHecke :
    satakeTransform μ (centralHecke μ) =
      (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) • monomial (fun _ : Fin n => (-1 : ℤ)) := by
  rw [satakeTransform_apply, satake_centralHecke, map_smul, monomial, normalize_single,
    halfModulus_const, one_mul]

theorem eigenSubalgebra_eq_top (z : Fin n → ℂˣ) {f : GL (Fin n) F → ℂ}
    (hf : ∀ g, ∀ k ∈ integralGL F n, f (g * k) = f g)
    (hT : ∀ r ≤ n, minusculeHecke μ r ∈ eigenSubalgebra μ z f hf)
    (hc : centralHecke μ ∈ eigenSubalgebra μ z f hf) : eigenSubalgebra μ z f hf = ⊤ := by
  set E := eigenSubalgebra μ z f hf
  set A := E.map (satakeTransform μ)
  have hK : (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2
      (measureReal_compactOpen_pos μ (isCompact_integralGL F n) (isOpen_integralGL F n)).ne'
  have h1 : ∀ k, polyEmb n (MvPolynomial.esymm (Fin n) ℂ k) ∈ A := by
    intro k
    rw [polyEmb_esymm]
    by_cases hk : k ≤ n
    · have hc' : (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) * sqrtQ F ^ (k * (n - k)) ≠ 0 :=
        mul_ne_zero hK (pow_ne_zero _ sqrtQ_ne_zero)
      refine Subalgebra.mem_map.2 ⟨((μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) *
        sqrtQ F ^ (k * (n - k)))⁻¹ • minusculeHecke μ k, E.smul_mem (hT k hk) _, ?_⟩
      rw [map_smul, satakeTransform_minusculeHecke hk, smul_smul, inv_mul_cancel₀ hc', one_smul]
    · rw [esymmL_eq_zero (by omega)]
      exact A.zero_mem
  have h2 : monomial (fun _ : Fin n => (-1 : ℤ)) ∈ A := by
    refine Subalgebra.mem_map.2 ⟨((μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ))⁻¹ •
      centralHecke μ, E.smul_mem hc _, ?_⟩
    rw [map_smul, satakeTransform_centralHecke, smul_smul, inv_mul_cancel₀ hK, one_smul]
  have hsym := symmetricLaurent_le h1 h2
  rw [Algebra.eq_top_iff]
  intro h
  obtain ⟨e, he, hSe⟩ := Subalgebra.mem_map.1 (hsym (satakeTransform_mem_symmetric h))
  rwa [← satakeTransform_injective hSe]

theorem antitone_add_const_iff (l : Fin n → ℤ) (c : ℤ) :
    Antitone (l + fun _ => c) ↔ Antitone l := by
  constructor
  · intro h i j hij
    have := h hij
    simp only [Pi.add_apply] at this
    linarith
  · intro h i j hij
    simp only [Pi.add_apply]
    linarith [h hij]

theorem schur_add_const (l : Fin n → ℤ) (c : ℤ) :
    schur (l + fun _ => c) = monomial (fun _ : Fin n => c) * schur l := by
  rw [schur, schur, show l + (fun _ => c) + staircase n = (fun _ => c) + (l + staircase n) by abel,
    monomial_add, altQuot_mul_of_symm (permAct_monomial_const c)]

theorem sphericalWhittaker_mul_const {ψ₀ : AddChar F ℂ} (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1)
    (z : Fin n → ℂˣ) (g : GL (Fin n) F) (c : ℤ) :
    sphericalWhittaker ψ₀ z (g * torusPow F n (fun _ => c)) =
      monomialChar (fun _ : Fin n => c) z * sphericalWhittaker ψ₀ z g := by
  have hg := eq_iwasawa g
  have hu := iwasawaUnip_mem g
  have hk := iwasawaInt_mem g
  set u := iwasawaUnip g
  set e := iwasawaExponent F n g
  set k := iwasawaInt g
  have : g * torusPow F n (fun _ => c) = u * torusPow F n (e + fun _ => c) * k := by
    rw [hg, torusPow_add, mul_assoc, ← torusPow_const_comm c k]
    group
  rw [this, sphericalWhittaker_apply hψ₀ z hu hk, hg, sphericalWhittaker_apply hψ₀ z hu hk]
  by_cases he : Antitone e
  · rw [if_pos ((antitone_add_const_iff e c).2 he), if_pos he, halfModulus_add, halfModulus_const,
      schur_add_const, map_mul, monomial, evalAt_single, one_mul]
    ring
  · rw [if_neg (fun h => he ((antitone_add_const_iff e c).1 h)), if_neg he, mul_zero]

theorem integral_centralHecke_mul_sphericalWhittaker {ψ₀ : AddChar F ℂ}
    (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1) (z : Fin n → ℂˣ) (g : GL (Fin n) F) :
    ∫ x, (centralHecke μ : HeckeAlgebra μ) x * sphericalWhittaker ψ₀ z (g * x) ∂μ =
      evalAt z (satakeTransform μ (centralHecke μ)) * sphericalWhittaker ψ₀ z g := by
  set g₀ := torusPow F n (fun _ : Fin n => (-1 : ℤ))
  have e := integral_mul_left_eq_self (μ := μ)
    (fun x => (centralHecke μ : HeckeAlgebra μ) x * sphericalWhittaker ψ₀ z (g * x)) g₀
  rw [← e]
  have hpt : (fun y => (centralHecke μ : HeckeAlgebra μ) (g₀ * y) *
      sphericalWhittaker ψ₀ z (g * (g₀ * y))) = (integralGL F n : Set (GL (Fin n) F)).indicator
        (fun _ => sphericalWhittaker ψ₀ z (g * g₀)) := by
    funext y
    rw [centralHecke_apply]
    by_cases hy : y ∈ integralGL F n
    · have hm : g₀ * y ∈ centralSet F n := by
        rw [mem_centralSet, inv_mul_cancel_left]
        exact hy
      rw [Set.indicator_of_mem hm, Set.indicator_of_mem (show y ∈ (integralGL F n : Set (GL (Fin n) F))
        from hy), one_mul, ← mul_assoc, sphericalWhittaker_mul_right hψ₀ z _ hy]
    · have hm : g₀ * y ∉ centralSet F n := by
        rw [mem_centralSet, inv_mul_cancel_left]
        exact hy
      rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (show y ∉ (integralGL F n :
        Set (GL (Fin n) F)) from hy), zero_mul]
  rw [hpt, integral_indicator (isOpen_integralGL F n).measurableSet, setIntegral_const,
    Complex.real_smul, sphericalWhittaker_mul_const hψ₀, satakeTransform_centralHecke, map_smul,
    monomial, evalAt_single, one_mul, smul_eq_mul]
  ring

theorem integral_mul_sphericalWhittaker {ψ₀ : AddChar F ℂ} (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1)
    (hψ₁ : ∃ x : F, π * x ∈ 𝒪[F] ∧ ψ₀ x ≠ 1) (z : Fin n → ℂˣ)
    (h : SphericalHecke μ (F := F) (n := n)) (g : GL (Fin n) F) :
    ∫ x, (h : HeckeAlgebra μ) x * sphericalWhittaker ψ₀ z (g * x) ∂μ =
      evalAt z (satakeTransform μ h) * sphericalWhittaker ψ₀ z g := by
  have htop := eigenSubalgebra_eq_top (μ := μ) z
    (fun g k hk => sphericalWhittaker_mul_right hψ₀ z g hk)
    (fun r hr g => integral_minusculeHecke_mul_sphericalWhittaker hψ₀ hψ₁ z hr g)
    (fun g => integral_centralHecke_mul_sphericalWhittaker hψ₀ z g)
  have hmem : h ∈ eigenSubalgebra μ z (sphericalWhittaker ψ₀ z)
      (fun g k hk => sphericalWhittaker_mul_right hψ₀ z g hk) := by
    rw [htop]
    exact Algebra.mem_top
  exact hmem g

theorem eq_smul_sphericalWhittaker {ψ₀ : AddChar F ℂ} (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1)
    (hψ₁ : ∃ x : F, π * x ∈ 𝒪[F] ∧ ψ₀ x ≠ 1) (z : Fin n → ℂˣ) {W : GL (Fin n) F → ℂ}
    (hWN : ∀ u ∈ unipotent F n, ∀ g, W (u * g) = Whittaker.psiN ψ₀ u * W g)
    (hWK : ∀ g, ∀ k ∈ integralGL F n, W (g * k) = W g)
    (heig : ∀ (h : SphericalHecke μ (F := F) (n := n)) (g : GL (Fin n) F),
      ∫ x, (h : HeckeAlgebra μ) x * W (g * x) ∂μ = evalAt z (satakeTransform μ h) * W g)
    (g : GL (Fin n) F) : W g = W 1 * sphericalWhittaker ψ₀ z g := by
  have hg := eq_iwasawa g
  have hu := iwasawaUnip_mem g
  have hk := iwasawaInt_mem g
  rw [hg, sphericalWhittaker_apply hψ₀ z hu hk, hWK _ _ hk, mul_assoc, hWN _ hu,
    casselman_shalika ψ₀ hψ₀ hψ₁ z hWN hWK heig]
  split_ifs <;> ring

end Spherical

end GroundTheory.Automorphic
