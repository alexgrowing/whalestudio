import Development.AutomorphicArithmetic.Foundations.Convolution.OrbitNormCounting.NormCount
import Development.AutomorphicArithmetic.Foundations.Convolution.OrbitNormCounting.IntUniq
import Development.AutomorphicArithmetic.Foundations.Convolution.OrbitNormCounting.CptInt
import Development.AutomorphicArithmetic.Foundations.Convolution.OrbitNormCounting.OrbUnit
import Development.AutomorphicArithmetic.Foundations.Convolution.OrbitNormCounting.OrbZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralTwistedConjInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralProductGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaConstantMulOfCoprimeEllipticPolynomials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralProperties

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace UpperTheory.ConvolutionTheory.G3

private theorem unit_conj_mem {G : Type} [Group G] (θ : G →* G) (K : Subgroup G) (hK : ∀ k ∈ K, θ k ∈ K)
    (z k : G) (hk : k ∈ K) : k⁻¹ * z * θ k ∈ K ↔ z ∈ K := by
  constructor
  · intro h
    have h' := K.mul_mem (K.mul_mem hk h) (K.inv_mem (hK k hk))
    have e : k * (k⁻¹ * z * θ k) * (θ k)⁻¹ = z := by group
    rwa [e] at h'
  · intro h
    exact K.mul_mem (K.mul_mem (K.inv_mem hk) h) (hK k hk)

private theorem unit_index {G : Type} [Group G] (θ : G →* G) (K : Subgroup G) (hK : ∀ k ∈ K, θ k ∈ K) (δ x : G) :
    (rStab fun k : K => (K : Set G).indicator (1 : G → ℂ) ((x * k)⁻¹ * δ * θ (x * k))).index ≠ 0 := by
  have key : ∀ k : K, (K : Set G).indicator (1 : G → ℂ) ((x * k)⁻¹ * δ * θ (x * k)) =
      (K : Set G).indicator (1 : G → ℂ) (x⁻¹ * δ * θ x) := by
    intro k
    have e : (x * (k : G))⁻¹ * δ * θ (x * k) = (k : G)⁻¹ * (x⁻¹ * δ * θ x) * θ k := by
      rw [map_mul]; group
    simp only [Set.indicator_apply, SetLike.mem_coe, e, unit_conj_mem θ K hK _ _ k.2, Pi.one_apply]
  have top : (rStab fun k : K => (K : Set G).indicator (1 : G → ℂ) ((x * k)⁻¹ * δ * θ (x * k))) = ⊤ := by
    refine (Subgroup.eq_top_iff' _).2 fun k y => ?_
    exact (key _).trans (key _).symm
  rw [top, Subgroup.index_top]
  exact one_ne_zero

private theorem tw_symm {G : Type} [Group G] {θ : G →* G} {x y : G} (h : Tw θ x y) : Tw θ y x := by
  obtain ⟨g, rfl⟩ := h
  exact ⟨g⁻¹, by rw [map_inv]; group⟩

private theorem tw_trans {G : Type} [Group G] {θ : G →* G} {x y z : G} (h : Tw θ x y) (h' : Tw θ y z) :
    Tw θ x z := by
  obtain ⟨g, rfl⟩ := h
  obtain ⟨g', rfl⟩ := h'
  exact ⟨g * g', by rw [map_mul]; group⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem lpol_tw (hU : Unr E) (n : ℕ) (w : Pl E) {x y : GLw n w} (h : Tw (thL n w) x y) :
    lpol w y = lpol w x := by
  obtain ⟨g, rfl⟩ := h
  unfold lpol
  rw [ThBasic.nrmL_twist hU, Units.val_mul, Units.val_mul, Matrix.charpoly_mul_comm, ← mul_assoc,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

private theorem lpol_locEl (hU : Unr E) (n : ℕ) (w : Pl E) (δ : GL (Fin n) E) :
    lpol w (locEl n w δ) = atPl w (gpol δ) :=
  ThBasic.charpoly_nrmL hU n w δ

private theorem unit_uniq (hU : Unr E) (n : ℕ) (w : Pl E) (δ : GL (Fin n) E)
    (i : ∀ y ∈ GlobalTheory.LFun.KGL w n, lpol w y = atPl w (gpol δ) →
      ∃ k ∈ GlobalTheory.LFun.KGL w n, y = k⁻¹ * locEl n w δ * thL n w k)
    (y : GLw n w) (hy : y ∈ GlobalTheory.LFun.KGL w n) (h : Tw (thL n w) (locEl n w δ) y) :
    ∃ k ∈ GlobalTheory.LFun.KGL w n, y = k⁻¹ * locEl n w δ * thL n w k :=
  i y hy ((lpol_tw hU n w h).trans (lpol_locEl hU n w δ))

theorem _root_.UpperTheory.ConvolutionTheory.G3.unitAe : UnitAe := by
  intro E _ _ _ hU a b δ₁ δ₂ h₁ h₂
  filter_upwards [intUniq E hU a δ₁ h₁, intUniq E hU b δ₂ h₂, cptInt E hU a δ₁ h₁, cptInt E hU b δ₂ h₂]
    with w i₁ i₂ c₁ c₂ y₁ y₂ l₁ l₂
  have hK₁ := ThBasic.thL_mem_KGL hU a w
  have hK₂ := ThBasic.thL_mem_KGL hU b w
  have hK : ∀ k ∈ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b),
      (thL a w).prodMap (thL b w) k ∈ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) :=
    fun k hk => Subgroup.mem_prod.2 ⟨hK₁ _ (Subgroup.mem_prod.1 hk).1, hK₂ _ (Subgroup.mem_prod.1 hk).2⟩
  by_cases ht : Tw (thL a w) (locEl a w δ₁) y₁ ∧ Tw (thL b w) (locEl b w δ₂) y₂
  · rw [if_pos ht]
    obtain ⟨⟨g₁, rfl⟩, ⟨g₂, rfl⟩⟩ := ht
    have e : ((g₁⁻¹ * locEl a w δ₁ * thL a w g₁, g₂⁻¹ * locEl b w δ₂ * thL b w g₂) : GLw a w × GLw b w) =
        (g₁, g₂)⁻¹ * (locEl a w δ₁, locEl b w δ₂) * (thL a w).prodMap (thL b w) (g₁, g₂) := rfl
    rw [e, GlobalTheory.TwOrbConj.twOrb_twConj _ _ _ _ _ _ fun x => unit_index _ _ hK _ x]
    refine orbUnit _ _ _ _ hK (Subgroup.mem_prod.2 ⟨i₁.1, i₂.1⟩) ?_ ?_
    · rintro ⟨z₁, z₂⟩ hz ⟨⟨x₁, x₂⟩, hx⟩
      have hz' := Subgroup.mem_prod.1 hz
      have e₁ : z₁ = x₁⁻¹ * locEl a w δ₁ * thL a w x₁ := congrArg Prod.fst hx
      have e₂ : z₂ = x₂⁻¹ * locEl b w δ₂ * thL b w x₂ := congrArg Prod.snd hx
      obtain ⟨k₁, hk₁, f₁⟩ := unit_uniq hU a w δ₁ i₁.2 z₁ hz'.1 ⟨x₁, e₁⟩
      obtain ⟨k₂, hk₂, f₂⟩ := unit_uniq hU b w δ₂ i₂.2 z₂ hz'.2 ⟨x₂, e₂⟩
      exact ⟨(k₁, k₂), Subgroup.mem_prod.2 ⟨hk₁, hk₂⟩, Prod.ext f₁ f₂⟩
    · rw [OrbProd.twCent_prod, KapMul.cptPart_prod, c₁, c₂, OrbProd.prod_inf_prod]
  · rw [if_neg ht]
    refine orbZero _ _ _ _ _ fun z hz => ?_
    refine Set.indicator_of_notMem (fun hzK => ht ?_) _
    have hz' := Subgroup.mem_prod.1 hzK
    obtain ⟨⟨x₁, x₂⟩, hx⟩ := hz
    have e₁ : z.1 = x₁⁻¹ * y₁ * thL a w x₁ := congrArg Prod.fst hx
    have e₂ : z.2 = x₂⁻¹ * y₂ * thL b w x₂ := congrArg Prod.snd hx
    have t₁ : Tw (thL a w) y₁ z.1 := ⟨x₁, e₁⟩
    have t₂ : Tw (thL b w) y₂ z.2 := ⟨x₂, e₂⟩
    obtain ⟨k₁, hk₁, f₁⟩ := i₁.2 z.1 hz'.1 ((lpol_tw hU a w t₁).trans l₁)
    obtain ⟨k₂, hk₂, f₂⟩ := i₂.2 z.2 hz'.2 ((lpol_tw hU b w t₂).trans l₂)
    exact ⟨tw_trans ⟨k₁, f₁⟩ (tw_symm t₁), tw_trans ⟨k₂, f₂⟩ (tw_symm t₂)⟩

end UpperTheory.ConvolutionTheory.G3
