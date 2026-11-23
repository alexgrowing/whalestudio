import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.DeltaProdAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.OrbitNormCounting.NormCount
import Development.AutomorphicArithmetic.Foundations.Convolution.OrbitNormCounting.UnitAe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaConstantMulOfCoprimeEllipticPolynomials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralTwistedConjInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralProperties

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem UpperTheory.ConvolutionTheory.G2.sum_one {G : Type} [Group G] (θ : G →* G) (S : Set G) (T : G → ℂ) (x₀ : G)
    (hS : ∀ g, g⁻¹ * x₀ * θ g ∈ S)
    (hT : ∀ y ∈ S, T y = if ∃ g, y = g⁻¹ * x₀ * θ g then 1 else 0) :
    (∑ᶠ c : TwCl θ, if c.rep ∈ S then (1 : G → ℂ) c.rep * T c.rep else 0) = 1 := by
  have hequiv : Equivalence fun x y : G => ∃ g, y = g⁻¹ * x * θ g := by
    refine ⟨fun x => ⟨1, by simp⟩, ?_, ?_⟩
    · rintro x y ⟨g, rfl⟩
      exact ⟨g⁻¹, by simp [mul_assoc]⟩
    · rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
      exact ⟨g * h, by simp [mul_assoc]⟩
  have hrep : ∀ c : TwCl θ, (Quot.mk _ c.rep : TwCl θ) = c := fun c => Quot.out_eq c
  have hex : ∀ x y : G, (Quot.mk _ x : TwCl θ) = Quot.mk _ y → ∃ g, y = g⁻¹ * x * θ g :=
    fun x y h => hequiv.eqvGen_iff.1 (Quot.eqvGen_exact h)
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : TwCl θ, c₀ = Quot.mk _ x₀ := ⟨_, rfl⟩
  rw [finsum_eq_single _ c₀]
  · obtain ⟨g, hg⟩ := hex _ _ ((hrep c₀).trans hc₀).symm
    have hm : c₀.rep ∈ S := hg ▸ hS g
    rw [if_pos hm, hT _ hm, if_pos ⟨g, hg⟩]
    simp
  · intro c hc
    by_cases hm : c.rep ∈ S
    · rw [if_pos hm, hT _ hm, if_neg, mul_zero]
      rintro ⟨g, hg⟩
      apply hc
      rw [← hrep c, hc₀]
      exact (Quot.sound ⟨g, hg⟩).symm
    · rw [if_neg hm]

private theorem UpperTheory.ConvolutionTheory.G2.lpol_twist {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (n : ℕ)
    (w : Pl E) (g y : GLw n w) :
    UpperTheory.ConvolutionTheory.G3.lpol w (g⁻¹ * y * thL n w g) = UpperTheory.ConvolutionTheory.G3.lpol w y := by
  unfold UpperTheory.ConvolutionTheory.G3.lpol
  rw [GlobalTheory.BCT.ThBasic.nrmL_twist hU, Units.val_mul, Matrix.charpoly_mul_comm, ← Units.val_mul, mul_inv_cancel_left]

theorem UpperTheory.ConvolutionTheory.G2.stAA :
    UpperTheory.ConvolutionTheory.G2.StAA := by
  intro E _ _ _ hU a b P₁ P₂ h₁ h₂
  obtain ⟨δ₁, e₁⟩ := GlobalTheory.BCT.KapMul.exists_norm E h₁
  obtain ⟨δ₂, e₂⟩ := GlobalTheory.BCT.KapMul.exists_norm E h₂
  have g₁ : UpperTheory.ConvolutionTheory.G3.gpol δ₁ = P₁ := e₁
  have g₂ : UpperTheory.ConvolutionTheory.G3.gpol δ₂ = P₂ := e₂
  subst g₁ g₂
  filter_upwards [UpperTheory.ConvolutionTheory.G3.unitAe E hU a b δ₁ δ₂ h₁.2.2.1 h₂.2.2.1] with w hw
  have l₁ : UpperTheory.ConvolutionTheory.G3.lpol w (locEl a w δ₁) = atPl w (UpperTheory.ConvolutionTheory.G3.gpol δ₁) :=
    GlobalTheory.BCT.ThBasic.charpoly_nrmL hU a w δ₁
  have l₂ : UpperTheory.ConvolutionTheory.G3.lpol w (locEl b w δ₂) = atPl w (UpperTheory.ConvolutionTheory.G3.gpol δ₂) :=
    GlobalTheory.BCT.ThBasic.charpoly_nrmL hU b w δ₂
  unfold stTw2 clSum
  refine UpperTheory.ConvolutionTheory.G2.sum_one ((thL a w).prodMap (thL b w)) _
    (fun y => twOrb ((thL a w).prodMap (thL b w)) ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) y
      (UpperTheory.ConvolutionTheory.G2.unit2 a b w)) (locEl a w δ₁, locEl b w δ₂) ?_ ?_
  · rintro ⟨k₁, k₂⟩
    exact ⟨(UpperTheory.ConvolutionTheory.G2.lpol_twist hU a w k₁ _).trans l₁, (UpperTheory.ConvolutionTheory.G2.lpol_twist hU b w k₂ _).trans l₂⟩
  · rintro ⟨y₁, y₂⟩ ⟨hy₁, hy₂⟩
    refine (hw y₁ y₂ hy₁ hy₂).trans (if_congr ?_ rfl rfl)
    constructor
    · rintro ⟨⟨k₁, r₁⟩, ⟨k₂, r₂⟩⟩
      exact ⟨(k₁, k₂), Prod.ext r₁ r₂⟩
    · rintro ⟨k, r⟩
      exact ⟨⟨k.1, congrArg Prod.fst r⟩, ⟨k.2, congrArg Prod.snd r⟩⟩
