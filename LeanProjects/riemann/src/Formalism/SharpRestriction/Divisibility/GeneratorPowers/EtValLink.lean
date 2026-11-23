import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ETExSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ETPointStatement

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Out IsLocalRing

structure EtFactor (E : Type) [Field E] [NumberField E] (cj : E → E) where
  V : Type
  [cr : CommRing V]
  [dom : IsDomain V]
  [dvr : IsDiscreteValuationRing V]
  ϖ : V
  hϖ : Irreducible ϖ
  D : DegData V (maximalIdeal V)
  [modX : Module (𝓞 E) D.toPre.X]
  Q : D.toPre.X → ℤ
  hQ : QForm.IsQ D.toPre ϖ Q
  β : SymB cj D.toPre.X
  hβQ : ∀ a b, (β : D.toPre.X →ₗ[ℤ] D.toPre.X →ₗ[ℤ] ℝ) a b = QForm.bOf D.toPre Q a b
  hβ2 : ∀ a, (β : D.toPre.X →ₗ[ℤ] D.toPre.X →ₗ[ℤ] ℝ) a a = 2 * (Q a : ℝ)
  hβpos : ∀ a, 0 ≤ (β : D.toPre.X →ₗ[ℤ] D.toPre.X →ₗ[ℤ] ℝ) a a
  F : Type
  [fF : Field F]
  [aF : Algebra (FractionRing V) F]
  v : AddValuation F (WithTop ℚ)
  hv : ValOver ϖ F v
  R' : ℕ
  R₀ : ℕ
  hR' : 2 ≤ R'
  hR₀ : 2 ≤ R₀
  hdvd : R₀ ∣ R'
  r : ℕ
  y : Fin r → D.toPre.X
  hgen : ∀ a : D.toPre.X, ∃ u ∈ Submodule.span (𝓞 E) (Set.range y), ∃ t : D.toPre.X, a = u + R₀ • t
  s : Fin r → Fam D.toPre F (R' ^ 2)
  w : Fin r → F
  hsupp : ∀ b (α : D.toPre.X), (∀ z : D.toPre.X, α ≠ y b + R' • z) → ∀ j, ((s b).s α).f j = 0
  hnu : ∀ b, NuGe D Q F v (R' ^ 2) (s b) 0
  hval : ∀ b, ValAt0 D F v (R' ^ 2) (s b) (w b)

attribute [instance] EtFactor.cr EtFactor.dom EtFactor.dvr EtFactor.modX EtFactor.fF EtFactor.aF

def wtE : WithTop ℚ → EReal
  | ⊤ => ⊤
  | (q : ℚ) => ((q : ℝ) : EReal)

namespace EtFactor

variable {E : Type} [Field E] [NumberField E] {cj : E → E}

def sumV (f : EtFactor E cj) : EReal := wtE (∑ b, f.v (f.w b))

def phiF (f : EtFactor E cj) : ℝ := phiC cj f.β / (f.R' ^ 2 : ℝ)

end EtFactor

theorem coe_sum_ereal {ι : Type} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, (f i : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]

theorem EtFactor.phiF_le {E : Type} [Field E] [NumberField E] {cj : E → E}
    (hcj : ∀ c : 𝓞 E, ∃ c' : 𝓞 E, (c' : E) = cj c) (w₀ : 𝓞 E) (hw : (w₀ : E) + cj w₀ = 1)
    (hP : ETPointStatement) (f : EtFactor E cj) : ((f.phiF : ℝ) : EReal) ≤ f.sumV := by
  have key : ∀ q : ℚ, (q : ℝ) ≤ f.phiF → ((q : ℚ) : WithTop ℚ) ≤ ∑ b, f.v (f.w b) := fun q hq =>
    hP E cj hcj w₀ hw f.V f.ϖ f.hϖ f.D f.Q f.hQ f.β f.hβQ f.hβ2 f.hβpos f.F f.v f.hv f.R' f.R₀ f.hR' f.hR₀ f.hdvd
      f.r f.y f.hgen f.s f.w f.hsupp f.hnu f.hval q hq
  unfold EtFactor.sumV
  generalize ∑ b, f.v (f.w b) = t at key
  induction t using WithTop.recTopCoe with
  | top => exact le_top
  | coe q0 =>
    show ((f.phiF : ℝ) : EReal) ≤ ((q0 : ℝ) : EReal)
    refine EReal.coe_le_coe_iff.2 (le_of_not_gt fun hlt => ?_)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    have h := WithTop.coe_le_coe.1 (key q hq2.le)
    have h' : (q : ℝ) ≤ q0 := by exact_mod_cast h
    linarith

section Link

variable {D : Formalism.BasicNotions.D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

def EtFormAtSt (E : Type) [Field E] [NumberField E] (cj : E → E) (X : WeightAlgebra.PJ D B P j) (i : ℕ)
    (η : B.Cusp j (WeightAlgebra.wscalar D j (WeightAlgebra.g0 D * i) (by unfold WeightAlgebra.g0; exact ⟨5 ^ 4 * D.R.r * i, by ring⟩))) : Prop :=
  ∀ la (y : X.Pt la), ∃ (N : ℕ) (fac : Fin N → EtFactor E cj) (κ : ℝ), 0 ≤ κ ∧
    (κ : EReal) * ∑ k, (fac k).sumV ≤ X.vAt la y (X.inc _ η) ∧
    2 * i * X.phiC la y ≤ κ * ∑ k, (fac k).phiF

theorem etVal_of {E : Type} [Field E] [NumberField E] {cj : E → E}
    (hcj : ∀ c : 𝓞 E, ∃ c' : 𝓞 E, (c' : E) = cj c) (w₀ : 𝓞 E) (hw : (w₀ : E) + cj w₀ = 1)
    (hP : ETPointStatement) (X : WeightAlgebra.PJ D B P j) (i : ℕ)
    (η : B.Cusp j (WeightAlgebra.wscalar D j (WeightAlgebra.g0 D * i) (by unfold WeightAlgebra.g0; exact ⟨5 ^ 4 * D.R.r * i, by ring⟩)))
    (hF : EtFormAtSt E cj X i η) : EtVal X i η := by
  intro la y
  obtain ⟨N, fac, κ, hκ, hv, hφ⟩ := hF la y
  have h2 : ((∑ k, (fac k).phiF : ℝ) : EReal) ≤ ∑ k, (fac k).sumV := by
    rw [coe_sum_ereal]
    exact Finset.sum_le_sum fun k _ => (fac k).phiF_le hcj w₀ hw hP
  have h3 : ((κ * ∑ k, (fac k).phiF : ℝ) : EReal) ≤ (κ : EReal) * ∑ k, (fac k).sumV := by
    rw [EReal.coe_mul]
    exact mul_le_mul_of_nonneg_left h2 (EReal.coe_nonneg.2 hκ)
  calc ((2 * i * X.phiC la y : ℝ) : EReal) ≤ ((κ * ∑ k, (fac k).phiF : ℝ) : EReal) := EReal.coe_le_coe_iff.2 hφ
    _ ≤ _ := h3
    _ ≤ _ := hv

end Link

end Formalism.MainNotions.ModuliIntegralCharts.H1
