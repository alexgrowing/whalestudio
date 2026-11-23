import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionZeroCompactQuotientSummable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionZeroCompactQuotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AeZeroOfSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section
open scoped ComplexConjugate

namespace GlobalTheory.RealDecay

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

example (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (f g : WO S T → ℂ) :
    thPair μ 𝓕 f g = GlobalTheory.Ker.ipO μ 𝓕 f g := rfl

theorem symplOH_swap (S T : HSp D) (u v : WO S T) : symplOH S T v u = -symplOH S T u v := by
  obtain ⟨l1, l2, l3, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  have h := l3 (u + v)
  rw [l1, l2, l2, l3, l3, zero_add, add_zero] at h
  linear_combination h

theorem symplO_zero_left (S T : HSp D) (w : WO S T) : symplO S T 0 w = 0 := by
  rw [GlobalTheory.ThetaSquare.symplO_eq, GlobalTheory.ThetaSquare.symplOH_zero_left, add_zero]

theorem heisO_comm (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (u w : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T u (heisO ψ S T w f) = ψ (symplO S T u w) • heisO ψ S T w (heisO ψ S T u f) := by
  have hc := (GlobalTheory.ThetaSquare.heisUnitary (V := S) (W := T) hψ).1
  obtain ⟨-, -, -, l4, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  rw [hc, hc, smul_smul, ← AddChar.map_add_eq_mul, add_comm w u, symplOH_swap S T u w, ← l4]
  congr 2
  ring

theorem dRho_heisO (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ) (S T : HSp D) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f₀ : WO S T → ℂ} (h₀ : IsThetaFunO ψ S T f₀) (w : WO S T)
    (hd : DifferentiableAt ℝ (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) 0) :
    Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (heisO ψ S T w f₀) =
      deriv (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) 0 • heisO ψ S T w f₀ +
        heisO ψ S T w (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f₀) := by
  have DS := GlobalTheory.ThetaSquare.derSkew (V := S) (W := T) hψ hθ τ z
  have hw : IsThetaFunO ψ S T (heisO ψ S T w f₀) := (GlobalTheory.ThetaSquare.heisUnitary (V := S) (W := T) hψ).2.2.1 w f₀ h₀
  funext x
  have h1 : HasDerivAt (fun t : ℝ => heisO ψ S T w (heisO ψ S T (lineAt θ τ z t) f₀) x)
      (heisO ψ S T w (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f₀) x) 0 :=
    (DS.1 f₀ h₀ (x + w)).const_mul (ψ (symplOH S T x w))
  have h2 := hd.hasDerivAt.mul h1
  have e : ((fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) *
      fun t : ℝ => heisO ψ S T w (heisO ψ S T (lineAt θ τ z t) f₀) x) =
      fun t : ℝ => heisO ψ S T (lineAt θ τ z t) (heisO ψ S T w f₀) x := by
    funext t
    rw [Pi.mul_apply, heisO_comm hψ S T (lineAt θ τ z t) w]
    rfl
  rw [e] at h2
  rw [(DS.1 _ hw x).unique h2]
  simp only [map_zero, symplO_zero_left, AddChar.map_zero_eq_one, one_mul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [GlobalTheory.OrientedHeis.heisO_zero]

theorem step_bound (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ) (S T : HSp D) {μ : Measure (WO S T)}
    {𝓕 : Set (WO S T)} (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f f₀ : WO S T → ℂ} (h : IsThetaFunO ψ S T f)
    (h₀ : IsThetaFunO ψ S T f₀) (w : WO S T) :
    ‖deriv (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) 0‖ * ‖thPair μ 𝓕 f (heisO ψ S T w f₀)‖ ≤
      ‖thPair μ 𝓕 (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) (heisO ψ S T w f₀)‖ +
        ‖thPair μ 𝓕 f (heisO ψ S T w (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f₀))‖ := by
  set ℓ := deriv (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) 0 with hℓ
  by_cases hl : ℓ = 0
  · rw [hl, norm_zero, zero_mul]
    positivity
  have hd : DifferentiableAt ℝ (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) 0 := by
    by_contra hn
    exact hl (deriv_zero_of_not_differentiableAt hn)
  have DS := GlobalTheory.ThetaSquare.derSkew (V := S) (W := T) hψ hθ τ z
  have HU := GlobalTheory.ThetaSquare.heisUnitary (V := S) (W := T) hψ
  have hw : IsThetaFunO ψ S T (heisO ψ S T w f₀) := HU.2.2.1 w f₀ h₀
  have hw' : IsThetaFunO ψ S T (heisO ψ S T w (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f₀)) :=
    HU.2.2.1 w _ (DS.2.1 f₀ h₀)
  have key := DS.2.2 μ 𝓕 hμ h𝓕 f _ h hw
  rw [dRho_heisO hψ hθ S T τ z h₀ w hd] at key
  have i1 := GlobalTheory.Size.integrableOn_mul_conj hψ hμ h𝓕 h hw
  have i2 := GlobalTheory.Size.integrableOn_mul_conj hψ hμ h𝓕 h hw'
  have e : GlobalTheory.Ker.ipO μ 𝓕 f (ℓ • heisO ψ S T w f₀ + heisO ψ S T w (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f₀)) =
      conj ℓ * thPair μ 𝓕 f (heisO ψ S T w f₀) +
        thPair μ 𝓕 f (heisO ψ S T w (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f₀)) := by
    simp only [GlobalTheory.Ker.ipO, thPair, Complex.star_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, mul_add]
    rw [integral_add _ i2, ← integral_const_mul]
    · congr 1
      refine integral_congr_ae (.of_forall fun x => ?_)
      dsimp only
      ring
    · exact (i1.const_mul (conj ℓ)).congr (.of_forall fun x => by dsimp only; ring)
  change thPair μ 𝓕 _ _ = _ at key
  rw [e] at key
  have e2 : conj ℓ * thPair μ 𝓕 f (heisO ψ S T w f₀) =
      -thPair μ 𝓕 (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) (heisO ψ S T w f₀) -
        thPair μ 𝓕 f (heisO ψ S T w (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f₀)) := by
    rw [key]; ring
  calc ‖ℓ‖ * ‖thPair μ 𝓕 f (heisO ψ S T w f₀)‖ = ‖conj ℓ * thPair μ 𝓕 f (heisO ψ S T w f₀)‖ := by
        rw [norm_mul, Complex.norm_conj]
    _ ≤ _ := by
        rw [e2]
        refine (norm_sub_le _ _).trans (le_of_eq ?_)
        rw [norm_neg]

theorem coeff_bounded (hψ : IsStdChar D ψ (-1)) (S T : HSp D) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (h1 : μ 𝓕 < ⊤) {f f₀ : WO S T → ℂ} (h : IsThetaFunO ψ S T f) (h₀ : IsThetaFunO ψ S T f₀) :
    ∃ C : ℝ, ∀ w : WO S T, ‖thPair μ 𝓕 f (heisO ψ S T w f₀)‖ ≤ C := by
  obtain ⟨a, ha⟩ := (GlobalTheory.ThetaSquare.squareIntegrable (V := S) (W := T) hψ f h).2.1
  obtain ⟨b, hb⟩ := (GlobalTheory.ThetaSquare.squareIntegrable (V := S) (W := T) hψ f₀ h₀).2.1
  refine ⟨a * b * μ.real 𝓕, fun w => norm_setIntegral_le_of_norm_le_const h1 fun x _ => ?_⟩
  rw [norm_mul, norm_star, GlobalTheory.ThetaSquare.norm_heisO hψ]
  exact mul_le_mul (ha x) (hb _) (norm_nonneg _) ((norm_nonneg _).trans (ha x))

theorem realDecay : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ →
    ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 →
    ∀ f f₀ : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T f₀ →
    ∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (k : ℕ), ∃ C : ℝ, ∀ w : WO S T,
      ‖deriv (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) 0‖ ^ k * ‖thPair μ 𝓕 f (heisO ψ S T w f₀)‖ ≤ C := by
  intro D ψ hψ θ hθ S T μ 𝓕 hc f f₀ h h₀ τ z k
  obtain ⟨hμ, h𝓕, h1⟩ := hc
  have DS := GlobalTheory.ThetaSquare.derSkew (V := S) (W := T) hψ hθ τ z
  induction k generalizing f f₀ with
  | zero =>
    obtain ⟨C, hC⟩ := coeff_bounded hψ S T (μ := μ) (𝓕 := 𝓕) (by rw [h1]; exact ENNReal.one_lt_top) h h₀
    exact ⟨C, fun w => by rw [pow_zero, one_mul]; exact hC w⟩
  | succ k ih =>
    obtain ⟨C₁, hC₁⟩ := ih _ f₀ (DS.2.1 f h) h₀
    obtain ⟨C₂, hC₂⟩ := ih f _ h (DS.2.1 f₀ h₀)
    refine ⟨C₁ + C₂, fun w => ?_⟩
    have hs := step_bound hψ hθ S T hμ h𝓕 τ z h h₀ w
    calc _ = ‖deriv (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) 0‖ ^ k *
          (‖deriv (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) 0‖ * ‖thPair μ 𝓕 f (heisO ψ S T w f₀)‖) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := mul_add _ _ _
      _ ≤ C₁ + C₂ := add_le_add (hC₁ w) (hC₂ w)

end GlobalTheory.RealDecay

end
