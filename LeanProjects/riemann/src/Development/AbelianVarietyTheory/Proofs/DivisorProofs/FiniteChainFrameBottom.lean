import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleFiniteFactorExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleMatchedFactors
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BotFinMatch

theorem gBig_two {Q₁ Q₂ Q₃ : GlobalTheory.SqTop.GP} (h₁ : GlobalTheory.SqTop.GBig Q₁) (h₂ : GlobalTheory.SqTop.GBig Q₂)
    (H : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Q₁ G μ₀ C x b → Q₂ G μ₀ C x b → Q₃ G μ₀ C x b) : GlobalTheory.SqTop.GBig Q₃ := by
  obtain ⟨a₁, h₁⟩ := h₁
  obtain ⟨a₂, h₂⟩ := h₂
  refine ⟨max a₁ a₂, fun ε CF hCF => ?_⟩
  obtain ⟨C₁, x₁, h₁⟩ := h₁ ε CF (le_of_max_le_left hCF)
  obtain ⟨C₂, x₂, h₂⟩ := h₂ ε CF (le_of_max_le_right hCF)
  exact ⟨max C₁ C₂, max x₁ x₂, fun C hC D large₂ he hx r T Lc μ hLc G =>
    H G μ C _ _ (h₁ C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) r T Lc μ hLc G)
      (h₂ C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) r T Lc μ hLc G)⟩

theorem finMatch : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (t : T), IsFinF W.ψ W.θ true FA FW (X.f t) → IsFinF W.ψ W.θ false FA' FW (X.f' t) → ∀ (Pi : ModuleCat.{0} ℂ) rf rl p p', IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi rf rl p p' → ∀ (Pr Pf : ModuleCat.{0} ℂ) (q : PolF D WW.rank A.rank →ₗ[ℂ] Pr) (q' : PolF D WW.rank A'.rank →ₗ[ℂ] Pr) (r : (WO A WW → ℂ) →ₗ[ℂ] Pf) (r' : (WO A' WW → ℂ) →ₗ[ℂ] Pf) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi), Function.Surjective q → Function.Surjective q' → (∀ f, IsFinF W.ψ W.θ true FA FW f → ∀ P, p (fockF W.ψ W.θ true FA FW f P) = e (q P ⊗ₜ r f)) → (∀ f, IsFinF W.ψ W.θ false FA' FW f → ∀ P, p' (fockF W.ψ W.θ false FA' FW f P) = e (q' P ⊗ₜ r' f)) → ∃ κ : ℂ, r (X.f t) = κ • r' (X.f' t) := by
  intro hH hP hK hL
  refine gBig_two (GlobalTheory.T.bottom_triangle_finite_factor_exists hH hP hK hL) (GlobalTheory.T.bottom_triangle_matched_factors hH hP hK hL) fun {D T Lc sc} G μ₀ C x b hA hB => ?_
  intro W i j A A' WW X hX FA FA' FW t hf hf' Pi rf rl p p' hm Pr Pf q q' r r' e hq hq' hp hp'
  obtain ⟨Pi₀, rf₀, rl₀, p₀, p₀', hm₀, hA'⟩ := hA W i j A A' WW X hX FA FA' FW t hf hf'
  obtain ⟨E, c, hc, hE, hE'⟩ := hB W i j A A' WW X hX FA FA' FW t Pi₀ rf₀ rl₀ p₀ p₀' Pi rf rl p p' hm₀ hm
  have k1 : ∀ f, IsFinF W.ψ W.θ true FA FW f → ∀ P, p₀ (fockF W.ψ W.θ true FA FW f P) = (e.trans E.symm) (q P ⊗ₜ (c⁻¹ • r) f) := by
    intro f hf P
    have hmem : fockF W.ψ W.θ true FA FW f P ∈ algF W.ψ W.θ true FA FW := Submodule.subset_span ⟨f, P, hf, rfl⟩
    have h1 := hE _ hmem
    rw [hp f hf P] at h1
    rw [LinearEquiv.trans_apply, LinearMap.smul_apply, TensorProduct.tmul_smul, LinearEquiv.map_smul, h1,
      LinearEquiv.map_smul, LinearEquiv.map_smul, LinearEquiv.symm_apply_apply, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have k2 : ∀ f, IsFinF W.ψ W.θ false FA' FW f → ∀ P, p₀' (fockF W.ψ W.θ false FA' FW f P) = (e.trans E.symm) (q' P ⊗ₜ r' f) := by
    intro f hf P
    have hmem : fockF W.ψ W.θ false FA' FW f P ∈ algF W.ψ W.θ false FA' FW := Submodule.subset_span ⟨f, P, hf, rfl⟩
    have h1 := hE' _ hmem
    rw [hp' f hf P] at h1
    rw [LinearEquiv.trans_apply, h1, LinearEquiv.symm_apply_apply]
  obtain ⟨κ, hκ⟩ := hA' Pr Pf q q' (c⁻¹ • r) r' (e.trans E.symm) hq hq' k1 k2
  refine ⟨c * κ, ?_⟩
  rw [LinearMap.smul_apply] at hκ
  rw [mul_smul, ← hκ, smul_smul, mul_inv_cancel₀ hc, one_smul]

end GlobalTheory.BotFinMatch
