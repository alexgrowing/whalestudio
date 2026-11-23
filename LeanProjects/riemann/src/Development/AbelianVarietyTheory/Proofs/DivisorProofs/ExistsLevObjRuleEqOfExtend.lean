import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDPModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorEvalOneTmulMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsModelVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelValHomog
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelValBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsChartFunOfRestrictsToVal

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

theorem isModelVal_of_isRapoport : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (R₀ : Type) [CommRing R₀] (k : ℕ)
  (r₀ : Rule (rapObj 𝔠) R₀ k) (M : Scheme.{0}) (U : Obj F 𝔠 M) (R : Type) [CommRing R] [Algebra R₀ R]
  (X : Obj F 𝔠 (Sp R)) (hX : X.IsRapoport) (δ : X.DetGen), IsModelVal r₀ U X δ (r₀.val R X hX δ) := by
  intro F _ _ 𝔠 R₀ _ k r₀ M U R _ _ X hX δ R' _ _ σ X' φ' δ' hX' hδ' W hW Y φY hY δY h hh ψ χ hψ δY' u hδY' hu
  have hX'R : X'.IsRapoport := hX'.isRapoport (σ : R →+* R') hX
  have e1 := hh R' ψ X' χ hX'R δY' hψ hδY'
  have e2 := r₀.homog R' X' hX'R δ' δY' u hu
  have e3 := r₀.baseChange R R' σ X hX X' hX'R φ' δ δ' hX' hδ'
  rw [← e3, ← e2, e1]

theorem exists_levObj_rule_eq_of_extend : GlobalTheory.Published.DelignePappasModel → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ),
  3 ≤ N → ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁], Function.Injective (algebraMap R₀ R₁) →
  ∀ (k : ℕ) (r₀ : Rule (rapObj 𝔠) R₀ k) (r₁ : Rule (trivialObjectCondition 𝔠) R₁ k),
  (∀ (R : Type) [CommRing R] [Algebra R₁ R] (X : Obj F 𝔠 (Sp R)) (hX : X.IsRapoport) (δ : X.DetGen),
    r₁.val R X trivial δ = (r₀.extend R₁).val R X hX δ) →
  ∃ r : Rule (levObj 𝔠 N) R₀ k, ∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (h : levObj 𝔠 N R X)
    (hX : X.IsRapoport) (δ : X.DetGen), r.val R X h δ = r₀.val R X hX δ := by
  intro hDP F _ _ _ 𝔠 N hN R₀ R₁ _ _ _ hinj k r₀ r₁ H
  obtain ⟨M, s, U, α, V, hM⟩ := exists_isDPModel hDP F 𝔠 N hN
  have hS1 : ∀ (N' : ℕ) (M' : Scheme.{0}) (s' : M' ⟶ Sp (Localization.Away (N' : ℤ))) (U' : Obj F 𝔠 M')
      (α' : U'.Level N') (V' : M'.Opens), 3 ≤ N' → IsDPModel N' s' U' α' V' → (∀ (W : M'.Opens) (hW : IsAffineOpen W) (Y : Obj F 𝔠 (Sp Γ(M', W))) (φY : Y.A.left ⟶ U'.A.left),
    Y.IsPullBy U' hW.fromSpec φY → ∀ δY : Y.DetGen, ∃ h : R₀ ⊗[ℤ] Γ(M', W), IsChartFun r₀ Y δY h) :=
    fun N' M' s' U' α' V' _ hM' ↦ GlobalTheory.RealMult.ChartFun.exists_isChartFun F 𝔠 N' M' s' U' α' V' hM' R₀ R₁ hinj k r₀ r₁ H
  have key := GlobalTheory.RealMult.ModelValGlue.existsUnique_isModelVal F 𝔠 N M s U α V hM R₀ k r₀ (hS1 N M s U α V hN hM)
    (GlobalTheory.RealMult.ChartIndep.presVal_indep hDP F 𝔠 N hN M s U α V hM R₀ k r₀ hS1)
  refine ⟨{ val := fun R _ _ X hX δ ↦ (key R X hX δ).exists.choose
            homog := fun R _ _ X hX δ δ' c hc ↦ (key R X hX δ).unique
              (GlobalTheory.RealMult.isModelVal_homog F 𝔠 R₀ k r₀ M U R X δ δ' c _ hc (key R X hX δ').exists.choose_spec)
              (key R X hX δ).exists.choose_spec
            baseChange := fun R R' _ _ _ _ σ X hX X' hX' φ δ δ' hφ hδ ↦ (key R' X' hX' δ').unique
              (key R' X' hX' δ').exists.choose_spec
              (GlobalTheory.RealMult.isModelVal_baseChange F 𝔠 R₀ k r₀ M U R R' σ X X' φ δ δ' _ hφ hδ (key R X hX δ).exists.choose_spec) }, ?_⟩
  intro R _ _ X h hX δ
  exact (key R X h δ).unique (key R X h δ).exists.choose_spec (isModelVal_of_isRapoport F 𝔠 R₀ k r₀ M U R X hX δ)

end GlobalTheory.RealMult
