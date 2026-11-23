import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatNormalFibersOpenExtension
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RTensorEqZeroOfRestrictAffineInf
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_normal_fibers_open_extension : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (R₀ : Type) [CommRing R₀] (k : ℕ)
    (s t : Rule (unitObj 𝔠 6) R₀ k) (N : ℕ) (M : Scheme.{0}) (sM : M ⟶ Sp (Localization.Away (N : ℤ)))
    (U : Obj F 𝔠 M) (V : M.Opens), Flat sM →
    (∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))), Geo.Tor.IsNormalScheme (pullback sM t)) →
    (∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))) (y : ↥(pullback sM t)),
      pullback.fst sM t y ∉ V → 2 ≤ ringKrullDim ((pullback sM t).presheaf.stalk y)) →
    ∀ (W : M.Opens) (hW : IsAffineOpen W),
    (∀ (W' : M.Opens) (hW' : IsAffineOpen W'), W' ≤ W ⊓ V → ∀ (Y' : Obj F 𝔠 (Sp Γ(M, W')))
      (φ' : Y'.A.left ⟶ U.A.left), Y'.IsPullBy U hW'.fromSpec φ' → (∀ (B : Type) [CommRing B] [Algebra R₀ B] (σ : Γ(M, W') →+* B) (Y'' : Obj F 𝔠 (Sp B)) (φ'' : Y''.A.left ⟶ Y'.A.left),
    Y''.IsPullBy Y' (spMap σ) φ'' → ∀ (h : IsUnit ((6 : ℕ) : B)) (δ : Y''.DetGen), s.val B Y'' h δ = t.val B Y'' h δ)) →
    ∀ (Y : Obj F 𝔠 (Sp Γ(M, W))) (φ : Y.A.left ⟶ U.A.left), Y.IsPullBy U hW.fromSpec φ →
    ∀ (YC : Obj F 𝔠 (Sp (R₀ ⊗[ℤ] Γ(M, W)))) (ψ : YC.A.left ⟶ Y.A.left),
      YC.IsPullBy Y (spMap (Algebra.TensorProduct.includeRight : Γ(M, W) →ₐ[ℤ] R₀ ⊗[ℤ] Γ(M, W)).toRingHom) ψ →
      ∀ (h : IsUnit ((6 : ℕ) : R₀ ⊗[ℤ] Γ(M, W))) (δ : YC.DetGen), s.val _ YC h δ = t.val _ YC h δ := by
  first | exact @GlobalTheory.RealMult.rule_eq_on_extend_chart | exact GlobalTheory.RealMult.rule_eq_on_extend_chart | (intros; apply GlobalTheory.RealMult.rule_eq_on_extend_chart <;> assumption)
