import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitObj

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

def tensorEval {R₀ A R : Type} [CommRing R₀] [CommRing A] [CommRing R] [Algebra R₀ R] (ψ : A →+* R) :
    R₀ ⊗[ℤ] A →ₗ[ℤ] R :=
  TensorProduct.lift ((LinearMap.mul ℤ R).compl₁₂ (algebraMap R₀ R).toAddMonoidHom.toIntLinearMap
    ψ.toAddMonoidHom.toIntLinearMap)

@[simp] theorem tensorEval_tmul {R₀ A R : Type} [CommRing R₀] [CommRing A] [CommRing R] [Algebra R₀ R]
    (ψ : A →+* R) (r : R₀) (a : A) : tensorEval ψ (r ⊗ₜ a) = algebraMap R₀ R r * ψ a := rfl

def IsChartFun {R₀ : Type} [CommRing R₀] {k : ℕ} (r₀ : Rule (rapObj 𝔠) R₀ k) {A : Type} [CommRing A]
    (Y : Obj F 𝔠 (Sp A)) (δY : Y.DetGen) (h : R₀ ⊗[ℤ] A) : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra R₀ R] (ψ : A →+* R) (X : Obj F 𝔠 (Sp R)) (φ : X.A.left ⟶ Y.A.left)
    (hX : X.IsRapoport) (δ : X.DetGen), X.IsPullBy Y (spMap ψ) φ → Obj.DetCorr ψ φ δY.1 δ.1 →
    r₀.val R X hX δ = tensorEval ψ h

def IsPresVal {R₀ : Type} [CommRing R₀] (k : ℕ) {A : Type} [CommRing A] {Y : Obj F 𝔠 (Sp A)} (δY : Y.DetGen)
    (h : R₀ ⊗[ℤ] A) {R : Type} [CommRing R] [Algebra R₀ R] {X : Obj F 𝔠 (Sp R)} (δ : X.DetGen) (ψ : A →+* R)
    (φ : X.A.left ⟶ Y.A.left) (v : R) : Prop :=
  ∀ (δ' : X.DetGen) (u : R), Obj.DetCorr ψ φ δY.1 δ'.1 → δ'.1 = u • δ.1 → v = u ^ k * tensorEval ψ h

def IsModelVal {R₀ : Type} [CommRing R₀] {k : ℕ} (r₀ : Rule (rapObj 𝔠) R₀ k) {M : Scheme.{0}} (U : Obj F 𝔠 M)
    {R : Type} [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (δ : X.DetGen) (v : R) : Prop :=
  ∀ (R' : Type) [CommRing R'] [Algebra R₀ R'] (σ : R →ₐ[R₀] R') (X' : Obj F 𝔠 (Sp R')) (φ' : X'.A.left ⟶ X.A.left)
    (δ' : X'.DetGen), X'.IsPullBy X (spMap (σ : R →+* R')) φ' → Obj.DetCorr (σ : R →+* R') φ' δ.1 δ'.1 →
    ∀ (W : M.Opens) (hW : IsAffineOpen W) (Y : Obj F 𝔠 (Sp Γ(M, W))) (φY : Y.A.left ⟶ U.A.left),
      Y.IsPullBy U hW.fromSpec φY → ∀ (δY : Y.DetGen) (h : R₀ ⊗[ℤ] Γ(M, W)), IsChartFun r₀ Y δY h →
      ∀ (ψ : Γ(M, W) →+* R') (χ : X'.A.left ⟶ Y.A.left), X'.IsPullBy Y (spMap ψ) χ →
        IsPresVal k δY h δ' ψ χ (σ v)

def IsDPModel (N : ℕ) {M : Scheme.{0}} (s : M ⟶ Sp (Localization.Away (N : ℤ))) (U : Obj F 𝔠 M) (α : U.Level N)
    (V : M.Opens) : Prop :=
  IsFineModuli s α ∧ IsSeparated s ∧ Flat s ∧ (V : Set M) = U.rapLocus ∧
    (∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))), Geo.Tor.IsNormalScheme (pullback s t)) ∧
    ∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))) (y : ↥(pullback s t)),
      pullback.fst s t y ∉ V → 2 ≤ ringKrullDim ((pullback s t).presheaf.stalk y)

theorem exists_isDPModel (hDP : GlobalTheory.Published.DelignePappasModel) (F : Type) [Field F] [NumberField F]
    [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ) (hN : 3 ≤ N) :
    ∃ (M : Scheme.{0}) (s : M ⟶ Sp (Localization.Away (N : ℤ))) (U : Obj F 𝔠 M) (α : U.Level N) (V : M.Opens),
      IsDPModel N s U α V := by
  obtain ⟨M, s, U, α, hfine, hsep, -, -, hflat, -, ⟨V, hV, -, -, hcod⟩, hnorm, -⟩ := hDP F 𝔠 N hN
  exact ⟨M, s, U, α, V, hfine, hsep, hflat, hV, hnorm, hcod⟩

end GlobalTheory.RealMult
