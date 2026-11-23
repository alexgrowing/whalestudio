import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsRapoportOfBasis

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

def IsFineModuli {B : Type} [CommRing B] {M : Scheme.{0}} (s : M ⟶ Sp B) {N : ℕ} {U : Obj F 𝔠 M}
    (α : U.Level N) : Prop :=
  ∀ (S : Scheme.{0}) (t : S ⟶ Sp B) (X : Obj F 𝔠 S) (β : X.Level N),
    ∃! b : S ⟶ M, b ≫ s = t ∧ Obj.IsLevelPull β α b

def IsRelCI {B : Type} [CommRing B] {M : Scheme.{0}} (s : M ⟶ Sp B) (n : ℕ) : Prop :=
  (∀ (K : Type) [Field K] (t : Sp K ⟶ Sp B), topologicalKrullDim ↥(pullback s t) = n) ∧
    ∀ x : M, ∃ (V : M.Opens) (_ : IsAffineOpen V) (_ : x ∈ V) (c : ℕ) (g : Fin c → MvPolynomial (Fin (c + n)) B)
      (e : Γ(M, V) ≃+* MvPolynomial (Fin (c + n)) B ⧸ Ideal.span (Set.range g)),
      ∀ b : B, e (constFn s V b) = Ideal.Quotient.mk _ (MvPolynomial.C b)

def Obj.IsLinearKS {R : Type} [CommRing R] (X : Obj F 𝔠 (Sp R)) (κ : Fil X.A →ₗ[R] X.Lie) : Prop :=
  ∀ (a : 𝓞 F) (x y : Fil X.A), (y : HdR X.A) = act (dp0 R) (𝟙 _) X.rm a x → κ y = a • κ x

def Obj.HasKS {R : Type} [CommRing R] {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp (DualNumber R))}
    {i : X.A.left ⟶ X'.A.left} (h : X.IsPullBy X' (DeRham.epsRed R) i) (κ : Fil X.A →ₗ[R] X.Lie) : Prop :=
  ∀ x : Fil X.A, IsKSValue h.grp (x : HdR X.A) (κ x).hom

def TorusPointsExist : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ))
    (𝔞 𝔟 : FracId F), ∀ z ∈ halfSpace F,
    ∃ (X : Obj F (𝔞 * 𝔟⁻¹) (Sp ℂ)) (δ : X.DetGen), X.IsRapoport ∧ IsTorusPoint e 𝔞 𝔟 z X δ.1

def QExpansionOnAll : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F →
    ∀ (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ)) (𝔞 𝔟 : FracId F) (k : ℕ) (R₀ : Subring ℂ)
      (g : ((F →+* ℝ) → ℂ) → ℂ) (a : (𝔞 * 𝔟).elt → ℂ),
      IsHolForm 𝔞 𝔟 k g → HasFourier 𝔞 𝔟 g a → (∀ ξ, a ξ ∈ R₀) →
      ∃! r : Rule (trivialObjectCondition (𝔞 * 𝔟⁻¹)) R₀ k, r.HasValues e 𝔞 𝔟 g

end GlobalTheory.RealMult

namespace GlobalTheory.Published

def DelignePappasModel : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ), 3 ≤ N →
    ∃ (M : Scheme.{0}) (s : M ⟶ Sp (Localization.Away (N : ℤ))) (U : Obj F 𝔠 M) (α : U.Level N),
      IsFineModuli s α ∧ IsSeparated s ∧ QuasiCompact s ∧ LocallyOfFinitePresentation s ∧
      Flat s ∧ IsRelCI s (Module.finrank ℚ F) ∧
      (∃ V : M.Opens, (V : Set M) = U.rapLocus ∧ SmoothOfRelativeDimension (Module.finrank ℚ F) (V.ι ≫ s) ∧
        M.basicOpen ((discr F : ℤ) : Γ(M, ⊤)) ≤ V ∧
        ∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))) (y : ↥(pullback s t)),
          pullback.fst s t y ∉ V → 2 ≤ ringKrullDim ((pullback s t).presheaf.stalk y)) ∧
      (∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))), Geo.Tor.IsNormalScheme (pullback s t)) ∧
      ∀ (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Algebra (Localization.Away (N : ℤ)) B]
        [IsCyclotomicExtension {N} (Localization.Away (N : ℤ)) B]
        (x : ↥(pullback s (spMap (algebraMap (Localization.Away (N : ℤ)) B))))
        (K : Type) [Field K] (t : Sp K ⟶ Sp B),
        IsIrreducible (pullback.fst (pullback.snd s (spMap (algebraMap (Localization.Away (N : ℤ)) B))) t ⁻¹'
          connectedComponent x)

def HilbertQExpansion : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F →
    ∀ (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ)) (𝔞 𝔟 : FracId F) (k : ℕ) (R₀ : Subring ℂ)
      (g : ((F →+* ℝ) → ℂ) → ℂ) (a : (𝔞 * 𝔟).elt → ℂ),
      IsHolForm 𝔞 𝔟 k g → HasFourier 𝔞 𝔟 g a → (∀ ξ, a ξ ∈ R₀) →
      ∃! r : Rule (rapObj (𝔞 * 𝔟⁻¹)) R₀ k, r.HasValues e 𝔞 𝔟 g

def GoetzkyKoecher : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F →
    ∀ (𝔞 𝔟 : FracId F) (k : ℕ) (g : ((F →+* ℝ) → ℂ) → ℂ), IsHolForm 𝔞 𝔟 k g →
      (∃! a, HasFourier 𝔞 𝔟 g a) ∧
      ∀ a, HasFourier 𝔞 𝔟 g a → ∀ ξ, a ξ ≠ 0 → ξ = 0 ∨ IsTotPos (ξ : F)

def HilbertKodairaSpencer : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R : Type) [CommRing R]
    (X : Obj F 𝔠 (Sp R)), X.IsRapoport →
    (∀ (X' : Obj F 𝔠 (Sp (DualNumber R))) (i : X.A.left ⟶ X'.A.left) (h : X.IsPullBy X' (DeRham.epsRed R) i),
      ∃! κ, X.IsLinearKS κ ∧ Obj.HasKS h κ) ∧
    (∀ κ, X.IsLinearKS κ → ∃ (X' : Obj F 𝔠 (Sp (DualNumber R))) (i : X.A.left ⟶ X'.A.left)
      (h : X.IsPullBy X' (DeRham.epsRed R) i), Obj.HasKS h κ) ∧
    ∀ (X' X'' : Obj F 𝔠 (Sp (DualNumber R))) (i' : X.A.left ⟶ X'.A.left) (i'' : X.A.left ⟶ X''.A.left)
      (h' : X.IsPullBy X' (DeRham.epsRed R) i') (h'' : X.IsPullBy X'' (DeRham.epsRed R) i'') κ, Obj.HasKS h' κ → Obj.HasKS h'' κ →
      ∃ ψ : X'.A.left ⟶ X''.A.left, X'.IsPullBy X'' (𝟙 _) ψ ∧ i' ≫ ψ = i''

def RealMultDeRhamRank : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R : Type) [CommRing R] [IsLocalRing R]
    (X : Obj F 𝔠 (Sp R)),
    letI := tensorModule (dp0 R) (𝟙 _) X.rm
    Nonempty (Module.Basis (Fin 2) (R ⊗[ℤ] 𝓞 F) (HdR X.A))

def HilbertBlumenthal : Prop :=
  DelignePappasModel ∧ HilbertQExpansion ∧ GoetzkyKoecher ∧ HilbertKodairaSpencer ∧ RealMultDeRhamRank

end GlobalTheory.Published
