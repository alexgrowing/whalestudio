import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp PSpace IsProjOver)

namespace LateralTheory.EWeil

attribute [local instance] MvPolynomial.gradedAlgebra

def Base : Prop :=
  (A1 ∧ A2 ∧ A3 ∧ A4 ∧ A5 ∧ DivisorNaturality ∧ DivisorRingCompatibility ∧ DivisorSupportCondition ∧ DivisorAdditivity ∧ A7 ∧ A8 ∧ A9 ∧ A10 ∧ A11) ∧
  (B1 ∧ B2 ∧ B3 ∧ B4 ∧ B5 ∧ DivisorPicardCompatibility ∧ B6h1 ∧ B7) ∧ (C1 ∧ C2 ∧ C3 ∧ C4 ∧ C5) ∧ D1 ∧ (E1 ∧ E2 ∧ E3 ∧ E4 ∧ E6 ∧ E8)

section Defs
variable (l : ℕ) [Fact l.Prime] {k : Type} [Field k]

def IsFrob {Ω : Type} [Field Ω] [Algebra k Ω] (σ : Ω ≃ₐ[k] Ω) : Prop := ∀ x, σ x = x ^ Nat.card k

abbrev HX (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Sp k) (n : ℤ) : Type 1 :=
  HQ l (sch.obj (geom Ω p)) n 0

def geoF {Ω : Type} [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Sp k) (n : ℤ) (σ : Ω ≃ₐ[k] Ω) :
    HX l Ω p n →ₗ[ℚ_[l]] HX l Ω p n := galHQ l Ω p n 0 σ⁻¹

def IsEig {Ω : Type} [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Sp k) (n : ℤ) (σ : Ω ≃ₐ[k] Ω)
    (α : AlgebraicClosure ℚ_[l]) : Prop :=
  Module.End.HasEigenvalue ((geoF l p n σ).baseChange (AlgebraicClosure ℚ_[l])) α

def WtIn {X : Scheme.{0}} (p : X ⟶ Sp k) (n : ℤ) (S : Set ℝ) : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (σ : Ω ≃ₐ[k] Ω), IsFrob σ → ∀ α, IsEig l p n σ α →
    ∀ ι : AlgebraicClosure ℚ_[l] →+* ℂ, Real.logb (Nat.card k) (‖ι α‖ ^ 2) ∈ S

def FinT {X : Scheme.{0}} (p : X ⟶ Sp k) : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (a : ℕ) (n i : ℤ), Finite (Ht (l ^ a) (sch.obj (geom Ω p)) n i)

def RatTr {X : Scheme.{0}} (p : X ⟶ Sp k) (n : ℤ) : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (σ : Ω ≃ₐ[k] Ω), IsFrob σ → ∀ r : ℕ, 0 < r →
    ∃ a : ℚ, LinearMap.trace ℚ_[l] _ ((geoF l p n σ : Module.End ℚ_[l] _) ^ r) = (a : ℚ_[l])

def SmProj (d : ℕ) {X : Scheme.{0}} (p : X ⟶ Sp k) : Prop := SmoothOfRelativeDimension d p ∧ IsProjOver p

def IsCI (d r : ℕ) {X : Scheme.{0}} (p : X ⟶ Sp k) : Prop := SmoothOfRelativeDimension d p ∧
  ∃ (f : Fin r → MvPolynomial (Fin (d + r)) k)
    (e : X ≅ Sp (MvPolynomial (Fin (d + r)) k ⧸ Ideal.span (Set.range f))),
    e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k _)) = p

def IsHyp {R : Type} [CommRing R] (d : ℕ) (F : MvPolynomial (Fin (d + 1 + 1)) R) {X : Scheme.{0}} (p : X ⟶ Sp R) : Prop :=
  SmoothOfRelativeDimension d p ∧ ∃ i : X ⟶ PSpace R (d + 1), IsClosedImmersion i ∧ i ≫ PSpace.str R (d + 1) = p ∧
    Set.range i = ((Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (d + 1 + 1)) R) F :
      (PSpace R (d + 1)).Opens) : Set (PSpace R (d + 1)))ᶜ

def Nonsing {m : ℕ} (F : MvPolynomial (Fin m) k) : Prop :=
  ∀ x : Fin m → AlgebraicClosure k, MvPolynomial.aeval x F = 0 →
    (∀ i, MvPolynomial.aeval x (MvPolynomial.pderiv i F) = 0) → x = 0

inductive Peel : ℕ → ∀ {Y : Scheme.{0}} (_ : Y ⟶ Sp k) {X : Scheme.{0}} (_ : X ⟶ Sp k), Prop
  | base {d : ℕ} {Y : Scheme.{0}} (pY : Y ⟶ Sp k) : SmProj d pY → Peel d pY pY
  | step {e : ℕ} {Y X Y' Z : Scheme.{0}} (pY : Y ⟶ Sp k) (pX : X ⟶ Sp k) (pY' : Y' ⟶ Sp k) (ι : Z ⟶ X) (U : X.Opens) :
      Peel (e + 1) pY pX → Peel e pY' (ι ≫ pX) → IsClosedImmersion ι → (U : Set X) = (Set.range ι)ᶜ →
      Peel (e + 1) pY (U.ι ≫ pX)

abbrev fibre {R k' : Type} [CommRing R] [Field k'] {X : Scheme.{0}} (f : X ⟶ Sp R) (φ : R →+* k') :
    pullback f (Spec.map (CommRingCat.ofHom φ)) ⟶ Sp k' := pullback.snd _ _

abbrev bc (k' : Type) [Field k'] [Algebra k k'] {X : Scheme.{0}} (p : X ⟶ Sp k) : geom k' p ⟶ Sp k' := pullback.snd _ _

def WeakAt (d : ℕ) : Prop := ∀ (k : Type) [Field k] [Finite k], (l : k) ≠ 0 → ∀ {X : Scheme.{0}} (p : X ⟶ Sp k),
  SmProj d p → ∀ n : ℤ, WtIn l p n (Set.Icc ((n : ℝ) - 3) (n + 3))

end Defs

def Goal : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k], (l : k) ≠ 0 →
  ∀ (d : ℕ) {X : Scheme.{0}} (p : X ⟶ Sp k), SmoothOfRelativeDimension d p → IsProjOver p →
  ∀ (Ω : Type) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (n : ℤ), Module.Finite ℚ_[l] (HX l Ω p n) ∧
    ∀ σ : Ω ≃ₐ[k] Ω, IsFrob σ → ∀ α, IsEig l p n σ α → ∀ ι : AlgebraicClosure ℚ_[l] →+* ℂ,
      ‖ι α‖ ^ 2 = (Nat.card k : ℝ) ^ n

def FinProj : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k], (l : k) ≠ 0 →
  ∀ {X : Scheme.{0}} (p : X ⟶ Sp k), IsProjOver p → IsProper p ∧ FinT l p

def FinQ : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k], (l : k) ≠ 0 →
  ∀ {X : Scheme.{0}} (p : X ⟶ Sp k), FinT l p → ∀ (Ω : Type) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (n : ℤ), Module.Finite ℚ_[l] (HX l Ω p n)

def BaseExt : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k], (l : k) ≠ 0 →
  ∀ (k' : Type) [Field k'] [Finite k'] [Algebra k k'] {X : Scheme.{0}} (p : X ⟶ Sp k),
  (∀ d, SmProj d p → SmProj d (bc k' p)) ∧ (FinT l (bc k' p) ↔ FinT l p) ∧
  (∀ n S, WtIn l (bc k' p) n S → WtIn l p n S) ∧ (FinT l p → ∀ n S, WtIn l p n S → WtIn l (bc k' p) n S)

def DualPair : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k], (l : k) ≠ 0 →
  ∀ (d : ℕ) {X : Scheme.{0}} (p : X ⟶ Sp k), SmProj d p → ∀ (Ω : Type) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (σ : Ω ≃ₐ[k] Ω), IsFrob σ →
  ∀ n m : ℤ, n + m = 2 * d → ∃ b : HX l Ω p n ≃ₗ[ℚ_[l]] Module.Dual ℚ_[l] (HX l Ω p m),
    ∀ x y, b (geoF l p n σ x) (geoF l p m σ y) = (Nat.card k : ℚ_[l]) ^ d * b x y

def DualWt : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k], (l : k) ≠ 0 →
  ∀ (d : ℕ) {X : Scheme.{0}} (p : X ⟶ Sp k), SmProj d p → ∀ n m : ℤ, n + m = 2 * d →
  ∀ S : Set ℝ, WtIn l p n S → WtIn l p m {w | 2 * (d : ℝ) - w ∈ S}

def GysinSeq : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k], (l : k) ≠ 0 →
  ∀ (e r : ℕ) {X Z : Scheme.{0}} [CompactSpace X] (p : X ⟶ Sp k) (ι : Z ⟶ X) (U : X.Opens), IsClosedImmersion ι →
  SmoothOfRelativeDimension (e + r) p → SmoothOfRelativeDimension e (ι ≫ p) → (U : Set X) = (Set.range ι)ᶜ →
  (FinT l (ι ≫ p) → (FinT l p ↔ FinT l (U.ι ≫ p))) ∧ (FinT l p → FinT l (U.ι ≫ p) → FinT l (ι ≫ p)) ∧
  (FinT l p → FinT l (ι ≫ p) → ∀ (Ω : Type) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (σ : Ω ≃ₐ[k] Ω), IsFrob σ →
    ∃ (g : ∀ a b : ℤ, a + 2 * r = b → (HX l Ω (ι ≫ p) a →ₗ[ℚ_[l]] HX l Ω p b))
      (δ : ∀ b a : ℤ, a + 2 * r = b + 1 → (HX l Ω (U.ι ≫ p) b →ₗ[ℚ_[l]] HX l Ω (ι ≫ p) a)),
      (∀ a b h, Function.Exact (g a b h) (pullHQ l (sch.map (geomMap Ω (p := U.ι ≫ p) (q := p) U.ι rfl)) b 0)) ∧
      (∀ b a h, Function.Exact (pullHQ l (sch.map (geomMap Ω (p := U.ι ≫ p) (q := p) U.ι rfl)) b 0) (δ b a h)) ∧
      (∀ b a h, Function.Exact (δ b a h) (g a (b + 1) h)) ∧
      (∀ a b h x, geoF l p b σ (g a b h x) = (Nat.card k : ℚ_[l]) ^ r • g a b h (geoF l (ι ≫ p) a σ x)) ∧
      ∀ b a h x, δ b a h (geoF l (U.ι ≫ p) b σ x) = (Nat.card k : ℚ_[l]) ^ r • geoF l (ι ≫ p) a σ (δ b a h x))

def GysinWt : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k], (l : k) ≠ 0 →
  ∀ (e r : ℕ) {X Z : Scheme.{0}} [CompactSpace X] (p : X ⟶ Sp k) (ι : Z ⟶ X) (U : X.Opens), IsClosedImmersion ι →
  SmoothOfRelativeDimension (e + r) p → SmoothOfRelativeDimension e (ι ≫ p) → (U : Set X) = (Set.range ι)ᶜ →
  FinT l p → FinT l (ι ≫ p) → ∀ (a b : ℤ) (S : Set ℝ),
  (a + 2 * r = b → WtIn l (ι ≫ p) a {w | w + 2 * r ∈ S} → WtIn l (U.ι ≫ p) b S → WtIn l p b S) ∧
  (a + 2 * r = b + 1 → WtIn l p b S → WtIn l (ι ≫ p) a {w | w + 2 * r ∈ S} → WtIn l (U.ι ≫ p) b S) ∧
  (a + 2 * r = b + 1 → WtIn l (U.ι ≫ p) b S → WtIn l p (b + 1) S → WtIn l (ι ≫ p) a {w | w + 2 * r ∈ S})

def Artin : Prop := Base → ∀ (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω], IsUnit (q : Ω) →
  ∀ (d : ℕ) {X : Scheme.{0}} [IsAffine X] (p : X ⟶ Sp Ω), SmoothOfRelativeDimension d p →
  ∀ n i : ℤ, (d : ℤ) < n → Subsingleton (Ht q (sch.obj X) n i)

def Segre : Prop := ∀ (k : Type) [Field k] (d e : ℕ) {X Y : Scheme.{0}} (p : X ⟶ Sp k) (p' : Y ⟶ Sp k),
  SmProj d p → SmProj e p' → SmProj (d + e) (pullback.fst p p' ≫ p)

def KunnethEig : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k], (l : k) ≠ 0 →
  ∀ (d e : ℕ) {X Y : Scheme.{0}} (p : X ⟶ Sp k) (p' : Y ⟶ Sp k), SmProj d p → SmProj e p' →
  ∀ (Ω : Type) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (σ : Ω ≃ₐ[k] Ω), IsFrob σ → ∀ (n m : ℤ) (α β : AlgebraicClosure ℚ_[l]),
    IsEig l p n σ α → IsEig l p' m σ β → IsEig l (pullback.fst p p' ≫ p) (n + m) σ (α * β)

def Tensor : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k], (l : k) ≠ 0 → (∀ d, WeakAt l d) →
  ∀ (d : ℕ) {X : Scheme.{0}} (p : X ⟶ Sp k), SmProj d p → ∀ n : ℤ, WtIn l p n {(n : ℝ)}

def Trace : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k], (l : k) ≠ 0 →
  ∀ (d : ℕ) {X : Scheme.{0}} (p : X ⟶ Sp k), SmProj d p → ∀ (Ω : Type) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (σ : Ω ≃ₐ[k] Ω), IsFrob σ → ∀ r : ℕ, 0 < r →
  (Nat.card {x : Sp Ω ⟶ X // x ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k Ω)) ∧
      Spec.map (CommRingCat.ofHom ((σ ^ r : Ω ≃ₐ[k] Ω) : Ω →+* Ω)) ≫ x = x} : ℚ_[l]) =
    ∑ n ∈ Finset.range (2 * d + 1), (-1) ^ n * LinearMap.trace ℚ_[l] _ ((geoF l p n σ : Module.End ℚ_[l] _) ^ r)

def Curve : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k], (l : k) ≠ 0 →
  ∀ (h : Polynomial k) {X : Scheme.{0}} (f : X ⟶ Sp (Localization.Away h)), IsProper f → Smooth f →
  (∀ (n : ℤ) (w : ℝ),
    (∀ (k' : Type) [Field k'] [Finite k'] [Algebra k k'] (φ : Localization.Away h →ₐ[k] k'), RatTr l (fibre f φ.toRingHom) n) →
    (∃ (k' : Type) (_ : Field k') (_ : Finite k') (_ : Algebra k k') (φ : Localization.Away h →ₐ[k] k'),
      WtIn l (fibre f φ.toRingHom) n (Set.Iic w)) →
    ∀ (k' : Type) [Field k'] [Finite k'] [Algebra k k'] (φ : Localization.Away h →ₐ[k] k'),
      WtIn l (fibre f φ.toRingHom) n (Set.Iic w)) ∧
  ((∀ (k' : Type) [Field k'] [Finite k'] [Algebra k k'] (φ : Localization.Away h →ₐ[k] k') (n : ℤ),
      WtIn l (fibre f φ.toRingHom) n {(n : ℝ)}) →
    FinT l (f ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away h)))) ∧
    ∀ n : ℤ, WtIn l (f ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away h)))) n (Set.Ici ((n : ℝ) - 1)))

def HypFamily : Prop := ∀ (k : Type) [Field k] [Finite k] (h : Polynomial k) (d e : ℕ), 0 < e →
  ∀ F : MvPolynomial (Fin (d + 1 + 1)) (Localization.Away h), F.IsHomogeneous e →
  (∀ (k' : Type) [Field k'] [Finite k'] [Algebra k k'] (φ : Localization.Away h →ₐ[k] k'),
    Nonsing (MvPolynomial.map φ.toRingHom F)) →
  ∃ (X : Scheme.{0}) (f : X ⟶ Sp (Localization.Away h)), IsHyp d F f ∧ IsProper f ∧
    ∀ (k' : Type) [Field k'] [Finite k'] [Algebra k k'] (φ : Localization.Away h →ₐ[k] k'),
      IsHyp d (MvPolynomial.map φ.toRingHom F) (fibre f φ.toRingHom)

def HypCoh : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k], (l : k) ≠ 0 →
  ∀ (d e : ℕ), 0 < e → ∀ F : MvPolynomial (Fin (d + 1 + 1)) k, F.IsHomogeneous e →
  ∀ {X : Scheme.{0}} (p : X ⟶ Sp k), IsHyp d F p → ∀ (Ω : Type) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (σ : Ω ≃ₐ[k] Ω), IsFrob σ → ∀ n : ℤ, n ≠ d →
  Module.finrank ℚ_[l] (HX l Ω p n) = (if Even n ∧ 0 ≤ n ∧ n ≤ 2 * d then 1 else 0) ∧
    ∀ x, geoF l p n σ x = (Nat.card k : ℚ_[l]) ^ (n / 2) • x

def FermatCount : Prop := ∀ (F : Type) [Field F] [Finite F] (m e : ℕ), 0 < m → 0 < e →
  ((Nat.card {x : Fin m → F // ∑ i, x i ^ e = 0} : ℝ) - (Nat.card F : ℝ) ^ (m - 1)) ^ 2 ≤
    (e : ℝ) ^ (2 * m) * (Nat.card F : ℝ) ^ m

def HypTrace : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k], (l : k) ≠ 0 →
  ∀ (d e : ℕ), 0 < e → ∀ F : MvPolynomial (Fin (d + 1 + 1)) k, F.IsHomogeneous e →
  ∀ {X : Scheme.{0}} (p : X ⟶ Sp k), IsHyp d F p →
  RatTr l p d ∧ (F = ∑ i, MvPolynomial.X i ^ e → WtIn l p d (Set.Iic (d : ℝ)))

def PureHyp : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k], (l : k) ≠ 0 →
  ∀ (d e : ℕ), (e : k) ≠ 0 → ∀ F : MvPolynomial (Fin (d + 1 + 1)) k, F.IsHomogeneous e → Nonsing F →
  ∀ {X : Scheme.{0}} (p : X ⟶ Sp k), IsHyp d F p → ∀ n : ℤ, WtIn l p n {(n : ℝ)}

def HypWt : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k], (l : k) ≠ 0 →
  ∀ (m : ℕ) {W : Scheme.{0}} (p : W ⟶ Sp k), IsCI m 1 p → FinT l p → WtIn l p m (Set.Ici ((m : ℝ) - 2))

def CIWt : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k], (l : k) ≠ 0 →
  ∀ (d r : ℕ) {U : Scheme.{0}} (p : U ⟶ Sp k), IsCI d r p → FinT l p → WtIn l p d (Set.Ici ((d : ℝ) - 3))

def Bertini : Prop := ∀ (k : Type) [Field k] [Finite k] (d : ℕ) {X : Scheme.{0}} (p : X ⟶ Sp k), SmProj (d + 1) p →
  ∃ (k' : Type) (_ : Field k') (_ : Finite k') (_ : Algebra k k') (Z : Scheme.{0}) (ι : Z ⟶ geom k' p)
    (U : (geom k' p).Opens), IsClosedImmersion ι ∧ SmProj d (ι ≫ bc k' p) ∧ (U : Set _) = (Set.range ι)ᶜ ∧ IsAffineOpen U

def Model : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k], (l : k) ≠ 0 →
  ∀ (d : ℕ) {X : Scheme.{0}} (p : X ⟶ Sp k), SmProj d p →
  ∃ (k' : Type) (_ : Field k') (_ : Finite k') (_ : Algebra k k') (Y U : Scheme.{0}) (pY : Y ⟶ Sp k') (pU : U ⟶ Sp k') (r : ℕ),
    Peel d pY pU ∧ IsCI d r pU ∧ ∀ S, WtIn l pY d S → WtIn l p d S

def PeelWt : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k], (l : k) ≠ 0 →
  ∀ (d : ℕ) {Y X : Scheme.{0}} (pY : Y ⟶ Sp k) (pX : X ⟶ Sp k), Peel d pY pX → (∀ e < d, WeakAt l e) →
  FinT l pX ∧ (WtIn l pX d (Set.Ici ((d : ℝ) - 3)) → WtIn l pY d (Set.Ici ((d : ℝ) - 3)))

def Upper : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k], (l : k) ≠ 0 →
  ∀ (d : ℕ) {X : Scheme.{0}} (p : X ⟶ Sp k), SmProj d p → (∀ e < d, WeakAt l e) →
  ∀ n : ℤ, (d : ℤ) < n → WtIn l p n (Set.Icc ((n : ℝ) - 3) (n + 3))

end LateralTheory.EWeil

end
