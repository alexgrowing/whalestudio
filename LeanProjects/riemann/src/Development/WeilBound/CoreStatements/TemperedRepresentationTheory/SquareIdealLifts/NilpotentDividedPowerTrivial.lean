import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIdealLifts.IsSqIdeal

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.JLift

def DPFlat : Prop :=
  ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A] (I : Ideal R) (κ : DividedPowers I),
    ∃ δ : DividedPowers (I.map (algebraMap R A)), IsDPMorphism κ δ (algebraMap R A)

def DPNil : Prop :=
  ∀ (R A : Type) [CommRing R] [CommRing A] (f : R →+* A) (I : Ideal R) (κ : DividedPowers I) (δ : DividedPowers (I.map f)),
    IsDPMorphism κ δ f → IsNilDP κ → IsNilDP δ

def ChartEx : Prop :=
  ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I), IsNilDP κ → ∀ (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I → ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left)
    (h : IsPullback i X₀.hom X.hom (spMap π)), Flat X.hom →
    ∀ U : X.left.Opens, IsAffineOpen U → ∃ a : Pt κ (X₀.hom ≫ spMap π) X i, a.IsChart ∧ Set.range a.y = (U : Set X.left)

def ChartHom : Prop :=
  ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R) (X : Over (Sp R)) (i : X₀ ⟶ X.left), Mono i → ∀ a b : Pt κ s₀ X i, a.IsChart → Set.range b.y ⊆ Set.range a.y →
    ∃! φ : a.T ⟶ b.T, spMap (φ.φ : a.T.B →+* b.T.B) ≫ a.y = b.y

def DividedPowerChartLift : Prop :=
  ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R) (X : Over (Sp R)) (i : X₀ ⟶ X.left), Mono i → ∀ (z : Z1 (O κ s₀)) (W : Type 1) (c : W → Pt κ s₀ X i), (∀ k, (c k).IsChart) →
    (∀ (x : X.left) (U : X.left.Opens), x ∈ U → ∃ k, x ∈ Set.range (c k).y ∧ Set.range (c k).y ⊆ (U : Set X.left)) →
    ∀ ζ : ∀ k, (c k).T.B, (∀ (k l : W) (φ : (c k).T ⟶ (c l).T), spMap (φ.φ : (c k).T.B →+* (c l).T.B) ≫ (c k).y = (c l).y →
      ev z φ = ζ l - φ.φ (ζ k)) →
    ∃! t : ∀ a : Pt κ s₀ X i, a.T.B, TrivBy z t ∧ ∀ k, t (c k) = ζ k

def TrivCongr : Prop :=
  ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R) (X : Over (Sp R)) (i : X₀ ⟶ X.left) (z z' : Z1 (O κ s₀)), Triv X i 0 (κ := κ) (s₀ := s₀) ∧ (H1.mk _ z = H1.mk _ z' → Triv X i z → Triv X i z') ∧
    (Triv X i z → Triv X i z' → Triv X i (z + z'))

def TrivForm : Prop :=
  ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R) (X : Over (Sp R)) (i : X₀ ⟶ X.left) (w : i ≫ X.hom = s₀) (ω : Form (X.hom ≫ 𝟙 _)), Triv X i ((redIsMor κ w).coef.pullbackOneCocycle ω.1)

def TrivPull : Prop :=
  ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R) (X : Over (Sp R)) (i : X₀ ⟶ X.left) (Z₀ : Scheme.{0}) (u₀ : Z₀ ⟶ Sp R) (Z : Over (Sp R)) (k : Z₀ ⟶ Z.left) (f : Z ⟶ X) (f₀ : Z₀ ⟶ X₀)
    (m : IsMor κ s₀ κ u₀ (RingHom.id R) f₀), k ≫ f.left = f₀ ≫ i → ∀ z : Z1 (O κ s₀), Triv X i z → Triv Z k (m.coef.pullbackOneCocycle z)

def TrivLin : Prop :=
  ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R) (X : Over (Sp R)) (i : X₀ ⟶ X.left) (P : Type 1) [AddCommGroup P] [Module R P], Module.Projective R P → ∀ z : P →ₗ[R] Z1 (O κ s₀), (∀ p, Triv X i (z p)) →
    ∃ t : P →ₗ[R] (∀ a : Pt κ s₀ X i, a.T.B), ∀ p, TrivBy (z p) (t p)

def NilpotentDividedPowerTrivial : Prop :=
  ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I), IsNilDP κ → ∀ (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I → ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left)
    (h : IsPullback i X₀.hom X.hom (spMap π)), Flat X.hom →
    ∀ z : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _)), Triv X i ((redIsMor κ h.w).coef.pullbackOneCocycle z) → H1.mk _ z ∈ F1 (X.hom ≫ 𝟙 _)

def Conn : Prop :=
  ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R) (T : Thick κ s₀), T.J = I.map (algebraMap R T.B) →
    (∃ e : Z1 (O κ s₀) →ₗ[R] Ω[T.B⁄R], ∀ z, IsConn z T (e z)) ∧ ∀ z e e', IsConn z T e → IsConn z T e' → e = e'

def EvDiff : Prop :=
  ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R) (J : Ideal R) (hJ : J ^ 2 = 0), IsDPMorphism (divided₂ hJ) κ (RingHom.id R) →
    ∀ (T T' : Thick κ s₀), T.J = I.map (algebraMap R T.B) → ∀ (ψ ψ' : T ⟶ T'), (∀ b, ψ'.φ b - ψ.φ b ∈ J.map (algebraMap R T'.B)) →
    ∀ z : Z1 (O κ s₀), ev z ψ' - ev z ψ ∈ J.map (algebraMap R T'.B)

def LFcore : Prop :=
  ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R) (J : Ideal R) (hJ : J ^ 2 = 0), IsDPMorphism (divided₂ hJ) κ (RingHom.id R) →
    ∀ (T : Thick κ s₀), T.J = I.map (algebraMap R T.B) → ∀ (P : Type 1) [AddCommGroup P] [Module R P] (z : P → Z1 (O κ s₀)) (e : P → Ω[T.B⁄R]) (ζ : P → T.B),
    (∀ p, IsConn (z p) T (e p)) → OmFrame (RingHom.id R) J T.B (fun p ↦ e p + KaehlerDifferential.D R T.B (ζ p)) → LocFrame J z T ζ

def FormZero : Prop :=
  ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), Function.Surjective s.appTop.hom → ∀ f : Form s, Form.cl s f = 0 →
    (∀ (E : SqExt R) (y : Sp E.C ⟶ X) (hy : y ≫ s = spMap (algebraMap R E.C)), E.val y hy f.1 = 0) ∧
    ∀ (B : Type) [CommRing B] [Algebra R B] (x : Sp B ⟶ X) (hx : x ≫ s = spMap (algebraMap R B)), connForm f.1 x hx = 0

def AbFns : Prop :=
  ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → Function.Surjective A.hom.appTop.hom

def TanSep : Prop :=
  AbelianDeRham → ∀ (R : Type) [CommRing R] (g : ℕ) (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ v : Over.mk (spMap (algebraMap R (DualNumber R))) ⟶ A, (∀ f : Form (A.hom ≫ 𝟙 _), tanVal v f = 0) →
    ∃ x : Sp R ⟶ A.left, v.left = spMap (algebraMap R (DualNumber R)) ≫ x

def CoSurj : Prop :=
  AbelianDeRham → ∀ (R : Type) [CommRing R] (g : ℕ) (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ ω : PrimitiveSubmodule A → Form (A.hom ≫ 𝟙 _), (∀ p, Form.cl _ (ω p) = p.1.1) →
    ∀ (B : Type) [CommRing B] [Algebra R B] (x : Sp B ⟶ A.left) (hx : x ≫ A.hom ≫ 𝟙 _ = spMap (algebraMap R B)), IsOpenImmersion x →
    Submodule.span B (Set.range fun p ↦ connForm (ω p).1 x hx) = ⊤

def CoFrameAb : Prop :=
  AbelianDeRham → ∀ (R : Type) [CommRing R] (g : ℕ) (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∃ ω : PrimitiveSubmodule A →ₗ[R] Form (A.hom ≫ 𝟙 _), (∀ p, Form.cl _ (ω p) = p.1.1) ∧ CoFrame (RingHom.id R) (A.hom ≫ 𝟙 _) ω

def StdLift : Prop :=
  ∀ (R R₁ B₁ : Type) [CommRing R] [CommRing R₁] [CommRing B₁] [Algebra R₁ B₁] (ρ : R →+* R₁), Function.Surjective ρ →
    IsNilpotent (RingHom.ker ρ) → Algebra.IsStandardSmooth R₁ B₁ →
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (q : B →+* B₁), Algebra.Smooth R B ∧ Function.Surjective q ∧
      q.comp (algebraMap R B) = (algebraMap R₁ B₁).comp ρ ∧ RingHom.ker q = (RingHom.ker ρ).map (algebraMap R B)

def PreChartEx : Prop :=
  ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I)
    (π : R →+* R₀) (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ →
    ∀ (X₁ : Over (Sp R₁)) (X₀ : Over (Sp R₀)) (i₁ : X₀.left ⟶ X₁.left), IsPullback i₁ X₀.hom X₁.hom (spMap π₁) → Smooth X₁.hom →
    ∀ (M : IsMor κ (X₀.hom ≫ spMap π) κ₁ (X₀.hom ≫ spMap π₁) ρ (𝟙 _)) (x : X₁.left) (U : X₁.left.Opens), x ∈ U →
    ∃ (a₁ : Pt κ₁ (X₀.hom ≫ spMap π₁) X₁ i₁) (T : Thick κ (X₀.hom ≫ spMap π)) (r : T ⟶ M.obj a₁.T),
      PreChart M a₁ T r ∧ x ∈ Set.range a₁.y ∧ Set.range a₁.y ⊆ (U : Set X₁.left)

def Glue : Prop :=
  ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ : R →+* R₁), Function.Surjective ρ → IsNilpotent (RingHom.ker ρ) →
    ∀ (X₁ : Over (Sp R₁)) (W : Type) (B B₁ : W → Type) [∀ k, CommRing (B k)] [∀ k, CommRing (B₁ k)] [∀ k, Algebra R (B k)]
      (y₁ : ∀ k, Sp (B₁ k) ⟶ X₁.left) (q : ∀ k, B k →+* B₁ k), (∀ k, IsOpenImmersion (y₁ k)) → (∀ k, Function.Surjective (q k)) →
      (∀ k, RingHom.ker (q k) = (RingHom.ker ρ).map (algebraMap R (B k))) → (∀ k, Algebra.Smooth R (B k)) →
      (∀ k, y₁ k ≫ X₁.hom ≫ spMap ρ = spMap ((q k).comp (algebraMap R (B k)))) →
      (∀ (x : X₁.left) (U : X₁.left.Opens), x ∈ U → ∃ k, x ∈ Set.range (y₁ k) ∧ Set.range (y₁ k) ⊆ (U : Set X₁.left)) →
    ∀ ψ : ∀ k l, Set.range (y₁ l) ⊆ Set.range (y₁ k) → (B k →ₐ[R] B l),
      (∀ k l h (u : B₁ k →+* B₁ l), spMap u ≫ y₁ k = y₁ l → ∀ b, u (q k b) = q l (ψ k l h b)) →
      (∀ k h b, ψ k k h b = b) → (∀ k l m h h' h'' b, ψ l m h' (ψ k l h b) = ψ k m h'' b) →
    ∃ (X : Over (Sp R)) (i₂ : X₁.left ⟶ X.left) (y : ∀ k, Sp (B k) ⟶ X.left), IsPullback i₂ X₁.hom X.hom (spMap ρ) ∧ Smooth X.hom ∧
      (∀ k, IsOpenImmersion (y k)) ∧ (∀ k, y k ≫ X.hom = spMap (algebraMap R (B k))) ∧ (∀ k, spMap (q k) ≫ y k = y₁ k ≫ i₂) ∧
      ∀ k l h, spMap (ψ k l h : B k →+* B l) ≫ y k = y l

def Lev1 : Prop :=
  ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ : R →+* R₁) (I₁ : Ideal R₁) (κ₁ : DividedPowers I₁) (X₀ : Scheme.{0}) (s₁ : X₀ ⟶ Sp R₁)
    (X₁ : Over (Sp R₁)) (i₁ : X₀ ⟶ X₁.left) (w : i₁ ≫ X₁.hom = s₁) (P : Type 1) [AddCommGroup P] [Module R P], Module.Projective R P →
    ∀ (z₁ : P →ₛₗ[ρ] Z1 (O κ₁ s₁)) (ω₁ : P →ₛₗ[ρ] Form (X₁.hom ≫ 𝟙 _)),
    (∀ p, H1.mk _ (z₁ p) = (redIsMor κ₁ w).pull1 (Form.cl _ (ω₁ p))) → CoFrame ρ (X₁.hom ≫ 𝟙 _) ω₁ →
    ∃ t₁ : P →ₛₗ[ρ] (∀ a : Pt κ₁ s₁ X₁ i₁, a.T.B), (∀ p, TrivBy (z₁ p) (t₁ p)) ∧
      ∀ a : Pt κ₁ s₁ X₁ i₁, a.IsChart → ∀ e : P → Ω[a.T.B⁄R₁], (∀ p, IsConn (z₁ p) a.T (e p)) →
        OmFrame ρ ⊥ a.T.B fun p ↦ e p + KaehlerDifferential.D R₁ a.T.B (t₁ p a)

def Transfer : Prop :=
  ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ : R →+* R₁), Function.Surjective ρ →
    ∀ (I : Ideal R) (κ : DividedPowers I) (I₁ : Ideal R₁) (κ₁ : DividedPowers I₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R) (s₁ : X₀ ⟶ Sp R₁)
    (M : IsMor κ s₀ κ₁ s₁ ρ (𝟙 X₀)) (X₁ : Over (Sp R₁)) (i₁ : X₀ ⟶ X₁.left) (a₁ : Pt κ₁ s₁ X₁ i₁) (T : Thick κ s₀) (r : T ⟶ M.obj a₁.T),
    PreChart M a₁ T r → ∀ (P : Type 1) [AddCommGroup P] [Module R P] (z : P → Z1 (O κ s₀)) (e : P → Ω[T.B⁄R]) (ζ : P → T.B) (ζ₁ : P → a₁.T.B),
    (∀ p, IsConn (z p) T (e p)) → (∀ p, r.φ (ζ p) + ev (z p) r = ζ₁ p) →
    (∀ e₁ : P → Ω[a₁.T.B⁄R₁], (∀ p, IsConn (M.coef.pullbackOneCocycle (z p)) a₁.T (e₁ p)) →
      OmFrame ρ ⊥ a₁.T.B fun p ↦ e₁ p + KaehlerDifferential.D R₁ a₁.T.B (ζ₁ p)) →
    OmFrame (RingHom.id R) (RingHom.ker ρ) T.B fun p ↦ e p + KaehlerDifferential.D R T.B (ζ p)

def Build : Prop :=
  ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I)
    (π : R →+* R₀) (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ →
    ∀ (X₁ : Over (Sp R₁)) (X₀ : Over (Sp R₀)) (i₁ : X₀.left ⟶ X₁.left) (h₁ : IsPullback i₁ X₀.hom X₁.hom (spMap π₁)), Smooth X₁.hom →
    ∀ (M : IsMor κ (X₀.hom ≫ spMap π) κ₁ (X₀.hom ≫ spMap π₁) ρ (𝟙 _)) (P : Type 1) [AddCommGroup P] [Module R P], Module.Projective R P →
    ∀ (z : P →ₗ[R] Z1 (O κ (X₀.hom ≫ spMap π))) (ω₁ : P →ₛₗ[ρ] Form (X₁.hom ≫ 𝟙 _)),
    (∀ p, M.pull1 (H1.mk _ (z p)) = (redIsMor κ₁ h₁.w).pull1 (Form.cl _ (ω₁ p))) → CoFrame ρ (X₁.hom ≫ 𝟙 _) ω₁ →
    ∃ (X : Over (Sp R)) (i₂ : X₁.left ⟶ X.left), IsPullback i₂ X₁.hom X.hom (spMap ρ) ∧ Smooth X.hom ∧
      ∃ t : P →ₗ[R] (∀ a : Pt κ (X₀.hom ≫ spMap π) X (i₁ ≫ i₂), a.T.B), (∀ p, TrivBy (z p) (t p)) ∧ Frame J z t

def MapLiftStep : Prop :=
  ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I)
    (π : R →+* R₀) (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ →
    ∀ (Y : Over (Sp R)) (Y₀ : Scheme.{0}) (sY : Y₀ ⟶ Sp R) (j : Y₀ ⟶ Y.left), Smooth Y.hom → Mono j →
    ∀ (Z : Over (Sp R)) (Z₁ : Over (Sp R₁)) (Z₀ : Over (Sp R₀)) (k₁ : Z₁.left ⟶ Z.left) (k₀ : Z₀.left ⟶ Z₁.left),
    IsPullback k₁ Z₁.hom Z.hom (spMap ρ) → IsPullback k₀ Z₀.hom Z₁.hom (spMap π₁) → Flat Z.hom → Function.Surjective Z₁.hom.appTop.hom →
    ∀ (f₁ : Z₁.left ⟶ Y.left) (f₀ : Z₀.left ⟶ Y₀), f₁ ≫ Y.hom = Z₁.hom ≫ spMap ρ → f₀ ≫ j = k₀ ≫ f₁ →
    ∀ (m : IsMor κ sY κ (Z₀.hom ≫ spMap π) (RingHom.id R) f₀) (P : Type 1) [AddCommGroup P] [Module R P], Module.Projective R P →
    ∀ (z : P →ₗ[R] Z1 (O κ sY)) (t : P →ₗ[R] (∀ a : Pt κ sY Y j, a.T.B)), (∀ p, TrivBy (z p) (t p)) → Frame J z t →
    (∀ p, Triv Z (k₀ ≫ k₁) (m.coef.pullbackOneCocycle (z p))) → ∃ f : Z ⟶ Y, k₁ ≫ f.left = f₁

def AlgStep : Prop :=
  AbelianDeRham → ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I)
    (π : R →+* R₀) (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ → LiftObj κ₁ π₁ →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A' : Over (Sp R)) [GrpObj A'] (i' : A₀.left ⟶ A'.left)
      (h' : IsGrpPullback A₀ A' (spMap π) i'), IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom →
    ∀ F : Submodule R (HdR A'), IsAdmissible h' F → ∀ (M : IsMor κ (A₀.hom ≫ spMap π) κ₁ (A₀.hom ≫ spMap π₁) ρ (𝟙 _)),
    Module.Projective R F.dualCoannihilator ∧
    ∃ (A₁ : Over (Sp R₁)) (_ : GrpObj A₁) (i₁ : A₀.left ⟶ A₁.left) (h₁ : IsGrpPullback A₀ A₁ (spMap π₁) i₁),
      IsAbelianScheme A₁ ∧ SmoothOfRelativeDimension g A₁.hom ∧ ∃ β : F.dualCoannihilator →ₛₗ[ρ] PrimitiveSubmodule A₁,
        (∀ p, ((liftMor κ₁ h₁).pull (β p).1).1 = M.pull1 ((liftMor κ h').pull p.1).1) ∧
        ∀ (N : Type) [AddCommGroup N] [Module R₁ N] (l : F.dualCoannihilator →ₛₗ[ρ] N), ∃! L : PrimitiveSubmodule A₁ →ₗ[R₁] N, ∀ p, L (β p) = l p

def FilEq : Prop :=
  AbelianDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I), IsNilDP κ → ∀ (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I → ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A A' : Over (Sp R)) [GrpObj A] [GrpObj A']
      (i : A₀.left ⟶ A.left) (i' : A₀.left ⟶ A'.left) (h : IsGrpPullback A₀ A (spMap π) i) (h' : IsGrpPullback A₀ A' (spMap π) i'),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom →
    ∀ F : Submodule R (HdR A'), IsAdmissible h' F →
    (∀ p ∈ F.dualCoannihilator, ∃ c ∈ PrimitiveSubmodule A, (liftMor κ h).pull c = (liftMor κ h').pull p) → liftFil κ h = F.comap (crysToDR κ h')

def FilHom : Prop :=
  AbelianDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I), IsNilDP κ → ∀ (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I → ∀ (g : ℕ) (A₀ B₀ : Over (Sp R₀)) [GrpObj A₀] [GrpObj B₀] (A B : Over (Sp R)) [GrpObj A] [GrpObj B]
      (i : A₀.left ⟶ A.left) (j : B₀.left ⟶ B.left) (h : IsGrpPullback A₀ A (spMap π) i) (k : IsGrpPullback B₀ B (spMap π) j),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀],
    (∀ d ∈ liftFil κ h, push κ (spMap π) f₀ d ∈ liftFil κ k) →
    ∀ p ∈ PrimitiveSubmodule B, ∃ c ∈ PrimitiveSubmodule A, (liftMor κ h).pull c = primPull κ (spMap π) f₀ ((liftMor κ k).pull p)

def Frame0 : Prop :=
  ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I), IsNilDP κ → ∀ (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I → ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left)
    (h : IsPullback i X₀.hom X.hom (spMap π)), Flat X.hom → ∀ (J : Ideal R) (hJ : J ^ 2 = 0), IsDPMorphism (divided₂ hJ) κ (RingHom.id R) →
    ∀ (P : Type 1) [AddCommGroup P] [Module R P], Module.Projective R P → ∀ (ω : P →ₗ[R] Form (X.hom ≫ 𝟙 _)), CoFrame (RingHom.id R) (X.hom ≫ 𝟙 _) ω →
    ∀ z : P →ₗ[R] Z1 (O κ (X₀.hom ≫ spMap π)), (∀ p, z p = (redIsMor κ h.w).coef.pullbackOneCocycle (ω p).1) →
    ∃ t : P →ₗ[R] (∀ a : Pt κ (X₀.hom ≫ spMap π) X i, a.T.B), (∀ p, TrivBy (z p) (t p)) ∧ Frame J z t

def GrpLift : Prop :=
  ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I)
    (π : R →+* R₀) (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ →
    ∀ (A₀ : Over (Sp R₀)) [GrpObj A₀] (A₁ : Over (Sp R₁)) [GrpObj A₁] (i₁ : A₀.left ⟶ A₁.left), IsGrpPullback A₀ A₁ (spMap π₁) i₁ →
    IsAbelianScheme A₁ → ∀ (X : Over (Sp R)) (i₂ : A₁.left ⟶ X.left), IsPullback i₂ A₁.hom X.hom (spMap ρ) → Smooth X.hom →
    ∀ (P : Type 1) [AddCommGroup P] [Module R P], Module.Projective R P → ∀ (z : P →ₗ[R] Z1 (O κ (A₀.hom ≫ spMap π)))
      (t : P →ₗ[R] (∀ a : Pt κ (A₀.hom ≫ spMap π) X (i₁ ≫ i₂), a.T.B)), (∀ p, H1.mk _ (z p) ∈ prim κ (spMap π) A₀) →
    (∀ p, TrivBy (z p) (t p)) → Frame J z t → ∃ _ : GrpObj X, IsGrpPullback A₁ X (spMap ρ) i₂ ∧ IsAbelianScheme X

def ObjStep : Prop :=
  AbelianDeRham → ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I)
    (π : R →+* R₀) (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ → LiftObj κ₁ π₁ → LiftObj κ π

def ObjId : Prop :=
  AbelianDeRham → ∀ (R : Type) [CommRing R], LiftObj (dp0 R) (RingHom.id R)

def HomSq : Prop :=
  AbelianDeRham → ∀ (R : Type) [CommRing R] (I : Ideal R) (h : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I → LiftHom (divided₂ h) π

end PositivityTheory.JLift
