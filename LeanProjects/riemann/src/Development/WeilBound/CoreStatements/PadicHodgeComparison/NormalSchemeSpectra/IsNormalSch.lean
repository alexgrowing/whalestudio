import Development.WeilBound.CoreStatements.PadicHodgeComparison.TransferCocycles.TransferCocycle

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace PositivityTheory.AutomorphicGaloisHodgeTate.NormalSchemeSpectra

def IsNormalSch (X : Scheme.{0}) : Prop :=
  ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)

def HasDeg {Y X : Scheme.{0}} (f : Y ⟶ X) (d : ℕ) : Prop :=
  IsFinite f ∧ ∀ U : X.affineOpens,
    letI := (f.appLE U.1 (f ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
    Module.Finite Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1) ∧ Module.Projective Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1) ∧
      ∀ P : PrimeSpectrum Γ(X, U.1), Module.rankAtStalk (R := Γ(X, U.1)) (M := Γ(Y, f ⁻¹ᵁ U.1)) P = d

abbrev pb (q : ℕ) {Y X : Scheme.{0}} (f : Y ⟶ X) (n i : ℤ) : Ht q (sch.obj X) n i →+ Ht q (sch.obj Y) n i :=
  pull (ZMod q) (sch.map f) (tw q i) n

def IsTrSys (q : ℕ) (tr : ∀ {Y X : Scheme.{0}} (_ : Y ⟶ X) (n i : ℤ), Ht q (sch.obj Y) n i →+ Ht q (sch.obj X) n i) : Prop :=
  (∀ {Y X : Scheme.{0}} (f : Y ⟶ X) (d : ℕ), HasDeg f d → ∀ (n i : ℤ) (a : Ht q (sch.obj X) n i),
    tr f n i (pb q f n i a) = d • a) ∧
  (∀ {Y X Y' X' : Scheme.{0}} (f : Y ⟶ X) (g : X' ⟶ X) (f' : Y' ⟶ X') (g' : Y' ⟶ Y) (d : ℕ), HasDeg f d →
    IsPullback g' f' f g → ∀ (n i : ℤ) (a : Ht q (sch.obj Y) n i),
      pb q g n i (tr f n i a) = tr f' n i (pb q g' n i a)) ∧
  (∀ {Z Y X : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (d e : ℕ), HasDeg f d → HasDeg g e → ∀ (n i : ℤ)
    (a : Ht q (sch.obj Z) n i), tr (f ≫ g) n i a = tr g n i (tr f n i a)) ∧
  (∀ {Y X : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Etale f] (n i : ℤ) (a : Ht q (sch.obj Y) n i),
    tr f n i a = PositivityTheory.AutomorphicGaloisHodgeTate.Tr.pushHt q f n i a)

def TrFFEx : Prop := ∀ (q : ℕ) [NeZero q], ∃ tr, IsTrSys q tr

def TrNormalEx : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] {Y X : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Surjective f] [IsIntegral X] [IsIntegral Y],
    IsNormalSch X → IsUnit (l : Γ(X, ⊤)) → ∀ (d : ℕ), HasDeg (pullback.snd f (X.fromSpecStalk (genericPoint X))) d →
    ∃ tr : ∀ n : ℤ, HQ l (sch.obj Y) n 0 →ₗ[ℚ_[l]] HQ l (sch.obj X) n 0,
      ∀ (n : ℤ) (a : HQ l (sch.obj X) n 0), tr n (pullHQ l (sch.map f) n 0 a) = (d : ℚ_[l]) • a

def GalInv : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] {Y X : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Surjective f] (G : Type) [Group G] [Finite G]
    (act : G →* Aut Y), (∀ g, (act g).hom ≫ f = f) → IsNormalSch X → IsNormalSch Y → IsUnit (l : Γ(X, ⊤)) →
    (∀ (Z : Scheme.{0}) (h : Y ⟶ Z), (∀ g, (act g).hom ≫ h = h) → ∃! h' : X ⟶ Z, f ≫ h' = h) →
    ∀ n : ℤ, Function.Injective (pullHQ l (sch.map f) n 0) ∧
      ∀ b : HQ l (sch.obj Y) n 0, (∀ g : G, pullHQ l (sch.map (act g).hom) n 0 b = b) →
        b ∈ LinearMap.range (pullHQ l (sch.map f) n 0)

def RadInv : Prop :=
  ∀ (p a q : ℕ) [Fact p.Prime] [NeZero q], Nat.Coprime q p → ∀ {X : Scheme.{0}} (F : X ⟶ X), (p : Γ(X, ⊤)) = 0 →
    (∀ (A : Type) [CommRing A] (x : Spec (CommRingCat.of A) ⟶ X) (φ : A →+* A), (∀ t, φ t = t ^ (p ^ a)) →
      x ≫ F = Spec.map (CommRingCat.ofHom φ) ≫ x) →
    ∀ (n i : ℤ) (c : Ht q (sch.obj X) n i), pb q F n i c = c

def SpecIso : Prop :=
  ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A], SH A →
    IsAlgClosed (IsLocalRing.ResidueField A) → IsUnit (q : A) →
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra (FractionRing A) Ω] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of A))
    [IsProper p] [Smooth p] (n i : ℤ),
      Function.Bijective (pb q (pullback.fst p (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))) n i) ∧
      Function.Bijective (pb q (pullback.fst p (Spec.map (CommRingCat.ofHom
        ((algebraMap (FractionRing A) Ω).comp (algebraMap A (FractionRing A)))))) n i)

def SpecIsoOf : Prop := E2 → E3 → SpecIso

end PositivityTheory.AutomorphicGaloisHodgeTate.NormalSchemeSpectra

end
