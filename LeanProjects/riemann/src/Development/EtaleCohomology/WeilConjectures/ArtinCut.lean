import Development.EtaleCohomology.WeilConjectures.FermatCount
import Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangeFractionFieldIndEtaleOverPolynomi

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open LateralTheory.E.t_E3Cut (Et IE SHExists IEComp pC)

namespace LateralTheory.EWeil.ArtinCut

def Van (q : ℕ) (D : CommRingCat.{0}) (n : ℤ) : Prop := ∀ i : ℤ, Subsingleton (Ht q (sch.obj (Spec D)) n i)

def Const (d : ℕ) : Prop := ∀ (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω], IsUnit (q : Ω) →
  ∀ (A : Type) [CommRing A] [Algebra Ω A] [Algebra.FiniteType Ω A], ringKrullDim A ≤ d →
  ∀ n : ℤ, (d : ℤ) < n → Van q (CommRingCat.of A) n

def IsStalk {A S : CommRingCat.{0}} (f : A ⟶ S) (p : PrimeSpectrum A) : Prop :=
  IE f ∧ SH S ∧ ∀ a : A, a ∈ p.asIdeal ↔ ¬ IsUnit (f.hom a)

instance (X : Scheme.{0}) : HasSheafify X.smallEtaleTopology AddCommGrpCat.{1} := by
  have : EssentiallySmall.{1} X.Etale := inferInstance
  infer_instance

instance (X : Scheme.{0}) : IsGrothendieckAbelian.{1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{1}) := by
  have : EssentiallySmall.{1} X.Etale := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

instance (X : Scheme.{0}) : HasExt.{1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{1}) := inferInstance

abbrev Sm (A : CommRingCat.{0}) : Type 2 := Sheaf (Spec A).smallEtaleTopology AddCommGrpCat.{1}

def StalkZero {A : CommRingCat.{0}} (F : Sm A) (p : PrimeSpectrum A) : Prop :=
  ∀ (V : (Spec A).Etale) (v : V.left), V.hom v = p → ∀ s : F.obj.obj (op V),
    ∃ (W : (Spec A).Etale) (g : W ⟶ V) (w : W.left), g.left w = v ∧ (F.obj.map g.op).hom s = 0

def SmallCd (q : ℕ) (A : CommRingCat.{0}) (δ : PrimeSpectrum A → ℕ∞) : Prop :=
  ∀ F : Sm A, (∀ (V : (Spec A).Etale) (s : F.obj.obj (op V)), q • s = 0) → ∀ a : ℕ,
    (∀ p, (a : ℕ∞) < δ p → StalkZero F p) → ∀ n : ℕ, a < n → Subsingleton (Sheaf.H.{1} F n)

def NormVan (q : ℕ) (A : CommRingCat.{0}) (δ : PrimeSpectrum A → ℕ∞) : Prop :=
  ∀ l : ℕ, l.Prime → l ∣ q → ∀ (C : CommRingCat.{0}) (c : A ⟶ C) [IsDomain C] [IsIntegrallyClosed C], c.hom.IsIntegral →
    ∀ p : PrimeSpectrum A, p.asIdeal = RingHom.ker c.hom → ∀ n : ℕ, δ p < n → Van l C n

def AtInf {R T B : CommRingCat.{0}} (φ : CommRingCat.of (Polynomial R) ⟶ T) (β : CommRingCat.of (Polynomial R) ⟶ B)
    (D : CommRingCat.{0}) : Prop :=
  ∃ (ψ : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (Localization.Away (φ.hom Polynomial.X)))
    (u : B ⟶ D) (v : CommRingCat.of (Localization.Away (φ.hom Polynomial.X)) ⟶ D),
    (∀ r : R, ψ.hom (Polynomial.C r) = algebraMap T _ (φ.hom (Polynomial.C r))) ∧
    ψ.hom Polynomial.X * algebraMap T _ (φ.hom Polynomial.X) = 1 ∧ IsPushout β ψ u v

def SHz : Prop := SHExists ∧ IEComp

def Dim : Prop :=
  (∀ {A B : CommRingCat.{0}} (f : A ⟶ B), f.hom.IsIntegral ∨ Et f → ringKrullDim B ≤ ringKrullDim A) ∧
  (∀ {A B : CommRingCat.{0}} (f : A ⟶ B), f.hom.IsIntegral → Function.Injective f.hom → ringKrullDim A ≤ ringKrullDim B) ∧
  (∀ (A : Type) [CommRing A] (p : PrimeSpectrum A), ((Order.coheight p : ℕ∞) : WithBot ℕ∞) = ringKrullDim (A ⧸ p.asIdeal)) ∧
  ∀ (A : Type) [CommRing A] (d : ℕ), ringKrullDim A ≤ d →
    StrictAnti (Order.coheight : PrimeSpectrum A → ℕ∞) ∧ ∀ p : PrimeSpectrum A, Order.coheight p ≤ d ∧
      ∀ e : ℕ, d = e + 1 → ∀ p' : PrimeSpectrum A, p' < p → Order.coheight p ≤ e

def GenStalk : Prop := ∀ {A S : CommRingCat.{0}} [IsDomain A] (f : A ⟶ S), IsStalk f ⊥ →
  IsField S ∧ ∀ s : S, ∃ P : Polynomial A, P ≠ 0 ∧ P.eval₂ f.hom s = 0

def Fibre : Prop := ∀ (Ω : Type) [Field Ω] (e : ℕ) (p : PrimeSpectrum (MvPolynomial (Fin e) Ω)),
  ∃ (a c : ℕ) (y : MvPolynomial (Fin a) Ω →ₐ[Ω] MvPolynomial (Fin e) Ω), a + c = e ∧ Order.coheight p ≤ a ∧
    (∀ g, y g ∈ p.asIdeal → g = 0) ∧
    ∀ (K : Type) [Field K] (κ : MvPolynomial (Fin a) Ω →+* K), Function.Injective κ →
    ∀ (D : CommRingCat.{0}) (u : CommRingCat.of (MvPolynomial (Fin e) Ω) ⟶ D) (v : CommRingCat.of K ⟶ D),
      IsPushout (CommRingCat.ofHom y.toRingHom) (CommRingCat.ofHom κ) u v → ringKrullDim D ≤ c

def Radicial : Prop := Base → ∀ (q : ℕ) {Y X : Scheme.{0}} (f : Y ⟶ X) [IsIntegralHom f] [Surjective f] [UniversallyInjective f],
  IsUnit (q : Γ(X, ⊤)) → ∀ i : ℤ, Eqv _ (sch.map f) (tw q i)

def Deviss : Prop := Base → ∀ (q : ℕ) [NeZero q] (A : CommRingCat.{0}) [IsNoetherianRing A], IsUnit (q : A) →
  ∀ δ : PrimeSpectrum A → ℕ∞, StrictAnti δ → NormVan q A δ → SmallCd q A δ

def Leray : Prop := Base → ∀ (q : ℕ) [NeZero q] {A B : CommRingCat.{0}} (β : A ⟶ B), IsUnit (q : A) →
  ∀ (δ : PrimeSpectrum A → ℕ∞) (d : ℕ), SmallCd q A δ →
  (∀ (p : PrimeSpectrum A) (S D : CommRingCat.{0}) (f : A ⟶ S) (u : B ⟶ D) (v : S ⟶ D), IsStalk f p → IsPushout β f u v →
    ∀ m : ℕ, (d : ℕ∞) < m + δ p → Van q D m) →
  ∀ n : ℤ, (d : ℤ) < n → Van q B n

def NormCurve : Prop := Base → ∀ (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω], IsUnit (q : Ω) →
  ∀ (A : Type) [CommRing A] [Algebra Ω A] [Algebra.FiniteType Ω A], ringKrullDim A ≤ 1 →
  NormVan q (CommRingCat.of A) Order.coheight

def Low : Prop := Base → Const 0 ∧ Const 1

def SepConst : Prop := Base → ∀ c : ℕ, Const c → ∀ (q : ℕ) [NeZero q] (K : Type) [Field K] [IsSepClosed K], IsUnit (q : K) →
  ∀ (D : Type) [CommRing D] [Algebra K D] [Algebra.FiniteType K D], ringKrullDim D ≤ c →
  ∀ n : ℤ, (c : ℤ) < n → Van q (CommRingCat.of D) n

def FieldCd1 : Prop := Base → ∀ c : ℕ, Const c → ∀ (q : ℕ) [NeZero q] (K : Type) [Field K], IsUnit (q : K) →
  (∀ l : ℕ, l.Prime → l ∣ q → ∀ (L : Type) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] (n : ℤ), 2 ≤ n →
    Van l (CommRingCat.of L) n) →
  ∀ (D : Type) [CommRing D] [Algebra K D] [Algebra.FiniteType K D], ringKrullDim D ≤ c →
  ∀ n : ℤ, (c : ℤ) + 1 < n → Van q (CommRingCat.of D) n

def TsenC1SeparablyClosed : Prop := Base → ∀ (q : ℕ) [NeZero q] (k L : Type) [Field k] [IsSepClosed k] [Field L] [Algebra (RatFunc k) L]
  [Algebra.IsAlgebraic (RatFunc k) L], IsUnit (q : L) → ∀ n : ℤ, 2 ≤ n → Van q (CommRingCat.of L) n

def Punct : Prop := Base → ∀ e : ℕ, (∀ b ≤ e, Const b) → ∀ (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω], IsUnit (q : Ω) →
  ∀ {T B : CommRingCat.{0}} (φ : CommRingCat.of (Polynomial (CommRingCat.of (MvPolynomial (Fin e) Ω))) ⟶ T)
    (β : CommRingCat.of (Polynomial (CommRingCat.of (MvPolynomial (Fin e) Ω))) ⟶ B), β.hom.Finite → IE φ → SH T →
  ¬ IsUnit (φ.hom Polynomial.X) → ∀ p : PrimeSpectrum (MvPolynomial (Fin e) Ω),
  (∀ a, a ∈ p.asIdeal ↔ ¬ IsUnit (φ.hom (Polynomial.C a))) → ∀ D, AtInf φ β D →
  ∀ m : ℕ, ((e + 1 : ℕ) : ℕ∞) < m + Order.coheight p → Van q D m

def AtInfinity : Prop := Base → Const 1 → ∀ (q : ℕ) [NeZero q] {S B : CommRingCat.{0}} (β : CommRingCat.of (Polynomial S) ⟶ B),
  SH S → IsUnit (q : S) → β.hom.Finite → ∀ m : ℤ, 3 ≤ m →
  (∀ (T : CommRingCat.{0}) (φ : CommRingCat.of (Polynomial S) ⟶ T), IE φ → SH T → ¬ IsUnit (φ.hom Polynomial.X) →
    (∀ s : S, IsUnit (φ.hom (Polynomial.C s)) → IsUnit s) → ∀ D, AtInf φ β D → Van q D m) → Van q B m

def Stalk : Prop := Base → ∀ e : ℕ, 1 ≤ e → (∀ b ≤ e, Const b) → ∀ (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω],
  IsUnit (q : Ω) → ∀ {B : CommRingCat.{0}} (β : CommRingCat.of (Polynomial (CommRingCat.of (MvPolynomial (Fin e) Ω))) ⟶ B),
  β.hom.Finite → ∀ (p : PrimeSpectrum (CommRingCat.of (MvPolynomial (Fin e) Ω))) (S D : CommRingCat.{0})
    (f : CommRingCat.of (MvPolynomial (Fin e) Ω) ⟶ S) (u : B ⟶ D) (v : S ⟶ D), IsStalk f p → IsPushout (pC _ ≫ β) f u v →
  ∀ m : ℕ, ((e + 1 : ℕ) : ℕ∞) < m + Order.coheight p → Van q D m

def NormFT : Prop := Base → ∀ e : ℕ, (∀ b ≤ e, Const b) → ∀ (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω], IsUnit (q : Ω) →
  ∀ (A : Type) [CommRing A] [Algebra Ω A] [Algebra.FiniteType Ω A], ringKrullDim A ≤ e →
  NormVan q (CommRingCat.of A) Order.coheight

def Step : Prop := Base → ∀ e : ℕ, 1 ≤ e → (∀ b ≤ e, Const b) → Const (e + 1)

def Final : Prop := (Base → ∀ d, Const d) → Artin

theorem goal_of (h1 : Low) (h2 : Step) (h3 : Final) : Artin := by
  refine h3 fun hb d => ?_
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    match d, ih with
    | 0, _ => exact (h1 hb).1
    | 1, _ => exact (h1 hb).2
    | e + 2, ih => exact h2 hb (e + 1) (by omega) fun b hb' => ih b (by omega)

end LateralTheory.EWeil.ArtinCut

end
