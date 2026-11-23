import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.WtDegConst
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericMulOfProd

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId)

namespace UpperTheory.Gal.Mod

abbrev sp {K L : Type} [CommRing K] [CommRing L] (a : K →+* L) : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom a)

def One {p : ℕ} {Y : Scheme.{0}} (T : crystallineComparison.Corr p Y) (w : Wt T.Z) : Prop :=
  IsWt T.p w ∧ ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (z : gp Ω ⟶ T.Z), (p : Ω) ≠ 0 → w Ω z = 1

def co (q j : ℕ) : ℤ := (-1) ^ j * (q : ℤ) ^ j.choose 2

def CycId (q n : ℕ) {p : ℕ} {Y : Scheme.{0}} (T : Fin (n + 1) → crystallineComparison.Corr p Y) (w : ∀ j, Wt (T j).Z) (Ω : Type) [Field Ω]
    [IsAlgClosed Ω] (φ : Ω →+* Ω) (x : gp Ω ⟶ Y) : Prop :=
  ∀ y : gp Ω ⟶ Y, ∑ j : Fin (n + 1),
    co q j * ∑ᶠ z ∈ {z : gp Ω ⟶ (T j).Z | z ≫ (T j).p = x ∧ (twist φ Y)^[n - j] (z ≫ (T j).r) = y}, w j Ω z = 0

def NwtOne : Prop := ∀ (p : ℕ) (Y : Scheme.{0}) (T : crystallineComparison.Corr p Y), LocNml Y →
  (∀ y : Y, TranscendenceTraces.GenPt y → y ∈ Y.basicOpen (p : Γ(Y, ⊤))) → One T (nwt T.p)

def ResClosed : Prop := ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)],
  IsAlgClosed (IsLocalRing.ResidueField V)

def HensSplit : Prop := ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)]
  (A : Type) [CommRing A] [Algebra V A] [Module.Finite V A] (m : Ideal A), m.IsMaximal →
  ∃ e : A, IsIdempotentElem e ∧ e ∉ m ∧ ∀ m' : Ideal A, m'.IsMaximal → m' ≠ m → e ∈ m'

def ValLift : Prop := ∀ (p : ℕ) (Y : Scheme.{0}) (Ω : Type) [Field Ω] (x : gp Ω ⟶ Y) (η : Y), η ⤳ pt x →
  η ∈ Y.basicOpen (p : Γ(Y, ⊤)) →
  ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : ValuationRing V) (_ : IsAlgClosed (FractionRing V))
    (y : Spec (CommRingCat.of V) ⟶ Y) (Ω' : Type) (_ : Field Ω') (_ : IsAlgClosed Ω') (a : Ω →+* Ω')
    (b : IsLocalRing.ResidueField V →+* Ω'), (p : V) ≠ 0 ∧ sp a ≫ x = sp b ≫ resPt V ≫ y

def FibExt : Prop := ∀ {Z Y : Scheme.{0}} (g : Z ⟶ Y) [IsFinite g] (Ω Ω' : Type) [Field Ω] [IsAlgClosed Ω] [Field Ω']
  (a : Ω →+* Ω') (x : gp Ω ⟶ Y), (fib g x).Finite ∧ Set.BijOn (fun z => sp a ≫ z) (fib g x) (fib g (sp a ≫ x)) ∧
    ∀ y y' : gp Ω ⟶ Y, sp a ≫ y = sp a ≫ y' → y = y'

def SecGen : Prop := ∀ {Z Y : Scheme.{0}} (g : Z ⟶ Y) [IsFinite g] (V : Type) [CommRing V] [IsDomain V] [ValuationRing V]
  (y : Spec (CommRingCat.of V) ⟶ Y),
  Set.BijOn (fun z => sp (algebraMap V (FractionRing V)) ≫ z) {z : Spec (CommRingCat.of V) ⟶ Z | z ≫ g = y}
    (fib g (sp (algebraMap V (FractionRing V)) ≫ y))

def ClopenAt : Prop := ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)]
  {W : Scheme.{0}} (g : W ⟶ Spec (CommRingCat.of V)) [IsFinite g] (z₀ : gp (IsLocalRing.ResidueField V) ⟶ W), z₀ ≫ g = resPt V →
  ∃ U : Set W, IsClopen U ∧ ∀ z : gp (IsLocalRing.ResidueField V) ⟶ W, z ≫ g = resPt V → (pt z ∈ U ↔ z = z₀)

def WtVal : Prop := ∀ (p : ℕ) (Y : Scheme.{0}) (T : crystallineComparison.Corr p Y) (w : Wt T.Z), One T w →
  ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)]
    [IsAlgClosed (IsLocalRing.ResidueField V)], (p : V) ≠ 0 → ∀ y : Spec (CommRingCat.of V) ⟶ Y,
    Finite (T.Sec y) ∧ ∀ z₀ : gp (IsLocalRing.ResidueField V) ⟶ T.Z, z₀ ≫ T.p = resPt V ≫ y →
      w _ z₀ = (Nat.card {z : T.Sec y // resPt V ≫ z.1 = z₀} : ℤ)

def CycRes : Prop := ∀ (p q n : ℕ) (Y : Scheme.{0}) (π : Γ(Y, ⊤)) (T : Fin (n + 1) → crystallineComparison.Corr p Y) (w : ∀ j, Wt (T j).Z),
  (∀ j, One (T j) (w j)) → PtId p q n π T →
  ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)]
    [IsAlgClosed (IsLocalRing.ResidueField V)], (p : V) ≠ 0 → ∀ y : Spec (CommRingCat.of V) ⟶ Y,
    crystallineComparison.GenPt π (y (IsLocalRing.closedPoint V)) →
    ∀ φ : IsLocalRing.ResidueField V →+* IsLocalRing.ResidueField V, (∀ a, φ a = a ^ q) → CycId q n T w _ φ (resPt V ≫ y)

def CycExt : Prop := ∀ (p q n : ℕ) (Y : Scheme.{0}) (T : Fin (n + 1) → crystallineComparison.Corr p Y) (w : ∀ j, Wt (T j).Z),
  (∀ j, IsWt (T j).p (w j)) → ∀ (Ω Ω' : Type) [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω'] (a : Ω →+* Ω')
    (φ : Ω →+* Ω) (φ' : Ω' →+* Ω'), a.comp φ = φ'.comp a → ∀ x : gp Ω ⟶ Y, CycId q n T w Ω φ x ↔ CycId q n T w Ω' φ' (sp a ≫ x)

def CycAll : Prop := ∀ (p f n : ℕ), p.Prime → ∀ (Y : Scheme.{0}) (π : Γ(Y, ⊤)) (T : Fin (n + 1) → crystallineComparison.Corr p Y)
  (w : ∀ j, Wt (T j).Z), (∀ j, One (T j) (w j)) → PtId p (p ^ f) n π T →
  (∀ y : Y, ∃ η ∈ Y.basicOpen (p : Γ(Y, ⊤)), η ⤳ y) → (∀ y ∈ Y.basicOpen (p : Γ(Y, ⊤)), y ∈ Y.basicOpen π) →
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : gp Ω ⟶ Y), crystallineComparison.GenPt π (pt x) →
    ∃ φ : Ω →+* Ω, (∀ a, φ a = a ^ p ^ f) ∧ CycId (p ^ f) n T w Ω φ x

def ESPt : Prop := ∀ (l : ℕ) [Fact l.Prime] (p f n : ℕ), p.Prime → ∀ (Y : Scheme.{0}) (π : Γ(Y, ⊤))
  (T : Fin (n + 1) → crystallineComparison.Corr p Y) (w : ∀ j, Wt (T j).Z), (∀ j, One (T j) (w j)) → PtId p (p ^ f) n π T →
  (∀ y : Y, ∃ η ∈ Y.basicOpen (p : Γ(Y, ⊤)), η ⤳ y) → (∀ y ∈ Y.basicOpen (p : Γ(Y, ⊤)), y ∈ Y.basicOpen π) →
  ∀ (S B : Scheme.{0}) (s : S ⟶ Y) (bS : S ⟶ B) [IsSeparated bS] [LocallyOfFiniteType bS] (Fr : S ⟶ S),
    IsUnit (l : Γ(S, ⊤)) → Dense {x : S | crystallineComparison.GenPt π (s x)} →
    (∀ (Ω : Type) [Field Ω] (x x' : gp Ω ⟶ S), x ≫ s = x' ≫ s → x ≫ bS = x' ≫ bS → x = x') → Fr ≫ bS = bS →
    (∀ (Ω : Type) [Field Ω] (φ : Ω →+* Ω), (∀ a, φ a = a ^ p ^ f) → ∀ x : gp Ω ⟶ S, x ≫ Fr ≫ s = twist φ Y (x ≫ s)) →
    ∀ (c : Fin (n + 1) → TranscendenceTraces.Corr S S) (v : ∀ j, (c j).Z ⟶ (T j).Z), (∀ j, IsPullback (v j) (c j).p (T j).p s) →
      (∀ j, (c j).f ≫ s = v j ≫ (T j).r) → (∀ j, (c j).f ≫ bS = (c j).p ≫ bS) → (∀ j, (c j).w = (w j).comap (v j)) →
      ∀ k i : ℤ, ∑ j : Fin (n + 1), ((co (p ^ f) j : ℤ) : ℚ_[l]) •
        ((c j).opQ l k i * (pullHQ l (sch.map Fr) k i : Module.End ℚ_[l] (HQ l (sch.obj S) k i)) ^ (n - j)) = 0

end UpperTheory.Gal.Mod

end
