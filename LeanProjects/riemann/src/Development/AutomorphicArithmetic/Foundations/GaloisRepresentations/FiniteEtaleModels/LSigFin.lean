import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsQuotTriv

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)

namespace UpperTheory.Gal.FiniteEtaleModels

def LGrp : Prop :=
  ∀ (Γ : Type) [Group Γ] (K K₀ K₁ KN KM : Subgroup Γ), KM ≤ KN → KN ≤ K → KN ≤ K₀ → KM ≤ K₁ → K₁ ≤ K₀ →
    (∀ u ∈ K₀, ∀ v ∈ KM, u * v * u⁻¹ ∈ KM) → (∀ u ∈ K₀, ∃ a ∈ K, a ∈ K₀ ∧ a⁻¹ * u ∈ K₁) → ∀ b₀ ∈ K, ∀ u ∈ K₀,
    Nat.card {cn : (K ⧸ KN.subgroupOf K) × (KN ⧸ KM.subgroupOf KN) //
      b₀⁻¹ * (cn.1.out : Γ) * (cn.2.out : Γ) * u⁻¹ ∈ K₁} = KM.relIndex (K ⊓ K₁)

def LPts : Prop :=
  ∀ (E : Type) [Field E] (Γ : Type) [Group Γ] (X : G3.Tower (Sp E) Γ) (O : Type) [CommRing O] [Algebra O E] (K K₀ K₁ KN : Subgroup Γ)
    (M N : X.ι) (Y Y' : Scheme.{0}) (pY : Y ⟶ Spec (CommRingCat.of O)) (π : X.Z N ⟶ Y) (π' : X.Z M ⟶ Y') (s : Y' ⟶ Y) (a b : _),
    X.K N = KN → KN ≤ K → KN ≤ K₀ → K₁ ≤ K₀ → π ≫ pY = X.q N ≫ gen O E →
    IsQuot X O K₀ M pY (π' ≫ s) → IsQuot X O K₁ M (s ≫ pY) π' → X.tr M N 1 a b ≫ π = π' ≫ s →
    (∀ u ∈ K₀, ∃ a ∈ K, a ∈ K₀ ∧ a⁻¹ * u ∈ K₁) → ∀ b₀ ∈ K,
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (z : sp Ω ⟶ X.Z N) (y' : sp Ω ⟶ Y'), y' ≫ s = z ≫ π →
      Nat.card {cx : (K ⧸ KN.subgroupOf K) × (sp Ω ⟶ X.Z M) // cx.2 ≫ X.tr M N 1 a b = z ∧ b₀⁻¹ * (cx.1.out : Γ) ∈ K₀ ∧
        ∀ a' b', cx.2 ≫ X.tr M M (b₀⁻¹ * (cx.1.out : Γ)) a' b' ≫ π' = y'} = (X.K M).relIndex (K ⊓ K₁)

def LSigPt : Prop :=
  ∀ (I : Type) (W : Scheme.{0}) (Ω : Type) [Field Ω],
    Function.Bijective fun x : I × (sp Ω ⟶ W) => x.2 ≫ Sigma.ι (fun _ : I => W) x.1

def LSigFin : Prop :=
  ∀ (I : Type) [Finite I] (W Z : Scheme.{0}) (f : W ⟶ Z), IsFinite f → Etale f →
    IsFinite (Sigma.desc fun _ : I => f) ∧ Etale (Sigma.desc fun _ : I => f)

def LCount : Prop :=
  ∀ (I B : Type) [Finite I] [Finite B] (W Z Y Y' : Scheme.{0}) (cls : I → B) (f : W ⟶ Z) (kc : I → (W ⟶ Y')) (π : Z ⟶ Y) (s : Y' ⟶ Y) (m : ℕ),
    IsFinite f → Etale f → IsFinite s → Etale s →
    (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (z : sp Ω ⟶ Z) (b : B) (y' : sp Ω ⟶ Y'), y' ≫ s = z ≫ π →
      Nat.card {cx : I × (sp Ω ⟶ W) // cx.2 ≫ f = z ∧ cls cx.1 = b ∧ cx.2 ≫ kc cx.1 = y'} = m) →
    ∀ h : (Sigma.desc fun _ : I => f) ≫ π = (Sigma.desc fun c : I => kc c ≫ Sigma.ι (fun _ : B => Y') (cls c)) ≫ Sigma.desc fun _ : B => s,
      FEt (pullback.lift _ _ h) m

def LIdx : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (N : ℕ), 0 < N → (L.KN N).relIndex (L.KN 1) ≠ 0

end UpperTheory.Gal.FiniteEtaleModels
