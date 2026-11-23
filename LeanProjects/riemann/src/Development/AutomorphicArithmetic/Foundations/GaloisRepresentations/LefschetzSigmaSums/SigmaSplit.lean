import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelBaseChangeUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePowerMapOfTotalSpacesIsPullback
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HodgeTraceFromLefschetzAndGroupSide

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo
open GlobalTheory.UPel.HT.Gen.BaseChange (down)
open GlobalTheory.GalV (Splits)
open UpperTheory.Gal.Int.Geo (KS Lv Mem IsTrans TIso)

namespace UpperTheory.Gal.LocalSmoothExtension

def MapEq : Prop :=
  ∀ (G : GDatum) (R : Type) [CommRing R] [Algebra ℚ R] (b : GBase G R) (N : ℕ) (S₁ S₂ S₃ : Scheme.{0}) (s₁ : S₁ ⟶ Sp R)
    (s₂ : S₂ ⟶ Sp R) (s₃ : S₃ ⟶ Sp R) (o₁ : GObj b N s₁) (o₂ : GObj b N s₂) (o₃ : GObj b N s₃) (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃)
    (m₂ : GObjMap o₂ o₃ g),
    (∀ m₁ : GObjMap o₁ o₂ f, ∃ n : GObjMap o₁ o₃ (f ≫ g), n.φ = m₁.φ ≫ m₂.φ) ∧
    ∀ m : GObjMap o₁ o₃ (f ≫ g), ∃ n : GObjMap o₁ o₂ f, n.φ ≫ m₂.φ = m.φ

def ModelBc : Prop :=
  ∀ (G : GDatum) (R₁ R₂ : Type) [CommRing R₁] [CommRing R₂] [Algebra ℚ R₁] [Algebra ℚ R₂] (τ : R₁ →+* R₂) (gb₁ : GBase G R₁)
    (gb₂ : GBase G R₂) (hρ : gb₂.ρ = τ gb₁.ρ) (ht : ∀ i, gb₂.t i = τ.comp (gb₁.t i)) (N : ℕ) (M : GenModel gb₁ N),
    ∃ (M' : GenModel gb₂ N) (f : M'.X ⟶ M.X), IsPullback f M'.s M.s (spMap τ) ∧
      Nonempty (GObjMap (down hρ ht rfl M'.univ) M.univ f)

def HomEx : Prop :=
  ∀ (G : GDatum) (R : Type) [CommRing R] [Algebra ℚ R] (b : GBase G R) (N N' : ℕ) (S S₁ : Scheme.{0}) (s : S ⟶ Sp R)
    (s₁ : S₁ ⟶ Sp R) (f : S₁ ⟶ S) (o' : GObj b N' s) (o'' : GObj b N s) (o₁' : GObj b N' s₁) (o₁'' : GObj b N s₁)
    (m' : GObjMap o₁' o' f) (m'' : GObjMap o₁'' o'' f),
    (∀ ψ : o'.A ⟶ o''.A, IsMonHom ψ → ∃ ψ₁ : o₁'.A ⟶ o₁''.A, IsMonHom ψ₁ ∧ ψ₁.left ≫ m''.φ = m'.φ ≫ ψ.left) ∧
    (∀ ψ₁ ψ₂ : o₁'.A ⟶ o₁''.A, ψ₁.left ≫ m''.φ = ψ₂.left ≫ m''.φ → ψ₁ = ψ₂) ∧
    ∀ d : ℕ, ((𝟙 o₁'.A) ^ d).left ≫ m'.φ = m'.φ ≫ ((𝟙 o'.A) ^ d).left

def PolPull : Prop :=
  ∀ (G : GDatum) (R : Type) [CommRing R] [Algebra ℚ R] (b : GBase G R) (N N' : ℕ) (S S₁ : Scheme.{0}) (s : S ⟶ Sp R)
    (s₁ : S₁ ⟶ Sp R) (f : S₁ ⟶ S) (o' : GObj b N' s) (o'' : GObj b N s) (o₁' : GObj b N' s₁) (o₁'' : GObj b N s₁)
    (m' : GObjMap o₁' o' f) (m'' : GObjMap o₁'' o'' f) (ψ : o'.A ⟶ o''.A) (ψ₁ : o₁'.A ⟶ o₁''.A),
    ψ₁.left ≫ m''.φ = m'.φ ≫ ψ.left → ∀ c : ℕ, Nonempty (LBIso (Hecke.lbPow o'.P c) (o''.P.pull (Hecke.sq2 ψ))) →
      Nonempty (LBIso (Hecke.lbPow o₁'.P c) (o₁''.P.pull (Hecke.sq2 ψ₁)))

def TatePull : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [Algebra ℚ R] (b : GBase D.toG R) (N : ℕ) (S S₁ : Scheme.{0})
    (s : S ⟶ Sp R) (s₁ : S₁ ⟶ Sp R) (f : S₁ ⟶ S) (o : GObj b N s) (o₁ : GObj b N s₁) (m : GObjMap o₁ o f)
    (k : Type) [Field k] (t : Sp k ⟶ S₁) (I : TIso o (t ≫ f)),
    ∃ I₁ : TIso o₁ t, ∀ n y, (I₁.ev n y).left ≫ m.φ = (I.ev n y).left

def TransPull : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [CommRing R] [Algebra ℚ R]
    (b : GBase D.toG R) (N N' : ℕ) (S S₁ : Scheme.{0}) (s : S ⟶ Sp R) (s₁ : S₁ ⟶ Sp R) (f : S₁ ⟶ S), f ≫ s = s₁ →
    ∀ (o' : GObj b N' s) (o'' : GObj b N s) (o₁' : GObj b N' s₁) (o₁'' : GObj b N s₁)
    (m' : GObjMap o₁' o' f) (m'' : GObjMap o₁'' o'' f) (h : G.GAf) (ψ : o'.A ⟶ o''.A), IsTrans L h o' o'' ψ →
      ∃ ψ₁ : o₁'.A ⟶ o₁''.A, ψ₁.left ≫ m''.φ = m'.φ ≫ ψ.left ∧ IsTrans L h o₁' o₁'' ψ₁

def LegBc : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R₁ R₂ : Type) [CommRing R₁] [CommRing R₂]
    [Algebra ℚ R₁] [Algebra ℚ R₂] (τ : R₁ →+* R₂) (gb₁ : GBase D.toG R₁) (gb₂ : GBase D.toG R₂) (hρ : gb₂.ρ = τ gb₁.ρ)
    (ht : ∀ i, gb₂.t i = τ.comp (gb₁.t i)) (N N' : ℕ) (M : GenModel gb₁ N) (M' : GenModel gb₁ N') (P : GenModel gb₂ N)
    (P' : GenModel gb₂ N') (f : P.X ⟶ M.X) (f' : P'.X ⟶ M'.X), IsPullback f P.s M.s (spMap τ) →
    IsPullback f' P'.s M'.s (spMap τ) → ∀ (m : GObjMap (down hρ ht rfl P.univ) M.univ f)
    (m' : GObjMap (down hρ ht rfl P'.univ) M'.univ f') (h : G.GAf) (π : M'.X ⟶ M.X) (o : GObj gb₁ N M'.s)
    (ψ : M'.univ.A ⟶ o.A) (φ : GObjMap o M.univ π), π ≫ M.s = M'.s → IsTrans L h M'.univ o ψ →
    ∃ (π₁ : P'.X ⟶ P.X) (o₁ : GObj gb₂ N P'.s) (ψ₁ : P'.univ.A ⟶ o₁.A) (φ₁ : GObjMap o₁ P.univ π₁),
      π₁ ≫ P.s = P'.s ∧ IsTrans L h P'.univ o₁ ψ₁ ∧ π₁ ≫ f = f' ≫ π ∧
        (ψ₁.left ≫ φ₁.φ) ≫ m.φ = m'.φ ≫ ψ.left ≫ φ.φ

def PowComp : Prop :=
  ∀ (S₁ S₂ S₃ : Scheme.{0}) (A₁ : Over S₁) (A₂ : Over S₂) (A₃ : Over S₃) (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃) (e : S₁ ⟶ S₃)
    (φ : A₁.left ⟶ A₂.left) (χ : A₂.left ⟶ A₃.left) (ω : A₁.left ⟶ A₃.left) (h₁ : φ ≫ A₂.hom = A₁.hom ≫ f)
    (h₂ : χ ≫ A₃.hom = A₂.hom ≫ g) (h₃ : ω ≫ A₃.hom = A₁.hom ≫ e), f ≫ g = e → φ ≫ χ = ω → ∀ k : ℕ,
    GlobalTheory.KS.powMap f φ h₁ k ≫ GlobalTheory.KS.powMap g χ h₂ k = GlobalTheory.KS.powMap e ω h₃ k

def KNNormal : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (M : ℕ),
    (∀ k ∈ L.KN 1, ∀ u ∈ L.KN M, k * u * k⁻¹ ∈ L.KN M) ∧ (0 < M → (L.KN M).relIndex (L.KN 1) ≠ 0)

def cntFn {Γ : Type} [Group Γ] (K K' M : Subgroup Γ) (h y : Γ) : ℂ :=
  (Nat.card {k : K' ⧸ M.subgroupOf K' // h * (k.out : Γ) * y ∈ K} : ℕ)

def CntFn : Prop :=
  ∀ (Γ : Type) [Group Γ] (K K' M : Subgroup Γ) (h : Γ), K ≤ K' → (∀ k ∈ K', ∀ u ∈ M, k * u * k⁻¹ ∈ M) →
    M.relIndex K' ≠ 0 → (∀ k ∈ K', ∀ u ∈ M, h * k * u * (h * k)⁻¹ ∈ K) →
    (∀ k ∈ K, ∀ y, cntFn K K' M h (k * y) = cntFn K K' M h y ∧ cntFn K K' M h (y * k) = cntFn K K' M h y) ∧
    (∀ y, cntFn K K' M h y ≠ 0 → ∃ k ∈ K, ∃ c ∈ K', y⁻¹ = k * (h * c)) ∧
    {y : Γ ⧸ K | cntFn K K' M h y.out ≠ 0}.Finite

def CntSum : Prop :=
  ∀ (Γ : Type) [Group Γ] (K K' M : Subgroup Γ) (h : Γ), M ≤ K → K ≤ K' → (∀ k ∈ K', ∀ u ∈ M, k * u * k⁻¹ ∈ M) →
    (∀ k ∈ K', ∀ u ∈ M, h * k * u * (h * k)⁻¹ ∈ K) →
    ∀ [Fintype (K' ⧸ K.subgroupOf K')] (Δ : Type) [Fintype Δ] (r : Δ → Γ), (∀ x, r x ∈ K) →
    (∀ k ∈ K, ∃! x, k * (r x)⁻¹ ∈ M) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (P : Γ → V),
    (∀ k ∈ K, ∀ c ∈ K', P (k * (h * c)) = P (h * c)) →
      ∑ z : (K' ⧸ K.subgroupOf K') × Δ, P (h * (z.1.out : Γ) * r z.2) = ∑ᶠ y : Γ ⧸ K, cntFn K K' M h y.out • P y.out⁻¹

def SigmaFEt : Prop :=
  ∀ (Y Z : Scheme.{0}) (s : Y ⟶ Z) [IsFinite s] [Etale s] (I : Type) [Finite I],
    IsFinite (Sigma.desc fun _ : I => s) ∧ Etale (Sigma.desc fun _ : I => s)

def SigmaSplit : Prop :=
  ∀ (Y Z W : Scheme.{0}) (s : Y ⟶ Z) [IsFinite s] [Etale s] (I : Type) [Finite I] (c : W ⟶ Z) (Δ : Type) [Finite Δ]
    (σ : Δ → (W ⟶ Y)), Splits s c σ →
    Splits (Sigma.desc fun _ : I => s) c fun z : I × Δ => σ z.2 ≫ Sigma.ι (fun _ : I => Y) z.1

end UpperTheory.Gal.LocalSmoothExtension
