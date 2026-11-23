import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Conj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} [StarRing (𝓞 E)]
  {Ω : Type} [Field Ω]

def stdLat (A : Subring Ω) {d : ℕ} (T : ((Fin d → Ω) × (Fin d → Ω)) →ₗ[Ω] (Fin d → Ω) × (Fin d → Ω)) :
    Submodule A ((Fin d → Ω) × (Fin d → Ω)) :=
  Submodule.span A {y | ∃ y₀ : (Fin d → Ω) × (Fin d → Ω), (∀ i, y₀.1 i ∈ A ∧ y₀.2 i ∈ A) ∧ y = T y₀}

structure GermSys (t : SAB H X) (ξ : Spec (CommRingCat.of Ω) ⟶ X) {d : ℕ} (M : LieModel t.G ξ (Fin d → Ω)) where

  g₀ : GermAt t ξ d
  dir₀ : ∀ l, (M.pt (Pi.single l 1)).left = g₀.tg l
  act₀ : ∀ a v, M.pt ((rho g₀.B a).mulVec v) = M.pt v ≫ t.act.act a

  g : ∀ p : Cpt ξ, GermAt t (S := X.presheaf.stalk p.1) (X.fromSpecStalk p.1) d

  BK : Cpt ξ → Germ.FB Ω d (𝓞 E)
  mapK : ∀ p, IsMapOf (genMap ξ p) (g p).B (BK p)

  φ : Cpt ξ → Germ.Pt Ω 1 d

  ψ : Cpt ξ → Germ.Pt Ω 1 d

  lam : Cpt ξ → Germ.PS Ω 2 d
  iso : ∀ p, IsIso g₀.B (BK p) (φ p) (ψ p) (lam p)
  dir : ∀ p l, (M.pt ((lin (φ p) 1).mulVec (Pi.single l 1))).left =
    Spec.map (CommRingCat.ofHom (dualMap (genMap ξ p))) ≫ (g p).tg l
  gen : ∀ (p q : Cpt ξ) (h : q.1 ⤳ p.1), ∃ (B' : Germ.FB (X.presheaf.stalk q.1) d (𝓞 E))
    (φ' ψ' : Germ.Pt (X.presheaf.stalk q.1) 1 d) (lam' : Germ.PS (X.presheaf.stalk q.1) 2 d),
    IsMapOf (X.presheaf.stalkSpecializes h).hom (g p).B B' ∧ IsIso (g q).B B' φ' ψ' lam' ∧
      transH (φ p) (ψ p) (lam p) = transH (φ q) (ψ q) (lam q) ∘ₗ
        transH (fun i => MvPowerSeries.map (genMap ξ q) (φ' i)) (fun i => MvPowerSeries.map (genMap ξ q) (ψ' i))
          (MvPowerSeries.map (genMap ξ q) lam')
  loc : ∀ p : Cpt ξ, ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U →
    stdLat (regAt ξ q) (transH (φ p) (ψ p) (lam p)) = stdLat (regAt ξ q) (transH (φ q) (ψ q) (lam q))

def HFree {R : Type} [CommRing R] {d : ℕ} (B : Germ.FB R d (𝓞 E)) (r : ℕ) : Prop :=
  ∃ x : Fin r → (Fin d → R) × (Fin d → R),
    LinearIndependent R (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      rhoH B (RingOfIntegers.basis E q.2) (x q.1)) ∧
    Submodule.span R (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      rhoH B (RingOfIntegers.basis E q.2) (x q.1)) = ⊤

def HChar {R : Type} [CommRing R] [Nontrivial R] {d : ℕ} (B : Germ.FB R d (𝓞 E)) (r : ℕ) : Prop :=
  ∀ a : 𝓞 E, (rhoH B a).charpoly =
    ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom R)) ^ r

def GermSys.Gives {t : SAB H X} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {d : ℕ} {M : LieModel t.G ξ (Fin d → Ω)}
    (S : GermSys t ξ M) {ρ : 𝓞 E →+* Module.End Ω (Fin d → Ω)} {r : ℕ} (𝓗 : HodgeLat M.lat ρ H.bar r) : Prop :=
  (∀ a y, 𝓗.ρH a (y.1, dotProductBilin Ω Ω y.2) =
    ((rhoH S.g₀.B a y).1, dotProductBilin Ω Ω (rhoH S.g₀.B a y).2)) ∧
  ∀ (p : Cpt ξ) (y : (Fin d → Ω) × (Fin d → Ω)), (y.1, dotProductBilin Ω Ω y.2) ∈ 𝓗.HL p ↔
    y ∈ stdLat (regAt ξ p) (transH (S.φ p) (S.ψ p) (S.lam p))

end GlobalTheory.CompanionTheory.Ar.Flat
