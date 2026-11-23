import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistAtEach
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFConstMul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section

namespace GlobalTheory.GSep.TransTerms

variable {I : Type}

def TorChar {X₁ : GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {t : X → V} {δ : I → X → X}
    (𝔪 : GMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ) : Prop :=
  χ ^ (X₁.S.r * X₁.S.N) = 1 ∧ ∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ →
    ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A),
      p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧
      x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left

def TransExp {X₁ : GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {t : X → V} {δ : I → X → X}
    (𝔪 : GMem X₁ z₁ act V ev X t δ) (x₀ a τ : X₁.S.Gam) (e : ℕ) : Prop :=
  ∀ χ, TorChar 𝔪 τ χ → ∀ (C : Type) (lab : C → X₁.S.Gam) (T : X → C → V), 𝔪.Terms x₀ lab T →
    ∀ c, lab c = a → ∀ (C' : Type) (lab' : C' → X₁.S.Gam) (T' : X → C' → V), 𝔪.Terms x₀ lab' T' →
    ∀ c', lab' c' = a + τ → ∀ mu : X,
      ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) * algebraMap V (FractionRing V) (T mu c) =
        𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)) * algebraMap V (FractionRing V) (T' mu c')

theorem sumF_comp_equiv {R : Type} [CommRing R] [IsDomain R] {J : Ideal R} {K : Type} [Field K]
    [Algebra (FractionRing R) K] {Ix Jx : Type} {x : Ix → K} {s : K} (e : Jx ≃ Ix) (h : SumF J K x s) :
    SumF J K (fun j => x (e j)) s := by
  letI : Module R K := Module.compHom K (algebraMap R (FractionRing R))
  obtain ⟨N, hN, hs, hx, hlim⟩ := h
  refine ⟨N, hN, hs, fun j => hx _, fun k => ?_⟩
  classical
  obtain ⟨S, hS⟩ := hlim k
  refine ⟨S.map e.symm.toEmbedding, fun T hT => ?_⟩
  have hsub : S ⊆ T.map e.toEmbedding := by
    intro a ha
    have := hT (Finset.mem_map_of_mem e.symm.toEmbedding ha)
    exact Finset.mem_map.2 ⟨e.symm a, this, by simp⟩
  have := hS _ hsub
  rwa [Finset.sum_map] at this

end GlobalTheory.GSep.TransTerms
