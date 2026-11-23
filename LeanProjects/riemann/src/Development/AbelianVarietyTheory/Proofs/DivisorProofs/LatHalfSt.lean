import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsBaseEqChain
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison

namespace GlobalTheory.ChainPts

section Pair

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

def IsHTPair (Z : LocM.Mdl Y i₀) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Vert.Model O}
    (h : B.X ⟶ Z.X) {r : ℕ} (x : Fin r → Letter Dw) (lw oo : EPres B (𝓞 E)) : Prop :=
  (∃ (π : Γ(B.X, ⊤)) (wl : lw.E ⟶ lw.E'), IsRootOfP p π (p - 1) ∧ lw.ψ ≫ wl = smulA _ π) ∧
    IsEqLatPres Z h x false lw ∧ IsEqLatPres Z h (fun k => x k.rev) true oo

end Pair

section admitted

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ} [Fact p.Prime] {hp : p.Prime}
  {W : ValuationSubring ℂ} {hW : (p : ℂ) ∈ W.nonunits}

def HTOne (z : AdmAt S κ hp hW) : Prop :=
  haveI := isDiscreteValuationRing_V z.Z.i.c hp hW
  ∀ c : (nmodel z.Z).Comp, ∃ (B₁ : Vert.Model (z.Z.i.c.V W)) (f₁ : Vert.Model.Hom B₁ ((nmodel z.Z).comp c)),
    GlobalTheory.IsNormalScheme B₁.X ∧ f₁.relDim = 0 ∧ ∃ lw oo : EPres B₁ (𝓞 D.host.E),
      IsHTPair z.Z (f₁.f ≫ (nmodel z.Z).compι c) (xAll S) lw oo

def HTHalf (z : AdmAt S κ hp hW) : Prop :=
  haveI := isDiscreteValuationRing_V z.Z.i.c hp hW
  ∀ c : (nmodel z.Z).Comp, ∃ (B₁ : Vert.Model (z.Z.i.c.V W)) (f₁ : Vert.Model.Hom B₁ ((nmodel z.Z).comp c)),
    GlobalTheory.IsNormalScheme B₁.X ∧ f₁.relDim = 0 ∧ ∀ (B : Vert.Model (z.Z.i.c.V W)) (g : Vert.Model.Hom B B₁),
      GlobalTheory.IsNormalScheme B.X → g.relDim = 0 → ∃ lw oo : EPres B (𝓞 D.host.E),
        IsHTPair z.Z ((g.comp f₁).f ≫ (nmodel z.Z).compι c) (xAll S) lw oo

def LatHalf (z : AdmAt S κ hp hW) : Prop :=
  haveI := isDiscreteValuationRing_V z.Z.i.c hp hW
  haveI := charP_residueField_of_mem_nonunits z.Z.i.c hp hW
  ∀ (c : (nmodel z.Z).Comp) (o : ℕ) (B₁ : Vert.Model (z.Z.i.c.V W)) (f₁ : Vert.Model.Hom B₁ ((nmodel z.Z).comp c)),
    GlobalTheory.IsNormalScheme B₁.X → f₁.relDim = 0 → ∃ (B : Vert.Model (z.Z.i.c.V W)) (g : Vert.Model.Hom B B₁),
      GlobalTheory.IsNormalScheme B.X ∧ g.relDim = 0 ∧ ∀ lw oo : EPres B (𝓞 D.host.E),
        IsHTPair z.Z ((g.comp f₁).f ≫ (nmodel z.Z).compι c) (xAll S) lw oo →
          ∃ Q : EqChain p B (𝓞 D.host.E) o, Q.lw = lw ∧ Q.oo = oo

end admitted

def HTOneSt : Prop := AtAll fun _ _ _ _ _ _ _ z => HTOne z

def HTHalfSt : Prop := AtAll fun _ _ _ _ _ _ _ z => HTHalf z

def LatHalfSt : Prop := AtAll fun _ _ _ _ _ _ _ z => LatHalf z

end GlobalTheory.ChainPts

end
