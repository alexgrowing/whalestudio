import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelAdd

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts

namespace GlobalTheory.Mean4O

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F}

def ConjInv (A : Adl C Y) : Prop :=
  ∀ (σ σ' : F →+* ℂ) (y : Pts Y σ) (y' : Pts Y σ'), y'.1 = spMap (starRingEnd ℂ) ≫ y.1 →
    C.pn Y σ' A.D (A.m σ') (C.cx Y σ' (genAt A.D (under y'))) y' =
      C.pn Y σ A.D (A.m σ) (C.cx Y σ (genAt A.D (under y))) y

namespace Cover

variable (V : Cover Y)

def FinInd (A : Adl C Y) (B : LB V.X) (r : (B.pull V.j).ι → V.G.functionFieldˣ) : Prop :=
  IsRatSec (B.pull V.j) r ∧
    (∀ i, ∀ x ∈ (B.pull V.j).U i, UnitAt x (V.φ (genAt A.D (V.π x)) * r i)) ∧
    ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X)
      (i : (B.pull V.j).ι), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ B.U (i PUnit.unit) →
      A.lg v e y = Real.log (e.w (valAt z (V.φ (genAt A.D (below y.1)) * (r i : V.G.functionField))))

end Cover

def HessRel {e : ℕ} {M : Man e} {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}
    (ε : (k →+* ℂ) → Fin (M.n + 1)) (π : ∀ σ, CxPts p σ → M.X (ε σ)) (L : HermLB p) (P : M.Pot) : Prop :=
  ∀ (σ : k →+* ℂ) (c : AlgChart p σ e), ∀ y ∈ c.e.source, ∀ i, y ∈ ptsIn p σ (L.B.U i) →
    c.hess (L.φ σ) i y =
      ReciprocityTheory.L2DbarEstimates.cHess e (fun v => ((2 * (P (ε σ)).φ (π σ y) (π σ (c.e.symm v)) : ℝ) : ℂ)) (c.e y)

theorem hessRel_fnB {e : ℕ} {M : Man e} {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}
    (ε : (k →+* ℂ) → Fin (M.n + 1)) (π : ∀ σ, CxPts p σ → M.X (ε σ)) (u : M.Fun) (hu hc) :
    HessRel ε π (ArInt.fnB (M.pull ε π ((2 : ℝ) • u)) hu hc) fun a => LocPot.ofFun (u a) :=
  fun _ _ _ _ _ _ => rfl

end GlobalTheory.Mean4O
