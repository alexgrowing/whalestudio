import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots

open AlgebraicGeometry CategoryTheory

abbrev gen {X : Scheme.{0}} (T : CDVR) (zV : Spec (CommRingCat.of T.V) ⟶ X) : Spec (CommRingCat.of T.Fr) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) ≫ zV

def ReadsPt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (A : Subring Ω) (T : CDVR)
    (evT : A →+* T.Fr) (zV : Spec (CommRingCat.of T.V) ⟶ X) : Prop :=
  ∀ a : A, ValAt ξ (gen T zV) (a : Ω) (evT a)

def TriIn {F EC : Type} [Field F] [AddCommGroup EC] [Module F EC] {r : ℕ} (u : Fin r → EC) (d : Fin r → F)
    (v : Fin r → EC) : Prop :=
  ∀ i, ∃ cf : Fin r → F, cf i = d i ∧ (∀ j, i < j → cf j = 0) ∧ v i = ∑ j, cf j • u j

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {SS : Finset ℕ} {RM : Top.RootModel (CMType H) (Dw.p + Dw.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))} {Fx : FixedData Y Sys}

def IsFrameVec (Or : RootOrigin Y SS RM Fx) {T : CDVR} (io : c.F →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr)
    {zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X} {EC : Type} [AddCommGroup EC] [Module T.Fr EC]
    (MC : LieModel Or.𝔐.t.G (gen T zV) EC) (w : EC) (s : CMType H ⊕ CMType H) (i : Fin (labelRk Dw s)) : Prop :=
  letI := io.toAlgebra
  (MC.pt w).left ≫ Or.𝔐.m.φ = Small.tanY Y zT (Small.labelC s) (Small.labelFin Dw s i)

def lieEig (Or : RootOrigin Y SS RM Fx) {T : CDVR} {zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X} {EC : Type}
    [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] (MC : LieModel Or.𝔐.t.G (gen T zV) EC)
    [IsScalarTower T.V T.Fr EC] (ρC : 𝓞 E →+* Module.End T.Fr EC) (σ : 𝓞 E →+* T.V) : Submodule T.V EC :=
  Or.𝔐.M.fibAt Or.𝔐.M.lat zV MC ⊓ (eigSp ρC ((algebraMap T.V T.Fr).comp σ)).restrictScalars T.V

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots
