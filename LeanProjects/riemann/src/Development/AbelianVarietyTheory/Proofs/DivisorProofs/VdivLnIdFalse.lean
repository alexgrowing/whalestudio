import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasChainW
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteTwistingNotIsGenerator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmEx

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.LocM

namespace GlobalTheory.PairTerm

section Lines

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

variable (Dw) in

abbrev Ln : Type := Bool × {st : ((E →+* ℂ) × ℕ) ⊕ ℕ // (letterOf Dw st).isSome}

def lnSym (a : ℕ → Bool) (R : Option ℝ) : Ln Dw → (Sym E →₀ ℤ)
  | (false, st) => Finsupp.single (a, R, st.1) 1
  | (true, st) => Finsupp.single (a, R, st.1) (-1)

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  (z : admitted Y i₀)

def lnLB (b : Bool) : Ln Dw → FinLB z.Z.X
  | (false, st) => (z.line b st.1 _ (Option.some_get st.2).symm).L
  | (true, st) => (z.line b st.1 _ (Option.some_get st.2).symm).L.dual

def lnId (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) : ∀ l : Ln Dw, Pad.GenIso z.Z (lnLB z false l) (lnLB z true l)
  | (false, st) => z.genId hp hW (Option.some_get st.2).symm
  | (true, st) => NModel.GenIso.dual (z.genId hp hW (Option.some_get st.2).symm)

theorem lnLB_false (b : Bool) (st) : lnLB z b (false, st) = z.stepLB b st.1 := (z.stepLB_of_some _ _).symm

theorem lnLB_true (b : Bool) (st) : lnLB z b (true, st) = (z.stepLB b st.1).dual :=
  congrArg FinLB.dual (z.stepLB_of_some _ _).symm

theorem vdiv_lnId_false (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (d : ℕ) (st) {x : Letter Dw}
    (h : letterOf Dw st.1 = some x) :
    vdiv hp hW d _ _ (lnId z hp hW (false, st)) = vdiv hp hW d _ _ (z.genId hp hW h) := by
  obtain rfl : (letterOf Dw st.1).get st.2 = x := Option.some.inj ((Option.some_get st.2).trans h)
  rfl

theorem vdiv_lnId_true (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (d : ℕ) (st) {x : Letter Dw}
    (h : letterOf Dw st.1 = some x) :
    vdiv hp hW d _ _ (lnId z hp hW (true, st)) = -vdiv hp hW d _ _ (z.genId hp hW h) := by
  rw [← vdiv_lnId_false z hp hW d st h]
  exact vdiv_dual hp hW d _ _ _

end Lines

def PairSt : Prop := ∀ (D : D7) (O : Setup D), O.Core → ∀ (p : ℕ) [Fact p.Prime]
  (W : Formalism.L2.Geo.PlL D p → ValuationSubring ℂ) (hW : ∀ la, (p : ℂ) ∈ (W la).nonunits),
  (∀ la (x : D.what₂.LL), D.what₂.embLL x ∈ W la ↔ IsDedekindDomain.HeightOneSpectrum.valuation D.what₂.LL la.1 x ≤ 1) →
  ∀ (z : ∀ la, AdmAt O.S O.κ (Fact.out : p.Prime) (hW la)) (Sx : Finset ℕ) (R : ℝ), 2 ≤ R →
  ∀ (l : Ln O.S.Dw) (ν : Fin (dimFl D.what₂.Tau O.N) → Bool × Ln O.S.Dw),
    ∑ c : O.s.Comp,
      ((arIn O.s O.Φ O.met.hm).num c (lnSym (Function.update (ArIn.ind Sx) p false) (some R) l ::ₘ
          Finset.univ.val.map fun i => lnSym (Function.update (ArIn.ind Sx) p (ν i).1) (some R) (ν i).2) -
        (arIn O.s O.Φ O.met.hm).num c (lnSym (Function.update (ArIn.ind Sx) p true) (some R) l ::ₘ
          Finset.univ.val.map fun i => lnSym (Function.update (ArIn.ind Sx) p (ν i).1) (some R) (ν i).2)) =
      Real.log p * (letI := Formalism.L2.Geo.finPl D p; ∑ la, Formalism.L2.Geo.wtL D p la *
        ((((ithOf Fact.out (hW la) (z la).Z (dimFl D.what₂.Tau O.N)).capDeg
          (vdiv Fact.out (hW la) _ _ _ (lnId (z la) Fact.out (hW la) l))
          (∏ i, (lnLB (z la) (ν i).1 (ν i).2).c1) : ℚ) : ℝ) / (cov (z la) : ℝ)))

end GlobalTheory.PairTerm

end
