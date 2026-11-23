import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

namespace GlobalTheory.BundleChernComparison

def LocalW {D : D7} {p : ℕ} [Fact p.Prime] {N : ℕ} {rk : Emb D p → ℕ} (M : DV.Mdl D p N rk) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ m : ℕ, m + k = dimFl D.what₂.Tau N + 1 → ∀ Q : MvPolynomial M.Z.LB ℚ, Q.IsHomogeneous m →
    chk M.lieW k (evQ _ Q) + chk M.omW k (evQ _ Q) =
      (((p : ℝ) ^ k - 1)⁻¹ - ((p : ℝ) - 1)⁻¹) * chDiv M.lieW.x (k - 1) (evQ _ Q)

def HasChainW {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ} [Fact p.Prime] {hp : p.Prime}
    {W : ValuationSubring ℂ} {hW : (p : ℂ) ∈ W.nonunits} (z : AdmAt S κ hp hW) (jc : KW p →+* ℂ) : Prop :=
  haveI := isDiscreteValuationRing_V z.Z.i.c hp hW
  haveI := charP_residueField_of_mem_nonunits z.Z.i.c hp hW
  ∀ c : (nmodel z.Z).Comp, ∃ (B : Vert.Model (z.Z.i.c.V W)) (f : Vert.Model.Hom B ((nmodel z.Z).comp c))
    (Ch : Chain p B (id : Unit → Unit) 1), GlobalTheory.IsNormalScheme B.X ∧ f.relDim = 0 ∧
      (Ch.lw ()).r = D.R.f * N ∧ (Ch.oo ()).r = D.R.f * N ∧
      Reads p (mdlOf z jc).lieW (fun x => picSymPull f.f (picSymPull ((nmodel z.Z).compι c) x))
        (fun d => Vert.Model.vPullQ f.comp_str (NModel.vResQ c d))
        (haveI := (Ch.lw ()).iso; (Vert.Model.GenIso.ofHom (Ch.lw ()).ψ).symm) ∧
      Reads p (mdlOf z jc).omW (fun x => picSymPull f.f (picSymPull ((nmodel z.Z).compι c) x))
        (fun d => Vert.Model.vPullQ f.comp_str (NModel.vResQ c d))
        (haveI := (Ch.oo ()).iso; Vert.Model.GenIso.ofHom (Ch.oo ()).ψ)

def TermW {D : D7} (Y : ShimX D.what₂.Tau) (p : ℕ) [Fact p.Prime] {ι : Type} [Fintype ι] (w : ι → ℝ)
    (jc : ι → (KW p →+* ℂ)) (M : ∀ la, DV.Mdl D p Y.N (rkOf (PsiOf D (jc la)) Y.N Y.j))
    (rt : ∀ la, Bool × Rt D.what₂.Tau Y.N → (M la).Z.LB) : Prop :=
  (∑ la, w la = 1) ∧ ∀ (Sx : Finset ℕ) (R : ℝ), 2 ≤ R → ∀ (k m : ℕ), 1 ≤ k → m + k = dimFl D.what₂.Tau Y.N + 1 →
    ∀ G : MvPolynomial (Vm D.what₂.Tau Y.N) ℚ, G.IsWeightedHomogeneous (wt D.what₂.Tau Y.N) m →
      Y.arMix Sx R p (dCh D.what₂.Tau Y.N k * toR G) = Real.log p * ∑ la, w la *
        ((chk (M la).lieW k (evC (M la) (rt la) G) + chk (M la).omW k (evC (M la) (rt la) G)) / ((M la).cov : ℝ))

def ConsW {D : D7} {p : ℕ} [Fact p.Prime] {N : ℕ} {rk : Emb D p → ℕ} (M : DV.Mdl D p N rk)
    (rt : Bool × Rt D.what₂.Tau N → M.Z.LB) (j : ℕ) (chern : MvPolynomial (Rt D.what₂.Tau N) ℝ →ₗ[ℝ] ℝ) : Prop :=
  ∀ m : ℕ, m + 1 = dimFl D.what₂.Tau N → ∀ G : MvPolynomial (Vm D.what₂.Tau N) ℚ,
    G.IsWeightedHomogeneous (wt D.what₂.Tau N) m →
    chDiv M.lieW.x 1 (evC M rt G) / (M.cov : ℝ) = chern (chLieA D N j 1 * collapse D N (toR G))

def AtAll (Q : ∀ (D : D7) (O : Setup D) (p : ℕ) [Fact p.Prime] (W : ValuationSubring ℂ) (hW : (p : ℂ) ∈ W.nonunits)
    (_ : KW p →+* ℂ) (_ : AdmAt O.S O.κ (Fact.out : p.Prime) hW), Prop) : Prop :=
  ∀ (D : D7) (O : Setup D), O.Core → ∀ (p : ℕ) [Fact p.Prime] (W : ValuationSubring ℂ) (hW : (p : ℂ) ∈ W.nonunits)
    (jc : KW p →+* ℂ), Pin W jc → ∀ z : AdmAt O.S O.κ (Fact.out : p.Prime) hW, Q D O p W hW jc z

def ChainWSt : Prop := AtAll fun _ _ _ _ _ _ jc z => HasChainW z jc

def ConsWSt : Prop := AtAll fun _ O _ _ _ _ jc z => ConsW (mdlOf z jc) (rootOf z jc) O.Y.j O.Y.chern

def TermWSt : Prop := ∀ (D : D7) (O : Setup D), O.Core → ∀ (p : ℕ) [Fact p.Prime],
  ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (W : ι → ValuationSubring ℂ) (hW : ∀ la, (p : ℂ) ∈ (W la).nonunits)
    (jc : ι → (KW p →+* ℂ)) (z : ∀ la, AdmAt O.S O.κ (Fact.out : p.Prime) (hW la)), (∀ la, Pin (W la) (jc la)) ∧
    TermW O.Y p w jc (fun la => mdlOf (z la) (jc la)) (fun la => rootOf (z la) (jc la))

end GlobalTheory.BundleChernComparison

end
