import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.ExtremeSph
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IwahoriDoubleCosets

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.CuspRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Tail.PExp

def DlBridge : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) (ϖ : (w.adicCompletion E)ˣ),
    ordL (ϖ : w.adicCompletion E) = 1 →
    valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) = uniformizer (w.adicCompletion E) ∧
    ∀ (N : ℕ) (x : Fin N → ℤ),
      (((deltaB (fun i => ϖ ^ x i))⁻¹ : ℝ) : ℂ) *
        (deltaHalf (w.adicCompletion E) (fun _ : Fin N => Unit)
          (leviTorus (w.adicCompletion E) (Fin N) fun i => ϖ ^ x i) : ℂ) =
        GlobalTheory.BCT.qh w ^ (∑ i : Fin N, ((N : ℤ) - 1 - 2 * (i : ℕ)) * x i)

def ExpToSat : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (c n : ℕ) (N : Fin c → ℕ)
    (h : ∑ i, N i = n) (σ : ∀ i, SmIrr (GL (Fin (N i)) (w.adicCompletion E)))
    (P : SmIrr (GL (Fin n) (w.adicCompletion E))) (ξ : Fin n → ℂˣ),
    IsSubquotient P.ρ (locProd h w σ) → PositivityTheory.Rg.BcB.N3.Mono ξ →
    (∃ y : Jacquet P.ρ (unipB (w.adicCompletion E) (Fin n)), y ≠ 0 ∧
      ∀ t, jacB P.ρ t y = (torusChar (fun i => unrChar (w.adicCompletion E) (ξ i)) t : ℂ) • y) →
    (∀ i, GlobalTheory.LGrp.IsSpherical (σ i).ρ (GlobalTheory.LFun.KGL w (N i))) ∧
      ∃ b : Fin c → Multiset ℂˣ, (∀ i, GlobalTheory.LFun.HasSatGL w (σ i).ρ (b i)) ∧ ∑ i, b i = Finset.univ.val.map ξ

end PositivityTheory.Rg.BcB.F.Tail.PExp

end
