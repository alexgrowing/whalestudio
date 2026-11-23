import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.TwistedSlicesSquareIntegrable
import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.Development

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Rs

def LocSub : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N a d : ℕ) (V : Submodule ℂ (Sm E N)) (π : CuspSub E a), 1 ≤ N → IsDiscrete V →
  AscEmb V π d → ∀ (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E)))
    (σ' : SmIrr (GL (Fin N) (w.adicCompletion E))), π.IsLocComp w σ → IsLocCompGL V w σ' →
    ∃ hd : ∑ i : Fin d, (GlobalTheory.LocGL.spehFactor (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred) d i.rev).1 = N,
      ∃ f : σ'.ρ.IntertwiningMap (GlobalTheory.LocGL.prodIrr
        (fun i : Fin d => GlobalTheory.LocGL.spehFactor (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred) d i.rev) hd), f ≠ 0

def LocDual : Prop := ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [CharZero k] (N d : ℕ) (x : GlobalTheory.LocGL.IrrGL k) (σ' : SmIrr (GL (Fin N) k)), IsUnitarisable x.rep → IsUnitarisable σ'.ρ →
  ∀ (hd : ∑ i : Fin d, (GlobalTheory.LocGL.spehFactor x d i.rev).1 = N)
    (f : σ'.ρ.IntertwiningMap (GlobalTheory.LocGL.prodIrr (fun i : Fin d => GlobalTheory.LocGL.spehFactor x d i.rev) hd)), f ≠ 0 →
    ∃ hd' : ∑ i, (GlobalTheory.LocGL.spehFactor x d i).1 = N,
      ∃ g : (GlobalTheory.LocGL.prodIrr (GlobalTheory.LocGL.spehFactor x d) hd').IntertwiningMap σ'.ρ, Function.Surjective g

def Clause3Asc : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N a d : ℕ) (V : Submodule ℂ (Sm E N)) (π : CuspSub E a), 1 ≤ N → IsDiscrete V →
  π.IsUnitary → IsNormalised π → AscEmb V π d → ∀ w σ σ', π.IsLocComp w σ → IsLocCompGL V w σ' →
    GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred) d σ'.ρ

def AscSeed : Prop := AscAll ∧ Clause3Asc

end PositivityTheory.Rg.Rs

end
