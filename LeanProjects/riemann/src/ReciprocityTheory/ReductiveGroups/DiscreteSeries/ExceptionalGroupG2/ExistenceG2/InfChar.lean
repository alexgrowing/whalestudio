import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.InfChar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.SigLamKTypeBounds
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.PropsEquiv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataClosGenEqTop
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CasimirGapAtNoncompactWeight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.LayerBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.BochIneq
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CrossOpSlotBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.NcVOneDecomp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CrossOpEigGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.Numerics
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.KhwEqZeroSharp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.RigidUniversal
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.RigidOrth
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.RorthFunctionalEqZero
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.ClosGenStable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.MultOne
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.PropsLowK
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.PropsKfin
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.PropsAdm

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.G2
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool}

section Fun

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

end Fun

section Scalar

end Scalar

section Good

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable {φ : E →L[ℂ] ℂ}

end Good

section Central

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

end Central

variable {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}

theorem capelli_sigLam (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hcap : ∀ (Y : ℂ) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
      Formalism.QuantumDeterminants.capelli ε (Y + ((n : ℂ) - 1) / 2) Ψ g = Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • Ψ g)
    (Y : ℂ) (x : smD ε (rreg ε)) (hx : x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) :
    Formalism.REAL.qdet (smE ε (rreg ε)) (Y + ((n : ℂ) - 1) / 2) x =
      Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • x := by
  have hE : IsGlRep (smE ε (rreg ε)) := (isDerivedOn_smE (rreg_isURepOn ε)).glRep
  refine icx_genSub_eigen (smE ε (rreg ε)) (datumV ε Ψ v₀) (Formalism.REAL.qdet (smE ε (rreg ε)) (Y + ((n : ℂ) - 1) / 2))
    (Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y)
    (fun a b => Formalism.REAL.qDetCentral (Module.End ℂ (smD ε (rreg ε))) n (smE ε (rreg ε)) hE _ a b) ?_ x hx
  intro y hy
  obtain ⟨v, hv⟩ := (mem_datumV_iff hP v₀ y).1 hy
  exact icx_val (icxGood_qdet (icx_good_datum hP hv) _) hv _ fun g hg => hcap Y g hg

end ReciprocityTheory.ChartRestriction.DS.G2
