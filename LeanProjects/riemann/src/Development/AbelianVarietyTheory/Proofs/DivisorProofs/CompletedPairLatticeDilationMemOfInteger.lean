import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NabBaseChange
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.BaseCmp

theorem dil_mem_latP (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (ϖ : 𝓞 D.host.E) : ∀ y ∈ lattice₂ R i, dil i (ϖ : D.host.E) y ∈ lattice₂ R i := by
  intro y hy
  have hint : finPart D (incA D (ϖ : D.host.E)) ∈ intAE D := by
    have e : finPart D (incA D (ϖ : D.host.E)) = (1 : Af D.host.F) ⊗ₜ[D.host.F] (ϖ : D.host.E) := rfl
    rw [e]
    exact AddSubgroup.subset_closure ⟨1, fun v => by simpa using (one_mem (v.adicCompletionIntegers D.host.F)), ϖ, rfl⟩
  have h := GlobalTheory.LatticeStable.smul_mem_latO D (Vc D i) (Wc D i) _ _ _ (incA D (ϖ : D.host.E)) hint y hy
  exact h

end GlobalTheory.BaseCmp
