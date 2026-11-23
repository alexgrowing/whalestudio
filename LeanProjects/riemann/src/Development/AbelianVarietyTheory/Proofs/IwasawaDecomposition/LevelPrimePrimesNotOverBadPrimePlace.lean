import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelNotMemRowSG
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ExistsIntegralMulOrderElement
import Formalism.LocalToGlobal.Columns.RecLevelLocP
import Formalism.LocalToGlobal.Columns.DecoFin
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.AdT

theorem vT_notOver_SBof : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (a : I.ι) (P : SBof I a) (v : HeightOneSpectrum (𝓞 B.host.F)), Formalism.L2.Col.IsOver v P.1 → ∀ (u : B.Word), ∀ P' ∈ (B.primes X).vT u, ¬ Formalism.L2.Col.IsOver v P' := by
  intro B X I hI a P v hP u P' hP' hv'
  have hok := (GlobalTheory.BasePrimes.primes_ok B X).1
  have hT : ((B.primes X).T u : 𝓞 B.fields.E) ∉ P.1.asIdeal :=
    GlobalTheory.MuOffMove.level_notMem_rowSG hok hI.sel_ok (hI.T_mem u) P.2
  have hpi : (B.primes X).piT u ∈ P'.asIdeal := Formalism.L2.Col.decoFin_mem_of_mem_divs hP'
  have hTP' : ((B.primes X).T u : 𝓞 B.fields.E) ∈ P'.asIdeal := by
    rw [← hok.piT_norm u]
    exact Ideal.mul_mem_right _ _ hpi
  rcases Formalism.L2.Col.rll_over_cases B.sp.cm hP hv' with h | h
  · subst h
    exact hT hTP'
  · subst h
    rw [Formalism.L2.Col.mem_conjP, map_natCast] at hTP'
    exact hT hTP'

end GlobalTheory.Mem.Col2.AdT
