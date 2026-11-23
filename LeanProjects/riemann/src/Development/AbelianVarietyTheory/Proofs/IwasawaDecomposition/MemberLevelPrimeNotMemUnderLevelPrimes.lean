import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormOneFiniteAdeleDetClassOfIsDetLift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LevTwist

theorem T_notMem_under_uSG : ∀ (B : Base) (X : PreX B.toPre) (I : ColIn B X), I.Ok → ∀ (u : B.Word)
    (P : HeightOneSpectrum (𝓞 B.host.E)), P ∈ uSG (B.primes X).vGs I.SQ →
    (B.T u : 𝓞 B.host.F) ∉ (P.under (𝓞 B.host.F)).asIdeal := by
  classical
  intro B X I hI u P hP hm
  have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1
  have hE : (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∈ P.asIdeal := by
    have h1 : ((B.T u : ℕ) : 𝓞 B.host.F) ∈ P.asIdeal.under (𝓞 B.host.F) := hm
    rw [Ideal.under_def, Ideal.mem_comap, map_natCast] at h1
    exact h1
  rcases Finset.mem_union.1 hP with h | h
  · exact T_notMem_vGs hPr u ⟨P, h⟩ hE
  · have hg := (good_of_mem hI h).2
    have e := (ReadTwist.plc_under_eq_iff (F := B.host.F) P (hPr.T_prime u)).2 hE
    refine hg.2.2 ?_
    rw [e]
    exact hI.T_mem u

end GlobalTheory.Mem.LevTwist
