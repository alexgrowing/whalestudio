import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtUHInjective

noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV

open NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.Mem.Col2.T_notMem_QE : ∀ {X : _root_.Formalism.L2.Col.Fields} {Pr : _root_.Formalism.L2.Col.Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    {S : Set ℕ} (mu : _root_.Formalism.L2.DIV.Tup X.F X.E X.K S) (u : Pr.Word), Pr.Ok → _root_.Formalism.L2.Col.IsSel X sel → Pr.T u ∈ S →
      ∀ w ∈ _root_.Formalism.L2.Col.QE sel (mu : _root_.Formalism.L2.DIV.Chr X.F X.E X.K), (Pr.T u : 𝓞 X.E) ∉ w.asIdeal := by
  classical
  intro X Pr sel S mu u hOk hsel hT w hw hmem
  unfold _root_.Formalism.L2.Col.QE at hw
  split_ifs at hw with hfin
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    rw [Set.Finite.mem_toFinset] at hv
    have hmu := mu.2
    unfold _root_.Formalism.L2.DIV.tupGrp at hmu
    simp only [Subgroup.mem_inf, Subgroup.mem_iInf] at hmu
    have hA : _root_.Formalism.L2.DIV.GoodPl X.E S v := by
      by_contra hA
      exact hv (hmu.2 v hA)
    have hchar : _root_.Formalism.EigenvalueLevelCeiling.plc v ∉ S := by
      unfold _root_.Formalism.L2.DIV.GoodPl at hA
      exact hA.2.2
    have hv' : ((Pr.T u : ℕ) : 𝓞 X.F) ∈ v.asIdeal := by
      rw [← hsel v, Ideal.mem_comap]
      simpa using hmem
    have hp := hOk.T_prime u
    have hzero : ((Pr.T u : ℕ) : 𝓞 X.F ⧸ v.asIdeal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk v.asIdeal)]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hv'
    have : Nontrivial (𝓞 X.F ⧸ v.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr v.isPrime.ne_top
    have hdvd : ringChar (𝓞 X.F ⧸ v.asIdeal) ∣ Pr.T u := (ringChar.spec _ _).mp hzero
    have heq : ringChar (𝓞 X.F ⧸ v.asIdeal) = Pr.T u :=
      ((Nat.dvd_prime hp).mp hdvd).resolve_left CharP.ringChar_ne_one
    apply hchar
    unfold _root_.Formalism.EigenvalueLevelCeiling.plc
    rw [heq]
    exact hT
  · simp at hw

end GlobalTheory.Mem.Col2
