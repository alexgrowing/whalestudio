import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.MemMirabIff

open NumberField GlobalTheory.CuspRep UpperTheory.V.Sd UpperTheory.V.Af UpperTheory.V.Af.Nf

theorem UpperTheory.V.Af.Nf.kOpen :
    UpperTheory.V.Af.Nf.KOpen := by
  intro M hM
  refine ⟨Subgroup.isOpen_mono (H₁ := KLev ℚ 2 M) (fun g hg => ?_) (isOpen_KLev hM), fun u hu x hx => ?_⟩
  · obtain ⟨ha, hb, hc⟩ := mem_KLev.1 hg
    refine (memK M g).2 ⟨ha, hb, ?_, ?_⟩
    · simpa using hc 1 0
    · simpa using hc 1 1
  · refine (memK M _).2 ⟨?_, ?_, ⟨0, zero_mem _, ?_⟩, ⟨0, zero_mem _, ?_⟩⟩
    · refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨hu.1, hx⟩, Fin.forall_fin_two.2 ⟨zero_mem _, one_mem _⟩⟩
    · refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨hu.2, neg_mem (mul_mem hu.2 hx)⟩,
        Fin.forall_fin_two.2 ⟨zero_mem _, one_mem _⟩⟩
    · exact (mul_zero _).symm
    · exact (sub_self (1 : Af ℚ)).trans (mul_zero _).symm
