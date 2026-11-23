import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrConjApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option synthInstance.maxHeartbeats 400000
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.FrameTransport.IntSwap

theorem toFinE_mem_intAd {D : D7} {x : StandardLatticesGL3.AE D} (hx : x ∈ StandardLatticesGL3.OhE D) :
    GlobalTheory.BotFormula.toFinE D x ∈ Formalism.UG.intAd D.host.E := by
  have key : ∀ y : StandardLatticesGL3.AE D,
      (Algebra.TensorProduct.comm ℚ D.host.E (FiniteAdeleRing (𝓞 ℚ) ℚ)) y ∈
        AddSubgroup.closure {z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af ℚ ⊗[ℚ] D.host.E |
          ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf ℚ, ∃ o : 𝓞 D.host.E, z = a ⊗ₜ[ℚ] (o : D.host.E)} →
      GlobalTheory.BotFormula.toFinE D y ∈ Formalism.UG.intAd D.host.E := fun y hy =>
    (GlobalTheory.LFun.mem_int_iff _).1 hy
  have hle : StandardLatticesGL3.OhE D ≤ (Formalism.UG.intAd D.host.E).comap (GlobalTheory.BotFormula.toFinE D).toRingHom := by
    refine Subring.closure_le.2 ?_
    rintro y (⟨⟨e, he⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩)
    · obtain ⟨o, rfl⟩ := he
      refine key _ (AddSubgroup.subset_closure ⟨1, fun v => ?_, o, rfl⟩)
      exact (one_mem (v.adicCompletionIntegers ℚ) : _)
    · refine key _ (AddSubgroup.subset_closure ⟨a, fun v => ha v, 1, ?_⟩)
      rfl
  exact hle hx

theorem swapAE_mem_intAf {D : D7} {y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E}
    (hy : y ∈ AddSubgroup.closure {z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E |
      ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F, ∃ o : 𝓞 D.host.E, z = a ⊗ₜ[D.host.F] (o : D.host.E)}) :
    Lev.swapAE D y ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have hle : AddSubgroup.closure {z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E |
      ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F, ∃ o : 𝓞 D.host.E, z = a ⊗ₜ[D.host.F] (o : D.host.E)} ≤
      (Formalism.L2.Herm.intAf D.host.F D.host.E).toAddSubgroup.comap (Lev.swapAE D).toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨a, ha, o, rfl⟩
    have e : Lev.swapAE D (a ⊗ₜ[D.host.F] (o : D.host.E)) =
        ((o : D.host.E) ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F)) *
          ((1 : D.host.E) ⊗ₜ[D.host.F] (a : Formalism.L2.Herm.Af D.host.F)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rfl
    show Lev.swapAE D (a ⊗ₜ[D.host.F] (o : D.host.E)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E
    rw [e]
    refine mul_mem (Subring.subset_closure (Or.inl ⟨⟨(o : D.host.E), o, rfl⟩, rfl⟩))
      (Subring.subset_closure (Or.inr ⟨⟨a, fun v => ha v⟩, rfl⟩))
  exact hle hy

end GlobalTheory.FrameTransport.IntSwap

theorem GlobalTheory.FrameTransport.adSwap_mem_intAf_of_OhE : ∀ {D : D7} (x : StandardLatticesGL3.AE D), x ∈ StandardLatticesGL3.OhE D →
    GlobalTheory.FrameTransport.adSwap D x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  intro D x hx
  have h1 := GlobalTheory.FrameTransport.IntSwap.toFinE_mem_intAd hx
  have h2 : GlobalTheory.BotFormula.toAfE D x ∈ AddSubgroup.closure
      {z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E |
        ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F, ∃ o : 𝓞 D.host.E, z = a ⊗ₜ[D.host.F] (o : D.host.E)} := by
    refine (GlobalTheory.LFun.mem_int_iff _).2 fun P => ?_
    have e : GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (GlobalTheory.BotFormula.toAfE D x) = GlobalTheory.BotFormula.toFinE D x :=
      (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).apply_symm_apply _
    rw [e]
    exact h1 P
  exact GlobalTheory.FrameTransport.IntSwap.swapAE_mem_intAf h2
