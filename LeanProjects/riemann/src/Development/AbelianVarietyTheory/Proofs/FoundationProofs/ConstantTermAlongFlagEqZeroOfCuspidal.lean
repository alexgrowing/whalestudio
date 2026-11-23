import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemExtSubSpanDepth
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurePreservingConj

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.Mem.Th GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Cusp

theorem constTerm_eq_zero_of_mem_cuspCont (D : D7) (V : HSp D) (φ : GA D V → ℂ) (h : φ ∈ cuspCont V) (𝔉 : IsoFlag V)
    (h𝔉 : 𝔉.Proper) : constTerm 𝔉 φ = 0 := by
  have hi : (⟨1, Nat.succ_lt_succ h𝔉⟩ : Fin (𝔉.k + 1)) ≠ 0 := Fin.ne_of_val_ne one_ne_zero
  have h0 : constTermOn (GQ V) (NA (.single (𝔉.isIsotropic hi))) φ = 0 :=
    (isCuspFun_iff h.2.1).1 h.2.2 _ (𝔉.isIsotropic hi)
  funext x
  refine (Stages.constTermOn_stages (GA D V) (GQ V) (NA 𝔉) (NA (.single (𝔉.isIsotropic hi)))
    (𝔉.unip_single_le D.sp.cm _ hi) (fun p hp n hn => IsoFlag.conj_mem_unip ?_ hn) (cocompact_flag D V 𝔉)
    (cocompact_single _) φ h.2.1 h.1 x).trans ?_
  · rw [IsoFlag.par_single]
    exact 𝔉.par_le_parab D.sp.cm _ _ (𝔉.unip_le_par D.sp.cm _ hp)
  · rw [h0]
    exact (cocompact_flag D V 𝔉).constTermOn_const 0 x

end GlobalTheory.Cusp
