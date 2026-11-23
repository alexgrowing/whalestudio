import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Leib

theorem nontrivial_piTensorProduct_iff {ι : Type} [Fintype ι] [DecidableEq ι] (M : ι → Type)
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] :
    Nontrivial (⨂[ℂ] i, M i) ↔ ∀ i, Nontrivial (M i) := by
  classical
  constructor
  · intro hN i
    by_contra hi
    rw [not_nontrivial_iff_subsingleton] at hi
    have h0 : ∀ x : ⨂[ℂ] i, M i, x = 0 := by
      intro x
      induction x using PiTensorProduct.induction_on with
      | smul_tprod r f =>
        rw [(PiTensorProduct.tprod ℂ).map_coord_zero i (Subsingleton.elim (f i) 0), smul_zero]
      | add x y hx hy => rw [hx, hy, add_zero]
    obtain ⟨x, y, hxy⟩ := hN.exists_pair_ne
    exact hxy ((h0 x).trans (h0 y).symm)
  · intro hM
    have hv : ∀ i, ∃ v : M i, v ≠ 0 := fun i => @exists_ne _ (hM i) 0
    choose v hv using hv
    have hφ : ∀ i, ∃ φ : Module.Dual ℂ (M i), φ (v i) ≠ 0 := fun i => by
      by_contra hc
      simp only [not_exists, ne_eq, not_not] at hc
      exact hv i ((Module.forall_dual_apply_eq_zero_iff ℂ (v i)).1 hc)
    choose φ hφ using hφ
    refine ⟨⟨PiTensorProduct.tprod ℂ v, 0, fun h => ?_⟩⟩
    have h1 := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap φ)) h
    simp only [PiTensorProduct.lift.tprod, map_zero, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply] at h1
    exact (Finset.prod_ne_zero_iff.2 fun i _ => hφ i) h1

theorem genericProdIff_of_whitHeredity (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : WhitHeredity k → GenericProdIff k := by
  intro hW h N d hd X _ _ π hsm
  obtain ⟨ψ, hψc, hψ1⟩ := GlobalTheory.LocGL.exists_continuous_addChar_ne_one k
  obtain ⟨e⟩ := hW ψ hψc hψ1 h N d hd X π hsm
  simp only [GlobalTheory.LocGL.isGeneric_iff_isGenericFor hψc hψ1, GlobalTheory.LocGL.IsGenericFor]
  exact Iff.trans ⟨fun hn => @Equiv.nontrivial _ _ e.symm.toEquiv hn, fun hn => @Equiv.nontrivial _ _ e.toEquiv hn⟩
    (nontrivial_piTensorProduct_iff _)

end GlobalTheory.CompanionTheory.Leib

end
