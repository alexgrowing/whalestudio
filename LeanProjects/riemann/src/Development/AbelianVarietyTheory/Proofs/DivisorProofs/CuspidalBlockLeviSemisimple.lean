import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivPiExteriorTensorBlockLevi
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSemisimpleRepresentationOfISupRangeEquivariant
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.CuspBlock

namespace GlobalTheory.CuspBlock

theorem isSemisimple_restrict_mid : GlobalTheory.Published.BernsteinZelevinskyFiniteness →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (l n N : ℕ)
    (Z : Type) [AddCommGroup Z] [Module ℂ Z]
    (τ : Representation ℂ (GlobalTheory.SmGL.Levi k (fun j : Fin 3 => Fin (GlobalTheory.CuspBlock.tripSizes l n N j))) Z),
    GlobalTheory.PRep.IsSmooth τ → τ.IsIrreducible →
      Representation.IsSemisimpleRepresentation (τ.comp (GlobalTheory.CuspBlock.midHom k l n N)) := by
  intro hBZ k _ _ _ _ l n N Z _ _ τ hs hi
  let τ' : GlobalTheory.SmGL.IrrRep (GlobalTheory.SmGL.Levi k (fun j : Fin 3 => Fin (GlobalTheory.CuspBlock.tripSizes l n N j))) :=
    ⟨Z, τ, hs, hi⟩
  obtain ⟨s, ⟨E⟩⟩ := GlobalTheory.LeviFactor.exists_equiv_piTensor_levi hBZ k (Fin 3) _ τ'

  have hs1 : ((s 1).ρ).IsSemisimpleRepresentation := by
    haveI := (s 1).irr
    exact (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).2 inferInstance
  have hP : Representation.IsSemisimpleRepresentation ((GlobalTheory.SmGL.piTensor fun j => (s j).ρ).comp (GlobalTheory.CuspBlock.midHom k l n N)) := by
    refine GlobalTheory.ClassFin.isSemisimpleRepresentation_of_iSup_range _ _ _ (∀ j, (s j).V) (fun _ => (s 1).V)
      (fun _ => (s 1).ρ) (fun f => (PiTensorProduct.tprod ℂ).toLinearMap f 1) (fun _ => hs1) ?_ ?_
    · intro f g v
      simp only [MultilinearMap.toLinearMap_apply, MonoidHom.comp_apply, GlobalTheory.SmGL.piTensor_tprod]
      congr 1
      funext a
      by_cases ha : a = 1
      · subst ha
        simp only [Function.update_self]
        have hm1 : midHom k l n N g 1 = (g : GL (Fin (tripSizes l n N 1)) k) :=
          Pi.mulSingle_eq_same (M := fun j : Fin 3 => GL (Fin (tripSizes l n N j)) k) 1 g
        rw [hm1]
        rfl
      · simp only [Function.update_of_ne ha]
        have hma : midHom k l n N g a = 1 :=
          Pi.mulSingle_eq_of_ne (M := fun j : Fin 3 => GL (Fin (tripSizes l n N j)) k) ha g
        rw [hma, map_one]
        rfl
    · rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
      rintro _ ⟨f, rfl⟩
      refine Submodule.mem_iSup_of_mem f ⟨f 1, ?_⟩
      simp
  refine GlobalTheory.ClassFin.isSemisimpleRepresentation_of_iSup_range _ _ _ Unit _
    (fun _ => (GlobalTheory.SmGL.piTensor fun j => (s j).ρ).comp (GlobalTheory.CuspBlock.midHom k l n N))
    (fun _ => E.toLinearEquiv.symm.toLinearMap) (fun _ => hP) ?_ ?_
  · intro _ g v
    apply E.toLinearEquiv.injective
    have h := LinearMap.congr_fun (E.isIntertwining' (GlobalTheory.CuspBlock.midHom k l n N g)) (E.toLinearEquiv.symm v)
    simp only [LinearMap.comp_apply] at h
    simp only [MonoidHom.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    exact (h.trans (congrArg _ (E.toLinearEquiv.apply_symm_apply v))).symm
  · rw [iSup_const, LinearEquiv.range]

end GlobalTheory.CuspBlock
