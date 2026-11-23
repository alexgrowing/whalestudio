import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackBijectiveOfQuasiIso
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.ExtHom

variable {R : Type} [CommRing R]

theorem cochain_sgl_neg_one_eq_zero (F : Shv R) (I : Cx R) [I.IsStrictlyGE 0]
    (β : Cochain (sgl F) I (-1)) : β = 0 := by
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  rw [Cochain.zero_v]
  by_cases hp : p = 0
  · subst hp
    exact (I.isZero_of_isStrictlyGE 0 q (by omega)).eq_of_tgt _ _
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F p hp).eq_of_src _ _

theorem ofHom_eq_of_cls {T I : Cx R} {f g : T ⟶ I}
    (h : CohomologyClass.mk (Cocycle.ofHom f) = CohomologyClass.mk (Cocycle.ofHom g)) :
    ∃ β : Cochain T I (-1), Cochain.ofHom f = δ (-1) 0 β + Cochain.ofHom g := by
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (-1) (by omega)] at h
  obtain ⟨β, hβ⟩ := h
  refine ⟨β, ?_⟩
  rw [hβ]
  simp

end GlobalTheory.EtC.ExtHom

open GlobalTheory.EtC.ExtHom in

theorem GlobalTheory.EtC.extHom_of_quasiIso : ∀ (R : Type) [CommRing R] (F : Shv R) (T I : Cx R) [I.IsKInjective] [I.IsStrictlyGE 0] (ε : sgl F ⟶ T) [QuasiIso ε], (∀ a : sgl F ⟶ I, ∃ m : T ⟶ I, ε ≫ m = a) ∧ ∀ m m' : T ⟶ I, ε ≫ m = ε ≫ m' → Nonempty (Homotopy m m') := by
  intro R _ F T I _ _ ε _
  have hb := GlobalTheory.EtC.cpull_bijective_of_quasiIso R ε I 0
  refine ⟨fun a => ?_, fun m m' h => ?_⟩
  · obtain ⟨y, hy⟩ := hb.2 (CohomologyClass.mk (Cocycle.ofHom a))
    obtain ⟨z, rfl⟩ := y.mk_surjective
    refine ⟨Cocycle.homOf z, ?_⟩
    have hz : Cocycle.ofHom (ε ≫ Cocycle.homOf z) = zcomp (Cocycle.ofHom ε) z (zero_add 0) := by
      apply Cocycle.ext
      simp [zcomp, Cochain.ofHom_comp]
    have h2 : CohomologyClass.mk (Cocycle.ofHom (ε ≫ Cocycle.homOf z)) = CohomologyClass.mk (Cocycle.ofHom a) := by
      rw [hz]; exact hy
    obtain ⟨β, hβ⟩ := ofHom_eq_of_cls h2
    rw [cochain_sgl_neg_one_eq_zero F I β, δ_zero, zero_add] at hβ
    exact (Cocycle.equivHom _ _).injective (Cocycle.ext hβ)
  · have h1 : cpull ε I 0 (CohomologyClass.mk (Cocycle.ofHom m)) = cpull ε I 0 (CohomologyClass.mk (Cocycle.ofHom m')) := by
      simp only [cpull, cpre_mk]
      congr 1
      apply Cocycle.ext
      change (Cochain.ofHom ε).comp (Cochain.ofHom m) (zero_add 0) = (Cochain.ofHom ε).comp (Cochain.ofHom m') (zero_add 0)
      rw [← Cochain.ofHom_comp, ← Cochain.ofHom_comp, h]
    obtain ⟨β, hβ⟩ := ofHom_eq_of_cls (hb.1 h1)
    exact ⟨(Cochain.equivHomotopy m m').symm ⟨β, hβ⟩⟩
