import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

namespace GlobalTheory

theorem satur_of_gram_det_unit : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {ι : Type} [Fintype ι] [DecidableEq ι] (Λ : Submodule M.L.O V) (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, H.h x y ∈ M.L.O) (m : ι → V) (hm : ∀ i, m i ∈ Λ) (hdet : IsUnitO M (H.gram m).det), ∀ v ∈ Λ, v ∈ Submodule.span E (Set.range m) → v ∈ Submodule.span M.L.O (Set.range m) := by
  intro F _ _ _ E _ _ _ _ M V _ _ H ι _ _ Λ hΛ m hm hdet v hv hvE
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hvE

  have hG : ∀ a b, H.gram m a b ∈ M.L.O := fun a b => hΛ _ (hm b) _ (hm a)
  let G' : Matrix ι ι M.L.O := Matrix.of fun a b => ⟨H.gram m a b, hG a b⟩
  have hmap : M.L.O.subtype.mapMatrix G' = H.gram m := by
    ext a b
    rfl
  have hadj : ∀ a b, (H.gram m).adjugate a b ∈ M.L.O := by
    intro a b
    rw [← hmap, ← RingHom.map_adjugate]
    exact (G'.adjugate a b).2

  have hpair : ∀ a, (Matrix.mulVec (H.gram m) c) a ∈ M.L.O := by
    intro a
    have hsum : H.h (∑ i, c i • m i) (m a) = (Matrix.mulVec (H.gram m) c) a := by
      let φ : V →+ E := AddMonoidHom.mk' (fun x => H.h x (m a)) (fun x x' => H.h_add_left x x' (m a))
      have hφ : H.h (∑ i, c i • m i) (m a) = φ (∑ i, c i • m i) := rfl
      rw [hφ, map_sum]
      simp only [Matrix.mulVec, dotProduct, HermSp.gram, Matrix.of_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      show H.h (c i • m i) (m a) = _
      rw [H.h_smul_left, mul_comm]
    rw [← hsum]
    exact hΛ _ hv _ (hm a)

  have hdc : ∀ i, (H.gram m).det * c i ∈ M.L.O := by
    intro i
    have key : Matrix.mulVec (H.gram m).adjugate (Matrix.mulVec (H.gram m) c) = (H.gram m).det • c := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    have hi := congrFun key i
    rw [Pi.smul_apply, smul_eq_mul] at hi
    have hmem : ∀ w : ι → E, (∀ j, w j ∈ M.L.O) → (Matrix.mulVec (H.gram m).adjugate w) i ∈ M.L.O := by
      intro w hw
      simp only [Matrix.mulVec, dotProduct]
      exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hadj i j) (hw j)
    rw [← hi]
    exact hmem _ hpair

  obtain ⟨_, y, hy, hdy⟩ := hdet
  have hc : ∀ i, c i ∈ M.L.O := by
    intro i
    have hci : c i = y * ((H.gram m).det * c i) := by
      rw [← mul_assoc, mul_comm y, hdy, one_mul]
    rw [hci]
    exact Subring.mul_mem _ hy (hdc i)
  refine Submodule.sum_mem _ fun i _ => ?_
  have hsm : c i • m i = (⟨c i, hc i⟩ : M.L.O) • m i := rfl
  rw [hsm]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end GlobalTheory
