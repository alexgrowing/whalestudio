import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.AugExact

theorem augmented_exact_iff (C : Type 2) [Category.{1} C] [Abelian C] (K : SimplicialObject C) (B : C)
    (f : K ⟶ (SimplicialObject.const C).obj B) :
    QuasiIso ((AlgebraicTopology.alternatingFaceMapComplex C).map f) ↔
      (Epi (f.app (op (SimplexCategory.mk (0)))) ∧
        (∃ w : (K.δ (n := 0) 0 - K.δ (n := 0) 1) ≫ f.app (op (SimplexCategory.mk (0))) = 0,
          (ShortComplex.mk _ _ w).Exact) ∧
        ∀ n : ℕ, ((AlgebraicTopology.alternatingFaceMapComplex C).obj K).ExactAt (n + 1)) := by
  let e := (SimplicialObject.Augmented.ExtraDegeneracy.const B).homotopyEquiv
  let g : (AlgebraicTopology.alternatingFaceMapComplex C).obj ((SimplicialObject.const C).obj B) ⟶
      (ChainComplex.single₀ C).obj B := e.hom
  haveI : QuasiIso g := e.quasiIso_hom
  have hg : g.f 0 = 𝟙 B := AlgebraicTopology.AlternatingFaceMapComplex.ε_app_f_zero _
  rw [← quasiIso_iff_comp_right _ g, quasiIso_iff]
  set φ := (AlgebraicTopology.alternatingFaceMapComplex C).map f ≫ g with hφ
  have h0 : φ.f 0 = f.app (op (SimplexCategory.mk 0)) := by
    rw [hφ, HomologicalComplex.comp_f, hg]
    exact Category.comp_id _
  have hd : ((AlgebraicTopology.alternatingFaceMapComplex C).obj K).d 1 0 =
      K.δ (n := 0) 0 - K.δ (n := 0) 1 := by
    change (AlgebraicTopology.AlternatingFaceMapComplex.obj K).d (0 + 1) 0 = _
    rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq, Fin.sum_univ_two]
    simp [sub_eq_add_neg]
  have w : (K.δ (n := 0) 0 - K.δ (n := 0) 1) ≫ f.app (op (SimplexCategory.mk (0))) = 0 := by
    simp [Preadditive.sub_comp, SimplicialObject.δ_naturality, SimplicialObject.δ]
  have he : Epi (φ.f 0) ↔ Epi (f.app (op (SimplexCategory.mk (0)))) := h0 ▸ Iff.rfl
  have hz : QuasiIsoAt φ 0 ↔ (Epi (f.app (op (SimplexCategory.mk (0)))) ∧
      (∃ w : (K.δ (n := 0) 0 - K.δ (n := 0) 1) ≫ f.app (op (SimplexCategory.mk (0))) = 0,
        (ShortComplex.mk _ _ w).Exact)) := by
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros' _ rfl rfl rfl]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨he.1 h2, w, (ShortComplex.exact_iff_of_iso ?_).1 h1⟩
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        ((Category.id_comp _).trans (hd.symm.trans (Category.comp_id _).symm))
        ((Category.id_comp _).trans (h0.symm.trans (Category.comp_id _).symm))
    · rintro ⟨h1, _, h2⟩
      refine ⟨(ShortComplex.exact_iff_of_iso ?_).1 h2, he.2 h1⟩
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        ((Category.id_comp _).trans (hd.trans (Category.comp_id _).symm))
        ((Category.id_comp _).trans (h0.trans (Category.comp_id _).symm))
  have hs : ∀ n : ℕ, QuasiIsoAt φ (n + 1) ↔
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj K).ExactAt (n + 1) :=
    fun n => quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _)
  constructor
  · intro h
    exact ⟨(hz.1 (h 0)).1, (hz.1 (h 0)).2, fun n => (hs n).1 (h (n + 1))⟩
  · rintro ⟨h1, h2, h3⟩ i
    cases i with
    | zero => exact hz.2 ⟨h1, h2⟩
    | succ n => exact (hs n).2 (h3 n)

end GlobalTheory.EtC.AugExact
