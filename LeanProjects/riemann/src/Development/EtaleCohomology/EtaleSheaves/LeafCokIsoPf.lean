import Development.EtaleCohomology.EtaleSheaves.ConeExcision.ExcisionOfCokernel

noncomputable section
open CategoryTheory Limits

namespace LateralTheory.E.LeafCokIsoPf

theorem isIso_cokernel_map_of_isPushout {C : Type*} [Category C] [HasZeroMorphisms C]
    {K' L' K L : C} (a : K' ⟶ L') (u : K' ⟶ K) (v : L' ⟶ L) (b : K ⟶ L)
    [HasCokernel a] [HasCokernel b] (w : a ≫ v = u ≫ b) (h : IsPushout a u v b) :
    IsIso (cokernel.map a b u v w) := by
  let φ : L ⟶ cokernel a := h.desc (cokernel.π a) 0 (by simp)
  have hφ : b ≫ φ = 0 := h.inr_desc _ _ _
  refine ⟨⟨cokernel.desc b φ hφ, ?_, ?_⟩⟩
  · ext
    simp [φ]
  · ext
    simp only [cokernel.π_desc_assoc, Category.comp_id]
    apply h.hom_ext
    · simp [φ]
    · simp [reassoc_of% hφ]

theorem isIso_cokernel_map_complex {C : Type*} [Category C] [Abelian C] {ι : Type*} {c : ComplexShape ι}
    {K' L' K L : HomologicalComplex C c}
    (a : K' ⟶ L') (u : K' ⟶ K) (v : L' ⟶ L) (b : K ⟶ L) (w : a ≫ v = u ≫ b)
    (hpo : ∀ n, IsPushout (a.f n) (u.f n) (v.f n) (b.f n)) :
    IsIso (cokernel.map a b u v w) := by
  suffices hc : ∀ n, IsIso ((cokernel.map a b u v w).f n) from
    HomologicalComplex.Hom.isIso_of_components _
  intro n
  let G : HomologicalComplex C c ⥤ C := HomologicalComplex.eval C c n
  have w' : G.map a ≫ G.map v = G.map u ≫ G.map b := by
    rw [← G.map_comp, w, G.map_comp]
  have h1 : IsIso (cokernel.map (G.map a) (G.map b) (G.map u) (G.map v) w') :=
    isIso_cokernel_map_of_isPushout (G.map a) (G.map u) (G.map v) (G.map b) w' (hpo n)
  have e : cokernelComparison a G ≫ G.map (cokernel.map a b u v w) =
      cokernel.map (G.map a) (G.map b) (G.map u) (G.map v) w' ≫ cokernelComparison b G := by
    rw [← cancel_epi (cokernel.π (G.map a))]
    rw [π_comp_cokernelComparison_assoc, ← G.map_comp, cokernel.π_desc, G.map_comp,
      cokernel.π_desc_assoc, Category.assoc, π_comp_cokernelComparison]
  have : IsIso (cokernelComparison a G ≫ G.map (cokernel.map a b u v w)) := by rw [e]; infer_instance
  exact IsIso.of_isIso_comp_left (cokernelComparison a G) (G.map (cokernel.map a b u v w))

open GlobalTheory.EtC in
theorem LeafCokIso_of : LateralTheory.E.LeafExcPf.LeafCokIso := by
  intro R _ K' L' K L a u v b w hpo
  exact isIso_cokernel_map_complex a u v b w hpo

end LateralTheory.E.LeafCokIsoPf
