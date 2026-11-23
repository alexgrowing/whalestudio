import Development.EtaleCohomology.EtaleSheaves.CxDescPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex LateralTheory.E.CxDescPf

namespace LateralTheory.E.stupidPf

theorem cpull_comp {R : Type} [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (I : Cx R) (n : ℤ)
    (x : CohomologyClass M I n) : cpull (f ≫ g) I n x = cpull f I n (cpull g I n x) := by
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
  simp only [cpull, cpre, CohomologyClass.descAddMonoidHom_cohomologyClass, AddMonoidHom.mk'_apply]
  congr 1
  apply Cocycle.ext
  simp only [zcomp, Cocycle.mk_coe, Cocycle.ofHom_coe, Cochain.ofHom_comp]
  rw [Cochain.comp_assoc_of_first_is_zero_cochain]

theorem cpull_id {R : Type} [CommRing R] (K I : Cx R) (n : ℤ) (x : CohomologyClass K I n) :
    cpull (𝟙 K) I n x = x := by
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
  simp only [cpull, cpre, CohomologyClass.descAddMonoidHom_cohomologyClass, AddMonoidHom.mk'_apply]
  congr 1
  apply Cocycle.ext
  simp only [zcomp, Cocycle.mk_coe, Cocycle.ofHom_coe]
  exact Cochain.id_comp _

theorem cpull_iso {R : Type} [CommRing R] {K L : Cx R} (e : K ≅ L) (I : Cx R) (n : ℤ) :
    Function.Bijective (cpull e.hom I n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨cpull e.inv I n, fun x => ?_, fun x => ?_⟩
  · rw [← cpull_comp, e.inv_hom_id, cpull_id]
  · rw [← cpull_comp, e.hom_inv_id, cpull_id]

def trunc0 : Prop := ∀ (R : Type) [CommRing R] {K L : Cx R} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (g : K ⟶ L),
  ∃ (eK : tr K 0 ≅ (CochainComplex.singleFunctor (Shv R) 0).obj (K.X (-((0 : ℕ) : ℤ))))
    (eL : tr L 0 ≅ (CochainComplex.singleFunctor (Shv R) 0).obj (L.X (-((0 : ℕ) : ℤ)))),
    trm g 0 ≫ eL.hom = eK.hom ≫ (CochainComplex.singleFunctor (Shv R) 0).map (g.f (-((0 : ℕ) : ℤ)))

def incl : Prop := ∀ (R : Type) [CommRing R] (I : Cx R) [I.IsStrictlyGE 0] {K L : Cx R} (g : K ⟶ L) (N : ℕ),
  ∃ (ιK : tr K N ⟶ K) (ιL : tr L N ⟶ L), trm g N ≫ ιL = ιK ≫ g ∧
    ∀ n : ℤ, n + 1 ≤ (N : ℤ) → Function.Bijective (cpull ιK I n) ∧ Function.Bijective (cpull ιL I n)

theorem stupid_of (h0 : trunc0) (hI : incl) : LateralTheory.E.CxDescPf.stupid := by
  intro R _ I _ _ K L _ _ g
  refine ⟨fun hb j => ?_, fun m N hN hG => ?_⟩
  · obtain ⟨eK, eL, hsq⟩ := h0 R g
    have hc : (cpull (trm g 0) I j) ∘ (cpull eL.hom I j) =
        (cpull eK.hom I j) ∘ (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (g.f (-((0 : ℕ) : ℤ)))) I j) := by
      funext x; simp only [Function.comp_apply, ← cpull_comp, hsq]
    have hb' : Function.Bijective ((cpull (trm g 0) I j) ∘ (cpull eL.hom I j)) := by
      rw [hc]; exact (cpull_iso eK I j).comp (hb j)
    exact (Function.Bijective.of_comp_iff _ (cpull_iso eL I j)).1 hb'
  · obtain ⟨ιK, ιL, hsq, hbij⟩ := hI R I g N
    have hc : ∀ j, (cpull ιK I j) ∘ (cpull g I j) = (cpull (trm g N) I j) ∘ (cpull ιL I j) := by
      intro j; funext x; simp only [Function.comp_apply, ← cpull_comp, hsq]
    refine ⟨fun j hj => ?_, ?_⟩
    · have hb' : Function.Bijective ((cpull ιK I j) ∘ (cpull g I j)) := by
        rw [hc]; exact (hG.1 j hj).comp (hbij j (by omega)).2
      exact (Function.Bijective.of_comp_iff' (hbij j (by omega)).1 _).1 hb'
    · have hi : Function.Injective ((cpull ιK I m) ∘ (cpull g I m)) := by
        rw [hc]; exact hG.2.comp (hbij m hN).2.1
      exact Function.Injective.of_comp hi

end LateralTheory.E.stupidPf
