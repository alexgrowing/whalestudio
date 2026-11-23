import Development.EtaleCohomology.CohomologicalPurity.LeafHsRelPfSplit

noncomputable section
open CategoryTheory Limits Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcSp

theorem chainsXIso_nat (R : Type) [CommRing R] {E E' : Spc} (f : E ⟶ E') (p : ℕ) :
    (chainsXIso R E p).hom ≫ (free R).map (f.app (op (SimplexCategory.mk p))) =
      ((chains R).map f).f (-(p : ℤ)) ≫ (chainsXIso R E' p).hom := by
  have h : ComplexShape.embeddingDownNat.f p = -(p : ℤ) := rfl
  change _ = (HomologicalComplex.extendMap ((chainsN R).map f) _).f _ ≫ _
  rw [HomologicalComplex.extendMap_f _ _ h]
  simp only [chainsXIso]
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

instance freePresSpan (R : Type) [CommRing R] : PreservesColimitsOfShape WalkingSpan (free R) := by
  have : PreservesColimitsOfShape WalkingSpan (ModuleCat.free.{1} (ULift.{1} R)) :=
    (ModuleCat.adj (ULift.{1} R)).leftAdjoint_preservesColimits.preservesColimitsOfShape
  have : PreservesColimitsOfShape WalkingSpan (freeP R) := by
    unfold freeP; infer_instance
  unfold free; infer_instance

theorem free_isPushout (R : Type) [CommRing R] (P : Arrow Spc) (p : ℕ) :
    IsPushout ((free R).map (P.hom.app (op (SimplexCategory.mk p))))
      ((free R).map (P.hom.app (op (SimplexCategory.mk p))))
      ((free R).map ((dbl.inl P).app (op (SimplexCategory.mk p))))
      ((free R).map ((dbl.inr P).app (op (SimplexCategory.mk p)))) := by
  have h0 : IsPushout P.hom P.hom (dbl.inl P) (dbl.inr P) := IsPushout.of_hasPushout P.hom P.hom
  have h1 := h0.map ((evaluation _ PSh).obj (op (SimplexCategory.mk p)))
  exact h1.map (free R)

theorem chains_isPushout (R : Type) [CommRing R] (P : Arrow Spc) (p : ℕ) :
    IsPushout (((chains R).map P.hom).f (-(p : ℤ))) (((chains R).map P.hom).f (-(p : ℤ)))
      (((chains R).map (dbl.inl P)).f (-(p : ℤ))) (((chains R).map (dbl.inr P)).f (-(p : ℤ))) :=
  (free_isPushout R P p).of_iso' (chainsXIso R _ p) (chainsXIso R _ p) (chainsXIso R _ p)
    (chainsXIso R _ p) (chainsXIso_nat R _ p) (chainsXIso_nat R _ p)
    (chainsXIso_nat R _ p) (chainsXIso_nat R _ p)

theorem leafDblCok_of : LeafDblCok := by
  intro R _ P _ n
  by_cases hn : ∃ p : ℕ, -(p : ℤ) = n
  · obtain ⟨p, rfl⟩ := hn
    exact isIso_cokernel_map_of_isPushout (chains_isPushout R P p)
  · push Not at hn
    have hz : ∀ E : Spc, IsZero (((chains R).obj E).X n) := fun E =>
      HomologicalComplex.isZero_extend_X _ _ _ (fun i => hn i)
    have hc : ∀ {E E' : Spc} (f : E ⟶ E'), IsZero (cokernel (((chains R).map f).f n)) := fun f => by
      rw [IsZero.iff_id_eq_zero]
      exact coequalizer.hom_ext ((hz _).eq_of_src _ _)
    exact ⟨⟨0, (hc _).eq_of_src _ _, (hc _).eq_of_src _ _⟩⟩

end LateralTheory.CohomologicalPurity.Thom.ExcSp
