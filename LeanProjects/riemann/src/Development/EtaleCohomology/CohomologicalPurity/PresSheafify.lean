import Development.EtaleCohomology.CohomologicalPurity.LeafBdCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Bd.PushPf

variable (R : Type) [CommRing R]

instance pres_ulift : PreservesColimitsOfShape WalkingSpan uliftFunctor.{1, 0} := inferInstance

instance pres_freeMod : PreservesColimitsOfShape WalkingSpan (ModuleCat.free.{1} (ULift.{1} R)) :=
  (ModuleCat.adj (ULift.{1} R)).leftAdjoint_preservesColimits.preservesColimitsOfShape

instance pres_freeP : PreservesColimitsOfShape WalkingSpan (freeP R) := by
  unfold freeP; infer_instance

instance pres_sheafify : PreservesColimitsOfShape WalkingSpan
    (presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))) := inferInstance

instance pres_free : PreservesColimitsOfShape WalkingSpan (free R) := by
  unfold free; infer_instance

instance pres_eval (k : ℕ) : PreservesColimitsOfShape WalkingSpan
    ((evaluation SimplexCategoryᵒᵖ PSh).obj (op (SimplexCategory.mk k))) := inferInstance

def isoN (k : ℕ) : chainsN R ⋙ HomologicalComplex.eval _ _ k ≅
    (evaluation SimplexCategoryᵒᵖ PSh).obj (op (SimplexCategory.mk k)) ⋙ free R :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

instance pres_N (k : ℕ) : PreservesColimitsOfShape WalkingSpan (chainsN R ⋙ HomologicalComplex.eval _ _ k) :=
  preservesColimitsOfShape_of_natIso (isoN R k).symm

theorem hk (k : ℕ) : ComplexShape.embeddingDownNat.f k = -(k : ℤ) := by simp

def isoC (k : ℕ) : chains R ⋙ HomologicalComplex.eval _ _ (-(k : ℤ)) ≅ chainsN R ⋙ HomologicalComplex.eval _ _ k :=
  NatIso.ofComponents (fun X => HomologicalComplex.extendXIso _ _ (hk k))
    (by
      intro X Y f
      change (HomologicalComplex.extendMap ((chainsN R).map f) ComplexShape.embeddingDownNat).f (-(k : ℤ)) ≫ _ =
        _ ≫ ((chainsN R).map f).f k
      rw [HomologicalComplex.extendMap_f _ _ (hk k)]
      simp)

theorem pres (p : ℤ) : PreservesColimitsOfShape WalkingSpan (chains R ⋙ HomologicalComplex.eval _ _ p) := by
  by_cases hp : ∃ k : ℕ, ComplexShape.embeddingDownNat.f k = p
  · obtain ⟨k, rfl⟩ := hp
    have := pres_N R k
    exact preservesColimitsOfShape_of_natIso (isoC R k).symm
  · push Not at hp
    apply Functor.preservesColimitsOfShape_of_isZero
    rw [Functor.isZero_iff]
    intro X
    exact HomologicalComplex.isZero_extend_X _ _ _ hp

end LateralTheory.CohomologicalPurity.Bd.PushPf

open LateralTheory.CohomologicalPurity.Bd.PushPf in
theorem LateralTheory.CohomologicalPurity.Bd.LeafPush_of : LateralTheory.CohomologicalPurity.Bd.LeafPush := by
  intro R _ U E E' D f g l r h p
  have := pres R p
  exact (chains R ⋙ HomologicalComplex.eval _ _ p).map_isPushout h
