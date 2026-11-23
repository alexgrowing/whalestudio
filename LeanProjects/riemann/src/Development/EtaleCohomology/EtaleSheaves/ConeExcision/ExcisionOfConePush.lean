import Development.EtaleCohomology.EtaleSheaves.ConeExcision

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafExcPf

variable (R : Type) [CommRing R]

theorem mono_freePresheaf_map {X Y : PSh} (g : X ⟶ Y) [Mono g] : Mono ((freeP R).map g) := by
  rw [NatTrans.mono_iff_mono_app]
  intro T
  have hg : Function.Injective (g.app T) :=
    (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app g).1 ‹_› T)
  rw [ModuleCat.mono_iff_injective]
  change Function.Injective (Finsupp.mapDomain (ULift.map (g.app T)))
  exact Finsupp.mapDomain_injective (fun a b h => ULift.ext _ _ (hg (congrArg ULift.down h)))

theorem free_mono {X Y : PSh} (g : X ⟶ Y) [Mono g] : Mono ((free R).map g) := by
  have := mono_freePresheaf_map R g
  change Mono ((presheafToSheaf _ _).map ((freeP R).map g))
  infer_instance

theorem LeafMono_pf : LeafMono := by
  intro R _ E E' f _ n
  have hlev : ∀ p : ℕ, Mono (f.app (op (SimplexCategory.mk p))) := fun p =>
    (NatTrans.mono_iff_mono_app f).1 ‹_› _
  change Mono (HomologicalComplex.extendMap ((chainsN R).map f) ComplexShape.embeddingDownNat |>.f n)
  by_cases h : ∃ p : ℕ, ComplexShape.embeddingDownNat.f p = n
  · obtain ⟨p, hp⟩ := h
    rw [HomologicalComplex.extendMap_f _ _ hp]
    have : Mono (((chainsN R).map f).f p) := by
      change Mono ((free R).map (f.app (op (SimplexCategory.mk p))))
      exact free_mono R _
    infer_instance
  · simp only [not_exists] at h
    have hz := HomologicalComplex.isZero_extend_X ((chainsN R).obj E) ComplexShape.embeddingDownNat n h
    exact ⟨fun g k _ => hz.eq_of_tgt g k⟩

theorem excision_of_conePush (hRel : LateralTheory.E.t_E6Cut.LeafRel) (hSq : LeafSq) (hCone : LeafConePush) :
    LateralTheory.E.t_E6Cut.LeafExc :=
  LeafExc_of hRel LeafMono_pf hSq hCone

end LateralTheory.E.LeafExcPf
