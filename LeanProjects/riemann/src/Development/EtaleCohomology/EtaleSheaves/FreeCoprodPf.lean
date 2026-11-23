import Development.EtaleCohomology.EtaleSheaves.CoprodPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC Opposite

namespace LateralTheory.E.FreeCoprodPf

variable {ι : Type} (X : ι → Scheme.{0})

def P0 : PSh where
  obj U := Σ j, (unop U ⟶ X j)
  map {U V} h := ↾fun (s : Σ j, (unop U ⟶ X j)) => (⟨s.1, h.unop ≫ s.2⟩ : Σ j, (unop V ⟶ X j))
  map_id U := by ext s <;> simp
  map_comp f g := by ext s <;> simp

def inj (j : ι) : yoneda.obj (X j) ⟶ P0 X where
  app U := ↾fun f => (⟨j, f⟩ : Σ j, (unop U ⟶ X j))

def isColimitCofanSigmaOfRepresentablePresheaves : IsColimit (Cofan.mk (P0 X) (inj X)) :=
  Cofan.IsColimit.mk _
    (fun s => { app := fun U => ↾fun (x : Σ j, (unop U ⟶ X j)) => (s.inj x.1).app U x.2
                naturality := fun U V h => by
                  ext x
                  exact NatTrans.naturality_apply (s.inj x.1) h x.2 })
    (fun s j => by ext U f; rfl)
    (fun s m hm => by
      ext U ⟨j, f⟩
      exact ConcreteCategory.congr_hom (congr_app (hm j) U) f)

def φ : P0 X ⟶ yoneda.obj (∐ X) where
  app U := ↾fun (x : Σ j, (unop U ⟶ X j)) => x.2 ≫ Sigma.ι X x.1

lemma inj_φ (j : ι) : inj X j ≫ φ X = yoneda.map (Sigma.ι X j) := rfl

abbrev ψ := Functor.whiskerRight (φ X) uliftFunctor.{1}

instance : Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (ψ X) where
  imageSieve_mem {U} s := by
    let 𝒰 := (sigmaOpenCover X).pullback₁ s.down
    apply Scheme.etaleTopology.superset_covering _
      (Scheme.zariskiTopology_le_etaleTopology _ (Scheme.Cover.mem_grothendieckTopology 𝒰))
    refine (Sieve.generate_le_iff _ _).2 ?_
    rintro _ _ ⟨i⟩
    refine ⟨⟨⟨i, pullback.snd _ _⟩⟩, ?_⟩
    apply ULift.ext
    exact (pullback.condition (f := s.down) (g := (sigmaOpenCover X).f i)).symm

instance : Presheaf.IsLocallyInjective Scheme.etaleTopology.{0} (ψ X) where
  equalizerSieve_mem {U} x y h := by
    obtain ⟨⟨j, a⟩⟩ := x
    obtain ⟨⟨k, b⟩⟩ := y
    have h' : a ≫ Sigma.ι X j = b ≫ Sigma.ι X k := congrArg ULift.down h
    by_cases hjk : j = k
    · subst hjk
      obtain rfl := (cancel_mono (Sigma.ι X j)).1 h'
      refine Scheme.etaleTopology.superset_covering ?_ (Scheme.etaleTopology.top_mem _)
      intro V g _
      simp [Presheaf.equalizerSieve]
    · have := isEmpty_of_commSq_sigmaι_of_ne ⟨h'⟩ hjk
      exact Scheme.etaleTopology.superset_covering bot_le (Scheme.bot_mem_grothendieckTopology _)

variable (R : Type) [CommRing R]

instance : (ModuleCat.free (ULift.{1} R)).IsLeftAdjoint := ⟨_, ⟨ModuleCat.adj _⟩⟩

instance : PreservesColimitsOfShape (Discrete ι) (freeP R) := by
  unfold freeP; infer_instance

instance : PreservesColimitsOfShape (Discrete ι) (free R) := by
  unfold free; infer_instance

lemma isIso_free_φ : IsIso ((free R).map (φ X)) := by
  have h1 : Scheme.etaleTopology.W (ψ X) := GrothendieckTopology.W_of_isLocallyBijective _ _
  have h2 := Scheme.etaleTopology.W_of_preservesSheafification (ModuleCat.free (ULift.{1} R)) _ h1
  rw [GrothendieckTopology.W_iff] at h2
  exact h2

theorem FreeCoprod_of : LateralTheory.E.CoprodPf.FreeCoprod := by
  intro R _ ι X
  have := isIso_free_φ X R
  have h0 := isColimitCofanMkObjOfIsColimit (free R) _ _ (isColimitCofanSigmaOfRepresentablePresheaves X)
  refine ⟨IsColimit.ofIsoColimit h0 (Cofan.ext (asIso ((free R).map (φ X))) fun j => ?_)⟩
  show (free R).map (inj X j) ≫ (free R).map (φ X) = (free R).map (yoneda.map (Sigma.ι X j))
  rw [← Functor.map_comp, inj_φ]

end LateralTheory.E.FreeCoprodPf
