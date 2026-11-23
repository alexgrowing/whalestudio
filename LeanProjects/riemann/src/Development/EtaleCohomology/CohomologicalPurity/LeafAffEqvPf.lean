import Development.EtaleCohomology.CohomologicalPurity.LeafPBPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

theorem affSieve_mem (U : Scheme.{0}) (S : Sieve U)
    (h : ∀ (A : Type) [CommRing A] (f : Spec (CommRingCat.of A) ⟶ U), S f) : S ∈ Scheme.etaleTopology U := by
  apply Scheme.zariskiTopology_le_etaleTopology
  refine GrothendieckTopology.superset_covering _ ?_ (Scheme.Cover.mem_grothendieckTopology U.affineCover)
  rintro _ _ ⟨_, k, _, ⟨i⟩, rfl⟩
  exact S.downward_closed (h _ (U.affineCover.f i)) k

theorem locBij {R : Type} [CommRing R] {F G : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (φ : F ⟶ G)
    (h : ∀ (A : Type) [CommRing A], IsIso (φ.app (op (Spec (CommRingCat.of A))))) :
    Presheaf.IsLocallyInjective Scheme.etaleTopology φ ∧ Presheaf.IsLocallySurjective Scheme.etaleTopology φ := by
  have hb : ∀ (A : Type) [CommRing A], Function.Bijective (φ.app (op (Spec (CommRingCat.of A)))) :=
    fun A _ => ConcreteCategory.bijective_of_isIso _
  refine ⟨⟨fun {X} x y hxy => ?_⟩, ⟨fun {U} s => ?_⟩⟩
  · refine affSieve_mem _ _ fun A _ f => ?_
    apply (hb A).1
    change φ.app _ (F.map f.op x) = φ.app _ (F.map f.op y)
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hxy]
  · refine affSieve_mem _ _ fun A _ f => ?_
    obtain ⟨t, ht⟩ := (hb A).2 (G.map f.op s)
    exact ⟨t, ht⟩

theorem freeIso (R : Type) [CommRing R] {P Q : PSh} (g : P ⟶ Q)
    (h : ∀ (A : Type) [CommRing A], Function.Bijective (g.app (op (Spec (CommRingCat.of A))))) :
    IsIso ((free R).map g) := by
  have h2 : ∀ (A : Type) [CommRing A], IsIso (((freeP R).map g).app (op (Spec (CommRingCat.of A)))) := by
    intro A _
    have : IsIso (g.app (op (Spec (CommRingCat.of A)))) := (isIso_iff_bijective _).2 (h A)
    change IsIso ((uliftFunctor.{1} ⋙ ModuleCat.free (ULift.{1} R)).map (g.app (op (Spec (CommRingCat.of A)))))
    infer_instance
  obtain ⟨h3, h4⟩ := locBij _ h2
  have hW : Scheme.etaleTopology.W ((freeP R).map g) := by
    rw [GrothendieckTopology.W_iff_isLocallyBijective]; exact ⟨h3, h4⟩
  exact (GrothendieckTopology.W_iff _ _).1 hW

theorem chainsIso (R : Type) [CommRing R] {E E' : Spc} (e : E ⟶ E')
    (h : ∀ (n : ℕ) (A : Type) [CommRing A], Function.Bijective
      (fun x : Sx E n (Spec (CommRingCat.of A)) => (e.app (op (SimplexCategory.mk n))).app (op (Spec (CommRingCat.of A))) x)) :
    IsIso ((chains R).map e) := by
  have : IsIso (((SimplicialObject.whiskering _ _).obj (free R)).map e) := by
    have hh : ∀ n, IsIso ((((SimplicialObject.whiskering _ _).obj (free R)).map e).app n) := by
      intro n
      induction n using Opposite.rec with | op n => ?_
      induction n using SimplexCategory.rec with | _ n => ?_
      exact freeIso R _ (h n)
    exact NatIso.isIso_of_isIso_app _
  change IsIso ((ComplexShape.embeddingDownNat.extendFunctor (Shv R)).map
    ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (((SimplicialObject.whiskering _ _).obj (free R)).map e)))
  infer_instance

theorem LeafAffEqv_of : LeafAffEqv := by
  intro hA1 q _ E E' e h i n
  have := chainsIso (ZMod q) e h
  exact hA1 (ZMod q) ((chains (ZMod q)).map e) (tw q i) n

end LateralTheory.CohomologicalPurity.Thom
