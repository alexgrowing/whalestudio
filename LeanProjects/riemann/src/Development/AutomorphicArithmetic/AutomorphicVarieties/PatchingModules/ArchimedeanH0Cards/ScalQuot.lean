import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ObstructionBoundFromDuality
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

private theorem UpperTheory.V.Pa.B2.scal_quot {R R' V : Type} [CommRing R] [CommRing R'] [AddCommGroup V]
    [Module R V] [Module R' V] (Z B : Submodule R V) (Z' B' : Submodule R' V)
    (hZ : ∀ v, v ∈ Z ↔ v ∈ Z') (hB : ∀ v, v ∈ B ↔ v ∈ B') :
    ∃ e : (Z ⧸ B.comap Z.subtype) ≃+ (Z' ⧸ B'.comap Z'.subtype),
      ∀ (z : Z) (z' : Z'), z.1 = z'.1 → e (Submodule.Quotient.mk z) = Submodule.Quotient.mk z' := by
  let f : Z ≃+ Z' :=
    { toFun := fun z => ⟨z.1, (hZ _).1 z.2⟩
      invFun := fun z => ⟨z.1, (hZ _).2 z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have hf : (B.comap Z.subtype).toAddSubgroup.map (f : Z →+ Z') = (B'.comap Z'.subtype).toAddSubgroup := by
    ext z'
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (hB _).1 hz
    · intro hz
      exact ⟨f.symm z', (hB _).2 hz, rfl⟩
  refine ⟨QuotientAddGroup.congr _ _ f hf, fun z z' h => ?_⟩
  have : z' = f z := Subtype.ext h.symm
  subst this
  rfl

theorem UpperTheory.V.Pa.B2.scal :
    ∀ (A G : Type) [CommRing A] [Group G] [TopologicalSpace G] (M : FRep A G) (N : ℕ) [Module (ZMod N) M.X], ContAction (GlobalTheory.Published.zmodRep N M.ρ) ∧ Nonempty (H0 M.ρ ≃+ H0 (GlobalTheory.Published.zmodRep N M.ρ)) ∧ (∃ e : H1 M.ρ ≃+ H1 (GlobalTheory.Published.zmodRep N M.ρ), ∀ (z : Z1 M.ρ) (z' : Z1 (GlobalTheory.Published.zmodRep N M.ρ)), z.1 = z'.1 → e (Submodule.Quotient.mk z) = Submodule.Quotient.mk z') ∧ ∃ e : H2 M.ρ ≃+ H2 (GlobalTheory.Published.zmodRep N M.ρ), ∀ (z : Z2 M.ρ) (z' : Z2 (GlobalTheory.Published.zmodRep N M.ρ)), z.1 = z'.1 → e (Submodule.Quotient.mk z) = Submodule.Quotient.mk z' := by
  intro A G _ _ _ M N _
  refine ⟨M.cont, ⟨?_⟩, ?_, ?_⟩
  · exact
      { toFun := fun z => ⟨z.1, z.2⟩
        invFun := fun z => ⟨z.1, z.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl }
  · exact UpperTheory.V.Pa.B2.scal_quot _ _ _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  · exact UpperTheory.V.Pa.B2.scal_quot _ _ _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
