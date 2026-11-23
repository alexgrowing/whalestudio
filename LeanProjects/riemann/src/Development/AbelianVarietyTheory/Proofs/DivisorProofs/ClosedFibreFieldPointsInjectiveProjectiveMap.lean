import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.ClosedFibreInj

theorem spMap_epi {K L : Type} [Field K] [Field L] (f : K →+* L) : Epi (spMap f) := by
  letI := f.toAlgebra
  haveI : Flat (spMap f) := by
    rw [spMap, HasRingHomProperty.Spec_iff (P := @Flat)]
    exact (show Module.Flat K L from inferInstance)
  haveI : Surjective (spMap f) := ⟨fun z => ⟨⟨⊥, Ideal.isPrime_bot⟩, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem point_lift (Ω : Type) [Field Ω] (X Y : Scheme.{0}) (g : Y ⟶ X) (hg : Surjective g) (x : Sp Ω ⟶ X) :
    ∃ (Ω' : Type) (_ : Field Ω') (io : Ω →+* Ω') (y : Sp Ω' ⟶ Y), y ≫ g = spMap io ≫ x := by
  haveI := hg
  obtain ⟨w⟩ : Nonempty ↥(Sp Ω) := inferInstance
  obtain ⟨z, -⟩ := (pullback.fst x g).surjective w
  refine ⟨(pullback x g).residueField z, inferInstance,
    (Spec.preimage ((pullback x g).fromSpecResidueField z ≫ pullback.fst x g)).hom,
    (pullback x g).fromSpecResidueField z ≫ pullback.snd x g, ?_⟩
  rw [Category.assoc, ← pullback.condition, ← Category.assoc]
  exact congrArg (· ≫ x) (Spec.map_preimage _).symm

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem closedFibre_inj : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G' : Over M.S) [GrpObj G'] (E : Emb M.π G') (N : Near M.π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom M.π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u → l ≫ E.f = pullback.fst _ _ ≫ fU → Surjective M.π → ∀ (Ω : Type) [Field Ω] (κ : ResidueField R →+* Ω) (a a' : Sp Ω ⟶ N.U.left), a ≫ N.U.hom = spMap (κ.comp (residue R)) → a' ≫ N.U.hom = spMap (κ.comp (residue R)) → a ≫ fU = a' ≫ fU → a = a' := by
  intro R _ _ _ M G' _ E N fU l hl hlf hπ Ω _ κ a a' ha ha' hf
  haveI := N.isOpen
  haveI := E.imm
  obtain ⟨Ω', _, io, s, hs⟩ := point_lift Ω (Sp R) M.S M.π hπ (spMap (κ.comp (residue R)))
  have hs' : s ≫ M.π = spMap ((io.comp κ).comp (residue R)) := by
    rw [hs, ← spMap_comp, RingHom.comp_assoc]
  obtain ⟨Ω'', _, io', e, l', -, hl'1, hl'2⟩ := E.fib Ω' s (io.comp κ) hs'

  have pt : ∀ (b : Sp Ω ⟶ N.U.left) (hb : b ≫ N.U.hom = spMap (κ.comp (residue R))),
      ∃ x : Sp Ω'' ⟶ pullback G'.hom (spMap io' ≫ s),
        x ≫ pullback.fst _ _ = spMap io' ≫ pullback.lift (spMap io ≫ b) s (by rw [Category.assoc, hb, hs]) ≫ N.u ∧
        x ≫ pullback.snd _ _ = 𝟙 _ ∧
        x ≫ e.hom.left ≫ pullback.fst _ _ ≫ E.j = spMap io' ≫ spMap io ≫ b ≫ fU := by
    intro b hb
    have hc : (spMap io ≫ b) ≫ N.U.hom = s ≫ M.π := by rw [Category.assoc, hb, hs]
    set p := pullback.lift (spMap io ≫ b) s hc with hp
    refine ⟨pullback.lift (spMap io' ≫ p ≫ N.u) (𝟙 _) (by
      rw [Category.id_comp, Category.assoc, Category.assoc, N.u_over, hp, pullback.lift_snd]), pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _, ?_⟩
    have h1 : pullback.lift (spMap io' ≫ p ≫ N.u) (𝟙 _) (by
        rw [Category.id_comp, Category.assoc, Category.assoc, N.u_over, hp, pullback.lift_snd]) ≫ l' =
        spMap io' ≫ p ≫ l := by
      rw [← cancel_mono E.H.ι, Category.assoc, hl'1, pullback.lift_fst, Category.assoc, Category.assoc, hl]
    rw [← hl'2, ← Category.assoc, h1, Category.assoc, Category.assoc, hlf, ← Category.assoc p, hp,
      pullback.lift_fst, Category.assoc]
  obtain ⟨x, hx1, hx2, hx3⟩ := pt a ha
  obtain ⟨x', hx1', hx2', hx3'⟩ := pt a' ha'
  have hj : x ≫ e.hom.left ≫ pullback.fst _ _ = x' ≫ e.hom.left ≫ pullback.fst _ _ := by
    rw [← cancel_mono E.j, Category.assoc, Category.assoc, Category.assoc, Category.assoc, hx3, hx3', hf]
  have hsec : ∀ y : Sp Ω'' ⟶ pullback G'.hom (spMap io' ≫ s), y ≫ pullback.snd _ _ = 𝟙 _ →
      y ≫ e.hom.left ≫ pullback.snd _ _ = 𝟙 _ := by
    intro y hy
    have hw := Over.w e.hom
    simp only [Over.pullback_obj_hom] at hw
    rw [hw, hy]
  have he : x ≫ e.hom.left = x' ≫ e.hom.left :=
    pullback.hom_ext (by simpa using hj) (by rw [Category.assoc, Category.assoc, hsec x hx2, hsec x' hx2'])
  have hxx : x = x' := by
    have := congrArg (· ≫ e.inv.left) he
    simpa [← Over.comp_left] using this
  subst hxx
  rw [hx1'] at hx1
  simp only [← Category.assoc, cancel_mono] at hx1
  have h2 := congrArg (· ≫ pullback.fst N.U.hom M.π) hx1
  simp only [Category.assoc, pullback.lift_fst] at h2
  haveI := spMap_epi io'
  haveI := spMap_epi io
  rw [cancel_epi, cancel_epi] at h2
  exact h2.symm

end GlobalTheory.Mum.ClosedFibreInj
