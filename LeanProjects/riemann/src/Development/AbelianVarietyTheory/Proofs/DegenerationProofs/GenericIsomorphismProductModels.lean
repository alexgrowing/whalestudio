import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.GenProj

theorem ext_of_dense {W X T Z : Scheme.{0}} (j : W ⟶ X)
    [IsSchemeTheoreticallyDominant j] {m m' : X ⟶ T} (g : T ⟶ Z) [IsSeparated g]
    (h₁ : j ≫ m = j ≫ m') (h₂ : m ≫ g = m' ≫ g) : m = m' := by
  let a : Over.mk (m ≫ g) ⟶ Over.mk g := Over.homMk m
  let b : Over.mk (m ≫ g) ⟶ Over.mk g := Over.homMk m' h₂.symm
  have : IsSeparated (Over.mk g).hom := ‹_›
  let c : Over.mk (j ≫ m ≫ g) ⟶ Over.mk (m ≫ g) := Over.homMk j
  have hc : c ≫ a = c ≫ b := by ext1; exact h₁
  have hk : (equalizer.ι a b).left.ker = ⊥ := by
    have e : (equalizer.lift c hc).left ≫ (equalizer.ι a b).left = j := by
      rw [← Over.comp_left, equalizer.lift_ι]; rfl
    have := (equalizer.lift c hc).left.le_ker_comp (equalizer.ι a b).left
    rw [e] at this
    exact le_bot_iff.mp (this.trans j.ker_eq_bot.le)
  have : IsIso (equalizer.ι a b).left := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hk
  rw [← cancel_epi (equalizer.ι a b).left]
  exact congr($(equalizer.condition a b).left)

theorem eq_of_generic {S E U X X' A : Scheme.{0}} (i : E ⟶ S) [IsSchemeTheoreticallyDominant i] [QuasiCompact i]
    (s : X ⟶ S) (s' : X' ⟶ S) [Flat s] [IsSeparated s'] (p : U ⟶ X) (q : U ⟶ X') [Flat p]
    (hs : p ≫ s = q ≫ s') (j : A ⟶ X) [Mono j] (j' : A ⟶ X')
    (H : ∀ (Z : Scheme.{0}) (a : Z ⟶ U) (t : Z ⟶ E), a ≫ p ≫ s = t ≫ i → ∃ c : Z ⟶ A, c ≫ j = a ≫ p ∧ c ≫ j' = a ≫ q)
    {Z : Scheme.{0}} (a b : Z ⟶ U) (hab : a ≫ p = b ≫ p) : a ≫ q = b ≫ q := by
  have key : pullback.fst p p ≫ q = pullback.snd p p ≫ q := by
    let w := pullback.fst p p ≫ p ≫ s
    have : Flat w := by dsimp only [w]; infer_instance
    refine ext_of_dense (pullback.fst w i) s' ?_ ?_
    · obtain ⟨c₁, h₁, h₁'⟩ := H _ (pullback.fst w i ≫ pullback.fst p p) (pullback.snd w i)
        (by rw [← pullback.condition]; simp [w])
      obtain ⟨c₂, h₂, h₂'⟩ := H _ (pullback.fst w i ≫ pullback.snd p p) (pullback.snd w i)
        (by rw [← pullback.condition, Category.assoc, ← pullback.condition_assoc])
      have e : c₁ = c₂ := by
        rw [← cancel_mono j, h₁, h₂, Category.assoc, Category.assoc, pullback.condition]
      rw [← Category.assoc, ← Category.assoc, ← h₁', ← h₂', e]
    · rw [Category.assoc, Category.assoc, ← hs, pullback.condition_assoc]
  have := congrArg (fun x => pullback.lift a b hab ≫ x) key
  simpa only [pullback.lift_fst_assoc, pullback.lift_snd_assoc] using this

theorem exists_image {U X : Scheme.{0}} (p : U ⟶ X) [Flat p] [LocallyOfFinitePresentation p] :
    ∃ (V : X.Opens) (p' : U ⟶ V.toScheme), p' ≫ V.ι = p ∧ Flat p' ∧ LocallyOfFinitePresentation p' ∧ Surjective p' := by
  let V : X.Opens := ⟨Set.range p, p.isOpenMap.isOpen_range⟩
  have hr : Set.range p ⊆ Set.range V.ι := by rw [Scheme.Opens.range_ι]; exact subset_rfl
  have e : IsOpenImmersion.lift V.ι p hr ≫ V.ι = p := IsOpenImmersion.lift_fac _ _ _
  have hP : IsPullback (IsOpenImmersion.lift V.ι p hr) (𝟙 U) V.ι p :=
    IsPullback.of_vert_isIso_mono ⟨by rw [e, Category.id_comp]⟩
  refine ⟨V, IsOpenImmersion.lift V.ι p hr, e, ?_, ?_, ⟨?_⟩⟩
  · exact MorphismProperty.of_isPullback (P := @Flat) hP.flip ‹_›
  · exact MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hP.flip ‹_›
  · rintro ⟨_, u, rfl⟩
    refine ⟨u, V.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, e]; rfl

theorem exists_openImmersion {U X X' : Scheme.{0}} (p : U ⟶ X) (q : U ⟶ X') [Flat p] [LocallyOfFinitePresentation p]
    [Flat q] [LocallyOfFinitePresentation q]
    (H : ∀ (Z : Scheme.{0}) (a b : Z ⟶ U), a ≫ p = b ≫ p ↔ a ≫ q = b ≫ q) :
    ∃ (V : X.Opens) (p' : U ⟶ V.toScheme) (h : V.toScheme ⟶ X'), p' ≫ V.ι = p ∧ Flat p' ∧ Surjective p' ∧
      p' ≫ h = q ∧ IsOpenImmersion h := by
  obtain ⟨V, p', hp, _, _, _⟩ := exists_image p
  obtain ⟨V', q', hq, _, _, _⟩ := exists_image q
  have H' : ∀ (Z : Scheme.{0}) (a b : Z ⟶ U), a ≫ p' = b ≫ p' ↔ a ≫ q' = b ≫ q' := by
    intro Z a b
    rw [← cancel_mono V.ι, ← cancel_mono V'.ι]
    simpa [hp, hq] using H Z a b
  let u := EffectiveEpi.desc p' q' (fun a b h => (H' _ a b).1 h)
  let v := EffectiveEpi.desc q' p' (fun a b h => (H' _ a b).2 h)
  have hu : p' ≫ u = q' := EffectiveEpi.fac _ _ _
  have hv : q' ≫ v = p' := EffectiveEpi.fac _ _ _
  have : IsIso u := ⟨v, by rw [← cancel_epi p', ← Category.assoc, hu, hv, Category.comp_id],
    by rw [← cancel_epi q', ← Category.assoc, hv, hu, Category.comp_id]⟩
  exact ⟨V, p', u ≫ V'.ι, hp, ‹_›, ‹_›, by rw [← Category.assoc, hu, hq], inferInstance⟩

variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' : Over (Sp K)}

theorem prod_j_fst (M : Model R A) (N : Model R A') :
    (M.prod N).j ≫ (fst M.Y N.Y).left = (fst A A').left ≫ M.j := by
  have h : (M.prod N).e.inv ≫ (Over.pullback (spMap (algebraMap R K))).map (fst M.Y N.Y) = fst A A' ≫ M.e.inv := by
    simp [Model.prod]
  have h2 := congrArg (fun q => q.left ≫ pullback.fst M.Y.hom (spMap (algebraMap R K))) h
  have h4 : ((Over.pullback (spMap (algebraMap R K))).map (fst M.Y N.Y)).left ≫ pullback.fst M.Y.hom (spMap (algebraMap R K))
      = pullback.fst (M.prod N).Y.hom (spMap (algebraMap R K)) ≫ (fst M.Y N.Y).left := pullback.lift_fst _ _ _
  simp only [Over.comp_left, Category.assoc] at h2
  exact (Category.assoc _ _ _).trans ((congrArg (fun q => (M.prod N).e.inv.left ≫ q) h4).symm.trans h2)

theorem exists_lift_j (M : Model R A) {Z : Scheme.{0}} (a : Z ⟶ M.Y.left) (t : Z ⟶ Sp K)
    (h : a ≫ M.Y.hom = t ≫ spMap (algebraMap R K)) : ∃ d : Z ⟶ A.left, d ≫ M.j = a := by
  refine ⟨pullback.lift a t h ≫ M.e.hom.left, ?_⟩
  have e : M.e.hom.left ≫ M.e.inv.left = 𝟙 _ := by rw [← Over.comp_left, Iso.hom_inv_id]; rfl
  unfold Model.j
  rw [Category.assoc, ← Category.assoc M.e.hom.left, e]
  exact (congrArg _ (Category.id_comp _)).trans (pullback.lift_fst _ _ _)

theorem mono_j [IsFractionRing R K] (M : Model R A) : Mono M.j := by
  have : IsPreimmersion (spMap (algebraMap R K)) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have : IsIso M.e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map M.e.inv))
  have : Mono (pullback.fst M.Y.hom (spMap (algebraMap R K))) := inferInstance
  exact mono_comp' inferInstance this

theorem genIso_of_prod : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A A' B B' : Over (Sp K)) [IsIntegral A.left] [IsIntegral (A ⊗ B).left] (M : Model R A) (M' : Model R A') (N : Model R B) (N' : Model R B') (f : A ≅ A') (Θ : A ⊗ B ⟶ A' ⊗ B'), M.Irr → M'.Irr → N.Irr → N'.Irr → Θ ≫ fst A' B' = fst A B ≫ f.hom → GenIso (M.prod N) (M'.prod N') Θ → GenIso M M' f.hom := by
  intro R K _ _ _ _ _ hSH A A' B B' _ _ M M' N N' f Θ _ _ _ _ hΘ ⟨z, hz, U, g, hzU, ⟨hg₁, hg₂⟩, hgo⟩
  have := hSH.2.2.2
  have := M.smooth; have := M'.smooth; have := N.smooth; have := N'.smooth
  have := M.sep; have := M'.sep
  have := mono_j M; have := mono_j M'
  have : IsDominant (spMap (algebraMap R K)) := by
    refine ⟨?_⟩
    show DenseRange (PrimeSpectrum.comap (algebraMap R K))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)]
    exact bot_le
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap R K))
  have : IsIso f.hom.left := inferInstanceAs (IsIso ((Over.forget _).map f.hom))
  let π : (M.prod N).Y.left ⟶ M.Y.left := (fst M.Y N.Y).left
  let π' : (M'.prod N').Y.left ⟶ M'.Y.left := (fst M'.Y N'.Y).left
  have : Smooth π := inferInstanceAs (Smooth (pullback.fst M.Y.hom N.Y.hom))
  have : Smooth π' := inferInstanceAs (Smooth (pullback.fst M'.Y.hom N'.Y.hom))
  have hπ : π ≫ M.Y.hom = (M.prod N).Y.hom := Over.w (fst M.Y N.Y)
  have hπ' : π' ≫ M'.Y.hom = (M'.prod N').Y.hom := Over.w (fst M'.Y N'.Y)
  have hj : (M.prod N).j ≫ π = (fst A B).left ≫ M.j := prod_j_fst M N
  have hj' : (M'.prod N').j ≫ π' = (fst A' B').left ≫ M'.j := prod_j_fst M' N'
  have hs : (U.ι ≫ π) ≫ M.Y.hom = (g ≫ π') ≫ M'.Y.hom := by
    rw [Category.assoc, Category.assoc, hπ, hπ', hg₁]
  have H : ∀ (Z : Scheme.{0}) (a : Z ⟶ U.toScheme) (t : Z ⟶ Sp K),
      a ≫ (U.ι ≫ π) ≫ M.Y.hom = t ≫ spMap (algebraMap R K) →
      ∃ c : Z ⟶ A.left, c ≫ M.j = a ≫ U.ι ≫ π ∧ c ≫ f.hom.left ≫ M'.j = a ≫ g ≫ π' := by
    intro Z a t h
    obtain ⟨d, hd⟩ := exists_lift_j (M.prod N) (a ≫ U.ι) t (by rw [← h, ← hπ]; simp only [Category.assoc])
    obtain ⟨d', h₁, h₂⟩ := (isPullback_morphismRestrict (M.prod N).j U).exists_lift a d hd.symm
    refine ⟨d ≫ (fst A B).left, ?_, ?_⟩
    · rw [Category.assoc, ← hj, ← Category.assoc, hd, Category.assoc]
    · have e : Θ.left ≫ (fst A' B').left = (fst A B).left ≫ f.hom.left := by
        rw [← Over.comp_left, hΘ, Over.comp_left]
      rw [← h₁, ← h₂]
      simp only [Category.assoc]
      rw [reassoc_of% hg₂, hj', reassoc_of% e]
  obtain ⟨V, p', h, hp, _, _, hq, hh⟩ := exists_openImmersion (U.ι ≫ π) (g ≫ π') (fun Z a b =>
    ⟨eq_of_generic (spMap (algebraMap R K)) M.Y.hom M'.Y.hom _ _ hs M.j (f.hom.left ≫ M'.j) H a b,
     eq_of_generic (spMap (algebraMap R K)) M'.Y.hom M.Y.hom _ _ hs.symm (f.hom.left ≫ M'.j) M.j
      (fun Z a t h => (H Z a t (by rw [hs, h])).imp fun _ h => h.symm) a b⟩)
  have : Epi p' := Flat.epi_of_flat_of_surjective _
  refine ⟨π z, ?_, V, h, ?_, ⟨?_, ?_⟩, hh⟩
  · show M.Y.hom (π z) = _
    rw [← Scheme.Hom.comp_apply, hπ]; exact hz
  · have : V.ι (p' ⟨z, hzU⟩) = π z := congrArg (fun q : U.toScheme ⟶ M.Y.left => q ⟨z, hzU⟩) hp
    rw [← this]; exact (p' ⟨z, hzU⟩).2
  · rw [← cancel_epi p', reassoc_of% hq, reassoc_of% hp]
    simpa only [Category.assoc] using hs.symm
  · have : Epi (pullback.snd p' (M.j ∣_ V)) := Flat.epi_of_flat_of_surjective _
    have e : pullback.fst p' (M.j ∣_ V) ≫ U.ι ≫ π = (pullback.snd p' (M.j ∣_ V) ≫ (M.j ⁻¹ᵁ V).ι) ≫ M.j := by
      rw [← hp, pullback.condition_assoc, morphismRestrict_ι, Category.assoc]
    obtain ⟨c, hc₁, hc₂⟩ := H _ (pullback.fst p' (M.j ∣_ V)) (pullback.snd p' (M.j ∣_ V) ≫ (M.j ⁻¹ᵁ V).ι ≫ A.hom)
      (by rw [← Category.assoc, e, Category.assoc, M.j_hom]; simp only [Category.assoc])
    rw [e, cancel_mono] at hc₁
    rw [← cancel_epi (pullback.snd p' (M.j ∣_ V)), ← pullback.condition_assoc, hq, ← hc₂, hc₁, Category.assoc]

end GlobalTheory.SS.GenProj
end
