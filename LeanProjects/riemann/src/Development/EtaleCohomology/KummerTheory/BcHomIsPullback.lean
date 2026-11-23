import Development.EtaleCohomology.KummerTheory.ContCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.BCPf
open LateralTheory.KummerTheory.ContCut

@[reassoc] theorem bcHom_fst {U X : Scheme.{0}} {R A : CommRingCat.{0}} (f : U ⟶ X) (p : X ⟶ Spec R) (r : U ⟶ Spec R)
    (e : f ≫ p = r) (s : R ⟶ A) :
    bcHom f p r e s ≫ pullback.fst p (Spec.map s) = pullback.fst r (Spec.map s) ≫ f := by
  unfold bcHom pullback.map; exact pullback.lift_fst _ _ _

theorem bcHom_snd {U X : Scheme.{0}} {R A : CommRingCat.{0}} (f : U ⟶ X) (p : X ⟶ Spec R) (r : U ⟶ Spec R)
    (e : f ≫ p = r) (s : R ⟶ A) :
    bcHom f p r e s ≫ pullback.snd p (Spec.map s) = pullback.snd r (Spec.map s) := by
  unfold bcHom pullback.map; rw [pullback.lift_snd, Category.comp_id]

theorem bcHom_isPullback {U X : Scheme.{0}} {R A : CommRingCat.{0}} (f : U ⟶ X) (p : X ⟶ Spec R) (r : U ⟶ Spec R)
    (e : f ≫ p = r) (s : R ⟶ A) :
    IsPullback (bcHom f p r e s) (pullback.fst r (Spec.map s)) (pullback.fst p (Spec.map s)) f := by
  have big : IsPullback (bcHom f p r e s ≫ pullback.snd p (Spec.map s)) (pullback.fst r (Spec.map s))
      (Spec.map s) (f ≫ p) := by
    rw [bcHom_snd, e]; exact (IsPullback.of_hasPullback r (Spec.map s)).flip
  exact IsPullback.of_right big (bcHom_fst f p r e s) (IsPullback.of_hasPullback p (Spec.map s)).flip

theorem bcHom_open {U X : Scheme.{0}} {R A : CommRingCat.{0}} (f : U ⟶ X) (p : X ⟶ Spec R) (r : U ⟶ Spec R)
    (e : f ≫ p = r) (s : R ⟶ A) [IsOpenImmersion f] : IsOpenImmersion (bcHom f p r e s) :=
  MorphismProperty.of_isPullback (bcHom_isPullback f p r e s).flip ‹_›

theorem bcHom_range {U X : Scheme.{0}} {R A : CommRingCat.{0}} (f : U ⟶ X) (p : X ⟶ Spec R) (r : U ⟶ Spec R)
    (e : f ≫ p = r) (s : R ⟶ A) (x : ↥(pullback p (Spec.map s))) (hx : pullback.fst p (Spec.map s) x ∈ Set.range f) :
    x ∈ Set.range (bcHom f p r e s) := by
  obtain ⟨u, hu⟩ := hx
  obtain ⟨q, hq, -⟩ := Scheme.exists_preimage_of_isPullback (bcHom_isPullback f p r e s) x u hu.symm
  exact ⟨q, hq⟩

theorem BC_of : BC := by
  intro R A s W U V X a b f g p pU pV pW ea eb ef eg h
  obtain ⟨hf, hg, hpb, hcov⟩ := h
  refine ⟨bcHom_open f p pU ef s, bcHom_open g p pV eg s, ?_, ?_⟩
  · have sq1 : IsPullback (pullback.fst pW (Spec.map s)) (bcHom b pV pW eb s) b (pullback.fst pV (Spec.map s)) :=
      (bcHom_isPullback b pV pW eb s).flip
    have big0 := sq1.paste_horiz hpb
    have big : IsPullback (bcHom a pU pW ea s ≫ pullback.fst pU (Spec.map s)) (bcHom b pV pW eb s) f
        (bcHom g p pV eg s ≫ pullback.fst p (Spec.map s)) := by
      rw [bcHom_fst, bcHom_fst]; exact big0
    refine IsPullback.of_right big ?_ (bcHom_isPullback f p pU ef s).flip
    apply pullback.hom_ext
    · simp only [Category.assoc, bcHom_fst, bcHom_fst_assoc]; rw [hpb.w]
    · simp only [Category.assoc, bcHom_snd]
  · intro x
    rcases hcov (pullback.fst p (Spec.map s) x) with hx | hx
    · exact Or.inl (bcHom_range f p pU ef s x hx)
    · exact Or.inr (bcHom_range g p pV eg s x hx)

end LateralTheory.KummerTheory.BCPf
