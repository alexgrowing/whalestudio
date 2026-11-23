import Development.EtaleCohomology.CohomologicalPurity.LeafCokIsoPf

noncomputable section
open CategoryTheory Limits Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcSp

theorem fin_pb {α β γ δ M : Type*} [AddCommMonoid M] (t : α → β) (l : α → γ) (r : β → δ) (b : γ → δ)
    (w : ∀ a, r (t a) = b (l a)) (hpb : ∀ x y, r x = b y → ∃ a, t a = x ∧ l a = y)
    (ht : Function.Injective t) (hr : Function.Injective r) (hb : Function.Injective b)
    (x : β →₀ M) (y : γ →₀ M) (h : Finsupp.mapDomain r x = Finsupp.mapDomain b y) :
    ∃ z : α →₀ M, Finsupp.mapDomain t z = x ∧ Finsupp.mapDomain l z = y := by
  classical
  have hsupp : ∀ s ∈ x.support, s ∈ Set.range t := by
    intro s hs
    have h1 : (Finsupp.mapDomain r x) (r s) ≠ 0 := by
      rw [Finsupp.mapDomain_apply hr]; exact Finsupp.mem_support_iff.1 hs
    rw [h] at h1
    have h2 : r s ∈ (Finsupp.mapDomain b y).support := Finsupp.mem_support_iff.2 h1
    have h3 := Finsupp.mapDomain_support h2
    obtain ⟨c, -, hc⟩ := Finset.mem_image.1 h3
    obtain ⟨a, ha, -⟩ := hpb s c hc.symm
    exact ⟨a, ha⟩
  refine ⟨x.comapDomain t ht.injOn, ?_, ?_⟩
  · exact Finsupp.mapDomain_comapDomain t ht x hsupp
  · apply Finsupp.mapDomain_injective hb
    rw [← Finsupp.mapDomain_comp]
    have : b ∘ l = r ∘ t := funext fun a => (w a).symm
    rw [this, Finsupp.mapDomain_comp, Finsupp.mapDomain_comapDomain t ht x hsupp, h]

theorem isPullback_of_app {J C : Type*} [Category J] [Category C] {A B X Y : J ⥤ C}
    {t : A ⟶ B} {l : A ⟶ X} {r : B ⟶ Y} {b : X ⟶ Y} (w : t ≫ r = l ≫ b)
    (h : ∀ j, IsPullback (t.app j) (l.app j) (r.app j) (b.app j)) : IsPullback t l r b :=
  IsPullback.of_isLimit' ⟨w⟩ (evaluationJointlyReflectsLimits _ fun j =>
    (isLimitMapConePullbackConeEquiv ((evaluation J C).obj j) w).symm (h j).isLimit)

theorem modfree_pb (R : Type) [CommRing R] {A' A B' B : Type} (t : A' ⟶ B') (l : A' ⟶ A) (r : B' ⟶ B)
    (b : A ⟶ B) (hpb : IsPullback t l r b) (hr : Function.Injective r) (hb : Function.Injective b) :
    IsPullback ((ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map t))
      ((ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map l))
      ((ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map r))
      ((ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map b)) := by
  obtain ⟨w, hinj, hex⟩ := (Types.isPullback_iff _ _ _ _).1 hpb
  have ht : Function.Injective t := fun x y h => hinj x y ⟨h, hb (by
    have := ConcreteCategory.congr_hom w x; have h2 := ConcreteCategory.congr_hom w y; simp only [ConcreteCategory.comp_apply, types_comp_apply] at this h2
    rw [← this, ← h2, h])⟩
  have hw : ∀ a : ULift.{1} A', ULift.up (r (t a.down)) = ULift.up (b (l a.down)) := fun a => by
    have := ConcreteCategory.congr_hom w a.down; simp only [ConcreteCategory.comp_apply, types_comp_apply] at this; rw [this]
  have sq : (ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map t) ≫
      (ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map r) =
      (ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map l) ≫
      (ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map b) := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, w]
  refine IsPullback.of_map (forget (ModuleCat (ULift.{1} R))) sq ?_
  rw [Types.isPullback_iff]
  refine ⟨congrArg (forget _).map sq, ?_, ?_⟩
  · rintro x y ⟨h1, -⟩
    have hu : Function.Injective (uliftFunctor.{1}.map t) := fun a c h =>
      ULift.ext _ _ (ht (congrArg ULift.down h))
    exact Finsupp.mapDomain_injective hu h1
  · intro x y h
    exact fin_pb (uliftFunctor.{1}.map t) (uliftFunctor.{1}.map l) (uliftFunctor.{1}.map r)
      (uliftFunctor.{1}.map b) hw
      (fun x y h => by
        obtain ⟨a, ha1, ha2⟩ := hex x.down y.down (congrArg ULift.down h)
        exact ⟨ULift.up a, ULift.ext _ _ ha1, ULift.ext _ _ ha2⟩)
      (fun a c h => ULift.ext _ _ (ht (congrArg ULift.down h)))
      (fun a c h => ULift.ext _ _ (hr (congrArg ULift.down h)))
      (fun a c h => ULift.ext _ _ (hb (congrArg ULift.down h))) x y h

theorem leafFreePb : LeafFreePb := by
  intro R _ A' A B' B t l r b hpb hr hb
  have hP : IsPullback ((freeP R).map t) ((freeP R).map l) ((freeP R).map r) ((freeP R).map b) := by
    refine isPullback_of_app (by rw [← Functor.map_comp, ← Functor.map_comp, hpb.w]) fun U => ?_
    have hrU : Mono (r.app U) := by rw [NatTrans.mono_iff_mono_app] at hr; exact hr U
    have hbU : Mono (b.app U) := by rw [NatTrans.mono_iff_mono_app] at hb; exact hb U
    exact modfree_pb R _ _ _ _ (hpb.map ((evaluation _ _).obj U))
      ((mono_iff_injective _).1 hrU) ((mono_iff_injective _).1 hbU)
  exact hP.map (presheafToSheaf _ _)

theorem LeafCokIso_of : LeafCokIso := leafCokIso_of leafFreePb

end LateralTheory.CohomologicalPurity.Thom.ExcSp
