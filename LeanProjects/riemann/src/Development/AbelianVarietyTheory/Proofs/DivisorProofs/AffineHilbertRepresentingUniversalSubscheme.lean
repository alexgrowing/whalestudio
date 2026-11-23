import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapBcComp
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace GlobalTheory.HilbAff

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]

theorem sigma_inv (r : ℕ) {T : Scheme.{0}} {g₀ g : T ⟶ Spec (CommRingCat.of A)}
    {I₀ : (pullback (str A B) g₀).IdealSheafData} {I : (pullback (str A B) g).IdealSheafData}
    {h₀ : Good A B r g₀ I₀} {h₁ : Good A B r g I}
    (e : (⟨g₀, ⟨I₀, h₀⟩⟩ : Σ g : T ⟶ Spec (CommRingCat.of A),
      {I : (pullback (str A B) g).IdealSheafData // Good A B r g I}) = ⟨g, ⟨I, h₁⟩⟩) :
    ∃ h : g₀ = g, I = I₀.comap
      (pullback.map (str A B) g (str A B) g₀ (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp [h])) := by
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp e
  refine ⟨rfl, ?_⟩
  have : pullback.map (str A B) g₀ (str A B) g₀ (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp) = 𝟙 _ := by
    ext <;> simp
  rw [this, Scheme.IdealSheafData.comap_id]
  exact (congrArg Subtype.val (eq_of_heq h2)).symm

theorem good_ker (r : ℕ) {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) {V : Scheme.{0}}
    (v : V ⟶ pullback (str A B) g) [IsClosedImmersion v] (h1 : IsFinite (v ≫ pullback.snd _ g))
    (h2 : Flat (v ≫ pullback.snd _ g)) (h3 : ∀ y, (v ≫ pullback.snd _ g).finrank y = r) :
    Good A B r g v.ker := by
  let φ := IsClosedImmersion.lift v v.ker.subschemeι (by rw [Scheme.IdealSheafData.ker_subschemeι])
  have hφ : φ ≫ v = v.ker.subschemeι := IsClosedImmersion.lift_fac _ _ _
  haveI : IsIso φ := IsClosedImmersion.isIso_of_ker_eq v.ker.subschemeι v φ hφ
    (Scheme.IdealSheafData.ker_subschemeι _)
  have e : v.ker.subschemeι ≫ pullback.snd _ g = φ ≫ (v ≫ pullback.snd _ g) := by
    rw [← Category.assoc, hφ]
  refine ⟨?_, ?_, fun y => ?_⟩
  · rw [e]; infer_instance
  · rw [e]; infer_instance
  · rw [e, Scheme.Hom.finrank_comp_left_of_isIso, h3]

end GlobalTheory.HilbAff

theorem GlobalTheory.HilbAff.universal : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ) (H : Scheme.{0}) (R : (GlobalTheory.HilbAff.functor A B r).RepresentableBy H), ∃ (U : Scheme.{0}) (u : U ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) (R.homEquiv (𝟙 H)).1), IsClosedImmersion u ∧ IsFinite (u ≫ pullback.snd _ (R.homEquiv (𝟙 H)).1) ∧ Flat (u ≫ pullback.snd _ (R.homEquiv (𝟙 H)).1) ∧ (∀ y, (u ≫ pullback.snd _ (R.homEquiv (𝟙 H)).1).finrank y = r) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ Spec (CommRingCat.of A)) (V : Scheme.{0}) (v : V ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) g), IsClosedImmersion v → IsFinite (v ≫ pullback.snd _ g) → Flat (v ≫ pullback.snd _ g) → (∀ y, (v ≫ pullback.snd _ g).finrank y = r) → ∃! f : T ⟶ H, ∃ hf : f ≫ (R.homEquiv (𝟙 H)).1 = g, ∃ w : V ⟶ U, IsPullback v w (pullback.map _ g _ (R.homEquiv (𝟙 H)).1 (𝟙 _) f (𝟙 _) (by simp) (by rw [Category.comp_id, hf])) u := by
  intro A B _ _ _ r H R
  have key : ∀ {T : Scheme.{0}} (f : T ⟶ H), R.homEquiv f =
      ⟨f ≫ (R.homEquiv (𝟙 H)).1, ⟨(R.homEquiv (𝟙 H)).2.1.comap
        (GlobalTheory.HilbAff.bc A B (R.homEquiv (𝟙 H)).1 f), GlobalTheory.HilbAff.good_comap A B r _ f _
          (R.homEquiv (𝟙 H)).2.2⟩⟩ := fun f => by
    have := R.homEquiv_comp f (𝟙 H)
    rw [Category.comp_id] at this
    rw [this]; rfl
  refine ⟨(R.homEquiv (𝟙 H)).2.1.subscheme, (R.homEquiv (𝟙 H)).2.1.subschemeι, inferInstance,
    (R.homEquiv (𝟙 H)).2.2.1, (R.homEquiv (𝟙 H)).2.2.2.1, (R.homEquiv (𝟙 H)).2.2.2.2, ?_⟩
  intro T g V v hv h1 h2 h3
  have hG := GlobalTheory.HilbAff.good_ker A B r g v h1 h2 h3
  let y : (GlobalTheory.HilbAff.functor A B r).obj (op T) := ⟨g, ⟨v.ker, hG⟩⟩

  have cmp : ∀ (f : T ⟶ H) (hf : f ≫ (R.homEquiv (𝟙 H)).1 = g),
      pullback.map (GlobalTheory.HilbAff.str A B) g (GlobalTheory.HilbAff.str A B) (f ≫ (R.homEquiv (𝟙 H)).1)
          (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp [hf]) ≫
        GlobalTheory.HilbAff.bc A B (R.homEquiv (𝟙 H)).1 f =
      pullback.map _ g _ (R.homEquiv (𝟙 H)).1 (𝟙 _) f (𝟙 _) (by simp)
        (by rw [Category.comp_id, hf]) := by
    intro f hf
    apply pullback.hom_ext <;>
      simp only [GlobalTheory.HilbAff.bc, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]
  have cmp' : ∀ (f : T ⟶ H) (hf : f ≫ (R.homEquiv (𝟙 H)).1 = g),
      pullback.map (GlobalTheory.HilbAff.str A B) (f ≫ (R.homEquiv (𝟙 H)).1) (GlobalTheory.HilbAff.str A B) g
          (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp [hf]) ≫
        pullback.map _ g _ (R.homEquiv (𝟙 H)).1 (𝟙 _) f (𝟙 _) (by simp)
          (by rw [Category.comp_id, hf]) =
      GlobalTheory.HilbAff.bc A B (R.homEquiv (𝟙 H)).1 f := by
    intro f hf
    apply pullback.hom_ext <;>
      simp only [GlobalTheory.HilbAff.bc, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]
  let f := R.homEquiv.symm y
  have hfy : R.homEquiv f = y := Equiv.apply_symm_apply _ _
  rw [key] at hfy
  obtain ⟨hf, hI⟩ := GlobalTheory.HilbAff.sigma_inv A B r hfy
  have hcomap : (R.homEquiv (𝟙 H)).2.1.comap (pullback.map _ g _ (R.homEquiv (𝟙 H)).1 (𝟙 _) f
      (𝟙 _) (by simp) (by rw [Category.comp_id, hf])) = v.ker := by
    rw [hI, ← Scheme.IdealSheafData.comap_comp, cmp f hf]
  refine ⟨f, ⟨hf, ?_⟩, ?_⟩
  · have hle : ((R.homEquiv (𝟙 H)).2.1.subschemeι).ker ≤ (v ≫ pullback.map _ g _
        (R.homEquiv (𝟙 H)).1 (𝟙 _) f (𝟙 _) (by simp) (by rw [Category.comp_id, hf])).ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_comp,
        Scheme.IdealSheafData.le_map_iff_comap_le, hcomap]
    refine ⟨IsClosedImmersion.lift _ _ hle, ?_⟩
    exact isPullback_of_isClosedImmersion _ _ _ _ (IsClosedImmersion.lift_fac _ _ hle).symm
      (by rw [Scheme.IdealSheafData.ker_subschemeι, hcomap])
  · rintro f' ⟨hf', w', hpb⟩
    have hv : v.ker = (R.homEquiv (𝟙 H)).2.1.comap (pullback.map _ g _ (R.homEquiv (𝟙 H)).1 (𝟙 _)
        f' (𝟙 _) (by simp) (by rw [Category.comp_id, hf'])) := by
      rw [← hpb.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
        Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, Scheme.IdealSheafData.ker_subschemeι]
    have h' : R.homEquiv f' = y := by
      rw [key]
      refine GlobalTheory.HilbAff.sigma_eq A B r hf' ?_ _ _
      rw [hv, ← Scheme.IdealSheafData.comap_comp, cmp' f' hf']
    apply R.homEquiv.injective
    rw [h']
    exact (Equiv.apply_symm_apply R.homEquiv y).symm
