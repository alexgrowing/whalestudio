import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

namespace GlobalTheory.LocOver.MoveTerm

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem mem_img (g : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) (x : V) : x ∈ img g Λ ↔ g.symm x ∈ Λ := by
  unfold img
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨g.symm x, h, by simp⟩

theorem map_mem_span_range {R : Type} [Semiring R] [Module R V] (φ : V →ₗ[R] V) {ι : Type} (v : ι → V)
    {x : V} (hx : x ∈ Submodule.span R (Set.range v)) :
    φ x ∈ Submodule.span R (Set.range fun a => φ (v a)) := by
  have := Submodule.apply_mem_span_image_of_mem_span φ hx
  rwa [← Set.range_comp] at this

variable (H : HermSp M V)

theorem h_symm {g : V ≃ₗ[E] V} (hg : IsUnitary H g) (x y : V) : H.h (g.symm x) (g.symm y) = H.h x y := by
  rw [← hg]; simp

theorem isSelfDual_img {g : V ≃ₗ[E] V} (hg : IsUnitary H g) {Λ : Submodule M.L.O V}
    (h : H.IsSelfDual Λ) : H.IsSelfDual (img g Λ) := by
  obtain ⟨hfg, hspan, hdual⟩ := h
  refine ⟨hfg.map _, ?_, fun x => ?_⟩
  · rw [eq_top_iff]
    intro x _
    have h1 : g.symm x ∈ Submodule.span E (Λ : Set V) := by rw [hspan]; trivial
    have h2 := Submodule.apply_mem_span_image_of_mem_span (g : V →ₗ[E] V) h1
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨y, hy, rfl⟩
    exact (mem_img g Λ _).2 (by simpa using hy)
  · rw [mem_img, hdual (g.symm x)]
    constructor
    · intro h y hy
      have := h _ ((mem_img g Λ y).1 hy)
      rwa [h_symm H hg] at this
    · intro h y hy
      have := h (g y) ((mem_img g Λ _).2 (by simpa using hy))
      rw [← hg (g.symm x) y, LinearEquiv.apply_symm_apply]; exact this

theorem prim_img (g : V ≃ₗ[E] V) {Λ : Submodule M.L.O V} {ι : Type} {v : ι → V}
    (h : H.Prim Λ v) : H.Prim (img g Λ) (fun a => g (v a)) := by
  obtain ⟨hmem, hli, hsat⟩ := h
  refine ⟨fun a => (mem_img g Λ _).2 (by simpa using hmem a), ?_, fun x hx hxs => ?_⟩
  · exact hli.map' (g : V →ₗ[E] V) (LinearEquiv.ker g)
  · have h1 : g.symm x ∈ Submodule.span E (Set.range v) := by
      have := map_mem_span_range (g.symm : V →ₗ[E] V) _ hxs
      simpa using this
    have h2 := hsat _ ((mem_img g Λ x).1 hx) h1
    have h3 := map_mem_span_range ((g : V →ₗ[E] V).restrictScalars M.L.O) _ h2
    simpa using h3

theorem isFrame_img {g : V ≃ₗ[E] V} (hg : IsUnitary H g) {Λ : Submodule M.L.O V} {r : ℕ}
    {f : Fin (r + 1) → V} {T : F} (h : H.IsFrame Λ r f T) :
    H.IsFrame (img g Λ) r (fun a => g (f a)) T := by
  obtain ⟨hp, hiso, hz, hT, hT0⟩ := h
  refine ⟨prim_img H g hp, fun a b hab => ?_, ?_, hT, hT0⟩
  · rw [hg]; exact hiso a b hab
  · rw [hg]; exact hz

theorem smulLat_img (g : V ≃ₗ[E] V) (c : E) {Λ : Submodule M.L.O V} {y : V}
    (hy : y ∈ H.smulLat c Λ) : g y ∈ H.smulLat c (img g Λ) := by
  unfold HermSp.smulLat at hy ⊢
  have := Submodule.apply_mem_span_image_of_mem_span ((g : V →ₗ[E] V).restrictScalars M.L.O) hy
  refine Submodule.span_mono ?_ (by simpa using this)
  rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
  exact ⟨g w, (mem_img g Λ _).2 (by simpa using hw), by simp⟩

theorem zhat_move {g : V ≃ₗ[E] V} (hg : IsUnitary H g) {r : ℕ} (f f' : Fin (r + 1) → V) :
    H.Zhat (fun a => g (f a)) (fun b => g (f' b)) = H.Zhat f f' := by
  ext a b
  exact hg _ _

theorem isTerm_move {r : ℕ} (g : V ≃ₗ[E] V) (t : Term V M r) (hg : IsUnitary H g) (ht : H.IsTerm t) :
    H.IsTerm (GlobalTheory.LocOver.move g t) := by
  obtain ⟨hSD, hF, hF', hU, hG, hsplit⟩ := ht
  have hD : ∀ l, H.Dl (GlobalTheory.LocOver.move g t).f (GlobalTheory.LocOver.move g t).f' l = H.Dl t.f t.f' l := by
    intro l
    unfold HermSp.Dl
    rw [show (GlobalTheory.LocOver.move g t).f = fun a => g (t.f a) from rfl,
      show (GlobalTheory.LocOver.move g t).f' = fun a => g (t.f' a) from rfl, zhat_move H hg]
  refine ⟨isSelfDual_img H hg hSD, isFrame_img H hg hF, isFrame_img H hg hF', ?_, ?_, fun gs hgs => ?_⟩
  · rw [hD]; exact hU
  · unfold HermSp.Gdet
    rw [hD, hD]
    exact hG
  · obtain ⟨h1, h2, h3⟩ := hsplit gs hgs
    refine ⟨h1, h2, fun b => ?_⟩
    show g (t.f' b) - g (t.f b) ∈ H.smulLat _ (img g t.abelian₂)
    rw [← map_sub]
    exact smulLat_img H g _ (h3 b)

end GlobalTheory.LocOver.MoveTerm

theorem GlobalTheory.LocOver.isTerm_move_of_unitary : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ} (g : V ≃ₗ[E] V) (t : Term V M r), IsUnitary H g → H.IsTerm t → H.IsTerm (GlobalTheory.LocOver.move g t) :=
  fun H _ g t hg ht => GlobalTheory.LocOver.MoveTerm.isTerm_move H g t hg ht
