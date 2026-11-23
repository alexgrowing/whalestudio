import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsDivPullEqVPull

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB
open GlobalTheory.QCoh (pullbackSections res_pullbackSections)
open GlobalTheory.Twist (resM app_resM)

namespace GlobalTheory.PullPull

section Sections

variable {X Y Z : Scheme.{0}}

theorem pullbackId_hom_app (E : X.Modules) {U V : X.Opens} (h : U ≤ (𝟙 X) ⁻¹ᵁ V) (h' : U ≤ V)
    (s : Γ(E, V)) :
    ((Scheme.Modules.pullbackId X).hom.app E).app U (pullbackSections (𝟙 X) E h s) =
      resM E h' s := by
  have e := unit_conjugateEquiv Adjunction.id
    (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)) (Scheme.Modules.pullbackId X).hom E
  rw [Scheme.Modules.conjugateEquiv_pullbackId_hom] at e
  refine (app_resM _ h _).trans ?_
  exact congrArg (resM _ h') congr(($e).app V s).symm

theorem pullbackComp_hom_app (b : Z ⟶ Y) (a : Y ⟶ X) (E : X.Modules) {U : X.Opens} {V : Y.Opens}
    {T : Z.Opens} (h₁ : V ≤ a ⁻¹ᵁ U) (h₂ : T ≤ b ⁻¹ᵁ V) (h : T ≤ (b ≫ a) ⁻¹ᵁ U) (s : Γ(E, U)) :
    ((Scheme.Modules.pullbackComp b a).hom.app E).app T
        (pullbackSections b _ h₂ (pullbackSections a E h₁ s)) =
      pullbackSections (b ≫ a) E h s := by
  rw [← Vert.DivPull.pullbackComp_inv_app b a E h₁ h₂ h s]
  have e : (Scheme.Modules.pullbackComp b a).inv.app E ≫
      (Scheme.Modules.pullbackComp b a).hom.app E = 𝟙 _ := by simp
  exact congr(($e).app T (pullbackSections (b ≫ a) E h s))

end Sections

section Met

variable {k : Type} [CommRing k] {X Y Z : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
  {E E' : X.Modules} {r : ℕ}

theorem eq_map_of_frames {h : Met p σ E r} {h' : Met p σ E' r} (φ : E ≅ E')
    (H : ∀ y, ∃ c : Chart E r, y ∈ ptsIn p σ c.U ∧ h'.G (c.map φ) y = h.G c y) : h' = h.map φ :=
  Met.ext_of_exists fun y => by
    obtain ⟨c, hc, e⟩ := H y
    exact ⟨c.map φ, hc, by rw [e, h.map_G φ c hc]⟩

theorem eq_map_pull_id (h : Met p σ E r) :
    h = (h.pull (𝟙 X) (Category.id_comp p)).map ((Scheme.Modules.pullbackId X).app E) := by
  refine eq_map_of_frames _ fun y => ?_
  obtain ⟨c, hc⟩ : ∃ c : Chart E r, PtsOver.map (𝟙 X) (Category.id_comp p) _ y ∈ ptsIn p σ c.U :=
    ⟨_, h.isVB.mem_pick _⟩
  refine ⟨Chart.pull c h.isVB (𝟙 X), hc, ?_⟩
  rw [h.pull_G _ _ _ hc, PtsOver.map_id]
  rw [PtsOver.map_id] at hc
  have hl : (𝟙 X) ⁻¹ᵁ c.U ≤ c.U := fun _ h => h
  have e (a : Fin r) : (Chart.map (Chart.pull c h.isVB (𝟙 X))
      ((Scheme.Modules.pullbackId X).app E)).e a = resM E hl (c.e a) :=
    pullbackId_hom_app E _ hl _
  ext a b
  rw [← h.form_frame (Chart.map (Chart.pull c h.isVB (𝟙 X))
    ((Scheme.Modules.pullbackId X).app E)) hc a b, ← h.form_frame c hc a b, e, e]
  exact h.form_resM _ _ hl hc

theorem pull_comp_eq_map (h : Met p σ E r) {q : Y ⟶ Sp k} {t : Z ⟶ Sp k} (π : Y ⟶ X) (τ : Z ⟶ Y)
    (hπ : π ≫ p = q) (hτ : τ ≫ q = t) (e : (τ ≫ π) ≫ p = t) :
    h.pull (τ ≫ π) e =
      ((h.pull π hπ).pull τ hτ).map ((Scheme.Modules.pullbackComp τ π).app E) := by
  refine eq_map_of_frames _ fun z => ?_
  obtain ⟨c, hc⟩ : ∃ c : Chart E r, PtsOver.map (τ ≫ π) e _ z ∈ ptsIn p σ c.U :=
    ⟨_, h.isVB.mem_pick _⟩
  have hc' : PtsOver.map π hπ _ (PtsOver.map τ hτ _ z) ∈ ptsIn p σ c.U := by
    rw [PtsOver.map_map]; exact hc
  refine ⟨Chart.pull (Chart.pull c h.isVB π) (h.pull π hπ).isVB τ, hc', ?_⟩
  have g₁ := (h.pull π hπ).pull_G τ hτ (Chart.pull c h.isVB π) hc'
  have g₂ := h.pull_G π hπ c hc'
  have g₃ : h.G c (PtsOver.map π hπ _ (PtsOver.map τ hτ _ z)) =
      h.G c (PtsOver.map (τ ≫ π) e _ z) := congrArg _ (PtsOver.map_map _ _ _ _ _ _)
  refine Eq.trans ?_ (g₁.trans (g₂.trans g₃)).symm
  have hT : τ ⁻¹ᵁ π ⁻¹ᵁ c.U ≤ (τ ≫ π) ⁻¹ᵁ c.U := fun _ h => h
  have f (a : Fin r) : (Chart.map (Chart.pull (Chart.pull c h.isVB π) (h.pull π hπ).isVB τ)
      ((Scheme.Modules.pullbackComp τ π).app E)).e a =
      pullbackSections (τ ≫ π) E hT (c.e a) :=
    pullbackComp_hom_app τ π E le_rfl le_rfl hT _
  refine Matrix.ext fun a b => ?_
  refine ((h.pull (τ ≫ π) e).form_frame (Chart.map (Chart.pull (Chart.pull c h.isVB π)
    (h.pull π hπ).isVB τ) ((Scheme.Modules.pullbackComp τ π).app E)) hc a b).symm.trans ?_
  refine Eq.trans ?_ (h.form_frame c hc a b)
  refine Eq.trans (congrArg₂ (fun s t => (h.pull (τ ≫ π) e).form s t z) (f a) (f b)) ?_
  exact h.form_pull (τ ≫ π) e _ _ hT hc

end Met

end GlobalTheory.PullPull

namespace GlobalTheory.VMetric

theorem isIsometry_pull_id_comp : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (E : X.Modules) (r : ℕ) (h : VMetric p E r), (h.pull (𝟙 X) (Category.id_comp p)).IsIsometry h ((Scheme.Modules.pullbackId X).app E) ∧ ∀ (Y Z : Scheme.{0}) (q : Y ⟶ Sp k) (t : Z ⟶ Sp k) (π : Y ⟶ X) (τ : Z ⟶ Y) (hπ : π ≫ p = q) (hτ : τ ≫ q = t) (e : (τ ≫ π) ≫ p = t), ((h.pull π hπ).pull τ hτ).IsIsometry (h.pull (τ ≫ π) e) ((Scheme.Modules.pullbackComp τ π).app E) := by
  intro k _ X p E r h
  refine ⟨isIsometry_iff _ |>.2 (VMetric.ext (funext fun σ => PullPull.eq_map_pull_id (h.met σ))), ?_⟩
  intro Y Z q t π τ hπ hτ e
  exact isIsometry_iff _ |>.2 (VMetric.ext (funext fun σ =>
    PullPull.pull_comp_eq_map (h.met σ) π τ hπ hτ e))

end GlobalTheory.VMetric
