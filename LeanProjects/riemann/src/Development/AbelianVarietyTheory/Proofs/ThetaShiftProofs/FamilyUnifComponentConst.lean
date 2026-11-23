import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

noncomputable section

namespace GlobalTheory

theorem isHolTo_comp_fin_one {X : Scheme.{0}} {B : Set ℂ} {y : ℂ → (Sp ℂ ⟶ X)} (h : IsHolTo B y) :
    IsHolTo {b : Fin 1 → ℂ | b 0 ∈ B} (fun b => y (b 0)) := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  have hc : Continuous (fun b : Fin 1 → ℂ => b 0) := continuous_apply (0 : Fin 1)
  refine ⟨h1.preimage hc, ?_⟩
  have hd : Differentiable ℂ (fun b : Fin 1 → ℂ => b 0) := differentiable_apply (0 : Fin 1)
  exact h2.comp hd.differentiableOn (fun b hb => hb)

theorem familyUnif_component_const :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo σ ty) (T : ℝ) (yw : ℂ → (Sp ℂ ⟶ Xo.X)), IsHolTo {w : ℂ | T < w.im} yw → (∀ w : ℂ, T < w.im → yw w ≫ Xo.s = spMap σ) → ∃ i, ∀ w : ℂ, T < w.im → ∃ P, IsPeriod (Fu.Di i) ty P ∧ Fu.u i P = yw w := by
  intro E _ _ _ H _ D l Xo σ g ty Fu T yw hhol hσ
  classical
  set B : Set (Fin 1 → ℂ) := {b | T < (b 0).im} with hB
  have hBo : IsOpen B := isOpen_lt continuous_const (Complex.continuous_im.comp (continuous_apply 0))
  have hBc : IsPreconnected B := by
    have hc : Convex ℝ B := by
      have := (convex_halfSpace_im_gt T).is_linear_preimage
        (f := fun b : Fin 1 → ℂ => b 0) ⟨fun _ _ => rfl, fun _ _ => rfl⟩
      exact this
    exact hc.isPreconnected
  have hy : IsHolTo B (fun b => yw (b 0)) := isHolTo_comp_fin_one hhol
  have hex : ∀ b : Fin 1 → ℂ, ∃ i : Fin Fu.n, b ∈ B → ∃ P, IsPeriod (Fu.Di i) ty P ∧ Fu.u i P = yw (b 0) := by
    intro b
    by_cases hb : b ∈ B
    · obtain ⟨i, P, h⟩ := Fu.onto _ (hσ (b 0) hb)
      exact ⟨i, fun _ => ⟨P, h⟩⟩
    · exact ⟨⟨0, Fu.n_pos⟩, fun h => absurd h hb⟩
  choose c hc using hex
  have hcont : ContinuousOn c B := by
    intro b₀ hb₀
    obtain ⟨B', i, P, ho, hm, hsub, hP, hu⟩ := Fu.lift 1 B _ hBo (fun b hb => hσ (b 0) hb) hy b₀ hb₀
    have key : ∀ b ∈ B', c b = i := by
      intro b hb
      obtain ⟨Q, hQ, hQu⟩ := hc b (hsub hb)
      exact Fu.disj _ _ Q (P b) hQ (hP.1 b hb) (hQu.trans (hu b hb).symm)
    have hev : c =ᶠ[nhds b₀] fun _ => i := Filter.eventually_of_mem (ho.mem_nhds hm) key
    exact (continuousAt_const.congr hev.symm).continuousWithinAt
  have h0 : (fun _ : Fin 1 => ((T + 1 : ℝ) : ℂ) * Complex.I) ∈ B := by
    simp [hB]
  refine ⟨c (fun _ : Fin 1 => ((T + 1 : ℝ) : ℂ) * Complex.I), fun w hw => ?_⟩
  have hwB : (fun _ : Fin 1 => w) ∈ B := hw
  rw [hBc.constant hcont h0 hwB]
  exact hc _ hwB

end GlobalTheory
