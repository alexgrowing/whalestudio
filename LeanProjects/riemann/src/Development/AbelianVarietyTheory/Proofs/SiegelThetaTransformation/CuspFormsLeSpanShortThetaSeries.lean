import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SpanGlue
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CuspFormsVanishingOffFramesLeSpanShortTheta
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReadingLinearIndependentAndInjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory

theorem mem_span_of_map_mem_span_image {K : Type*} [Field K] {σ : K →+* ℂ} {C : Type*} [AddCommGroup C]
    [Module K C] {W : Type*} [AddCommGroup W] [Module ℂ W] (j : C →ₛₗ[σ] W) (V : Submodule K C)
    (hj : ∀ (m : ℕ) (b : Fin m → C), (∀ i, b i ∈ V) → LinearIndependent K b →
      LinearIndependent ℂ (fun i => j (b i)))
    (S : Set C) (hS : S ⊆ V) {f : C} (hf : f ∈ V) (hjf : j f ∈ Submodule.span ℂ (j '' S)) :
    f ∈ Submodule.span K S := by
  let V' : Submodule K C := V ⊓ (Submodule.span ℂ (j '' S)).comap j
  have hSV : S ⊆ V' := fun s hs => ⟨hS hs, Submodule.subset_span ⟨s, hs, rfl⟩⟩
  have hind : ReciprocityTheory.ChartRestriction.G.PullbackSections.IndepToC (j.domRestrict V') := by
    intro m b hb
    exact hj m (fun i => (b i : C)) (fun i => (b i).2.1) (hb.map' V'.subtype (Submodule.ker_subtype V'))
  have himg : (j.domRestrict V') '' (V'.subtype ⁻¹' S) = j '' S := by
    ext w
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hSV hx⟩, hx, rfl⟩
  have htop := ReciprocityTheory.ChartRestriction.G.PullbackSections.span_eq_top_of_indepToC (j.domRestrict V') hind (V'.subtype ⁻¹' S)
    (fun g => by rw [himg]; exact g.2.2)
  have h1 : (⟨f, hf, hjf⟩ : V') ∈ Submodule.span K (V'.subtype ⁻¹' S) := by
    rw [htop]; exact Submodule.mem_top
  have h2 := Submodule.mem_map_of_mem (f := V'.subtype) h1
  rw [Submodule.map_span] at h2
  exact Submodule.span_mono (Set.image_preimage_subset _ _) h2

theorem cusp_le_span_shortGen : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r) (σ : c.F →+* ℂ), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ) → 1 ≤ r → l.A = 1 → (∀ k k', ((U σ).X k).Gm = ((U σ).X k').Gm ∧ ((U σ).X k).ξ0 = ((U σ).X k').ξ0) → (∀ k, HasPrinc ((U σ).X k) l.M) → (∀ a n, Dom a n → ∀ k, ChiOne ((U σ).X k) (Formalism.L2.PjFree.laU (U σ) a n k)) → ∀ (nab : NabV Xo c) (bad nV : ℕ) (dδ : ∀ n, DeltaDat Xo c n), 0 < bad → (∀ n, (dδ n).IsLev ∧ (∃ _ : StarRing (𝓞 E), IsNab (dδ n).Xo₂ (dδ n).c₂ (dδ n).nab₂) ∧ UnitC (dδ n) ∧ ¬ 3 ∣ (dδ n).pd ∧ (Dw.p + Dw.q ≤ n → ∃ ph ψ x₀, (dδ n).PhiPin ph ψ x₀) ∧ ∀ a, Dom a n → ShortValTot Xo c nab bad nV a n (dδ n)) → SpanningAtDominantWeight Xo c nab bad nV (Formalism.L2.PjFree.cusp Xo c U) dδ := by
  intro hC E _ _ _ H Dw l Xo c r U σ hσ hU hr hA hG hP hχ nab bad nV dδ hbad hd a n hDom _ hn f hf
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hd n
  have hrk : 4 * (Module.finrank ℚ E * r) + 4 ≤ n := by
    have he : Module.finrank ℚ E = 2 * NumberField.InfinitePlace.nrComplexPlaces E :=
      NumberField.IsTotallyComplex.finrank E
    have hr' : r = Dw.p + Dw.q := hU.1
    rw [he, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2), ← hr'] at hn
    rw [he]
    calc 4 * (2 * NumberField.InfinitePlace.nrComplexPlaces E * r) + 4
        = 8 * NumberField.InfinitePlace.nrComplexPlaces E * r + 4 := by ring
      _ ≤ n := hn
  have hsp := GlobalTheory.Dict.holSub0_le_span_shortGen hC E H Dw l Xo c n (dδ n) σ r (U σ) hσ hU hr hA hG hP h1 h2 h3 h4 h5 nab bad nV a
    hbad hDom hrk (hχ a n hDom) (h6 a hDom)
  have hf' := (Formalism.L2.PjFree.mem_cusp Xo c U a n f).1 hf
  have hind := (GlobalTheory.reading_linearIndependent_and_injective GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c σ r
    (U σ) hU a n).1
  refine mem_span_of_map_mem_span_image (Formalism.L2.PjFree.rdU (U σ)) (sec Xo c a n) hind _ (fun g hg => hg.1) hf'.1 (hsp ?_)
  refine ⟨hf'.2 σ hσ, fun k x hx => ?_⟩
  exact dif_neg hx

end GlobalTheory
