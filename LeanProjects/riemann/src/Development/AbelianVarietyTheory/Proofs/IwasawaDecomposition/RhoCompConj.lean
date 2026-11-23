import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousAndExistsConjChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjSmoothOnPreimageCharts
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.RhoConj

open ReciprocityTheory.L2DbarEstimates (V leviV)

def starEquiv (d : ℕ) : (Fin d → ℂ) ≃ₗ[ℝ] (Fin d → ℂ) where
  toFun := star
  invFun := star
  map_add' := star_add
  map_smul' r x := by
    ext i
    simp [Complex.conj_ofReal]
  left_inv := star_star
  right_inv := star_star

theorem rho_comp_conj : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (σ σ' : F →+* ℂ) (ι : Pts Y σ' → Pts Y σ) (a : ChartForm Y.str σ Y.dim) (a' : ChartForm Y.str σ' Y.dim) (E : ChartMap Y.str σ Y.dim) (E' : ChartMap Y.str σ' Y.dim), IsConjMap ι → IsKaehlerForm (Y.an σ) a → IsKaehlerForm (Y.an σ') a' → (∀ W φ, IsPotential (Y.an σ) a W φ → IsPotential (Y.an σ') a' (ι ⁻¹' W) (φ ∘ ι)) → IsExph a E → IsExph a' E' → ConjComm ι E E' → ∀ (ψ : Pts Y σ → ℝ) (z : Pts Y σ') (t : ℝ), rho a' E' (ψ ∘ ι) z t = rho a E ψ (ι z) t := by
  intro F _ _ Y σ σ' ι a a' E E' hj ha ha' hpot hE hE' hc ψ z t
  have hσ : σ = (starRingEnd ℂ).comp σ' := by
    have h1 := (ι z).2
    rw [hj z, Category.assoc, z.2, spMap, spMap, spMap, ← Spec.map_comp] at h1
    have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    exact h2.symm
  obtain ⟨c', hz⟩ := AlgChart.exists_mem_source (D := Y.dim) z
  obtain ⟨-, hch⟩ := GlobalTheory.ConjChart.continuous_and_exists_conj_chart F Y.X Y.str Y.dim σ σ' ι hσ hj
  obtain ⟨c, hs, he⟩ := hch c'
  have e1 : ∀ w ∈ c'.e.source, c.e (ι w) = conjV Y.dim (c'.e w) := fun w hw => by
    ext i
    rw [he w hw i, conjV_apply]
  have e2 : ∀ v ∈ c'.e.target, ι (c'.e.symm v) = c.e.symm (conjV Y.dim v) := fun v hv => by
    have hw : c'.e.symm v ∈ c'.e.source := c'.e.map_target hv
    rw [← c.e.left_inv ((hs _).2 hw), e1 _ hw, c'.e.right_inv hv]
  have hιz : ι z ∈ c.e.source := (hs z).2 hz

  have hEE : ∀ ξ, ι (E' c' z ξ) = E c (ι z) (star ξ) :=
    hc c c' (fun w hw _ i => by rw [he w hw i, Complex.conj_conj]) z hz hιz

  have hddc : ∀ (φ : Pts Y σ → ℝ) (ξ : Fin Y.dim → ℂ), ddcForm (φ ∘ ι) c' z ξ = ddcForm φ c (ι z) (star ξ) := by
    intro φ ξ
    have h := leviV_comp_conjV Y.dim (fun v => φ (c.e.symm v)) (c'.e z) ξ
    simp only [ddcForm, AlgChart.levi]
    congr 1
    rw [e1 z hz]
    refine Eq.trans (congrArg Complex.re (ReciprocityTheory.L2DbarEstimates.leviV_congr ?_ ξ))
      (Eq.trans (congrArg Complex.re h) (Complex.conj_re _))
    refine Filter.eventually_of_mem (c'.e.open_target.mem_nhds (c'.e.map_source hz)) fun v hv => ?_
    simp only [Function.comp_apply, e2 v hv]
  have haa : ∀ ξ, a' c' z ξ = a c (ι z) (star ξ) := by
    obtain ⟨W, φ, hW, hp⟩ := ha.1 (ι z)
    have hp' := hpot W φ hp
    intro ξ
    rw [hp'.2.2 c' z hz hW ξ, hp.2.2 c (ι z) hιz hW, hddc]
  rw [rho_eq ha' hE' _ hz, rho_eq ha hE _ hιz, rhoIn, rhoIn, ← mean_comp (a c (ι z)) _ (starEquiv Y.dim)]
  congr 1
  · exact funext fun ξ => haa ξ
  · funext ξ
    simp only [Function.comp_apply, hEE]
    congr 2
    exact (starEquiv Y.dim).map_smul t ξ

end GlobalTheory.ShFam.RhoConj
