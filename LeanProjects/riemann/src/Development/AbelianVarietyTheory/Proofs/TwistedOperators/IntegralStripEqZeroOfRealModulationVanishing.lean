import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierUniquenessRealComponentsAdelicHomStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicStripSetMeasurableReadOnRealPartStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftUnfoldingIntegratedOverFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceMode
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.StripVanish

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W : HSp D} {ρ : ℕ} {Y : Type} [TopologicalSpace Y] [MeasurableSpace Y]

theorem dualPair_action_embedded_hyperbolic_extY (d : HypDec V V₀ ρ) (g : GA D V₀) (h : GA D W) (c : Mx D W.rank ρ) :
    actO V W (d.emb0 g) h (d.extY W c) = d.extY W (Formalism.L2.Theta.mt W h ⬝ c) := by
  simp only [actO]
  rw [show (d.emb0 g)⁻¹ = d.emb0 g⁻¹ from (map_inv _ _).symm]
  simp only [ HypDec.extY, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.mul_assoc, HypDec.wittDecomp_projY_anisotropicEmbedding]

theorem symplO_extX_extY_mt (d : HypDec V V₀ ρ) (h : GA D W) (x c : Mx D W.rank ρ) :
    symplO V W (d.extX W x) (d.extY W (Formalism.L2.Theta.mt W h ⬝ c)) =
      symplO V W (d.extX W (Formalism.L2.Theta.mt W h⁻¹ ⬝ x)) (d.extY W c) := by
  rw [← GlobalTheory.SplitHecke.symplO_actO V W 1 h⁻¹]
  congr 1
  · simp only [actO, HypDec.extX, AddMonoidHom.coe_mk, ZeroHom.coe_mk, inv_one, mt_one, Matrix.mul_one, Matrix.mul_assoc]
  · simp only [actO, HypDec.extY, AddMonoidHom.coe_mk, ZeroHom.coe_mk, inv_one, mt_one, Matrix.mul_one]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]

theorem tot_heisO_extY (a : Gen ψ V V₀ W ρ Y) (ha : a.Is) (G : GA D W → ℂ) (Φ : WO V W → ℂ) (hΦ : IsThetaFunO ψ V W Φ)
    (c : Mx D W.rank ρ) (p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank) :
    a.tot G (heisO ψ V W (a.d.extY W c) Φ) p =
      ψ (symplO V W (a.d.extX W (Formalism.L2.Theta.mt W p.1.1⁻¹ ⬝ ((rat a.x₀ : Mx D W.rank ρ) ⬝ p.2.1.1.1))) (a.d.extY W c)) *
        a.tot G Φ p := by
  simp only [Gen.tot, flFun]
  rw [ha.weil.om_heis _ _ _ _ hΦ, dualPair_action_embedded_hyperbolic_extY,
    (@GlobalTheory.HeisMixSource.heis_mixS D ψ ha.weil.std V V₀ W ρ a.d a.vS _ (ha.weil.om_pres _ _ hΦ)).2.1, Pi.smul_apply, smul_eq_mul,
    symplO_extX_extY_mt]
  ring

def pointHU (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (q : GA D W × UX D ρ) : Mx D W.rank ρ :=
  Formalism.L2.Theta.mt W q.1⁻¹ ⬝ ((rat x₀ : Mx D W.rank ρ) ⬝ q.2.1.1)

theorem measurable_pointHU (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) : Measurable (pointHU (W := W) x₀) := by
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  haveI : BorelSpace (Mx D W.rank ρ) := ⟨rfl⟩
  haveI : SecondCountableTopologyEither (GA D W) (UX D ρ) := secondCountableTopologyEither_of_left _ _
  haveI : OpensMeasurableSpace (GA D W × UX D ρ) := Prod.opensMeasurableSpace
  exact (((continuous_mt W).comp continuous_fst.inv).matrix_mul
      (continuous_const.matrix_mul (Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd)))).measurable

theorem measurable_point (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) :
    Measurable fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank =>
      Formalism.L2.Theta.mt W p.1.1⁻¹ ⬝ ((rat x₀ : Mx D W.rank ρ) ⬝ p.2.1.1.1) := by
  have h1 : Measurable fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank => (p.1.1, p.2.1) :=
    (measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)
  have h2 : Measurable (pointHU (W := W) x₀ ∘ fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank => (p.1.1, p.2.1)) :=
    Measurable.comp (measurable_pointHU x₀) h1
  exact h2

end GlobalTheory.StripVanish

open GlobalTheory.StripVanish in

theorem GlobalTheory.StripVanish.integral_strip_eq_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (Y : Type) [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (a : Gen ψ V V₀ W ρ Y), a.Is → ∀ (G : GA D W → ℂ), RapidDec W G → ∀ Φ : WO V W → ℂ, IsThetaFunO ψ V W Φ → (∀ c : Mx D W.rank ρ, c.map (finPart D) = 0 → a.lhs G (heisO ψ V W (a.d.extY W c) Φ) = 0) → ∀ 𝓑 : Set (GA D W), IsFundamentalDomain (GQ W ⊓ Rgrp W (rat a.x₀) : Subgroup (GA D W)) 𝓑 a.vW.μ → ∀ C : Set (GA D W), IsCompact C → C ⊆ GinfC W → ∫ h in 𝓑 ∩ strip W (Rgrp W (rat a.x₀)) C, a.ker G Φ h ∂a.vW.μ = 0 := by
  intro D ψ V V₀ W ρ Y _ _ _ _ a ha G hG Φ hΦ hvan 𝓑 h𝓑 C hC hCinf
  obtain ⟨hSmeas, S, hS, hSinf, hSiff⟩ := GlobalTheory.T.adelicStripSet_measurable_read_on_realPart D W ρ a.x₀ ha.base C hC hCinf
  obtain ⟨hint, -, -, hres⟩ := GlobalTheory.T.thetaLift_unfolding_integrated_over_family D ψ V V₀ W ρ Y a ha G Φ hG hΦ 𝓑 h𝓑
  rw [hres _ hSmeas]
  have hpre : {p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank | p.1.1 ∈ strip W (Rgrp W (rat a.x₀)) C} =
      (fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank =>
        Formalism.L2.Theta.mt W p.1.1⁻¹ ⬝ ((rat a.x₀ : Mx D W.rank ρ) ⬝ p.2.1.1.1)) ⁻¹' S := by
    ext p
    exact (hSiff p.1.1 p.2.1).symm
  rw [hpre]
  refine GlobalTheory.T.fourier_uniqueness_realComponents_adelicHom D ψ ha.weil.std V V₀ W ρ a.d _ (a.totMeas 𝓑) (a.tot G Φ) hint _ (measurable_point a.x₀) ?_ S hS hSinf
  intro c hc
  have h0 := hvan c hc
  rw [(GlobalTheory.T.thetaLift_unfolding_integrated_over_family D ψ V V₀ W ρ Y a ha G _ hG (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all ha.weil.std hΦ _) 𝓑 h𝓑).2.2.1] at h0
  simpa only [tot_heisO_extY a ha G Φ hΦ c] using h0
