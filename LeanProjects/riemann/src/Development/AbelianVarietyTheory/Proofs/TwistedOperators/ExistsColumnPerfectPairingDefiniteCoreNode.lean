import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TopColumn

open GlobalTheory.DefiniteMult GlobalTheory.DefLift

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {θ : InfFam D} {c : CoefA V}
  {pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ}

set_option maxHeartbeats 1000000 in

theorem exists_form_triv (hθ : IsInfFam θ) (hp : AllPlus M) (hc : c.Is) (hpr : IsDualPair θ M c pr)
    (K : Subgroup (GA D V)) (J : Subgroup (Bridge.Gf V))
    (hJ : ∀ κ ∈ GfC V, (finHom V).rangeRestrict κ ∈ J → κ ∈ K)
    {T : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hT : T ∈ MultT θ M (K : Set (GA D V)) 1) :
    ∃ f ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ J 1, c.toMap pr f = T := by
  have m := AllPlus.finite_smooth_irreducible D V S M hp
  have h2 := tensor_irreducible D V S M m hp
  obtain ⟨fd, inj, πt, hπ, irr⟩ := h2
  have key := pair_tens hp (fun τ => (m τ).2.1) inj hπ hpr
  have hb := pair_bijective hθ hp hc hpr
  have hE := GlobalTheory.multT_cont_left_equiv D θ V S M πt _ _ hp (fun τ => (m τ).2.1) inj hπ T hT
  choose Ψ hΨ using fun h : GA D V => hb.2 (LinearMap.proj h ∘ₗ T)
  replace hΨ : ∀ h x, pr (Ψ h) x = T x h := fun h x => LinearMap.congr_fun (hΨ h) x
  have hlev : ∀ k ∈ K, ∀ x g, T x (g * k) = T x g := fun k hk x g => by
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      have := (GlobalTheory.mult_value_left_cont_level θ M _ _ _ ((mem_multT θ M _ _ _).1 hT) v).2.2 k hk g
      rw [Pi.one_apply, one_mul] at this
      rw [map_smul, Pi.smul_apply, Pi.smul_apply]
      exact congrArg (r • ·) this
    | add x y hx hy => rw [map_add, Pi.add_apply, Pi.add_apply, hx, hy]
  let U : Submonoid (GA D V) :=
    { carrier := {a | ∀ h, Ψ (h * a) = c.ρ a⁻¹ (Ψ h)}
      one_mem' := fun h => by rw [mul_one, inv_one, map_one]; rfl
      mul_mem' := fun {a b} ha hb h => by rw [← mul_assoc, hb, ha, mul_inv_rev, map_mul]; rfl }
  obtain ⟨f, hf⟩ := exists_descend (finHom V) c.ρ Ψ fun a ha => real_le hθ U (fun τ g hg h => by
      obtain ⟨u, rfl⟩ := hp.exists_unfr τ hg
      refine hb.1 (LinearMap.ext fun x => ?_)
      rw [← key, hΨ, hΨ, (hE x).2.2]; rfl) ha
  refine ⟨f, mem_adForms (finHom V) (GQ V) (GfC V) (exists_fin_lift V) c.ρ hc.1 _ _ Ψ f hf fun γ hγ g κ hκ hk => ?_,
    LinearMap.ext fun x => funext fun h => ?_⟩
  · have e2 : Ψ (γ * g * κ) = Ψ g := by
      refine hb.1 (LinearMap.ext fun x => ?_)
      rw [hΨ, hΨ, hlev κ (hJ κ hκ hk), (hE x).2.1 γ hγ]
    rw [e2]
    simp
  · have e := GlobalTheory.DefiniteEnd.rho_inv_cancel (c := c) h⁻¹ (Ψ h)
    rw [inv_inv] at e
    exact (congrArg (fun w => pr w x) ((congrArg (c.ρ h⁻¹) (hf h)).trans e)).trans (hΨ h x)

end GlobalTheory.TopColumn

theorem GlobalTheory.TopColumn.exists_col : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (θ : InfFam D), IsInfFam θ → ∀ {S : D.what₂.Tau → SPar} (M : DSModel (G.V (.core D.R.m)) S), (∀ τ a, M.ε τ a = true) → (coefPlus G θ).Is → ∀ (pr : (coefPlus G θ).W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ), IsDualPair θ M (coefPlus G θ) pr → ∀ y ∈ CoreForms G θ D.R.m M, ∃ c ∈ Cols G θ, (coefPlus G θ).toMap pr c = y := by
  intro D T L sc G θ hθ S M hε hc pr hpr y hy
  exact GlobalTheory.TopColumn.exists_form_triv (V := G.V (.core D.R.m)) (c := coefPlus G θ) hθ hε hc hpr
    (lev G (.core D.R.m)) (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.levPlus G) (fun κ hκ h => ⟨hκ, h⟩) hy
