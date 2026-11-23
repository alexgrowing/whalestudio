import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArcZeroZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceComponentSmoothProjectiveConnectedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionExtensionOfDenseLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothAffineChartBoundaryZeroSetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionOfArcVanishingSmoothChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArcZeroCuspSec

noncomputable section

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter Topology NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.Vanishing
open GlobalTheory.FlagMod (FlagCover)

theorem ext_of_arcZero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (la : GlobalTheory.AllWt.Weight Dw) (σ : c.F →+* ℂ),
    IsVariety₀ TF.X Z → ∀ m : H0 (str₀ TF.X Z) (L₀ TF.X Z la) (U₀ TF.X Z), ArcZero TF.X Z la σ m →
      ∃ s ∈ vanBd TF.X Z la, H0.restr le_top s = m := by
  intro E _ _ _ H Dw l Xo c TF Z la σ hv m hm
  obtain ⟨s, hs, hz⟩ := GlobalTheory.T.exists_section_extension_of_dense_local (str₀ TF.X Z) (L₀ TF.X Z la) (isLB_L₀ TF.X Z la) (U₀ TF.X Z) (dense_U₀ TF.X Z) m
    fun y _ => by
      obtain ⟨W, hW, i, p, hyW, hi, hd, hsm, hp, hb⟩ := GlobalTheory.T.exists_smooth_affine_chart_boundary_zero_set E H Dw l Xo c TF Z la hv y
      obtain ⟨b, h1, h2⟩ := GlobalTheory.T.exists_extension_of_arc_vanishing_smooth_chart E H Dw l Xo c TF.Y TF.X Z la σ m hm W hW i p hi hd hsm hp hb
      exact ⟨W, i, hi, b, hyW, h1, fun y' h h' => h2 y' h h'⟩
  exact ⟨s, fun y hy i hi => hz y hy i hi, hs⟩

end GlobalTheory.CompHS

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal GlobalTheory.KoecherArc

theorem arcZero_cusp : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (la : AllWt.Weight (T.Q.Dw j)), ∀ σ : Y.d.c₂.F →+* ℂ, GoodEmb Y.d.c₂ σ → ∀ f : Cusp Z Y.U la, ArcZero TF.X Z la σ (cuspSec TF.X Z Y.U la f) := by
  intro D T j Y e o hY Z TF la σ hσ f
  haveI : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)
  have hU := hY.unf σ hσ
  obtain ⟨hfW, -⟩ := Submodule.mem_inf.1 f.2
  obtain ⟨-, hhol⟩ := AllWt.mem_cuspW.1 hfW
  have hS := GlobalTheory.CuspSecFin.mem_SS_of_mem_holSub _ _ (hhol σ hσ)
  have hχ := AllWt.Model.chi_modelWt (Y.U σ) (hY.chiTriv σ hσ) (AllWt.wtOf _ la 0) (AllWt.even_wtOf la 0)
  have he : AllWt.exOf (T.Q.Dw j) la 0 none = 0 := by
    show (AllWt.wtOf (T.Q.Dw j) la 0).2 = 0
    rw [AllWt.wtOf_snd, mul_zero]
  intro W hW i hWi ψ r hψ hs hin hout ε hε
  obtain ⟨φ, x, fr, y, hb, hm, hval⟩ := GlobalTheory.T.exists_eigenFrame_along_arc_flagSpaceChart TF Z la σ hσ W hW i hWi ψ r hψ hs hin hout
  obtain ⟨ρ, p, q, hρ, hρr, hpq⟩ := GlobalTheory.T.exists_holomorphic_quotient_along_arc (cuspSec TF.X Z Y.U la f) W hW i hWi ψ r hψ hout
  have hi : ∀ u, ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) ⁻¹ᵁ
      (L₀ TF.X Z la).U i := fun u s _ => hWi (hW.range_fromSpec.le ⟨_, rfl⟩)
  let g : AllWt.secZ Y.d.Xo₂ Y.d.c₂ (AllWt.exOf (T.Q.Dw j) la 0) := ⟨f.1, cusp_le_secZ Z Y.U la f.2⟩
  have hv : ∀ u ∈ Metric.ball (0 : ℂ) ρ, u ≠ 0 → ψ u q ≠ 0 ∧ toC (evR _ _ g.1 (y u)) * ψ u q = ψ u p :=
    fun u hu h => by
      have hur : u ∈ Metric.ball (0 : ℂ) r := Metric.ball_subset_ball hρr hu
      refine ⟨(hpq u hu h).1, ?_⟩
      rw [← hval g u hur h (hout u hur h) (hi u)]
      exact (hpq u hu h).2 _ _
  have ht := tendsto_val TF.Y hσ hU _ hχ he g.2 hS fr (isBdArc_mono hb hρ hρr)
    (fun u hu h => hm u (Metric.ball_subset_ball hρr hu) h) p q hv
  have h2 : Tendsto (fun u => ‖toC (evR _ _ g.1 (y u))‖) (𝓝[≠] 0) (𝓝 0) := by simpa using ht.norm
  filter_upwards [h2.eventually (gt_mem_nhds hε), self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℂ) hρ)] with u h1 h3 h4 hO hi'
  rw [show cuspSec TF.X Z Y.U la f = sec₀ TF.X Z _ g from rfl,
    hval g u (Metric.ball_subset_ball hρr h4) h3 hO hi']
  exact h1

end GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

theorem GlobalTheory.CompHS.cusp_extends_comp : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (la : AllWt.Weight (T.Q.Dw j)), Extends TF.X Z Y.U la := by
  intro D T j Y e o hG hE Z TF la
  have hσ : GoodEmb Y.d.c₂ Y.d.c₂.F.val.toRingHom := rfl
  intro f
  exact ext_of_arcZero _ _ _ _ _ _ TF Z la _ (GlobalTheory.T.flagSpace_component_smooth_projective_connected _ _ _ _ _ _ TF Z hG.geo) _
    (arcZero_cusp D T j Y e o hG Z TF la _ hσ f)
