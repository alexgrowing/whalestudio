import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Formalism.LocalToGlobal.ProjectiveLattices.ReadQuot
import Formalism.LocalToGlobal.ProjectiveLattices.ReadLeaves
import Development.AbelianVarietyTheory.Proofs.HeightProofs.VolPairExAndFinVol
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoreGoodMatch
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.LocClauseOfUnifPlaces
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open MeasureTheory Formalism.L2.Theta Formalism.BasicNotions.TH ReciprocityTheory.ChartRestriction.G.FD Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Topology TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IntWtRead

open Formalism.L2.Pj

theorem wtAllZ_of_borChart {K : Type} [Field K] {ι : Type} [Fintype ι]
    {pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type}
    {mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T], (S →ₐ[K] T) → pts S → pts T → Prop}
    {borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop}
    (h : BorChart pts mapR borR) (e : ι → ℤ) {f : Rules pts} (hf : IsNatural pts mapR f)
    (hw : ∀ (p : TRing K) (t : ι → (p.R)ˣ) (y y' : pts p.R), borR t y y' →
      f p y' = ((∏ i, t i ^ e i : (p.R)ˣ) : p.R) * f p y)
    (S : Type) [CommRing S] [Algebra K S] (t : ι → Sˣ) (y y' : pts S) (hy : FromTest pts mapR y)
    (hy' : FromTest pts mapR y') (hb : borR t y y') :
    evalAt pts mapR f y' = ((∏ i, t i ^ e i : Sˣ) : S) * evalAt pts mapR f y := by
  unfold evalAt
  rw [dif_pos hy, dif_pos hy']
  apply eq_of_locM (K := K)
  intro m hm
  obtain ⟨A, u, c, c', B, uB, uB', tB, π, π', cB, hc, hc', hπ, hπ', hbB, e1, e2, e3⟩ := h S t y y' hb m
  rw [map_mul, chartAt_val hf hc' hy'.choose_spec.choose_spec.choose_spec,
    chartAt_val hf hc hy.choose_spec.choose_spec.choose_spec, ← e1, ← e2, AlgHom.comp_apply, AlgHom.comp_apply,
    ← hf A B π u uB hπ, ← hf A B π' u uB' hπ', hw B tB uB uB' hbB, map_mul]
  congr 1
  have hu : ∀ i, Units.map (cB : B.R →* Localization.AtPrime m) (tB i)
      = Units.map ((locM K m : S →ₐ[K] Localization.AtPrime m) : S →* Localization.AtPrime m) (t i) :=
    fun i => Units.ext (by simpa using e3 i)
  have h1 : cB ((∏ i, tB i ^ e i : (B.R)ˣ) : B.R) =
      ((Units.map (cB : B.R →* Localization.AtPrime m) (∏ i, tB i ^ e i) : (Localization.AtPrime m)ˣ) :
        Localization.AtPrime m) := rfl
  have h2 : locM K m ((∏ i, t i ^ e i : Sˣ) : S) =
      ((Units.map ((locM K m : S →ₐ[K] Localization.AtPrime m) : S →* Localization.AtPrime m)
        (∏ i, t i ^ e i) : (Localization.AtPrime m)ˣ) : Localization.AtPrime m) := rfl
  rw [h1, h2, map_prod, map_prod]
  simp only [map_zpow, hu]

end GlobalTheory.IntWtRead

namespace GlobalTheory.IntWtRead

open Formalism.L2.Pj

set_option maxHeartbeats 800000 in

theorem cuspW_eq_zero_of_reading : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ σ : Y.d.c₂.F →+* ℂ, GoodEmb Y.d.c₂ σ → ∀ (G : WTZ D.host.E) (x : Y.V G), (∀ k, ∀ z ∈ ((Y.U σ).X k).dom, rdU (Y.U σ) (x : Rul Y.d.Xo₂ Y.d.c₂) k z = 0) → x = 0 := by
  intro D T j Y e o hY σ hσ G x h0
  have hS : Out.SecBaseChangeSt := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hU := hY.unf σ hσ
  obtain ⟨-, hB, hW, -, -, -, -⟩ := GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hS _ _ _ _ Y.d.Xo₂ Y.d.c₂
  have hall : AllTest Y.d.Xo₂ Y.d.c₂ := GlobalTheory.T.framedPoint_reduced_from_testRing hS _ _ _ _ Y.d.Xo₂ Y.d.c₂
  have hx : (x : Rul Y.d.Xo₂ Y.d.c₂) ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (exZ _ G) :=
    GlobalTheory.AllWt.cuspW_le_secZ G x.2
  apply Subtype.ext
  funext p y
  show (x : Rul Y.d.Xo₂ Y.d.c₂) p y = 0
  refine eq_zero_of_cpts σ p _ fun ψ => ?_
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS _ _ _ _ Y.d.Xo₂ Y.d.c₂ p.R (CAt σ) ψ y
  obtain ⟨k, x', t, ht⟩ := hU.2.2.1 z
  have hft : FromTest (K := Y.d.c₂.F) (fun S _ _ => FrPt Y.d.Xo₂ Y.d.c₂ S) (fun φ y z => FrMap φ y z) z :=
    ⟨p, ψ, y, hz⟩
  have hev : evR Y.d.Xo₂ Y.d.c₂ (x : Rul Y.d.Xo₂ Y.d.c₂) z = ψ ((x : Rul Y.d.Xo₂ Y.d.c₂) p y) := by
    unfold evR evalAt
    rw [dif_pos hft]
    exact hW _ hx.1 (CAt σ) _ p _ ψ _ y z hft.choose_spec.choose_spec.choose_spec hz
  haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  have hw := wtAllZ_of_borChart hB (exZ _ G) hx.1 hx.2 (CAt σ) t _ z (hall _ _) (hall _ _) ht
  have h1 := h0 k x'.1 x'.2
  have h2 : toC (evR Y.d.Xo₂ Y.d.c₂ (x : Rul Y.d.Xo₂ Y.d.c₂) ((Y.U σ).un k x')) = 0 := by
    rw [← h1]
    classical
    show _ = (if h : x'.1 ∈ ((Y.U σ).X k).dom then toC (evR Y.d.Xo₂ Y.d.c₂ (x : Rul Y.d.Xo₂ Y.d.c₂) ((Y.U σ).un k ⟨x'.1, h⟩)) else 0)
    rw [dif_pos x'.2]
  have h3 : evR Y.d.Xo₂ Y.d.c₂ (x : Rul Y.d.Xo₂ Y.d.c₂) ((Y.U σ).un k x') = 0 := h2
  rw [← hev]
  unfold evR
  rw [hw]
  unfold evR at h3
  rw [h3, mul_zero]

end GlobalTheory.IntWtRead
