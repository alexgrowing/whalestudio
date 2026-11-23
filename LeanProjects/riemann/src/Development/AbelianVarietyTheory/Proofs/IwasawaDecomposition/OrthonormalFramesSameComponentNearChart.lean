import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricUniformisationSmoothOnInterior
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExponentialModelFiberOfUniformisationExp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolomorphicUniformisationExpModelFiber
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpModelFiberEqOneIffMemPeriodLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilPairingExpModelFiberEqAlternatingForm
open AlgebraicGeometry CategoryTheory Limits MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.FrameNormLie GlobalTheory.HodgeSmooth
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

theorem GlobalTheory.HodgeSmooth.chart_comp_locconst : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → ∀ (n : ℕ) (ch : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr Z) σ) (Fin n → ℂ)), IsHolTo ch.target (fun z => (ch.symm z).1) → ∀ (k₀ : U.Comp) (x₀ : (U.X k₀).dom), cxPt Z (U.un k₀ x₀) ∈ ch.source → ∃ B : Set (Fin n → ℂ), IsOpen B ∧ ch (cxPt Z (U.un k₀ x₀)) ∈ B ∧ ∀ z ∈ B, ∀ (k : U.Comp) (x : (U.X k).dom), cxPt Z (U.un k x) = ch.symm z → k = k₀ := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ r U hσ hU h1 n ch hsy k₀ x₀ hy₀
  obtain ⟨W, hinj⟩ := GlobalTheory.HodgeSmooth.exists_unfWit_inj hσ hU h1
  have := Z.jQ_open
  have hB₀ := (hsy Z.jQ.opensRange 0).1
  set B₀ := {b ∈ ch.target | ⊤ ≤ (ch.symm b).1 ⁻¹ᵁ Z.jQ.opensRange} with hB₀def
  set y₀ := U.un k₀ x₀ with hy₀def
  have hb₀ : ch (cxPt Z y₀) ∈ B₀ := by
    refine ⟨ch.map_source hy₀, ?_⟩
    rw [ch.left_inv hy₀]
    intro s _
    exact ⟨GlobalTheory.AllWt.ptF (S := Formalism.L2.Pj.CAt σ) y₀ s, (Scheme.Hom.comp_apply (GlobalTheory.AllWt.ptF (S := Formalism.L2.Pj.CAt σ) y₀) Z.jQ s).symm⟩
  have : Nonempty (Sp ℂ ⟶ Xo.XF c) := ⟨GlobalTheory.AllWt.ptF (S := Formalism.L2.Pj.CAt σ) y₀⟩
  have hw : ∀ b ∈ B₀, ∃ w : Sp ℂ ⟶ Xo.XF c, w ≫ Z.jQ = (ch.symm b).1 := fun b hb =>
    ⟨IsOpenImmersion.lift Z.jQ _ (by rintro _ ⟨s, rfl⟩; exact hb.2 (Set.mem_univ s)), IsOpenImmersion.lift_fac _ _ _⟩
  choose! w hw using hw
  have hwh : IsHolTo B₀ w := GlobalTheory.TrueCx.TorHolo.isHolTo_of_openImmersion Z.jQ
    (GlobalTheory.LocLift.isHolTo_congr (GlobalTheory.LocLift.isHolTo_mono hsy hB₀ fun b hb => hb.1) hw)
  have hyh := ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp hwh (pullback.fst _ _)
  have hsnd : ∀ b ∈ B₀, w b ≫ pullback.snd _ _ = spMap σ := fun b hb => by
    rw [← Z.jQ_over, ← Category.assoc, hw b hb]
    exact (ch.symm b).2
  obtain ⟨B, i, P, hB, hbB, hsub, hP, hu⟩ := W.F.lift n B₀ (fun x => w x ≫ pullback.fst _ _) hB₀
    (fun x hx => by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hsnd _ hx, ← Spec.map_comp]
      rfl) hyh _ hb₀
  have hik : ∀ z ∈ B, ∀ (k : U.Comp) (x : (U.X k).dom), cxPt Z (U.un k x) = ch.symm z → W.ik k = i := by
    intro z hz k x hkx
    have h1' : w z = GlobalTheory.AllWt.ptF (S := Formalism.L2.Pj.CAt σ) (U.un k x) :=
      (cancel_mono Z.jQ).1 ((hw z (hsub hz)).trans (congrArg Subtype.val hkx.symm))
    have h2 : W.F.u i (P z) = (U.un k x).x := by
      rw [hu z hz, h1']
      exact GlobalTheory.ShFam.ptF_fst _
    exact W.F.disj _ _ _ _ (W.period k x) (hP.1 z hz) ((W.lie k x).1.symm.trans h2.symm)
  have hk₀ : W.ik k₀ = i := hik _ hbB k₀ x₀ (by rw [ch.left_inv hy₀])
  exact ⟨B, hB, hbB, fun z hz k x hkx => hinj ((hik z hz k x hkx).trans hk₀.symm)⟩
