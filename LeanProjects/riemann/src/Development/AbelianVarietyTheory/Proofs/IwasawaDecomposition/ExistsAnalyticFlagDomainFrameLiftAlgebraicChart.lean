import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultOfNotMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricUniformisationSmoothOnInterior
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtEqOfPtOfFrameEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicChartLiftHolomorphicPeriodMapsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodMapMemberEqFramePeriodMapLinearChangeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticFrameFamilyOfHolomorphicPeriodMapsStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase

theorem exists_analytic_frame_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∃ (k' : U.Comp) (s : ReciprocityTheory.L2DbarEstimates.V X.dim → ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k').Ψ (Dw.p + Dw.q)), AnalyticAt ℂ s (c'.e y) ∧ ∀ᶠ w in 𝓝 (c'.e y), ∃ hs : s w ∈ (U.X k').dom, cxPt T.Z (U.un k' ⟨s w, hs⟩) = cxOf e σ hj (c'.e.symm w) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU X j hj hjo y hy c' hyc
  rcases Nat.eq_zero_or_pos (Dw.p + Dw.q) with hr | hr
  · obtain ⟨W⟩ := GlobalTheory.ArcQ.nonempty_unfWit_of_isUnf _ _ _ _ _ _ _ _ U hU
    obtain ⟨i, B, P, hB, hb₀, -, hper, -, hq⟩ := GlobalTheory.T.algebraicChart_lift_holomorphic_periodMaps E H Dw l Xo c O β Y T F e σ W.g _ W.F X j hj hjo y hy c' hyc
    obtain ⟨q₀, hq₀, hu₀⟩ := hq _ hb₀
    have hne : ¬ LiesIn (cxOf e σ hj y) (genBd T.Z) := by
      rw [← c'.e.left_inv hyc, ← hq₀]; exact not_liesIn_cxPt q₀
    obtain ⟨k, x, -, hkx⟩ := GlobalTheory.HodgeSmooth.exists_orth (Z := T.Z) hσ hU hne
    have hg : IsEmpty (Fin W.g) := by
      refine ⟨fun a => ?_⟩
      have := (W.e a).2.2
      simp only [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult] at this
      split_ifs at this <;> omega
    refine ⟨k, fun _ => x.1, analyticAt_const, Filter.mem_of_superset (hB.mem_nhds hb₀) fun w hw => ⟨x.2, ?_⟩⟩
    obtain ⟨q, hq1, hq2⟩ := hq w hw
    have hfib : W.F.u i (P (c'.e y)) = W.F.u i (P w) :=
      (W.F.fibre i _ _ (hper _ hb₀) (hper w hw)).2 ⟨LinearEquiv.refl _ _, LinearEquiv.refl _ _, fun _ _ => rfl,
        fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩, fun a => funext fun t => (hg.false t).elim⟩
    have e1 : cxPt T.Z q₀ = cxPt T.Z q := cxPt_congr (hu₀.symm.trans (hfib.trans hq2))
    rw [← hq1, ← e1, hq₀, c'.e.left_inv hyc]
    exact hkx
  · obtain ⟨W, hinj⟩ := GlobalTheory.HodgeSmooth.exists_unfWit_inj hσ hU hr
    obtain ⟨i, B, P, hB, hb₀, -, hper, hdiff, hq⟩ := GlobalTheory.T.algebraicChart_lift_holomorphic_periodMaps E H Dw l Xo c O β Y T F e σ W.g _ W.F X j hj hjo y hy c' hyc
    obtain ⟨q₀, -, hu₀⟩ := hq _ hb₀
    obtain ⟨k, x₁, t, hbor⟩ := hU.2.2.1 q₀
    have hk : W.ik k = i := W.F.disj _ _ _ _ (W.period k x₁) (hper _ hb₀)
      (((W.lie k x₁).1.symm.trans hbor.1.symm).trans hu₀.symm)
    subst hk
    obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
    obtain ⟨hp0, hty⟩ := hU.2.1 k
    have hmult : ∀ τ : E →+* ℂ, Formalism.L2.PjFree.relab c σ τ ∉ (U.X k).Ψ → Dw.mult τ = (U.X k).p0 := by
      intro τ hτ
      rw [hp0]
      exact if_neg fun h => hτ ((hty _).2 ((hrt τ).2 h))
    have hrep : ∀ b ∈ B, ∀ q : FrPt Xo c (Formalism.L2.Pj.CAt σ), W.F.u (W.ik k) (P b) = q.x →
        ∃ x' : (U.X k).dom, (U.un k x').x = q.x ∧ ∃ h : (Fin W.g → ℂ) ≃ₗ[ℂ] (Fin W.g → ℂ), ∀ v, P b v =
          h (fun j => Formalism.L2.PjFree.perFr (U.X k) x'.1 (W.φ k v : Fin (Dw.p + Dw.q) → E)
            (Formalism.L2.PjFree.relab c σ (W.e j).1) ((W.e j).2 : ℕ)) := by
      intro b hb q hqu
      obtain ⟨x', hx', h, hh⟩ := GlobalTheory.T.periodMap_member_eq_frame_periodMap_linear_change E H Dw l Xo c σ _ U W hσ hU hinj k (P b) (hper b hb) q hqu
      exact ⟨x', hx', h, fun v => (hh v).trans (congrArg h (funext fun j => W.Pm_eq k x' v j))⟩
    obtain ⟨s, hs, hev⟩ := GlobalTheory.T.exists_analytic_frame_family_of_holomorphic_periodMaps E (Dw.p + Dw.q) (U.X k) _ (W.φ k) W.g (fun j => Formalism.L2.PjFree.relab c σ (W.e j).1)
      (fun j => ((W.e j).2 : ℕ)) X.dim B P (c'.e y) hB hb₀ (fun b hb => (hper b hb).1) hdiff
      (fun ρ hρ m hm => by
        obtain ⟨τ', hτ'⟩ := hbij.2 (conjEmb ρ)
        have hn : Formalism.L2.PjFree.relab c σ τ' ∉ (U.X k).Ψ := by
          rw [hτ']
          exact ((U.X k).cmType ρ).1 hρ
        have hm' : m < Dw.mult τ' := by rw [hmult τ' hn]; exact hm
        exact ⟨W.e.symm ⟨τ', ⟨m, hm'⟩⟩, by rw [Equiv.apply_symm_apply]; exact hτ', by rw [Equiv.apply_symm_apply]⟩)
      (fun j j' h1 h2 => by
        have h1' := hbij.1 h1
        exact W.e.injective (Sigma.ext h1' ((Fin.heq_ext_iff (by rw [h1'])).2 h2)))
      (fun j hj' => by
        exact lt_of_lt_of_eq (W.e j).2.2 (hmult _ hj'))
      (fun b hb => by
        obtain ⟨q, -, hqu⟩ := hq b hb
        obtain ⟨x', -, h, hh⟩ := hrep b hb q hqu
        exact ⟨x'.1, x'.2, h, hh⟩)
    refine ⟨k, s, hs, (hev.and (hB.mem_nhds hb₀)).mono fun w hw => ⟨hw.1.1, ?_⟩⟩
    obtain ⟨q, hq1, hqu⟩ := hq w hw.2
    obtain ⟨x', hx', h, hh⟩ := hrep w hw.2 q hqu
    obtain ⟨h1, h2⟩ := hw.1.2 x'.1 x'.2 ⟨h, hh⟩
    rw [← hq1]
    exact cxPt_congr ((GlobalTheory.TrueCx.PointWell.pt_eq_of_block hU hσ k ⟨s w, hw.1.1⟩ x' h1 h2).trans hx')

end GlobalTheory.LieBase
