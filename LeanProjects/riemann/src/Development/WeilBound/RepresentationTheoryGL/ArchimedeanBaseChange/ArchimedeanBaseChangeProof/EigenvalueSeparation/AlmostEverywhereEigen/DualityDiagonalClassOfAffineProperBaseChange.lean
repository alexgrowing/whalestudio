import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.OneStepOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds

noncomputable section

open NumberField Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.E1
open scoped ENNReal

namespace PositivityTheory.Rg.BcB.E2

attribute [local instance] borelH

theorem measurable_wt {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} : Measurable (wt : H E a b → ℝ) :=
  (measurable_const.add ((redBasic E a).2.2.comp
    (@Continuous.measurable _ _ _ _ ⟨le_rfl⟩ _ (borel _) ⟨rfl⟩ _ continuous_fst))).add ((redBasic E b).2.2.comp
    (@Continuous.measurable _ _ _ _ ⟨le_rfl⟩ _ (borel _) ⟨rfl⟩ _ continuous_snd))

theorem orthogonal_keeping_of_estimate (h : OneStep) : OrthogonalKeepingOperator := by
  classical
  intro E _ _ _ a b D ι _ K _ _ _ J hJ B _ _ _ _ R p a₀ C Φ g hp ha hC h1 hΦ hT hg hg'
  set M := 2 * (a + b)
  have hw : ∀ x : H E a b, 0 < wt x := fun x => by
    rw [wt_eq]; linarith [((redBasic E a).2.1 x.1).1, ((redBasic E b).2.1 x.2).1]
  obtain ⟨c, hc⟩ := hC.exists_eq_range ⟨1, h1⟩
  have key := fun k : ℕ => h (ctx ratProper_holds D) ι K J B R p a₀ C Φ g
    (fun x : H E a b => ENNReal.ofReal (wt x ^ (-(2 * M : ℤ)))) hJ hp ha hC h1 hΦ
    (fun x => (hT x).imp fun T t => ⟨t.1, t.2.1⟩) (measurable_wt.pow_const _).ennreal_ofReal
    (fun x => ⟨(ENNReal.ofReal_pos.2 (zpow_pos (hw x) _)).ne', ENNReal.ofReal_ne_top⟩)
    (fun Ω hΩ => wtCount E a b D Ω hΩ M le_rfl) hg
    (fun n i => by
      refine ne_of_eq_of_ne (lintegral_congr fun x : H E a b => ?_) (hg' n i M).ne
      have e : (ENNReal.ofReal (wt x ^ (-(2 * M : ℤ))))⁻¹ = ENNReal.ofReal (wt x ^ (2 * M)) := by
        rw [← ENNReal.ofReal_inv_of_pos (zpow_pos (hw x) _), _root_.zpow_neg, inv_inv,
          show (2 * M : ℤ) = ((2 * M : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
      exact congrArg (· * ‖(g n i : H E a b → ℂ) x‖ₑ ^ 2) e)
    ((Finset.range (k + 1)).image c) (1 / ((k : ℝ) + 1)) Nat.one_div_pos_of_nat
  choose s f h1 h2 _ h3 using key
  refine ⟨M, s, f, fun x hx => ?_, fun k => ⟨h2 k, (h3 k).cont, (h3 k).ne, fun i γ x => (h3 k).inv i γ.1 γ.2 x, (h3 k).wt,
    fun x hx => funext fun i => funext fun y => (h3 k).eig ⟨x, hx⟩ i y, (h3 k).orth⟩⟩
  obtain ⟨n, rfl⟩ : x ∈ Set.range c := hc ▸ hx
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ tendsto_one_div_add_atTop_nhds_zero_nat
  filter_upwards [eventually_ge_atTop n] with k hk
  exact h1 k _ (Finset.mem_image_of_mem c (Finset.mem_range.2 (by omega)))

theorem duality_diagonalClass_of_affineProperBaseChange (h : OrthogonalKeepingOperator) : E.E2 := by
  intro E _ _ _ a b D ι _ K _ _ _ J hJ B _ _ _ _ R p a₀ C Φ hp ha hC h1 hΦ hT
  obtain ⟨M, s, f, a1, a2⟩ := h E a b D ι K J hJ B R p a₀ C Φ (fun _ => 0) hp ha hC h1 hΦ
    (fun x => (hT x).imp fun T t => ⟨t.1, t.2.1, fun u hu v => by rw [t.2.2 u hu, inner_zero_right]⟩)
    (fun _ _ => inner_zero_right _) (fun _ i M => by
      rw [lintegral_congr_ae (g := fun _ => 0), lintegral_zero]
      · exact ENNReal.zero_lt_top
      · filter_upwards [Lp.coeFn_zero ℂ 2 D.ν] with x hx
        have : ((0 : Hs (ι := ι) D) i : H E a b → ℂ) x = 0 := hx
        rw [this, enorm_zero, zero_pow two_ne_zero, mul_zero])
  exact ⟨M, s, f, a1, fun k => ⟨(a2 k).1, (a2 k).2.1, (a2 k).2.2.1, (a2 k).2.2.2.1, (a2 k).2.2.2.2.1, (a2 k).2.2.2.2.2.1⟩⟩

end PositivityTheory.Rg.BcB.E2

end
