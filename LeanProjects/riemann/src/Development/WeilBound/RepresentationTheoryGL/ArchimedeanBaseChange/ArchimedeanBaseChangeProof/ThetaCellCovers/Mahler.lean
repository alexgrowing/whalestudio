import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.ContinuousPA

namespace PositivityTheory.Rg.BcB.E1

theorem cellCover_holds : CellCover := cellCover_of cover_holds (conjCpt_of admissible_le_holds)

theorem cutBox_of' (h1 : DegBasis) (h2 : DegAdelic) (h3 : DegBdd) : CutBox := cutBox_of (degCell_of h1 h2 h3 torNorm_holds)

open PositivityTheory.Rg.Rs GlobalTheory.CuspRep in
theorem mahlerC_of_deg (h1 : DegBasis) (h2 : DegAdelic) (h3 : DegBdd) (h4 : DegRat) : D1.MahlerC := by
  intro E _ _ _ n c
  obtain ⟨Ω₀, hΩ, hc⟩ := cellCover_holds E n
  obtain ⟨C, -, hC⟩ := cutBox_of' h1 h2 h3 E n Ω₀ hΩ
  refine ⟨(fun p : (Fin n → ℝ) × GA E n => An.tor E p.1 * p.2) '' (Metric.closedBall 0 (C * (1 + |c|)) ×ˢ Ω₀),
    ((isCompact_closedBall _ _).prod hΩ).image ((JSqIntGlue.continuous_tor.comp continuous_fst).mul continuous_snd),
    fun g a1 a2 => ?_⟩
  obtain ⟨γ, m, o, ho, e⟩ := hc g
  refine ⟨ratGL E n γ⁻¹, ⟨_, rfl⟩, _, ⟨(_, o), ⟨mem_closedBall_zero_iff.2
    (hC (fun i => (m i : ℝ)) o ho _ (abs_nonneg c) (fun W hW => ?_) ?_), ho⟩, rfl⟩, ?_⟩
  · rw [← e, ← img_img_inv γ W, h4]
    exact (a1 _ (by rw [finrank_img, hW])).trans (le_abs_self c)
  · rw [← e, ← img_top γ, h4]
    linarith [le_abs_self c, (abs_le.1 a2).1]
  · simp only [← e, map_inv, inv_mul_cancel_left]

end PositivityTheory.Rg.BcB.E1
