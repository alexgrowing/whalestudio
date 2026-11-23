import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.WeilBound.CoreStatements.NefModelVolumes.Nvuonto
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
theorem PositivityTheory.Xj7N.local_unit_map_surjective : PositivityTheory.Xj7N.NV → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : GlobalTheory.CompHS.TorFlag Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)), GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) → GlobalTheory.DegVal.BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) → ∀ σ : Y.d.c₂.F →+* ℂ, GoodEmb Y.d.c₂ σ → ∀ P ∈ holSub (Y.U σ).X (modelWt (Y.U σ) (wtOf (T.Q.Dw j) u 0)), ∃ (m : ℕ) (as : Fin m → ℂ) (fs : Fin m → Rul Y.d.Xo₂ Y.d.c₂), (∀ i, fs i ∈ GlobalTheory.CompanionTheory.Ar.OntoDef.extVanZ TF.X (exOf (T.Q.Dw j) u 0)) ∧ ∀ w ∈ framesOn (Y.U σ) Z, P w.1 w.2 = ∑ i, as i * rdU (Y.U σ) (fs i) w.1 w.2 := by
  intro hNV _ D T j Y e o hY _ Z TF u _ hB σ hσ P hP
  have hU := hY.unf σ hσ
  obtain ⟨κ⟩ := GlobalTheory.HSApp.VanishingBound.keySec D T j Y e o hY σ hσ
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    have hr := hU.1
    have h1 : 1 ≤ D.R.r := by
      have := D.R.two_le_m
      unfold Formalism.BasicNotions.Ranks.r
      omega
    omega
  have hdec : ∀ (τ : D.host.E →+* ℂ) (i j' : ℕ), i ≤ j' → j' < (T.Q.Dw j).mult τ →
      (wtOf (T.Q.Dw j) u 0).1 (τ, j') ≤ (wtOf (T.Q.Dw j) u 0).1 (τ, i) := by
    have hne : ∀ (τ : D.host.E →+* ℂ) (m : ℕ), m + 1 < (T.Q.Dw j).mult τ →
        (wtOf (T.Q.Dw j) u 0).1 (τ, m + 1) ≤ (wtOf (T.Q.Dw j) u 0).1 (τ, m) := fun τ m hm => by
      by_contra hlt
      refine hB.1 (LinearMap.ext fun f => ?_)
      have h0 : (f : Rul Y.d.Xo₂ Y.d.c₂) = 0 :=
        GlobalTheory.NonDomVanish.eq_zero_of_lt f.2.1.1 τ ⟨m, by omega⟩ ⟨m + 1, hm⟩ rfl (not_le.1 hlt)
      rw [show f = 0 from Subtype.ext h0, map_zero, map_zero]
    intro τ i j' hij hj'
    induction j', hij using Nat.le_induction with
    | base => exact le_refl _
    | succ n hn ih => exact (hne τ n hj').trans (ih (by omega))
  obtain ⟨m, as, fs, h1, h2⟩ := PositivityTheory.UnitarySelfGeneration.VuOnto.exists_comb hσ hU TF (e := exOf (T.Q.Dw j) u 0) rfl
    (PositivityTheory.UnitarySelfGeneration.VuOnto.tw_of_dec hσ hU κ (fun a n hD => hNV _ _ _ _ _ _ σ hpq a n hD) (wtOf (T.Q.Dw j) u 0) rfl hdec)
    (GlobalTheory.CuspSecFin.mem_SS_of_mem_holSub _ _ hP)
  exact ⟨m, as, fs, h1, fun w hw => h2 w.1 w.2 hw.1⟩
end
