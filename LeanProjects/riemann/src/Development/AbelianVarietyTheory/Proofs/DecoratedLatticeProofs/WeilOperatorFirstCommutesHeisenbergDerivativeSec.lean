import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLast
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfAeFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBiThetaIffJoin
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsJointlySmoothBiThetaHeisenbergDerivStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorIntegralCommOfBoundedFiniteMeasureStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DerivComm

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem exists_biBound (hψ : IsStdChar D ψ (-1)) {A S A' : HSp D} {C : WO A S → WO S A' → ℂ}
    (h : IsBiTheta ψ A S A' C) : ∃ B : ℝ, ∀ u v, ‖C u v‖ ≤ B := by
  obtain ⟨B, hB⟩ := GlobalTheory.WeilVacMove.exists_bound hψ
    (GlobalTheory.BiTransfer.isThetaFunO_join (GlobalTheory.BiTransfer.sumDec A (GlobalTheory.ChiGrid.negSp A')) h)
  refine ⟨B, fun u v => ?_⟩
  have := hB (GlobalTheory.BiTransfer.inlH (GlobalTheory.BiTransfer.sumDec A (GlobalTheory.ChiGrid.negSp A')) S u +
    GlobalTheory.BiTransfer.inrH (GlobalTheory.BiTransfer.sumDec A (GlobalTheory.ChiGrid.negSp A')) S v)
  rwa [GlobalTheory.BiTransfer.join_inl_inr] at this

theorem om_dLine_right : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (χA χS χS' χA' : (AE D)ˣ →* Circle) (oma : Om A S) (omb : Om S A'), IsWeilDatumO ψ A S χA χS oma → IsWeilDatumO ψ S A' χS' χA' omb → BiAct D → ∀ G : WO A S → WO S A' → ℂ, IsBiTheta ψ A S A' G → ∀ M' : ℝ →+ WO S A', Continuous M' → (∀ s, (M' s).map (finPart D) = 0) → ∀ p u v, oma p (fun u' => GlobalTheory.WeilVacMove.dLine ψ S A' M' (G u') v) u = GlobalTheory.WeilVacMove.dLine ψ S A' M' (fun v' => oma p (fun u' => G u' v') u) v := by
  intro D ψ A S A' χA χS χS' χA' oma omb hA hB hBi G hG M' hM hM0 p u v
  have hψ : IsStdChar D ψ (-1) := hA.std
  set G' : WO A S → WO S A' → ℂ := fun u v => GlobalTheory.WeilVacMove.dLine ψ S A' M' (G u) v with hG'def
  have hG' : IsBiTheta ψ A S A' G' := (GlobalTheory.T.isJointlySmoothBiTheta_heisenbergDeriv D ψ hψ A S A' G hG).2 M' hM hM0
  set H : WO A S → WO S A' → ℂ := fun u v => oma p (fun u' => G u' v) u with hHdef
  have hH : IsBiTheta ψ A S A' H := (hBi ψ A S A' χA χS χS' χA' oma omb hA hB G hG).1 p
  set H' : WO A S → WO S A' → ℂ := fun u v => oma p (fun u' => G' u' v) u with hH'def
  have hH' : IsBiTheta ψ A S A' H' := (hBi ψ A S A' χA χS χS' χA' oma omb hA hB G' hG').1 p

  set c : ℝ → ℂ := fun s => ψ (symplOH S A' v (M' s)) with hcdef
  have hc : Continuous c := hψ.1.1.comp (GlobalTheory.WeilVacMove.continuous_symplOH S A' continuous_const hM)
  have hc1 : ∀ s, ‖c s‖ = 1 := fun s => hψ.1.2.1 _
  have hheis : ∀ (f : WO S A' → ℂ) s, heisO ψ S A' (M' s) f v = c s * f (v + M' s) := fun f s => rfl
  have hvm : Continuous fun s => v + M' s := continuous_const.add hM
  have hG'c : Continuous fun q : ℝ × WO A S => G' q.2 (v + M' q.1) :=
    hG'.cont.comp (f := fun q : ℝ × WO A S => (q.2, v + M' q.1)) (continuous_snd.prodMk (hvm.comp continuous_fst))
  have hH'c : Continuous fun q : ℝ × WO A S => H' q.2 (v + M' q.1) :=
    hH'.cont.comp (f := fun q : ℝ × WO A S => (q.2, v + M' q.1)) (continuous_snd.prodMk (hvm.comp continuous_fst))
  have hF0 : Continuous fun q : ℝ × WO A S => c q.1 * G' q.2 (v + M' q.1) := (hc.comp continuous_fst).mul hG'c
  have hoF0 : Continuous fun q : ℝ × WO A S => c q.1 * H' q.2 (v + M' q.1) := (hc.comp continuous_fst).mul hH'c

  set F : ℝ → WO A S → ℂ := fun s u' => c s * G' u' (v + M' s) with hFdef
  have hFth : ∀ s, IsThetaFunO ψ A S (F s) := fun s =>
    GlobalTheory.WeilVacMove.isTheta_smul (c s) (GlobalTheory.FrComb.slice_left hG' (v + M' s))
  have hFc : Continuous fun q : ℝ × WO A S => F q.1 q.2 := hF0
  obtain ⟨B1, hB1⟩ := exists_biBound hψ hG'
  have hFb : ∃ C : ℝ, ∀ a x, ‖F a x‖ ≤ C := ⟨B1, fun a x => by
    rw [hFdef, norm_mul, hc1, one_mul]; exact hB1 _ _⟩
  have hoF : ∀ s, oma p (F s) = fun u => c s * H' u (v + M' s) := by
    intro s
    have e : F s = c s • (fun u' => G' u' (v + M' s)) := rfl
    rw [e, map_smul]
    rfl
  have hoFc : Continuous fun q : ℝ × WO A S => oma p (F q.1) q.2 := by
    simp only [hoF]
    exact hoF0
  obtain ⟨B2, hB2⟩ := exists_biBound hψ hH'
  have hoFb : ∃ C : ℝ, ∀ a x, ‖oma p (F a) x‖ ≤ C := ⟨B2, fun a x => by
    rw [hoF, norm_mul, hc1, one_mul]; exact hB2 _ _⟩

  have hftc : ∀ u' t, ∫ s in (0 : ℝ)..t, F s u' = c t * G u' (v + M' t) - G u' v := by
    intro u' t
    have hd : ∀ s, HasDerivAt (fun t : ℝ => heisO ψ S A' (M' t) (G u') v)
        (heisO ψ S A' (M' s) (G' u') v) s := fun s =>
      GlobalTheory.WeilVacMove.hasDerivAt_line hψ hM hM0 (GlobalTheory.FrComb.slice_right hG u') v s
    have hcont : Continuous fun s => F s u' :=
      hF0.comp (f := fun s : ℝ => (s, u')) (continuous_id.prodMk continuous_const)
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t) (fun s _ => hd s)
      (hcont.intervalIntegrable _ _)
    change ∫ s in (0 : ℝ)..t, heisO ψ S A' (M' s) (G' u') v = _
    rw [this, hheis, hheis]
    simp only [hcdef, map_zero, add_zero, GlobalTheory.WeilVacMove.symplOH_zero_right, AddChar.map_zero_eq_one, one_mul]

  set φ : ℝ → ℂ := fun t => c t * H u (v + M' t) with hφdef
  set k : ℝ → ℂ := fun s => c s * H' u (v + M' s) with hkdef
  have hk : Continuous k := hoF0.comp (f := fun s : ℝ => (s, u)) (continuous_id.prodMk continuous_const)
  have hφint : ∀ t, 0 ≤ t → φ t = φ 0 + ∫ s in (0 : ℝ)..t, k s := by
    intro t ht
    haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) t)) :=
      isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
    have hth : IsThetaFunO ψ A S (fun x => ∫ a, F a x ∂(volume.restrict (Set.Ioc (0 : ℝ) t))) := by
      have e : (fun x => ∫ a, F a x ∂(volume.restrict (Set.Ioc (0 : ℝ) t))) =
          c t • (fun u' => G u' (v + M' t)) - (fun u' => G u' v) := by
        funext x
        rw [← intervalIntegral.integral_of_le ht, hftc]
        rfl
      rw [e]
      exact GlobalTheory.WeilVacMove.isTheta_sub (GlobalTheory.WeilVacMove.isTheta_smul _ (GlobalTheory.FrComb.slice_left hG _))
        (GlobalTheory.FrComb.slice_left hG v)
    have hcomm := GlobalTheory.T.weilOperator_integral_comm_of_bounded_finiteMeasure D ψ A S χA χS oma hA ℝ (volume.restrict (Set.Ioc (0 : ℝ) t)) F p hFth hFc hFb hoFc hoFb hth u
    have e1 : (fun y => ∫ a, F a y ∂(volume.restrict (Set.Ioc (0 : ℝ) t))) =
        c t • (fun u' => G u' (v + M' t)) - (fun u' => G u' v) := by
      funext x
      rw [← intervalIntegral.integral_of_le ht, hftc]
      rfl
    rw [e1, map_sub, map_smul] at hcomm
    have e2 : ∫ a, oma p (F a) u ∂(volume.restrict (Set.Ioc (0 : ℝ) t)) = ∫ s in (0 : ℝ)..t, k s := by
      rw [intervalIntegral.integral_of_le ht]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      show oma p (F s) u = k s
      rw [hoF]
    rw [e2] at hcomm
    have e3 : φ 0 = H u v := by
      rw [hφdef]; simp only [map_zero, add_zero, GlobalTheory.WeilVacMove.symplOH_zero_right, hcdef, AddChar.map_zero_eq_one, one_mul]
    rw [e3, ← hcomm]
    simp only [hφdef, hHdef, LinearMap.sub_apply, Pi.sub_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    ring

  have h1 : HasDerivAt φ (GlobalTheory.WeilVacMove.dLine ψ S A' M' (H u) v) 0 :=
    (GlobalTheory.WeilVacMove.hasDerivAt_zero_and_isTheta hψ hM hM0 (GlobalTheory.FrComb.slice_right hH u)).1 v
  have h2 : HasDerivWithinAt φ (k 0) (Set.Ici 0) 0 := by
    have h3 : HasDerivAt (fun t => φ 0 + ∫ s in (0 : ℝ)..t, k s) (k 0) 0 :=
      ((hk.integral_hasStrictDerivAt 0 0).hasDerivAt).const_add _
    refine h3.hasDerivWithinAt.congr (fun t ht => hφint t ht) (hφint 0 le_rfl)
  have h4 := (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv _ h1.hasDerivWithinAt h2
  have e4 : k 0 = H' u v := by
    simp only [hkdef, hcdef, map_zero, add_zero, GlobalTheory.WeilVacMove.symplOH_zero_right, AddChar.map_zero_eq_one, one_mul]
  rw [e4] at h4
  exact h4.symm

end GlobalTheory.DerivComm
