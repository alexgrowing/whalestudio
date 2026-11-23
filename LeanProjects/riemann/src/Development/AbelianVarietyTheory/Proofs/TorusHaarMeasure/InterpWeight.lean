import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfB
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DetFderivNeZeroOrbit
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ContinuousOnOfCharts
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.WeightContDiffOn
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasurableIndicatorOfContOn
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LintegralLtTopOfCutoff
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.KronHolPsiOf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.InterpWeight

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem core (hN : NfacRmulStatement (E := E) ∧ NfacLactStatement (E := E) ∧ PnormInvStatement (E := E))
    (hExt : ExtFStatement (E := E)) (hMI : MeasInvStatement (E := E)) (hV : VanishAtSStatement (E := E))
    (hK : KapGGStatement (E := E)) {r : ℕ} (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa)
    (G : Wt X.Ψ r) (bb m η : ℝ) (hbb : 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb) (hbm : bb < m) (hη : 0 < η)
    (hmar : ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        m * leviRh X x0 z ξ ≤ leviO X x0 (phla X G) z ξ - leviDens X x0 z ξ -
          (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ)
    (hstr : ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      2 * η * leviO X x0 (phla X Xa.L) z ξ ≤ leviO X x0 (phla X G) z ξ - leviDens X x0 z ξ -
        (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ) (j : Fin Fl.δ) :
    ∃ (x0 : Frame X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ),
      IsOrth X x0 ∧ IsMetricW X G W ∧ WLower X G W ∧
      DifferentiableOn ℂ F (OmF X x0) ∧ InAt X x0 W bb F ∧ IsBEq X G P ∧
      (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) ∧ P (lact 1 (Fl.xs j)) ≠ 0 ∧
      ∀ γ ∈ X.Γ, ∀ j', (γ ≠ 1 ∨ j' ≠ j) → P (lact γ (Fl.xs j')) = 0 := by
  have hCo := GlobalTheory.OrbitCoord.det_fderiv_ne_zero_orbit hK
  have hn : 0 < nd X := lt_of_lt_of_le (by norm_num) Xa.n_ge
  have hbb0 : 0 ≤ bb := le_trans (by positivity) hbb.le
  have hw0b : X.IsBddSec Xa.L Fl.w0 := Fl.weightForm_vanishes.1.1
  have hsb : ∀ k, X.IsBddSec Xa.L (Fl.s k) := fun k => (Fl.s_van k).1.1
  have hw0 : X.IsSec Xa.L Fl.w0 := hw0b.1
  have hs : ∀ k, X.IsSec Xa.L (Fl.s k) := fun k => (hsb k).1
  have key : ∀ j', ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, ∀ x1, x1 = lact γ (rmul (Fl.xs j') b) →
      Fl.w0 x1 ≠ 0 ∧ (∀ k, Fl.s k x1 = 0) ∧
      (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
        Fl.s k (cpt X x1 z) / Fl.w0 (cpt X x1 z) : V (nd X))) 0).det ≠ 0 := by
    rintro j' γ hγ b hb x1 rfl
    refine ⟨KronAssembly.sec_ne_zero X hw0 (Fl.xs_mem j') (Fl.w0_ne j') hγ hb, ?_,
      hCo r X Xa.L Fl.w0 Fl.s hw0 hs _ (Fl.xs_mem j') (Fl.w0_ne j') (Fl.coord j') γ hγ b hb⟩
    exact (Fl.S_eq _ (OntoS.dom_lact X hγ (OntoS.dom_rmul X (Fl.xs_mem j') hb))).2
      ⟨j', γ, hγ, b, hb, rfl⟩
  obtain ⟨x0, ho, b0, hb0, b0', hb0', hx0, hx0'⟩ :=
    KronAssembly.exists_orth X (Fl.xs_mem j) X.Γ.one_mem
  have hx0d : x0 ∈ X.dom := IW.orth_mem_dom X x0 ho
  obtain ⟨k1, k2, k3⟩ := key j 1 X.Γ.one_mem b0' hb0' x0 hx0'
  have hψb : ∃ C : ℝ, ∀ x ∈ X.dom, (fun _ : Frame X.Ψ r => (0 : ℝ)) x ≤ C := ⟨0, fun _ _ => le_rfl⟩
  obtain ⟨hψc, hMW, hWL⟩ := GlobalTheory.KronMetric.kronMetric hN r X G (fun _ => 0) (fun _ _ _ _ _ _ => rfl)
    (fun _ _ => contDiffOn_const) hψb
  obtain ⟨ε, χ, F, hε, hball, hiso, hχc, hχ1, hχ0, hF, hint⟩ :=
    GlobalTheory.kronSolve r X G Xa.L Fl.w0 Fl.s (fun _ => 0) x0 bb m η hn ho hw0 hs contDiffOn_const hbb0 hbm hη
      (fun z hz ξ => by rw [leviO_zero, add_zero]; exact hmar x0 ho z hz ξ)
      (fun z hz ξ => by rw [leviO_zero, add_zero]; exact hstr x0 ho z hz ξ)
      (fun z hz ξ hξ => Xa.posL x0 hx0d z hz ξ hξ) k1 k2 k3
  obtain ⟨hF0, hInAt, hloc⟩ :=
    GlobalTheory.KronValue.value_and_integrability hV r X G Xa.L Fl.w0 Fl.s (fun _ => 0) x0 bb ε (2 * ε) χ F hn
      ho hw0b hsb hψc hψb hbb0 hε hball hχc hχ1 hχ0 hF hint k1 k2 k3
  obtain ⟨P, hP, hPF⟩ := hExt r X x0 ho G F hF hloc
  have h0 : (0 : V (nd X)) ∈ OmF X x0 := by
    show cpt X x0 0 ∈ X.dom
    rw [IW.cpt_zero]; exact hx0d
  have hP0 : P x0 = 1 := by
    have := hPF 0 h0
    rwa [IW.cpt_zero, hF0] at this
  refine ⟨x0, _, F, P, ho, hMW, hWL, hF, hInAt, hP, hPF, ?_, ?_⟩
  · rw [hx0, hP.2 x0 hx0d b0 hb0, hP0, mul_one]
    exact OntoE.bchar_ne X _ hb0
  · intro γ hγ j' hne
    obtain ⟨x1, ho1, b1, hb1, b1', hb1', hx1, hx1'⟩ := KronAssembly.exists_orth X (Fl.xs_mem j') hγ
    have hx1d : x1 ∈ X.dom := IW.orth_mem_dom X x1 ho1
    obtain ⟨l1, l2, l3⟩ := key j' γ hγ b1' hb1' x1 hx1'
    have hP1 : P x1 = 0 := by
      refine GlobalTheory.KronOff.vanish_off hMI hV hN r X G Xa.L Fl.w0 Fl.s (fun _ => 0) x0 x1 bb (2 * ε) χ F P
        hn ho ho1 hw0 hs hψc (fun _ _ _ _ => rfl) hbb0 hball hχ0 hP hPF hint ?_ l1 l2 l3
      intro z hz b hb hxz
      have hz0 : z = 0 := by
        refine hiso z hz fun k => ?_
        have h1 := l2 k
        rw [hxz, (hs k).2.1 _ (hball hz) b hb] at h1
        exact (mul_eq_zero.mp h1).resolve_left (OntoE.bchar_ne X _ hb)
      rw [hz0, IW.cpt_zero] at hxz
      rw [FundSetPf.lact_one] at hx0'
      have hc : rmul b0' (rmul b b1) ∈ Bor X.Ψ r := ExtFPf.mul_mem X hb0' (ExtFPf.mul_mem X hb hb1)
      have he : lact γ (Fl.xs j') = rmul (Fl.xs j) (rmul b0' (rmul b b1)) := by
        rw [hx1, hxz, ← ExtFPf.rmul_assoc X (Fl.xs j) b0', ← hx0', ExtFPf.rmul_assoc]
      have hjj : j = j' := by
        refine Fl.xs_inj j j' γ⁻¹ (X.Γ.inv_mem hγ) _ hc ?_
        rw [← he, FundSetPf.lact_inv]
      subst hjj
      have hγ1 : γ = 1 := X.Γ_free γ hγ _ (Fl.xs_mem j) _ hc he
      rcases hne with h | h
      · exact h hγ1
      · exact h rfl
    rw [hx1, hP.2 x1 hx1d b1 hb1, hP1, mul_zero]

theorem interp_weight : (NfacRmulStatement (E := E) ∧ NfacLactStatement (E := E) ∧ PnormInvStatement (E := E)) → PoinStatement (E := E) → ExtFStatement (E := E) → MeasInvStatement (E := E) → VanishAtSStatement (E := E) → KapGGStatement (E := E) →
    ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r), PropDisc X →
    (∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧ bb < m ∧
      ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        m * leviRh X x0 z ξ ≤ leviO X x0 (phla X G) z ξ - leviDens X x0 z ξ -
          (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ) →
    (∃ η : ℝ, 0 < η ∧ ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      2 * η * leviO X x0 (phla X Xa.L) z ξ ≤ leviO X x0 (phla X G) z ξ - leviDens X x0 z ξ -
        (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ) →
    (∀ P, X.IsBddSec G P → P ∈ X.SS G) →
    ∀ v : Fin Fl.δ → ℂ, ∃ F ∈ X.SSgt G 0, ∀ j, F (Fl.xs j) = v j := by
  intro hN hPo hExt hMI hV hK r X Xa Fl G hPD ⟨bb, m, hbb, hbm, hmar⟩ ⟨η, hη, hstr⟩ hcusp
  apply interp_of_kron X G Fl.xs
  intro j
  obtain ⟨x0, W, F, P, hx0, hW, hWl, hF, hA, hBE, hPF, hne, hz⟩ :=
    core hN hExt hMI hV hK X Xa Fl G bb m η hbb hbm hη hmar hstr j
  obtain ⟨-, hQ, -⟩ := hPo r X x0 hx0 hPD G W bb hW hWl hbb F P hF hA hBE hPF
  have hQne : poin X G P (Fl.xs j) ≠ 0 := by
    rw [poin_single X G P _ X.Γ.one_mem fun γ hγ hne' => hz γ hγ j (Or.inl hne')]
    exact mul_ne_zero (inv_ne_zero (KronAssembly.chi_ne_zero X G X.Γ.one_mem)) hne
  have hQz : ∀ j', j' ≠ j → poin X G P (Fl.xs j') = 0 := fun j' hj' =>
    poin_zero X G P _ fun γ hγ => hz γ hγ j' (Or.inr hj')
  have hQs : poin X G P ∈ X.SSgt G 0 := ss_sub_ssgt0 X G (hcusp _ hQ)
  obtain ⟨-, -, ⟨-, -, hsmul⟩, -⟩ := siegelSpaceAlgebra_holds (E := E) r X G G 0
  refine ⟨(poin X G P (Fl.xs j))⁻¹ • poin X G P, hsmul _ _ hQs, fun j' => ?_⟩
  by_cases h : j' = j
  · subst h
    simp [hQne]
  · simp [h, hQz j' h]

end GlobalTheory.InterpWeight
