import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfE
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsCompactOfLeSumPnormSq
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.EventuallySplit

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.FlatPoints

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem norm_comb_sq_le {N : ℕ} (t a : Fin N → ℂ) :
    ‖∑ j, t j * a j‖ ^ 2 ≤ (∑ j, ‖t j‖ ^ 2) * ∑ j, ‖a j‖ ^ 2 := by
  have h1 : ‖∑ j, t j * a j‖ ≤ ∑ j, ‖t j‖ * ‖a j‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => norm_mul _ _))
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)

theorem pnorm_sq_eq {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.pnorm la P x ^ 2 = ‖P x‖ ^ 2 * X.nfac la x ^ 2 := by
  have e : X.pnorm la P x = ‖P x‖ * X.nfac la x := rfl
  rw [e, mul_pow]

theorem sum_pnorm_sq_eq {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {N : ℕ} (P : Fin N → Frame X.Ψ r → ℂ)
    (x : Frame X.Ψ r) :
    ∑ k, X.pnorm la (P k) x ^ 2 = (∑ k, ‖P k x‖ ^ 2) * X.nfac la x ^ 2 := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => pnorm_sq_eq X la _ x

theorem comb_mem {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (c : ℝ) {N : ℕ} (t : Fin N → ℂ)
    (w : Fin N → Frame X.Ψ r → ℂ) (hw : ∀ k, w k ∈ X.SSgt la c) :
    (fun x => ∑ j, t j * w j x) ∈ X.SSgt la c := by
  classical
  obtain ⟨-, -, ⟨h0, hadd, hsmul⟩, -⟩ := siegelSpaceAlgebra_holds (E := E) r X la la c
  have hmem : ∀ s : Finset (Fin N), ∑ j ∈ s, t j • w j ∈ X.SSgt la c := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using h0
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact hadd _ (hsmul _ _ (hw a)) _ ih
  have e : (fun x => ∑ j, t j * w j x) = ∑ j, t j • w j := by
    funext x; simp [Finset.sum_apply]
  rw [e]; exact hmem _

theorem sum_norm_sq_orbit {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {N : ℕ}
    (P : Fin N → Frame X.Ψ r → ℂ) (hP : ∀ k, X.IsSec la (P k)) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r) :
    ∑ k, ‖P k (lact γ (rmul x b))‖ ^ 2 = ‖bchar la b‖ ^ 2 * ∑ k, ‖P k x‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [(hP k).2.2 γ hγ _ (OntoS.dom_rmul X hx hb), (hP k).2.1 x hx b hb, norm_mul, norm_mul,
    OntoE.chi_norm X la hγ, one_mul, mul_pow]

theorem exists_flat : LineBundleFirstBoundGlobalGeneration (E := E) → MahlerCompactnessCriterion (E := E) → ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (t : Fin (nd X + 1) → Fin Xa.N → ℂ),
    let sf : Fin (nd X + 1) → Frame X.Ψ r → ℂ := fun i x => ∑ j, t i j * Xa.w j x
    (∃ K : ℝ, ∀ x ∈ X.dom, ∑ k, ‖Xa.w k x‖ ^ 2 ≤ K * ∑ i, ‖sf i x‖ ^ 2) →
    (∃ ε c0 : ℝ, 0 < ε ∧ 0 < c0 ∧ ∀ x ∈ X.dom, ∑ i : Fin (nd X), ‖sf i.succ x‖ ^ 2 < ε * ‖sf 0 x‖ ^ 2 →
      c0 ≤ ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) →
    (∀ x ∈ X.dom, (∀ k : Fin (nd X), sf k.succ x = 0) → (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
      sf k.succ (cpt X x z) / sf 0 (cpt X x z) : V (nd X))) 0).det ≠ 0) →
    ∃ Fl : FlatM X Xa, Fl.w0 = sf 0 ∧ Fl.s = fun k => sf k.succ := by
  intro hLa hM2 r X Xa t sf ⟨K, hK⟩ ⟨ε, c0, hε, hc0, hsm⟩ hdet
  have hvan : ∀ i, sf i ∈ X.SSgt Xa.L 0 := fun i => comb_mem X _ 0 (t i) Xa.w Xa.w_van
  have hsec : ∀ i, X.IsSec Xa.L (sf i) := fun i => (hvan i).1.1.1
  have hwsec : ∀ k, X.IsSec Xa.L (Xa.w k) := fun k => (Xa.w_van k).1.1.1
  have hcs : ∀ i x, ‖sf i x‖ ^ 2 ≤ (∑ j, ‖t i j‖ ^ 2) * ∑ j, ‖Xa.w j x‖ ^ 2 :=
    fun i x => norm_comb_sq_le (t i) fun j => Xa.w j x
  have hK' : ∀ x ∈ X.dom, ∑ k, ‖Xa.w k x‖ ^ 2 ≤
      K * (‖sf 0 x‖ ^ 2 + ∑ i : Fin (nd X), ‖sf i.succ x‖ ^ 2) := fun x hx => by
    have := hK x hx
    rwa [Fin.sum_univ_succ] at this
  have hw0 : ∀ x ∈ X.dom, (∀ k : Fin (nd X), sf k.succ x = 0) → sf 0 x ≠ 0 := by
    intro x hx h0 h00
    have h1 := hK' x hx
    simp only [h0, h00, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero, add_zero, mul_zero] at h1
    obtain ⟨k, hk⟩ := Xa.w_nz x hx
    have : 0 < ∑ k, ‖Xa.w k x‖ ^ 2 := Finset.sum_pos' (fun j _ => by positivity)
      ⟨k, Finset.mem_univ k, pow_pos (norm_pos_iff.2 hk) 2⟩
    linarith
  obtain ⟨C, hC, hCd, hCx⟩ :=
    GlobalTheory.CuspCompact.exists_compact_of_le_sum_pnorm_sq hLa hM2 r X Xa c0 hc0
  obtain ⟨δ, xs, hxs, hS, hinj⟩ := GlobalTheory.FiniteZeroOrbits.finite_orbits r X Xa.L (sf 0)
    (fun k => sf k.succ) (hsec 0) (fun k => hsec _) (fun x hx h0 => ⟨hw0 x hx h0, hdet x hx h0⟩)
    C hC hCd (fun x hx h0 => hCx x hx (hsm x hx (by
      have := pow_pos (norm_pos_iff.2 (hw0 x hx h0)) 2
      have h0' : ∀ k : Fin (nd X), sf k.succ x = 0 := h0
      simp only [h0', norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        Finset.sum_const_zero]
      positivity)))
  have hxs0 : ∀ j, ∀ k : Fin (nd X), sf k.succ (xs j) = 0 := fun j =>
    (hS _ (hxs j)).2 ⟨j, (GlobalTheory.FiniteZeroOrbits.orbitSetoid X).iseqv.refl (xs j)⟩
  refine ⟨⟨sf 0, fun k => sf k.succ, hvan 0, fun k => hvan _, δ, xs, hxs, hS, hinj,
    fun j => hw0 _ (hxs j) (hxs0 j), fun j => hdet _ (hxs j) (hxs0 j), ⟨K, fun x hx => ?_⟩,
    ⟨∑ j, ‖t 0 j‖ ^ 2, fun x hx => ?_⟩,
    ⟨∑ i : Fin (nd X), ∑ j, ‖t i.succ j‖ ^ 2, fun x hx => ?_⟩, fun U hU hxU hsat => ?_⟩, rfl, rfl⟩
  · rw [sum_pnorm_sq_eq, sum_pnorm_sq_eq, pnorm_sq_eq, ← add_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hK' x hx) (sq_nonneg _)
  · rw [sum_pnorm_sq_eq, pnorm_sq_eq, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hcs 0 x) (sq_nonneg _)
  · rw [sum_pnorm_sq_eq, sum_pnorm_sq_eq, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => hcs _ x
  · have hpos : ∀ x ∈ X.dom, x ∉ U → 0 < ∑ i : Fin (nd X), ‖sf i.succ x‖ ^ 2 := by
      intro x hx hxU'
      by_contra hle
      have hz : ∑ i : Fin (nd X), ‖sf i.succ x‖ ^ 2 = 0 :=
        le_antisymm (not_lt.1 hle) (Finset.sum_nonneg fun i _ => by positivity)
      have h0 : ∀ k : Fin (nd X), sf k.succ x = 0 := fun k => by
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).1 hz k (Finset.mem_univ k)
        simpa using this
      obtain ⟨j, γ, hγ, b, hb, he⟩ := (hS x hx).1 h0
      exact hxU' (he ▸ hsat _ (hxU j) γ hγ b hb)
    have hCU : IsCompact (C \ U) := hC.diff hU
    have hcont : ContinuousOn
        (fun x => (∑ k, ‖Xa.w k x‖ ^ 2) / ∑ i : Fin (nd X), ‖sf i.succ x‖ ^ 2) (C \ U) := by
      refine ContinuousOn.div ?_ ?_ fun x hx => (hpos x (hCd hx.1) hx.2).ne'
      · exact continuousOn_finsetSum _ fun k _ =>
          (((hwsec k).1.continuousOn.mono fun x hx => hCd hx.1).norm.pow 2)
      · exact continuousOn_finsetSum _ fun k _ =>
          (((hsec k.succ).1.continuousOn.mono fun x hx => hCd hx.1).norm.pow 2)
    obtain ⟨M, hM⟩ := (hCU.image_of_continuousOn hcont).bddAbove
    refine ⟨max M (|K| * (ε⁻¹ + 1)), fun x hx hxU' => ?_⟩
    rw [sum_pnorm_sq_eq, sum_pnorm_sq_eq, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have hp := hpos x hx hxU'
    rcases lt_or_ge (∑ i : Fin (nd X), ‖sf i.succ x‖ ^ 2) (ε * ‖sf 0 x‖ ^ 2) with h | h
    · obtain ⟨γ, hγ, b, hb, hy⟩ := hCx x hx (hsm x hx h)
      have hyU : lact γ (rmul x b) ∉ U := by
        intro hU'
        obtain ⟨γ', hγ', b', hb', he⟩ := (GlobalTheory.FiniteZeroOrbits.orbitSetoid X).iseqv.symm
          (show (GlobalTheory.FiniteZeroOrbits.orbitSetoid X).r x (lact γ (rmul x b)) from ⟨γ, hγ, b, hb, rfl⟩)
        exact hxU' (he ▸ hsat _ hU' γ' hγ' b' hb')
      have h1 := hM ⟨_, ⟨hy, hyU⟩, rfl⟩
      have hb0 : ‖bchar Xa.L b‖ ^ 2 ≠ 0 := (pow_pos (norm_pos_iff.2 (OntoE.bchar_ne X _ hb)) 2).ne'
      simp only at h1
      rw [sum_norm_sq_orbit X Xa.L Xa.w hwsec hγ hx hb,
        sum_norm_sq_orbit X Xa.L (fun k : Fin (nd X) => sf k.succ) (fun k => hsec _) hγ hx hb,
        mul_div_mul_left _ _ hb0, div_le_iff₀ hp] at h1
      exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp.le)
    · refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right _ _) hp.le)
      have h2 : ‖sf 0 x‖ ^ 2 ≤ ε⁻¹ * ∑ i : Fin (nd X), ‖sf i.succ x‖ ^ 2 := by
        rw [le_inv_mul_iff₀ hε]; exact h
      calc _ ≤ K * (‖sf 0 x‖ ^ 2 + ∑ i : Fin (nd X), ‖sf i.succ x‖ ^ 2) := hK' x hx
        _ ≤ |K| * (‖sf 0 x‖ ^ 2 + ∑ i : Fin (nd X), ‖sf i.succ x‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
        _ ≤ |K| * (ε⁻¹ * ∑ i : Fin (nd X), ‖sf i.succ x‖ ^ 2 + ∑ i : Fin (nd X), ‖sf i.succ x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg K)
        _ = _ := by ring

end GlobalTheory.FlatPoints
