import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.IndCount
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.JetsPf
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.KronHolPsiInterpInterpC
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CurvAndMarginClosed
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.BddMulProd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.LowerInterp

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem kron_at {r : ℕ} (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (la : Wt X.Ψ r)
    (ψ : Frame X.Ψ r → ℝ) (hψ : IsInvFn X ψ)
    (hψs : ∀ x0, IsOrth X x0 → ContDiffOn ℝ ∞ (fun z => ψ (cpt X x0 z)) (OmF X x0))
    (hψb : ∃ C : ℝ, ∀ x ∈ X.dom, ψ x ≤ C)
    (hm : ∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧ bb < m ∧
      ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        m * leviRh X x0 z ξ ≤ leviO X x0 (phla X la) z ξ - leviDens X x0 z ξ -
          (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ + leviO X x0 ψ z ξ)
    (hs : ∃ η : ℝ, 0 < η ∧ ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      2 * η * leviO X x0 (phla X Xa.L) z ξ ≤ leviO X x0 (phla X la) z ξ - leviDens X x0 z ξ -
        (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ + leviO X x0 ψ z ξ)
    (j : Fin Fl.δ) :
    ∃ (x0 : Frame X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ) (F : V (nd X) → ℂ)
      (P : Frame X.Ψ r → ℂ) (γ0 : GL (Fin r) E),
      IsOrth X x0 ∧ IsMetricW X la W ∧ WLower X la W ∧ 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧
      DifferentiableOn ℂ F (OmF X x0) ∧ InAt X x0 W bb F ∧ IsBEq X la P ∧
      (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) ∧ γ0 ∈ X.Γ ∧ P (lact γ0 (Fl.xs j)) ≠ 0 ∧
      ∀ γ ∈ X.Γ, ∀ j', (γ ≠ γ0 ∨ j' ≠ j) → P (lact γ (Fl.xs j')) = 0 := by
  have hExt := (GlobalTheory.FrameMeasureClosed.measure_statements (E := E)).2.2.2
  have hCo := GlobalTheory.OrbitCoord.det_fderiv_ne_zero_orbit (E := E) GlobalTheory.FrameMeasureClosed.measure_statements.1
  have hMet := GlobalTheory.KronMetric.kronMetric (E := E) GlobalTheory.NormFactor.nfac_transform
  have hSol := GlobalTheory.kronSolve (E := E)
  have hVan := GlobalTheory.KronOff.vanish_off (E := E) GlobalTheory.FrameMeasureClosed.measure_statements.2.1
      GlobalTheory.vanishAtS_holds GlobalTheory.NormFactor.nfac_transform
  have hOne := GlobalTheory.KronValue.value_and_integrability (E := E) GlobalTheory.vanishAtS_holds
  obtain ⟨bb, m, hbb, hbm, hmar⟩ := hm
  obtain ⟨η, hη, hstr⟩ := hs
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
    refine ⟨GlobalTheory.KronAssembly.sec_ne_zero X hw0 (Fl.xs_mem j') (Fl.w0_ne j') hγ hb, ?_,
      hCo r X Xa.L Fl.w0 Fl.s hw0 hs _ (Fl.xs_mem j') (Fl.w0_ne j') (Fl.coord j') γ hγ b hb⟩
    exact (Fl.S_eq _ (OntoS.dom_lact X hγ (OntoS.dom_rmul X (Fl.xs_mem j') hb))).2
      ⟨j', γ, hγ, b, hb, rfl⟩
  obtain ⟨x0, ho, b0, hb0, b0', hb0', hx0, hx0'⟩ := GlobalTheory.KronAssembly.exists_orth X (Fl.xs_mem j) X.Γ.one_mem
  have hx0d : x0 ∈ X.dom := IW.orth_mem_dom X x0 ho
  obtain ⟨k1, k2, k3⟩ := key j 1 X.Γ.one_mem b0' hb0' x0 hx0'
  obtain ⟨hψc, hMW, hWL⟩ := hMet r X la ψ hψ hψs hψb
  have hψB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x b) = ψ x := by
    intro x hx b hb
    have := hψ 1 X.Γ.one_mem x hx b hb
    rwa [FundSetPf.lact_one] at this
  obtain ⟨ε, χ, F, hε, hball, hiso, hχc, hχ1, hχ0, hF, hint⟩ :=
    hSol r X la Xa.L Fl.w0 Fl.s ψ x0 bb m η hn ho hw0 hs (hψs x0 ho) hbb0 hbm hη (hmar x0 ho)
      (hstr x0 ho) (fun z hz ξ hξ => Xa.posL x0 hx0d z hz ξ hξ) k1 k2 k3
  obtain ⟨hF0, hInAt, hloc⟩ :=
    hOne r X la Xa.L Fl.w0 Fl.s ψ x0 bb ε (2 * ε) χ F hn ho hw0b hsb hψc hψb hbb0 hε hball hχc hχ1
      hχ0 hF hint k1 k2 k3
  obtain ⟨P, hP, hPF⟩ := hExt r X x0 ho la F hF hloc
  have h0 : (0 : V (nd X)) ∈ OmF X x0 := by
    show cpt X x0 0 ∈ X.dom
    rw [IW.cpt_zero]; exact hx0d
  have hP0 : P x0 = 1 := by
    have := hPF 0 h0
    rwa [IW.cpt_zero, hF0] at this
  refine ⟨x0, _, bb, F, P, 1, ho, hMW, hWL, hbb, hF, hInAt, hP, hPF, X.Γ.one_mem, ?_, ?_⟩
  · rw [hx0, hP.2 x0 hx0d b0 hb0, hP0, mul_one]
    exact OntoE.bchar_ne X _ hb0
  · intro γ hγ j' hne
    obtain ⟨x1, ho1, b1, hb1, b1', hb1', hx1, hx1'⟩ := GlobalTheory.KronAssembly.exists_orth X (Fl.xs_mem j') hγ
    have hx1d : x1 ∈ X.dom := IW.orth_mem_dom X x1 ho1
    obtain ⟨l1, l2, l3⟩ := key j' γ hγ b1' hb1' x1 hx1'
    have hP1 : P x1 = 0 := by
      refine hVan r X la Xa.L Fl.w0 Fl.s ψ x0 x1 bb (2 * ε) χ F P hn ho ho1 hw0 hs hψc hψB hbb0 hball
        hχ0 hP hPF hint ?_ l1 l2 l3
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

end GlobalTheory.LowerInterp

namespace GlobalTheory.LowerInterp

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mono_of_gaps {Ψ : Finset (E →+* ℂ)} {r p0 : ℕ} {la : Wt Ψ r} {a : ℤ} (ha : 0 ≤ a)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds.GapsGe p0 la a) (τ : Ψ) :
    ∀ (i j : Fin r), i ≤ j → ((j : ℕ) < p0 ∨ p0 ≤ (i : ℕ)) → la τ j ≤ la τ i := by
  intro i j hij hc
  obtain ⟨d, hd⟩ : ∃ d, (j : ℕ) = i + d := ⟨j - i, by have := Fin.le_def.1 hij; omega⟩
  induction d generalizing j with
  | zero =>
    have : j = i := Fin.ext (by omega)
    subst this
    exact le_rfl
  | succ d ih =>
    have hk : (i : ℕ) + d < r := by have := j.2; omega
    have h1 := ih ⟨i + d, hk⟩ (Fin.le_def.2 (by simp)) (by
      rcases hc with hc | hc
      · left; simp; omega
      · right; exact hc) rfl
    have h2 := h τ ⟨i + d, hk⟩ j (by simp; omega) (by rcases hc with hc | hc <;> omega)
    linarith

theorem pair_of {Ψ : Finset (E →+* ℂ)} {r p0 : ℕ} {la : Wt Ψ r} {a : ℤ} (ha : 0 ≤ a)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds.GapsGe p0 la a) {c : ℝ} (hp : GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds.PairGe la c) (τ : Ψ) (i j : Fin r)
    (hi : (i : ℕ) < p0) (hj : p0 ≤ (j : ℕ)) : c ≤ (la τ j : ℝ) - (la τ i : ℝ) := by
  have h0 : 0 < r := lt_of_le_of_lt (Nat.zero_le _) i.2
  have e1 := mono_of_gaps ha h τ ⟨0, h0⟩ i (Fin.le_def.2 (by simp)) (Or.inl hi)
  have e2 := mono_of_gaps ha h τ j ⟨r - 1, by omega⟩ (Fin.le_def.2 (by simp; have := j.2; omega)) (Or.inr hj)
  have e3 := hp τ ⟨0, h0⟩ ⟨r - 1, by omega⟩ rfl rfl
  push_cast at e3
  have e1' : (la τ i : ℝ) ≤ la τ ⟨0, h0⟩ := by exact_mod_cast e1
  have e2' : (la τ ⟨r - 1, by omega⟩ : ℝ) ≤ la τ j := by exact_mod_cast e2
  linarith

theorem comb_facts {Ψ : Finset (E →+* ℂ)} {r p0 : ℕ} (s c : ℕ) {A L la : Wt Ψ r} {b : ℝ}
    (hA : GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds.GapsGe p0 A 0) (hL : GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds.GapsGe p0 L 1)
    (hpA : GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds.PairGe A 1) (hpL : GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds.PairGe L b)
    (hla : ∀ τ k, la τ k = A τ k + (c : ℤ) * L τ k - GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds.deMul Ψ r p0 s τ k) :
    (∀ τ (i j : Fin r), i ≤ j → (j : ℕ) < p0 → la τ j ≤ la τ i) ∧
    (∀ τ (i j : Fin r), p0 ≤ (i : ℕ) → i ≤ j → la τ j ≤ la τ i) ∧
    (∀ τ (i j : Fin r), (i : ℕ) < p0 → p0 ≤ (j : ℕ) → 1 + c * b - s ≤ (la τ j : ℝ) - (la τ i : ℝ)) := by
  have mA := mono_of_gaps le_rfl hA
  have mL := mono_of_gaps zero_le_one hL
  have hc : (0 : ℤ) ≤ c := Nat.cast_nonneg c
  refine ⟨fun τ i j hij hj => ?_, fun τ i j hi hij => ?_, fun τ i j hi hj => ?_⟩
  · have hi : (i : ℕ) < p0 := lt_of_le_of_lt (Fin.le_def.1 hij) hj
    rw [hla, hla]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds.deMul, if_pos hi, if_pos hj]
    have h1 := mA τ i j hij (Or.inl hj)
    have h2 := mul_le_mul_of_nonneg_left (mL τ i j hij (Or.inl hj)) hc
    linarith
  · have hj : ¬ (j : ℕ) < p0 := by have := Fin.le_def.1 hij; omega
    have hi' : ¬ (i : ℕ) < p0 := by omega
    rw [hla, hla]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds.deMul, if_neg hi', if_neg hj]
    have h1 := mA τ i j hij (Or.inr hi)
    have h2 := mul_le_mul_of_nonneg_left (mL τ i j hij (Or.inr hi)) hc
    linarith
  · rw [hla, hla]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds.deMul, if_pos hi, if_neg (not_lt.2 hj)]
    have pA := pair_of le_rfl hA hpA τ i j hi hj
    have pL := mul_le_mul_of_nonneg_left (pair_of zero_le_one hL hpL τ i j hi hj) (Nat.cast_nonneg (α := ℝ) c)
    have hs2 : ((s / 2 : ℕ) : ℝ) * 2 ≤ s := by exact_mod_cast Nat.div_mul_le_self s 2
    generalize s / 2 = q at *
    push_cast
    nlinarith

theorem card_sq_le {r : ℕ} (X : Data E r) (hr : 2 ≤ r) : X.Ψ.card * r ^ 2 ≤ 4 * nd X ^ 2 := by
  have hnd : X.Ψ.card * (r - 1) ≤ nd X := by
    unfold nd
    rw [Fintype.card_prod, Fintype.card_coe]
    apply Nat.mul_le_mul_left
    have := Fintype.card_le_of_injective
      (fun k : Fin (r - 1) => (⟨(⟨k.1 + 1, by omega⟩, ⟨k.1, by omega⟩), by simp [Fin.lt_def]⟩ :
        {p : Fin r × Fin r // p.2 < p.1}))
      (by
        intro a b hab
        simp only [Subtype.mk.injEq, Prod.mk.injEq, Fin.mk.injEq] at hab
        exact Fin.ext hab.2)
    simpa using this
  obtain ⟨q, rfl⟩ : ∃ q, r = q + 2 := ⟨r - 2, by omega⟩
  have e : q + 2 - 1 = q + 1 := by omega
  rw [e] at hnd
  set f := X.Ψ.card
  have h1 : (q + 2) ^ 2 ≤ 4 * (q + 1) ^ 2 := by nlinarith
  have h2 : f * (q + 1) ^ 2 ≤ (f * (q + 1)) ^ 2 := by
    rw [mul_pow]
    rcases Nat.eq_zero_or_pos f with hf | hf
    · simp [hf]
    · exact Nat.mul_le_mul_right _ (by nlinarith)
  have h3 : (f * (q + 1)) ^ 2 ≤ nd X ^ 2 := Nat.pow_le_pow_left hnd 2
  calc f * (q + 2) ^ 2 ≤ f * (4 * (q + 1) ^ 2) := Nat.mul_le_mul_left _ h1
    _ = 4 * (f * (q + 1) ^ 2) := by ring
    _ ≤ 4 * nd X ^ 2 := by omega

theorem prod_mem_SS {r : ℕ} (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) {la : Wt X.Ψ r}
    {Q : Frame X.Ψ r → ℂ} (hQ : X.IsBddSec la Q) (α : Fin (nd X) → ℕ) (hα : ∑ q, α q ≤ Xa.T)
    (hT : 1 ≤ Xa.T) :
    (fun x => Q x * monoM X Fl.s α x * Fl.w0 x ^ (Xa.T - ∑ q, α q)) ∈ X.SS (la + Xa.T • Xa.L) := by
  classical
  have hsb : ∀ k, X.IsBddSec Xa.L (Fl.s k) := fun k => (Fl.s_van k).1.1
  have hw0b : X.IsBddSec Xa.L Fl.w0 := Fl.weightForm_vanishes.1.1
  by_cases hn : 1 ≤ Xa.T - ∑ q, α q
  · obtain ⟨n, hn'⟩ : ∃ n, Xa.T - ∑ q, α q = n + 1 := ⟨Xa.T - ∑ q, α q - 1, by omega⟩
    have hB := GlobalTheory.UpTie.LeadCount.bdd_mul_pow X
      (GlobalTheory.UpTie.LeadCount.bdd_mul_prod X hQ hsb α Finset.univ) hw0b n
    have h := (siegelSpaceAlgebra_holds r X Xa.L (la + (∑ k, α k) • Xa.L + n • Xa.L) 0).2.1 Fl.w0 Fl.weightForm_vanishes.1 _ hB
    have hw : Xa.L + (la + (∑ k, α k) • Xa.L + n • Xa.L) = la + Xa.T • Xa.L := by
      have e : Xa.T = ∑ k, α k + n + 1 := by omega
      rw [e, add_smul, add_smul, one_smul]
      abel
    rw [hw] at h
    convert h using 1
    funext x
    simp only [Pi.mul_apply, Pi.pow_apply, Finset.prod_apply, monoM, hn', pow_succ]
    ring
  · have hsum : ∑ q, α q = Xa.T := by omega
    obtain ⟨k, hk⟩ : ∃ k, α k ≠ 0 := by
      by_contra hc
      push_neg at hc
      simp [hc] at hsum
      omega
    have hB := GlobalTheory.UpTie.LeadCount.bdd_mul_prod X (GlobalTheory.UpTie.LeadCount.bdd_mul_pow X hQ (hsb k) (α k - 1))
      hsb α (Finset.univ.erase k)
    have h := (siegelSpaceAlgebra_holds r X Xa.L (la + (α k - 1) • Xa.L + (∑ i ∈ Finset.univ.erase k, α i) • Xa.L) 0).2.1
      (Fl.s k) (Fl.s_van k).1 _ hB
    have hw : Xa.L + (la + (α k - 1) • Xa.L + (∑ i ∈ Finset.univ.erase k, α i) • Xa.L) =
        la + Xa.T • Xa.L := by
      have e1 := Finset.add_sum_erase Finset.univ α (Finset.mem_univ k)
      have e : Xa.T = 1 + (α k - 1) + ∑ i ∈ Finset.univ.erase k, α i := by omega
      rw [e, add_smul, add_smul, one_smul]
      abel
    rw [hw] at h
    convert h using 1
    funext x
    have hpk : Fl.s k x ^ α k = Fl.s k x * Fl.s k x ^ (α k - 1) := by
      rw [← pow_succ']; congr 1; omega
    simp only [Pi.mul_apply, Pi.pow_apply, Finset.prod_apply, monoM]
    rw [← Finset.mul_prod_erase Finset.univ (fun i => Fl.s i x ^ α i) (Finset.mem_univ k), hsum,
      Nat.sub_self, pow_zero, hpk]
    ring

end GlobalTheory.LowerInterp

namespace GlobalTheory.LowerInterp

open GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

theorem lowered_interp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r)
    (Xa : ArchInM X.toData) (Fl : FlatM X.toData Xa), GlobalTheory.Shares.Margins X.toData Xa → 0 < X.p0 → X.p0 < r →
    GapsGe X.p0 Xa.L 1 → PairGe Xa.L (1.9 * Xa.T) →
    GapsGe X.p0 (Xa.Fp - kLog X.Ψ r - (nd X.toData + 2) • Xa.L) 0 →
    PairGe (Xa.Fp - kLog X.Ψ r - (nd X.toData + 2) • Xa.L) 1 →
    ∀ s : ℕ, Even s → s ≤ Xa.T → ∀ u : Frame X.Ψ r → ℂ, u ∈ X.SS (deMul X.Ψ r X.p0 s) →
    (∃ x ∈ X.dom, u x ≠ 0) → ∀ j : Fin Fl.δ, ∃ F : Frame X.Ψ r → ℂ, DifferentiableOn ℂ F X.dom ∧
      (∀ j', F (Fl.xs j') = if j' = j then 1 else 0) ∧
      ∀ α : Fin (nd X.toData) → ℕ, ∑ q, α q ≤ Xa.T →
        (fun x => F x * monoM X.toData Fl.s α x * Fl.w0 x ^ (Xa.T - ∑ q, α q)) ∈
          X.SS (Xa.Fp + Xa.T • Xa.L - deMul X.Ψ r X.p0 s) := by
  intro E _ _ _ r X Xa Fl _ hp0 hp0r hgL hpL hgA hpA s _ hsT _ _ _ j
  classical
  have hcm := (GlobalTheory.CurvMarginClosed.curv_and_margin_closed (E := E)).2
  have e1 : ∀ τ k, (Xa.Fp - deMul X.Ψ r X.p0 s - kapW X.toData - nd X.toData • Xa.L) τ k =
      (Xa.Fp - kLog X.Ψ r - (nd X.toData + 2) • Xa.L) τ k + ((2 : ℕ) : ℤ) * Xa.L τ k -
        deMul X.Ψ r X.p0 s τ k := by
    intro τ k
    simp only [Pi.sub_apply, Pi.smul_apply, kapW, kLog]
    simp only [nsmul_eq_mul]
    push_cast
    ring
  have e2 : ∀ τ k, (Xa.Fp - deMul X.Ψ r X.p0 s - kapW X.toData - (nd X.toData + 1) • Xa.L) τ k =
      (Xa.Fp - kLog X.Ψ r - (nd X.toData + 2) • Xa.L) τ k + ((1 : ℕ) : ℤ) * Xa.L τ k -
        deMul X.Ψ r X.p0 s τ k := by
    intro τ k
    simp only [Pi.sub_apply, Pi.smul_apply, kapW, kLog]
    simp only [nsmul_eq_mul]
    push_cast
    ring
  have F1 := comb_facts s 2 hgA hgL hpA hpL e1
  have F2 := comb_facts s 1 hgA hgL hpA hpL e2
  have hT := Xa.T_ge
  have hcard : (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 ≤ 4 * (nd X.toData : ℝ) ^ 2 := by
    exact_mod_cast card_sq_le X.toData (by omega)
  have hT' : 11 * (nd X.toData : ℝ) ^ 2 ≤ Xa.T := by exact_mod_cast hT
  have hsT' : (s : ℝ) ≤ Xa.T := by exact_mod_cast hsT
  set m : ℝ := 1 + ((2 : ℕ) : ℝ) * (1.9 * Xa.T) - s with hm
  have hm4 : 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < m := by
    rw [hm]; push_cast; nlinarith
  have hmar : ∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧ bb < m ∧
      ∀ x0, IsOrth X.toData x0 → ∀ z ∈ OmF X.toData x0, ∀ ξ : Fin (nd X.toData) → ℂ,
        m * leviRh X.toData x0 z ξ ≤ leviO X.toData x0 (phla X.toData (Xa.Fp - deMul X.Ψ r X.p0 s)) z ξ -
          leviDens X.toData x0 z ξ - (nd X.toData : ℝ) * leviO X.toData x0 (phla X.toData Xa.L) z ξ +
          leviO X.toData x0 (fun _ => (0 : ℝ)) z ξ := by
    refine ⟨(4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + m) / 2, m, by linarith, by linarith, fun x0 ho z hz ξ => ?_⟩
    rw [leviO_zero, add_zero, ← IW.leviM_comb X.toData x0 ho hz]
    exact hcm r X.toData _ m F1.1 F1.2.1 F1.2.2 x0 ho z hz ξ
  have hstr : ∃ η : ℝ, 0 < η ∧ ∀ x0, IsOrth X.toData x0 → ∀ z ∈ OmF X.toData x0, ∀ ξ : Fin (nd X.toData) → ℂ,
      2 * η * leviO X.toData x0 (phla X.toData Xa.L) z ξ ≤
        leviO X.toData x0 (phla X.toData (Xa.Fp - deMul X.Ψ r X.p0 s)) z ξ - leviDens X.toData x0 z ξ -
        (nd X.toData : ℝ) * leviO X.toData x0 (phla X.toData Xa.L) z ξ +
          leviO X.toData x0 (fun _ => (0 : ℝ)) z ξ := by
    refine ⟨1 / 2, by norm_num, fun x0 ho z hz ξ => ?_⟩
    have h1 := IW.leviM_comb X.toData x0 ho hz (Xa.Fp - deMul X.Ψ r X.p0 s) Xa.L (nd X.toData + 1) ξ
    have h2 := hcm r X.toData _ 0 F2.1 F2.2.1 (fun τ i j hi hj => by
      have := F2.2.2 τ i j hi hj
      push_cast at this ⊢
      linarith) x0 ho z hz ξ
    rw [leviO_zero, add_zero]
    have h3 : leviO X.toData x0 (phla X.toData (Xa.Fp - deMul X.Ψ r X.p0 s - kapW X.toData -
        (nd X.toData + 1) • Xa.L)) z ξ = leviM X.toData (phla X.toData (Xa.Fp - deMul X.Ψ r X.p0 s - kapW X.toData -
        (nd X.toData + 1) • Xa.L)) x0 z ξ := rfl
    rw [h3, h1] at h2
    push_cast at h2
    linarith
  obtain ⟨x0, W, bb, F0, P, γ0, ho, hW, hWl, hbb, hF0, hA, hBE, hPF, h0, hne, hz⟩ :=
    kron_at X.toData Xa Fl (Xa.Fp - deMul X.Ψ r X.p0 s) (fun _ => 0) (fun _ _ _ _ _ _ => rfl)
      (fun _ _ => contDiffOn_const) ⟨0, fun _ _ => le_rfl⟩ hmar hstr j
  obtain ⟨-, hbdd, -⟩ := poin_holds r X.toData x0 ho (GlobalTheory.ClosedDiscontinuity.propDisc_closed r X.toData)
    (Xa.Fp - deMul X.Ψ r X.p0 s) W bb hW hWl hbb F0 P hF0 hA hBE hPF
  set Q := poin X.toData (Xa.Fp - deMul X.Ψ r X.p0 s) P with hQ
  have hQj : Q (Fl.xs j) ≠ 0 := by
    rw [hQ, poin_single X.toData _ P _ h0 fun γ hγ hne' => hz γ hγ j (Or.inl hne')]
    exact mul_ne_zero (inv_ne_zero (chi_ne_zero X.toData _ h0)) hne
  have hQz : ∀ j', j' ≠ j → Q (Fl.xs j') = 0 := fun j' hj' =>
    poin_zero X.toData _ P _ fun γ hγ => hz γ hγ j' (Or.inr hj')
  refine ⟨fun x => (Q (Fl.xs j))⁻¹ * Q x, hbdd.1.1.const_mul _, fun j' => ?_, fun α hα => ?_⟩
  · by_cases h : j' = j
    · subst h
      simp [hQj]
    · simp [h, hQz j' h]
  · have hp := prod_mem_SS X.toData Xa Fl hbdd α hα (by have := Xa.n_ge; nlinarith)
    have hw : Xa.Fp - deMul X.Ψ r X.p0 s + Xa.T • Xa.L = Xa.Fp + Xa.T • Xa.L - deMul X.Ψ r X.p0 s := by abel
    rw [hw] at hp
    have hsm := (siegelSpaceAlgebra_holds r X.toData (Xa.Fp + Xa.T • Xa.L - deMul X.Ψ r X.p0 s)
      (Xa.Fp + Xa.T • Xa.L - deMul X.Ψ r X.p0 s) 0).1.2.2 (Q (Fl.xs j))⁻¹ _ hp
    convert hsm using 1
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

end GlobalTheory.LowerInterp
