import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.ExistsNonzeroPhysicalHighestWeightVectorTensFock
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SchSharpA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CsqDdPt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.KernelLemma
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PRVComponents

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ}

theorem gb_rhoN_eq (ε : Fin n → Bool) {a b : Fin n} (hab : a < b) (he : ε a = ε b)
    (hc : ∀ c, a < c → c < b → ε c = ε a) : rhoN ε a = rhoN ε b := by
  have h := lfD_cnt (fun c => ε c ≠ ε a) hab
  have h1 : (univ.filter fun c => c = a ∧ ε c ≠ ε a).card = 0 := by
    rw [lfD_single]; simp
  have h2 : (univ.filter fun c => c = b ∧ ε c ≠ ε a).card = 0 := by
    rw [lfD_single]; simp [he]
  have h3 : (univ.filter fun c => a < c ∧ c < b ∧ ε c ≠ ε a).card = 0 := by
    rw [card_eq_zero, filter_eq_empty_iff]
    intro c _ hc'
    exact hc'.2.2 (hc c hc'.1 hc'.2.1)
  simp only [rhoN, ← he]
  rw [h1, h2, h3] at h
  have h' := congrArg (Nat.cast : ℕ → ℝ) h
  push_cast at h'
  linarith

theorem gb_rhoC_ge (ε : Fin n → Bool) {a b : Fin n} (hab : a < b) (he : ε a = ε b) :
    1 ≤ rhoC ε a - rhoC ε b := by
  have h := lfD_cnt (fun c => ε c = ε a) hab
  have h1 : (univ.filter fun c => c = a ∧ ε c = ε a).card = 1 := by
    rw [lfD_single]; simp
  have h2 : (univ.filter fun c => c = b ∧ ε c = ε a).card = 1 := by
    rw [lfD_single]; simp [he]
  simp only [rhoC, ← he]
  rw [h1, h2] at h
  have h' := congrArg (Nat.cast : ℕ → ℝ) h
  push_cast at h'
  have : (0 : ℝ) ≤ ((univ.filter fun c => a < c ∧ c < b ∧ ε c = ε a).card : ℝ) := Nat.cast_nonneg _
  linarith

theorem gb_phSum_le (ε : Fin n → Bool) {Ph : Finset (Fin n × Fin n)} (hnc : ∀ x ∈ Ph, ε x.1 ≠ ε x.2)
    (a : Fin n) : phSum Ph a ≤ oppCount ε a := by
  unfold phSum; rw [sum_root_apply]
  have h0 : (0:ℝ) ≤ ((Ph.filter fun y => y.2 = a).card : ℝ) := Nat.cast_nonneg _
  have h3 : ((Ph.filter fun y => y.1 = a).card : ℝ) ≤ oppCount ε a := by exact_mod_cast card_fst_le ε Ph hnc a
  linarith

theorem gb_phSum_ge (ε : Fin n → Bool) {Ph : Finset (Fin n × Fin n)} (hnc : ∀ x ∈ Ph, ε x.1 ≠ ε x.2)
    (a : Fin n) : -(oppCount ε a : ℝ) ≤ phSum Ph a := by
  unfold phSum; rw [sum_root_apply]
  have h0 : (0:ℝ) ≤ ((Ph.filter fun y => y.1 = a).card : ℝ) := Nat.cast_nonneg _
  have h3 : ((Ph.filter fun y => y.2 = a).card : ℝ) ≤ oppCount ε a := by exact_mod_cast card_snd_le ε Ph hnc a
  linarith

theorem dirac_block {ε : Fin n → Bool} {lam : Fin n → ℝ} (hg : Gap3 ε lam)
    {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E)
    {Ph : Finset (Fin n × Fin n)} (hPh : IsPosNC ε Ph) {W : Submodule ℂ M}
    (hW : IsKIrrHW ε E (lowK ε lam - phSum Ph) W) : BlockAnti ε (lam - phSum Ph) := by
  classical
  obtain ⟨hmono, h, hh, hn⟩ := hg
  have hF : Formalism.REAL.KRel ε E := fun a b c d _ _ => hE a b c d
  have hnc : ∀ x ∈ Ph, ε x.1 ≠ ε x.2 := fun x hx => (hPh x hx).2
  have hW' : IsKIrrHW ε E (lowK ε (lam - phSum Ph)) W := by
    have : lowK ε (lam - phSum Ph) = lowK ε lam - phSum Ph := by unfold lowK; abel
    rw [this]; exact hW
  intro a b hab he
  simp only [Pi.sub_apply]
  by_cases hc : ∃ c, a < c ∧ c < b ∧ ε c ≠ ε a
  · obtain ⟨c, hac, hcb, hce⟩ := hc
    have g1 := hh a c (Ne.symm hce)
    have g2 := hh c b (by rw [← he]; exact hce)
    rw [abs_of_pos (sub_pos.mpr (hmono hac))] at g1
    rw [abs_of_pos (sub_pos.mpr (hmono hcb))] at g2
    have pa := gb_phSum_le ε hnc a
    have pb := gb_phSum_ge ε hnc b
    have ob : oppCount ε b = oppCount ε a := by unfold oppCount; rw [he]
    rw [ob] at pb
    have oc : 2 ≤ oppCount ε c := by
      unfold oppCount
      have hsub : ({a, b} : Finset (Fin n)) ⊆ univ.filter fun x => ε x ≠ ε c := by
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        simp only [mem_filter, mem_univ, true_and]
        rcases hx with rfl | rfl
        · exact Ne.symm hce
        · rw [← he]; exact Ne.symm hce
      have := Finset.card_le_card hsub
      rwa [Finset.card_pair hab.ne] at this
    have hsum := oppCount_add ε (Ne.symm hce)
    have oc' : (2:ℝ) ≤ oppCount ε c := by exact_mod_cast oc
    linarith
  · push Not at hc
    obtain ⟨N, hN⟩ := HW.kIrrHW_int ε hF hW' a b hab he
    have hC := gb_rhoC_ge ε hab he
    have hR := gb_rhoN_eq ε hab he hc
    simp only [lowK, Pi.add_apply, Pi.sub_apply] at hN
    have : (0:ℝ) ≤ N := Nat.cast_nonneg _
    linarith

theorem dirac_sharp {ε : Fin n → Bool} {lam : Fin n → ℝ} (hg : Gap3 ε lam)
    {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
    (hE : IsGlRep E) (hU : IsInfUnitary ε E) {Ph : Finset (Fin n × Fin n)} (hPh : IsPosNC ε Ph)
    (hne : Ph.Nonempty) {W : Submodule ℂ M} (hW : IsKIrrHW ε E (lowK ε lam - phSum Ph) W)
    (hc : ∀ v ∈ W, casimir E v = (casVal lam : ℂ) • v) : False := by
  classical
  have hb := dirac_block hg hE hPh hW
  obtain ⟨hmono, h, hh, hn⟩ := hg
  have hnc : ∀ x ∈ Ph, ε x.1 ≠ ε x.2 := fun x hx => (hPh x hx).2
  have hW' : IsKIrrHW ε E (lowK ε (lam - phSum Ph)) W := by
    have : lowK ε (lam - phSum Ph) = lowK ε lam - phSum Ph := by unfold lowK; abel
    rw [this]; exact hW
  obtain ⟨z, hzW, -, hz0, hzK⟩ := exists_nonzero_physical_highestWeight_vector_tensFock ε hE hb hW'
  have hzK' : IsKHWVec ε (diagE ε (eT E) cpT cmT) ((lam - phSum Ph - rhoC ε) + rhoHol ε) z := hzK
  have hcas : casimir (eT E) z = ((casVal lam : ℝ) : ℂ) • z := by
    obtain ⟨z0, hz0eq⟩ := LinearMap.mem_range.mp hzW
    rw [ssh_casimir_eT, ← hz0eq]
    clear hz0eq
    induction z0 using TensorProduct.induction_on with
    | zero => simp
    | tmul m f => simp [TensorProduct.map_tmul, hc _ m.2, TensorProduct.smul_tmul']
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  have hD2 := two_D_sq_khw (eT_isGlRep hE) cpT_cmT_isCAR (eT_commutesCAR E) hzK' hcas
  have hval : nsq (lam - phSum Ph - rhoC ε + rhoC ε) - nsq (rho n) - casVal lam =
      nsq (lam - phSum Ph) - nsq lam := by
    rw [sub_add_cancel]
    unfold casVal
    ring
  obtain ⟨x0, hx0⟩ := hne
  have hx0' := (hPh x0 hx0).1
  have hn2 : (2 : ℝ) ≤ n := by
    have := x0.2.2
    have := Fin.lt_def.mp hx0'
    exact_mod_cast (show 2 ≤ n by omega)
  have hpos : ∀ x ∈ Ph, h ≤ lam x.1 - lam x.2 := by
    intro x hx
    have := hh x.1 x.2 (hnc x hx)
    rwa [abs_of_pos (sub_pos.mpr (hmono (hPh x hx).1))] at this
  have hker := kernel_lemma ε lam (h := h) (by linarith) Ph hnc hpos
  have hcard : (1 : ℝ) ≤ Ph.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨x0, hx0⟩
  have hneg : nsq (lam - phSum Ph) - nsq lam < 0 := by
    have h2n : 0 < 2 * h - n := by linarith
    have : 0 < (2 * h - n) * Ph.card := by positivity
    unfold phSum
    linarith
  set D := dOp ε (eT E) cpT + dOp' ε (eT E) cmT with hDdef
  have key : tform z ((2 : ℂ) • (D * D) z) = ((nsq (lam - phSum Ph) - nsq lam : ℝ) : ℂ) * tform z z := by
    rw [hD2, tform_smul_right, ← hval]
    push_cast
    ring
  rw [tform_smul_right, Module.End.mul_apply, ← tform_D hU] at key
  have hre := congrArg Complex.re key
  rw [Complex.re_ofReal_mul] at hre
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero] at hre
  have p1 := tform_self_re_nonneg (D z)
  have p2 := tform_self_re_pos hz0
  nlinarith

theorem no_irreducible_at_noncompact_root_shift {ε : Fin n → Bool} {lam : Fin n → ℝ} (hg : Gap3 ε lam)
    {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
    (hE : IsGlRep E) (hU : IsInfUnitary ε E) {a b : Fin n} (hab : a < b) (hε : ε a ≠ ε b)
    {W : Submodule ℂ M} (hW : IsKIrrHW ε E (lowK ε lam - root a b) W)
    (hc : ∀ v ∈ W, casimir E v = (casVal lam : ℂ) • v) : False := by
  have hP : phSum {(a, b)} = root a b := by simp [phSum]
  refine dirac_sharp hg hE hU (Ph := {(a, b)}) ?_ (singleton_nonempty _) (by rw [hP]; exact hW) hc
  intro x hx
  rw [mem_singleton] at hx
  subst hx
  exact ⟨hab, hε⟩

end ReciprocityTheory.ChartRestriction.DS.TRGap
