import Formalism.PeriodIntegrals.SDiffGram
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramDifferenceRenaming.RenGramRhs

noncomputable section

open Classical

namespace PI.UnitaryGroupMassFormula.SDiffGram

open PI.FglGram MvPowerSeries
open PI.UnitaryGroupMassFormula.PhDualGram (ren ren_X simeq_ren ren_be)
open PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram (Good simeq_iff_good good_add good_sub)

variable {p : ℕ} [Fact p.Prime] {l ex ph : PowerSeries ℂ_[p]}

theorem block_simeq (hl0 : PowerSeries.constantCoeff l = 0) (hex0 : PowerSeries.constantCoeff ex = 0)
    {S : Set (ℂ_[p] × ℂ_[p])}
    (hG : ∀ (κ : Type) [Fintype κ] (k : ℕ) (A : Fin k → κ → ℂ_[p] × ℂ_[p]), (∀ j i, A j i ∈ S) →
      Simeq (PhOn l ex ph A) (GramRhs l ex ph A))
    {κ T τ : Type} [Fintype κ] [Fintype T] {n : ℕ} (e : T ≃ Fin n) (r : T → τ)
    (a : T → κ → ℂ_[p] × ℂ_[p]) (ha : ∀ x k, a x k ∈ S) :
    Simeq (PhVF l ex ph a (fun x => X (r x))) (GR l ex ph e a (fun x => X (r x))) := by
  have h := simeq_ren (p := p) (fun j => r (e.symm j)) (hG κ n (fun j => a (e.symm j)) (fun j i => ha _ i))
  rw [PhOn_eq, ren_PhVF hex0 hl0 _ _ _ (fun j => constantCoeff_X j), ren_GramRhs hex0 hl0 e] at h
  simp only [ren_X, Equiv.symm_apply_apply] at h
  have eA : PhVF l ex ph (fun j => a (e.symm j)) (fun j => X (r (e.symm j)) : Fin n → MvPowerSeries τ ℂ_[p]) =
      PhVF l ex ph a (fun x => X (r x)) := PhVF_equiv e a (fun x => X (r x))
  rwa [eA] at h

theorem numbering (ι ι' : Type) [Fintype ι] [Fintype ι'] :
    ∃ (E : ι ⊕ ι' ≃ Fin (Fintype.card ι + Fintype.card ι')) (eι : ι ≃ Fin (Fintype.card ι))
      (eι' : ι' ≃ Fin (Fintype.card ι')),
      (∀ i i', E (Sum.inl i) < E (Sum.inl i') ↔ eι i < eι i') ∧
      (∀ g g', E (Sum.inr g) < E (Sum.inr g') ↔ eι' g < eι' g') ∧
      (∀ i g, E (Sum.inl i) < E (Sum.inr g)) ∧ (∀ g i, ¬ E (Sum.inr g) < E (Sum.inl i)) := by
  let eι : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let eι' : ι' ≃ Fin (Fintype.card ι') := Fintype.equivFin ι'
  have hlr : ∀ i g, (Equiv.sumCongr eι eι').trans finSumFinEquiv (Sum.inl i) <
      (Equiv.sumCongr eι eι').trans finSumFinEquiv (Sum.inr g) := by
    intro i g
    simp only [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
      finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.lt_def, Fin.val_castAdd,
      Fin.val_natAdd]
    have := (eι i).isLt
    omega
  refine ⟨(Equiv.sumCongr eι eι').trans finSumFinEquiv, eι, eι', ?_, ?_, hlr,
    fun g i h => lt_asymm h (hlr i g)⟩
  · intro i i'
    simp only [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, finSumFinEquiv_apply_left]
    rw [Fin.lt_def, Fin.lt_def, Fin.val_castAdd, Fin.val_castAdd]
  · intro g g'
    simp only [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, finSumFinEquiv_apply_right]
    rw [Fin.lt_def, Fin.lt_def, Fin.val_natAdd, Fin.val_natAdd]
    omega

theorem cross (hl0 : PowerSeries.constantCoeff l = 0) (hex0 : PowerSeries.constantCoeff ex = 0)
    {S : Set (ℂ_[p] × ℂ_[p])} (h0 : (0 : ℂ_[p] × ℂ_[p]) ∈ S) (hsw : ∀ α ∈ S, α.swap ∈ S)
    (hadd : ∀ α ∈ S, ∀ β ∈ S, α + β ∈ S) (hmul : ∀ α ∈ S, ∀ β ∈ S, α * β ∈ S)
    (hconj : ∀ α ∈ S, Simeq (be l ex ph (mulBy l ex α.1 (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
        (be l ex ph (Xv 0) (mulBy l ex α.2 (Xv 1))))
    {κ ι ι' : Type} [Fintype κ] [Fintype ι] [Fintype ι']
    (a : ι → κ → ℂ_[p] × ℂ_[p]) (a' : ι' → κ → ℂ_[p] × ℂ_[p])
    (ha : ∀ e k, a e k ∈ S) (ha' : ∀ e k, a' e k ∈ S) :
    Good (sdRF l ex ph a a' - sdRF' l ex ph a a') := by
  unfold sdRF sdRF'
  rw [← Finset.sum_sub_distrib]
  refine good_sum _ _ fun f _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine good_sum _ _ fun g _ => ?_
  have hα := hP_mem h0 hsw hadd hmul (a f) (a' g) (ha f) (ha' g)
  have h := simeq_ren (p := p) (![Sum.inl f, Sum.inr g] : Fin 2 → ι ⊕ ι') (hconj _ hα)
  simp only [Xv] at h
  rw [ren_be hex0 hl0 _ (cc_mulBy hex0 hl0 _ (constantCoeff_X _)) (constantCoeff_X _),
    ren_be hex0 hl0 _ (constantCoeff_X _) (cc_mulBy hex0 hl0 _ (constantCoeff_X _)),
    ren_mulBy hl0 _ _ (constantCoeff_X _), ren_mulBy hl0 _ _ (constantCoeff_X _)] at h
  simp only [ren_X, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  exact (simeq_iff_good _ _).mp h

theorem core (hl0 : PowerSeries.constantCoeff l = 0) (hex0 : PowerSeries.constantCoeff ex = 0)
    {S : Set (ℂ_[p] × ℂ_[p])} (h0 : (0 : ℂ_[p] × ℂ_[p]) ∈ S) (hsw : ∀ α ∈ S, α.swap ∈ S)
    (hadd : ∀ α ∈ S, ∀ β ∈ S, α + β ∈ S) (hmul : ∀ α ∈ S, ∀ β ∈ S, α * β ∈ S)
    (hG : ∀ (κ : Type) [Fintype κ] (k : ℕ) (A : Fin k → κ → ℂ_[p] × ℂ_[p]), (∀ j i, A j i ∈ S) →
      Simeq (PhOn l ex ph A) (GramRhs l ex ph A))
    (hconj : ∀ α ∈ S, Simeq (be l ex ph (mulBy l ex α.1 (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
        (be l ex ph (Xv 0) (mulBy l ex α.2 (Xv 1))))
    {κ ι ι' : Type} [Fintype κ] [Fintype ι] [Fintype ι']
    (a : ι → κ → ℂ_[p] × ℂ_[p]) (a' : ι' → κ → ℂ_[p] × ℂ_[p])
    (ha : ∀ e k, a e k ∈ S) (ha' : ∀ e k, a' e k ∈ S) :
    Simeq (PhOn l ex ph (Sum.elim a a') - PhVF l ex ph a (fun e => X (Sum.inl e)) -
        PhVF l ex ph a' (fun e => X (Sum.inr e))) (sdRF l ex ph a a') ∧
    Simeq (PhOn l ex ph (Sum.elim a a') - PhVF l ex ph a (fun e => X (Sum.inl e)) -
        PhVF l ex ph a' (fun e => X (Sum.inr e))) (sdRF' l ex ph a a') := by
  obtain ⟨E, eι, eι', hll, hrr, hlr, hrl⟩ := numbering ι ι'
  have hS : ∀ x k, Sum.elim a a' x k ∈ S := by
    rintro (e | e) k
    exacts [ha e k, ha' e k]
  have hF := block_simeq hl0 hex0 hG E (fun x => x) (Sum.elim a a') hS
  rw [gr_split (E := E) eι eι' hll hrr hlr hrl a a'] at hF
  have hA := block_simeq hl0 hex0 hG eι (fun i => (Sum.inl i : ι ⊕ ι')) a ha
  have hA' := block_simeq hl0 hex0 hG eι' (fun g => (Sum.inr g : ι ⊕ ι')) a' ha'
  have first : Good (PhOn l ex ph (Sum.elim a a') - PhVF l ex ph a (fun e => X (Sum.inl e)) -
      PhVF l ex ph a' (fun e => X (Sum.inr e)) - sdRF l ex ph a a') := by
    have g := good_sub (good_sub ((simeq_iff_good _ _).mp hF) ((simeq_iff_good _ _).mp hA))
      ((simeq_iff_good _ _).mp hA')
    rw [← PhOn_eq] at g
    convert g using 1
    abel
  refine ⟨first, ?_⟩
  have g := good_add first (cross hl0 hex0 h0 hsw hadd hmul hconj a a' ha ha')
  rw [simeq_iff_good]
  convert g using 1
  abel

theorem sDiffGram_main : PI.SDiffGram.SDiffGram := by
  intro p _ l ex ph hl0 hex0 _ _ S h0 hsw hadd hmul hG hconj κ ι ι' _ _ _ a a' ha ha'
  exact core hl0 hex0 h0 hsw hadd hmul (fun κ _ k A hA => hG κ k A hA) hconj a a' ha ha'

end PI.UnitaryGroupMassFormula.SDiffGram

end
