import Formalism.PeriodIntegrals.FglGram
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DualGramSubstitution.BeMulByZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CubeFormalIdentities.CoeffPowMulPowEqZero

noncomputable section

open Classical

namespace PI.UnitaryGroupMassFormula.SDiffGram

open PI.FglGram MvPowerSeries
open PI.UnitaryGroupMassFormula.PhDualGram (ren ren_apply ren_psubst ren_X ren_C simeq_ren cc_lin ren_lin ren_be ren_PhOn)
open PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram (Good simeq_iff_good good_add good_sub expMv_zero int_one)

variable {p : ℕ} [Fact p.Prime] {l ex ph : PowerSeries ℂ_[p]}

def PhVF (l ex ph : PowerSeries ℂ_[p]) {κ T σ : Type} [Fintype κ] [Fintype T]
    (B : T → κ → ℂ_[p] × ℂ_[p]) (w : T → MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  ∑ k, phAt ph (lin l ex (fun e => (B e k).1) w)

def GR (l ex ph : PowerSeries ℂ_[p]) {κ T σ : Type} [Fintype κ] [Fintype T] {m : ℕ} (o : T → Fin m)
    (B : T → κ → ℂ_[p] × ℂ_[p]) (w : T → MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  ∑ x, C (hP (B x) (B x)).1 * phAt ph (w x) +
    ∑ x, ∑ y, if o x < o y then be l ex ph (mulBy l ex (hP (B x) (B y)).1 (w x)) (w y) else 0

def sdRF (l ex ph : PowerSeries ℂ_[p]) {κ ι ι' : Type} [Fintype κ] [Fintype ι] [Fintype ι']
    (a : ι → κ → ℂ_[p] × ℂ_[p]) (a' : ι' → κ → ℂ_[p] × ℂ_[p]) : MvPowerSeries (ι ⊕ ι') ℂ_[p] :=
  ∑ f, ∑ f', be l ex ph (mulBy l ex (hP (a f) (a' f')).1 (X (Sum.inl f))) (X (Sum.inr f'))

def sdRF' (l ex ph : PowerSeries ℂ_[p]) {κ ι ι' : Type} [Fintype κ] [Fintype ι] [Fintype ι']
    (a : ι → κ → ℂ_[p] × ℂ_[p]) (a' : ι' → κ → ℂ_[p] × ℂ_[p]) : MvPowerSeries (ι ⊕ ι') ℂ_[p] :=
  ∑ f, ∑ f', be l ex ph (X (Sum.inl f)) (mulBy l ex (hP (a f) (a' f')).2 (X (Sum.inr f')))

theorem PhOn_eq {κ T : Type} [Fintype κ] [Fintype T] (B : T → κ → ℂ_[p] × ℂ_[p]) :
    PhOn l ex ph B = PhVF l ex ph B (fun e => X e) := rfl

theorem cc_lg (hl0 : PowerSeries.constantCoeff l = 0) {σ : Type} {x : MvPowerSeries σ ℂ_[p]}
    (hx : constantCoeff x = 0) : constantCoeff (lg l x) = 0 :=
  PI.FglPhSplit.Wk.cc_psubst _ hl0 hx

theorem cc_mulBy (hex0 : PowerSeries.constantCoeff ex = 0) (hl0 : PowerSeries.constantCoeff l = 0)
    {σ : Type} (c : ℂ_[p]) {x : MvPowerSeries σ ℂ_[p]} (hx : constantCoeff x = 0) :
    constantCoeff (mulBy l ex c x) = 0 := by
  have h : constantCoeff (C c * lg l x) = 0 := by rw [map_mul, cc_lg hl0 hx, mul_zero]
  exact PI.FglPhSplit.Wk.cc_psubst _ hex0 h

theorem cc_linF (hex0 : PowerSeries.constantCoeff ex = 0) (hl0 : PowerSeries.constantCoeff l = 0)
    {σ T : Type} [Fintype T] (c : T → ℂ_[p]) (w : T → MvPowerSeries σ ℂ_[p])
    (hw : ∀ e, constantCoeff (w e) = 0) : constantCoeff (lin l ex c w) = 0 :=
  PI.FglPhSplit.Wk.cc_psubst _ hex0 (cc_lin hl0 c w hw)

theorem ren_mulBy (hl0 : PowerSeries.constantCoeff l = 0) {σ τ : Type} [Finite σ] (r : σ → τ)
    (c : ℂ_[p]) {x : MvPowerSeries σ ℂ_[p]} (hx : constantCoeff x = 0) :
    ren (p := p) r (mulBy l ex c x) = mulBy l ex c (ren r x) := by
  have h : constantCoeff (C c * lg l x) = 0 := by rw [map_mul, cc_lg hl0 hx, mul_zero]
  have e1 : mulBy l ex c x = PowerSeries.subst (C c * lg l x) ex := rfl
  have e2 : lg l x = PowerSeries.subst x l := rfl
  have e3 : mulBy l ex c (ren r x) = PowerSeries.subst (C c * PowerSeries.subst (ren r x) l) ex := rfl
  rw [e1, ren_psubst r _ h, map_mul, ren_C, e2, ren_psubst r _ hx, e3]

theorem ren_phAt {σ τ : Type} [Finite σ] (r : σ → τ) {x : MvPowerSeries σ ℂ_[p]}
    (hx : constantCoeff x = 0) : ren (p := p) r (phAt ph x) = phAt ph (ren r x) :=
  ren_psubst r ph hx

theorem ren_PhVF (hex0 : PowerSeries.constantCoeff ex = 0) (hl0 : PowerSeries.constantCoeff l = 0)
    {κ T σ τ : Type} [Fintype κ] [Fintype T] [Finite σ] (r : σ → τ)
    (B : T → κ → ℂ_[p] × ℂ_[p]) (w : T → MvPowerSeries σ ℂ_[p]) (hw : ∀ e, constantCoeff (w e) = 0) :
    ren (p := p) r (PhVF l ex ph B w) = PhVF l ex ph B (fun e => ren r (w e)) := by
  unfold PhVF
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ren_phAt r (cc_linF hex0 hl0 _ w hw), ren_lin r hl0 _ w hw]

theorem PhVF_equiv {κ T T' σ : Type} [Fintype κ] [Fintype T] [Fintype T'] (E : T ≃ T')
    (B : T → κ → ℂ_[p] × ℂ_[p]) (w : T → MvPowerSeries σ ℂ_[p]) :
    PhVF l ex ph (fun j => B (E.symm j)) (fun j => w (E.symm j)) = PhVF l ex ph B w := by
  unfold PhVF
  refine Finset.sum_congr rfl fun k _ => ?_
  exact congrArg (fun S => phAt ph (pt ex S)) (Equiv.sum_comp E.symm (fun e => C (B e k).1 * lg l (w e)))

theorem ren_GramRhs (hex0 : PowerSeries.constantCoeff ex = 0) (hl0 : PowerSeries.constantCoeff l = 0)
    {κ T τ : Type} [Fintype κ] [Fintype T] {m : ℕ} (E : T ≃ Fin m) (r : Fin m → τ)
    (B : T → κ → ℂ_[p] × ℂ_[p]) :
    ren (p := p) r (GramRhs l ex ph (fun j => B (E.symm j))) = GR l ex ph E B (fun x => X (r (E x))) := by
  unfold GramRhs GR
  simp only [Finset.sum_filter, Xv]
  rw [map_add, map_sum, map_sum]
  congr 1
  · refine Fintype.sum_equiv E.symm _ _ fun j => ?_
    rw [map_mul, ren_C, ren_phAt r (constantCoeff_X j), ren_X, Equiv.apply_symm_apply]
  · refine Fintype.sum_equiv E.symm _ _ fun j => ?_
    rw [map_sum]
    refine Fintype.sum_equiv E.symm _ _ fun j' => ?_
    simp only [Equiv.apply_symm_apply]
    split_ifs
    · rw [ren_be hex0 hl0 r (cc_mulBy hex0 hl0 _ (constantCoeff_X _)) (constantCoeff_X _),
        ren_mulBy hl0 r _ (constantCoeff_X _), ren_X, ren_X]
    · exact map_zero _

theorem gr_split {κ ι ι' : Type} [Fintype κ] [Fintype ι] [Fintype ι'] {n n' m : ℕ}
    (E : ι ⊕ ι' → Fin m) (o : ι → Fin n) (o' : ι' → Fin n')
    (hll : ∀ i i', E (Sum.inl i) < E (Sum.inl i') ↔ o i < o i')
    (hrr : ∀ g g', E (Sum.inr g) < E (Sum.inr g') ↔ o' g < o' g')
    (hlr : ∀ i g, E (Sum.inl i) < E (Sum.inr g))
    (hrl : ∀ g i, ¬ E (Sum.inr g) < E (Sum.inl i))
    (a : ι → κ → ℂ_[p] × ℂ_[p]) (a' : ι' → κ → ℂ_[p] × ℂ_[p]) :
    GR l ex ph E (Sum.elim a a') (fun x => X x) =
      GR l ex ph o a (fun i => X (Sum.inl i)) + GR l ex ph o' a' (fun g => X (Sum.inr g)) +
        sdRF l ex ph a a' := by
  unfold GR sdRF
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hll, hrr, hlr, hrl, ↓reduceIte,
    Finset.sum_const_zero, add_zero, zero_add, Finset.sum_add_distrib]
  abel

theorem hP_mem {S : Set (ℂ_[p] × ℂ_[p])} (h0 : (0 : ℂ_[p] × ℂ_[p]) ∈ S) (hsw : ∀ α ∈ S, α.swap ∈ S)
    (hadd : ∀ α ∈ S, ∀ β ∈ S, α + β ∈ S) (hmul : ∀ α ∈ S, ∀ β ∈ S, α * β ∈ S)
    {κ : Type} [Fintype κ] (x y : κ → ℂ_[p] × ℂ_[p]) (hx : ∀ k, x k ∈ S) (hy : ∀ k, y k ∈ S) :
    hP x y ∈ S := by
  unfold hP
  exact Finset.sum_induction _ (· ∈ S) (fun u v hu hv => hadd u hu v hv) h0
    (fun k _ => hmul _ (hx k) _ (hsw _ (hy k)))

theorem good_zero {σ : Type} : Good (0 : MvPowerSeries σ ℂ_[p]) :=
  ⟨map_zero _, by rw [expMv_zero]; exact int_one⟩

theorem good_sum {σ T : Type} (s : Finset T) (F : T → MvPowerSeries σ ℂ_[p]) (h : ∀ i ∈ s, Good (F i)) :
    Good (∑ i ∈ s, F i) :=
  Finset.sum_induction _ Good (fun _ _ => good_add) good_zero h

end PI.UnitaryGroupMassFormula.SDiffGram

end
