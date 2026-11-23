import Formalism.LocalToGlobal.CharacterGerms.ConstantCoeffSinglePointZero

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

section Inv

variable {C : Type} [Field C] {V : VF C} {σ : Type}

theorem inv_int {c : C} (hc : V.v c = 0) : V.Ge 0 c⁻¹ := by
  simp [VF.Ge, AddValuation.map_inv, hc]

theorem intInv {U : MvPowerSeries σ C} (hU : IntS V U) (h0 : V.v (MvPowerSeries.constantCoeff U) = 0) :
    ∃ U' : MvPowerSeries σ C, IntS V U' ∧ U' * U = 1 := by
  have hc0 : MvPowerSeries.constantCoeff U ≠ 0 := by
    intro h
    simp [h] at h0
  refine ⟨U⁻¹, ?_, MvPowerSeries.inv_mul_cancel _ hc0⟩
  have hge0 : V.Ge 0 (0 : C) := by simp [VF.Ge]
  have hmul : ∀ a b : C, V.Ge 0 a → V.Ge 0 b → V.Ge 0 (a * b) := by
    intro a b ha hb
    unfold VF.Ge at *
    rw [AddValuation.map_mul]
    simpa using add_le_add ha hb
  have hadd : ∀ a b : C, V.Ge 0 a → V.Ge 0 b → V.Ge 0 (a + b) :=
    fun a b ha hb => le_trans (le_min ha hb) (V.v.map_add a b)
  have hneg : ∀ a : C, V.Ge 0 a → V.Ge 0 (-a) := by
    intro a ha
    unfold VF.Ge at *
    rwa [AddValuation.map_neg]
  intro μ
  induction μ using WellFoundedLT.induction with
  | _ μ ih =>
    rw [MvPowerSeries.coeff_inv]
    split_ifs with hμ
    · exact inv_int h0
    · refine hmul _ _ (hneg _ (inv_int h0)) ?_
      refine Finset.sum_induction _ (V.Ge 0) hadd hge0 (fun x _ => ?_)
      split_ifs with hlt
      · exact hmul _ _ (hU x.1) (ih x.2 hlt)
      · exact hge0

theorem IntS_prod {ι : Type} (s : Finset ι) {F : ι → MvPowerSeries σ C} (h : ∀ i ∈ s, IntS V (F i)) :
    IntS V (∏ i ∈ s, F i) := by
  classical
  have hge : ∀ c : C, (c = 0 ∨ c = 1) → V.Ge 0 c := by
    rintro c (rfl | rfl)
    · simp [VF.Ge]
    · simp [VF.Ge]
  have hone : IntS V (1 : MvPowerSeries σ C) := by
    intro μ
    rw [MvPowerSeries.coeff_one]
    split_ifs
    · exact hge 1 (Or.inr rfl)
    · exact hge 0 (Or.inl rfl)
  have hmul : ∀ F G : MvPowerSeries σ C, IntS V F → IntS V G → IntS V (F * G) := by
    intro F G hF hG μ
    rw [MvPowerSeries.coeff_mul]
    refine Finset.sum_induction _ (V.Ge 0) (fun a b ha hb => ?_) (hge 0 (Or.inl rfl)) (fun q _ => ?_)
    · exact le_trans (le_min ha hb) (V.v.map_add a b)
    · have h1 := add_le_add (hF q.1) (hG q.2)
      unfold VF.Ge
      rw [AddValuation.map_mul]
      simpa using h1
  induction s using Finset.induction_on with
  | empty => simpa using hone
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact hmul _ _ (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem IntS_X (s : σ) : IntS V (MvPowerSeries.X s : MvPowerSeries σ C) := by
  intro μ
  rw [MvPowerSeries.coeff_X]
  split_ifs
  · simp [VF.Ge]
  · simp [VF.Ge]

end Inv

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

private theorem cc_ev_lemma {m n : ℕ} (a : Fin m → Pt C n dd)
    (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) (f : PS C m dd) :
    MvPowerSeries.constantCoeff (ev a f) = MvPowerSeries.constantCoeff f := by
  have hs : MvPowerSeries.HasSubst (fun p : Fin m × Fin dd => a p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => ha p.1 p.2)
  unfold ev
  rw [MvPowerSeries.constantCoeff_subst hs, finsum_eq_single _ 0]
  · simp
  · intro d hd
    obtain ⟨s, hs'⟩ : ∃ s, d s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hd (Finsupp.ext h)
    have h0 : MvPowerSeries.constantCoeff (d.prod fun s e => (a s.1 s.2) ^ e) = 0 := by
      rw [Finsupp.prod, map_prod]
      exact Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs') (by rw [map_pow, ha, zero_pow hs'])
    rw [h0, smul_zero]

theorem cc_h (Y : FBChart C V O dd) : MvPowerSeries.constantCoeff Y.h = 0 := by
  have hax := Y.gauge.ax0
  have e : MvPowerSeries.constantCoeff (ev (n := 1) ![0, pt C dd 0] Y.h) = MvPowerSeries.constantCoeff Y.h :=
    cc_ev_lemma _ (fun j i => by fin_cases j <;> simp [pt]) _
  rw [← e, hax, map_zero]

theorem cc_hL (Y : FBChart C V O dd) : MvPowerSeries.constantCoeff (Y.B.hL C Y.h Y.w0) = 0 := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.FB.hL
  rw [cc_ev_lemma _ ?_ _]
  · exact cc_h Y
  · intro j i
    fin_cases j
    · simp [pt]
    · show MvPowerSeries.constantCoeff (comp1 (Y.B.actK C Y.w0) (pt C dd 0) i) = 0
      simp only [comp1]
      rw [cc_ev_lemma _ (fun j i => by rw [Fin.fin_one_eq_zero j]; simp [pt]) _]
      simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.FB.actK, MvPowerSeries.constantCoeff_map, Y.B.A.const]

end VP

end Formalism.L2.FormalSeriesBounds
