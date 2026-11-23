import Formalism.LocalToGlobal.CharacterGerms.FirstVanishingCore
import Formalism.LocalToGlobal.CharacterGerms.PderivDoubleMultiplicationJacobian

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace ZeroAxisEmbedding

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ PartialDerivEval MaximalIdealCongruence

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

def io0 (μ : Fin 1 × Fin dd →₀ ℕ) : Fin 2 × Fin dd →₀ ℕ := μ.mapDomain (fun q => ((0 : Fin 2), q.2))

theorem zero_axis_embedding_injective : Function.Injective (fun q : Fin 1 × Fin dd => ((0 : Fin 2), q.2)) := by
  intro a b h
  exact Prod.ext (Subsingleton.elim _ _) (Prod.ext_iff.1 h).2

theorem prod_E (d : Fin 2 × Fin dd →₀ ℕ) :
    (d.prod fun p m => ((![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) p.1 p.2) ^ m) =
      if ∀ i, d ((1 : Fin 2), i) = 0 then
        MvPowerSeries.monomial (d.comapDomain (fun q : Fin 1 × Fin dd => ((0 : Fin 2), q.2)) zero_axis_embedding_injective.injOn) 1
      else 0 := by
  split_ifs with h
  · have hsupp : ∀ p ∈ d.support, p.1 = 0 := by
      intro p hp
      by_contra h1
      have : p.1 = 1 := by
        have := p.1.isLt
        omega
      have h2 := h p.2
      rw [show ((1 : Fin 2), p.2) = p from Prod.ext this.symm rfl] at h2
      exact (Finsupp.mem_support_iff.1 hp) h2
    have hd : d = io0 (d.comapDomain (fun q : Fin 1 × Fin dd => ((0 : Fin 2), q.2)) zero_axis_embedding_injective.injOn) := by
      unfold io0
      rw [Finsupp.mapDomain_comapDomain _ zero_axis_embedding_injective]
      intro p hp
      refine ⟨((0 : Fin 1), p.2), ?_⟩
      exact Prod.ext (hsupp p (by simpa using hp)).symm rfl
    conv_lhs => rw [hd]
    unfold io0
    rw [Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
    have hf : ∀ a : Fin 1 × Fin dd, ((![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) ((0 : Fin 2), a.2).1 ((0 : Fin 2), a.2).2) =
        (MvPowerSeries.X a : PS C 1 dd) := fun a => by
      obtain ⟨k, j⟩ := a
      fin_cases k
      rfl
    rw [Finsupp.prod_congr (g2 := fun (a : Fin 1 × Fin dd) (m : ℕ) => (MvPowerSeries.X a : PS C 1 dd) ^ m)
      (fun a _ => congrArg (fun t => t ^ _) (hf a))]
    have h3 := prod_X_rename (C := C) (fun q : Fin 1 × Fin dd => q)
      ((d.comapDomain (fun q : Fin 1 × Fin dd => ((0 : Fin 2), q.2)) zero_axis_embedding_injective.injOn))
    rw [h3]
    exact congrArg (fun e => (MvPowerSeries.monomial e (1 : C) : PS C 1 dd)) (Finsupp.mapDomain_id (M := ℕ))
  · push Not at h
    obtain ⟨i, hi⟩ := h
    apply Finset.prod_eq_zero (i := ((1 : Fin 2), i)) (Finsupp.mem_support_iff.2 hi)
    show ((0 : Pt C 1 dd) i) ^ d ((1 : Fin 2), i) = 0
    rw [Pi.zero_apply, zero_pow hi]

theorem coeff_E (G : PS C 2 dd) (μ : Fin 1 × Fin dd →₀ ℕ) :
    MvPowerSeries.coeff μ (ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) G) = MvPowerSeries.coeff (io0 μ) G := by
  unfold ev
  rw [MvPowerSeries.coeff_subst (hasSubst_ev ZeroPointGroupLaw.constant_zero_first_then_zero), finsum_eq_single _ (io0 μ)]
  · rw [prod_E, if_pos]
    · rw [show (io0 μ).comapDomain (fun q : Fin 1 × Fin dd => ((0 : Fin 2), q.2)) zero_axis_embedding_injective.injOn = μ from
        Finsupp.comapDomain_mapDomain _ zero_axis_embedding_injective μ, MvPowerSeries.coeff_monomial, if_pos rfl, smul_eq_mul, mul_one]
    · intro i
      unfold io0
      rw [Finsupp.mapDomain_of_notMem_range]
      rintro ⟨q, hq⟩
      have := (Prod.ext_iff.1 hq).1
      simp at this
  · intro d hd
    rw [prod_E]
    split_ifs with h
    · rw [MvPowerSeries.coeff_monomial, if_neg, smul_zero]
      intro he
      apply hd
      have hsupp : ∀ p ∈ d.support, p.1 = 0 := by
        intro p hp
        by_contra h1
        have : p.1 = 1 := by
          have := p.1.isLt
          omega
        have h2 := h p.2
        rw [show ((1 : Fin 2), p.2) = p from Prod.ext this.symm rfl] at h2
        exact (Finsupp.mem_support_iff.1 hp) h2
      unfold io0
      rw [he, Finsupp.mapDomain_comapDomain _ zero_axis_embedding_injective]
      intro p hp
      refine ⟨((0 : Fin 1), p.2), ?_⟩
      exact Prod.ext (hsupp p (by simpa using hp)).symm rfl
    · rw [MvPowerSeries.coeff_zero, smul_zero]

def Sv (Y : FBChart C V O dd) (v : Fin dd → C) : PS C 1 dd :=
  fun μ => ∑ j, v j * MvPowerSeries.coeff (io0 μ + Finsupp.single ((1 : Fin 2), j) 1) Y.u1

theorem zero_axis_embedding_second (μ : Fin 1 × Fin dd →₀ ℕ) (j : Fin dd) : io0 μ ((1 : Fin 2), j) = 0 := by
  unfold io0
  rw [Finsupp.mapDomain_of_notMem_range]
  rintro ⟨q, hq⟩
  have := (Prod.ext_iff.1 hq).1
  simp at this

theorem Sv_eq_sum (Y : FBChart C V O dd) (v : Fin dd → C) :
    Sv Y v = ∑ j, MvPowerSeries.C (v j) *
      ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) (MvPowerSeries.pderiv C ((1 : Fin 2), j) Y.u1) := by
  ext μ
  rw [map_sum]
  show ∑ j, v j * MvPowerSeries.coeff (io0 μ + Finsupp.single ((1 : Fin 2), j) 1) Y.u1 = _
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MvPowerSeries.coeff_C_mul, coeff_E, MvPowerSeries.coeff_pderiv, zero_axis_embedding_second, Nat.cast_zero, zero_add, mul_one]

abbrev M2 (Y : FBChart C V O dd) : Pt C 2 dd := comp1 (mulL Y.B.G.F V.l) (pt C (n := 2) dd 0)

theorem constant_zero_multiplication_pair (Y : FBChart C V O dd) : Z0 (![M2 Y, pt C dd 1] : Fin 2 → Pt C 2 dd) := fun k j => by
  fin_cases k
  · exact FirstUnitSeriesIntegrality.double_multiplication_constantCoeff Y.B.G V.l j
  · exact z0_pt 1 j

theorem pderiv_second_multiplication_pair (Y : FBChart C V O dd) (k j : Fin dd) : MvPowerSeries.pderiv C ((1 : Fin 2), j) (M2 Y k) = 0 := by
  show MvPowerSeries.pderiv C ((1 : Fin 2), j) (ev (n := 2) ![pt C dd 0] (mulL Y.B.G.F V.l k)) = 0
  rw [ZeroPointGroupLaw.pderiv_eval_single (pt C dd 0) (z0_pt 0)]
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [show MvPowerSeries.pderiv C ((1 : Fin 2), j) (pt C (n := 2) dd 0 r) = 0 from
    MvPowerSeries.pderiv_X_of_ne (fun h' => by simp at h'), mul_zero]

theorem eval_multiplication_pair_zero (Y : FBChart C V O dd) (g : PS C 2 dd) :
    ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) (ev (n := 2) ![M2 Y, pt C dd 1] g) =
      ev (n := 1) ![mulL Y.B.G.F V.l, 0] g := by
  rw [ev_ev (constant_zero_multiplication_pair Y) ZeroPointGroupLaw.constant_zero_first_then_zero]
  congr 1
  funext k i
  fin_cases k
  · show ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) (ev (n := 2) ![pt C dd 0] (mulL Y.B.G.F V.l i)) =
      mulL Y.B.G.F V.l i
    rw [ev_ev (z0_1 _ (z0_pt 0)) ZeroPointGroupLaw.constant_zero_first_then_zero]
    have e : (fun k' i' => ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd)
        ((![pt C (n := 2) dd 0] : Fin 1 → Pt C 2 dd) k' i')) = ![pt C dd 0] := by
      funext k' i'
      fin_cases k'
      exact ev_X ZeroPointGroupLaw.constant_zero_first_then_zero 0 i'
    rw [e, ZeroPointGroupLaw.eval_identity_point]
  · exact ev_X ZeroPointGroupLaw.constant_zero_first_then_zero 1 i

theorem eval_point_zero_factor (M : Pt C 1 dd) (hM : ∀ j, MvPowerSeries.constantCoeff (M j) = 0) (g : PS C 2 dd) :
    ev (n := 1) ![M, 0] g = ev (n := 1) ![M] (ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) g) := by
  rw [ev_ev ZeroPointGroupLaw.constant_zero_first_then_zero (z0_1 M hM)]
  congr 1
  funext k i
  fin_cases k
  · exact (ev_X (z0_1 M hM) 0 i).symm
  · exact (ev_zero (z0_1 M hM)).symm

theorem eval_pderiv_first_unit_series (Y : FBChart C V O dd) (j : Fin dd) :
    ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) (MvPowerSeries.pderiv C ((1 : Fin 2), j) Y.u1) =
      ev (n := 1) ![mulL Y.B.G.F V.l, 0] (MvPowerSeries.pderiv C ((1 : Fin 2), j) Y.h) -
        (V.l : C) • ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) (MvPowerSeries.pderiv C ((1 : Fin 2), j) Y.h) := by
  have hZ2 := constant_zero_multiplication_pair Y
  have hH0 : MvPowerSeries.constantCoeff (ev (n := 2) ![M2 Y, pt C dd 1] Y.h - (V.l : C) • Y.h) = 0 := by
    rw [map_sub, const_ev hZ2 (h_const Y), MvPowerSeries.smul_eq_C_mul, map_mul, h_const Y, mul_zero, sub_zero]
  have hu : Y.u1 = FB.expS C (ev (n := 2) ![M2 Y, pt C dd 1] Y.h - (V.l : C) • Y.h) := rfl
  have hEh : ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) Y.h = 0 := Y.gauge.ax1
  have hEH : ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) (ev (n := 2) ![M2 Y, pt C dd 1] Y.h - (V.l : C) • Y.h) = 0 := by
    rw [ev_sub ZeroPointGroupLaw.constant_zero_first_then_zero, eval_multiplication_pair_zero, eval_point_zero_factor _ (FirstUnitSeriesIntegrality.multiplication_constantCoeff_zero Y.B.G V.l), hEh, ev_zero (z0_1 _ (FirstUnitSeriesIntegrality.multiplication_constantCoeff_zero Y.B.G V.l)),
      MvPowerSeries.smul_eq_C_mul, ev_mul ZeroPointGroupLaw.constant_zero_first_then_zero, ev_C, hEh, mul_zero, sub_zero]
  have hD : MvPowerSeries.pderiv C ((1 : Fin 2), j) (ev (n := 2) ![M2 Y, pt C dd 1] Y.h) =
      ev (n := 2) ![M2 Y, pt C dd 1] (MvPowerSeries.pderiv C ((1 : Fin 2), j) Y.h) := by
    rw [pderiv_eval_pair hZ2]
    have e0 : ∀ k, MvPowerSeries.pderiv C ((1 : Fin 2), j) ((![M2 Y, pt C dd 1] : Fin 2 → Pt C 2 dd) 0 k) = 0 :=
      fun k => pderiv_second_multiplication_pair Y k j
    have e1 : ∀ k, MvPowerSeries.pderiv C ((1 : Fin 2), j) ((![M2 Y, pt C dd 1] : Fin 2 → Pt C 2 dd) 1 k) =
        if k = j then 1 else 0 := fun k => by
      show MvPowerSeries.pderiv C ((1 : Fin 2), j) (MvPowerSeries.X ((1 : Fin 2), k)) = _
      split_ifs with hk
      · subst hk
        exact MvPowerSeries.pderiv_X_self
      · exact MvPowerSeries.pderiv_X_of_ne (fun h' => hk (Prod.ext_iff.1 h').2)
    simp only [e0, e1, mul_zero, Finset.sum_const_zero, zero_add, mul_ite, mul_one, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  rw [hu, pderiv_expS hH0, ev_mul ZeroPointGroupLaw.constant_zero_first_then_zero, FirstUnitSeriesIntegrality.expS_eq, FirstUnitSeriesIntegrality.ev_ex ZeroPointGroupLaw.constant_zero_first_then_zero _ hH0, hEH, FirstUnitSeriesIntegrality.ex_zero,
    one_mul, map_sub, hD, Derivation.map_smul, ev_sub ZeroPointGroupLaw.constant_zero_first_then_zero, eval_multiplication_pair_zero, MvPowerSeries.smul_eq_C_mul, ev_mul ZeroPointGroupLaw.constant_zero_first_then_zero, ev_C,
    ← MvPowerSeries.smul_eq_C_mul]

theorem Sv_eq (Y : FBChart C V O dd) (v : Fin dd → C) :
    Sv Y v = (V.l : C) • Y.sgP v - ev (n := 1) ![mulL Y.B.G.F V.l] (Y.sgP v) := by
  have h1 := ev_sgP Y v (mulL Y.B.G.F V.l) (FirstUnitSeriesIntegrality.multiplication_constantCoeff_zero Y.B.G V.l)
  have h2 := ev_sgP Y v (n := 1) (pt C dd 0) (z0_pt 0)
  rw [ZeroPointGroupLaw.eval_identity_point] at h2
  rw [Sv_eq_sum, h1, h2]
  simp only [eval_pderiv_first_unit_series, mul_sub, Finset.sum_sub_distrib, MvPowerSeries.smul_eq_C_mul]
  ring_nf
  rw [Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun x _ => by ring

theorem coeff_l_frob0 (P : PS C 1 dd) (hP : IntS V P) (hPz : MvPowerSeries.constantCoeff P = 0)
    (hfrob : ∀ μ : Fin 1 × Fin dd →₀ ℕ, (∃ i, ¬ V.l ∣ μ ((0 : Fin 1), i)) → V.MM (MvPowerSeries.coeff μ P))
    {γ : Fin dd → PowerSeries C} (hγ : IsCv V γ) :
    V.MM (PowerSeries.coeff V.l (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) P) -
      ∑ i, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) V.l) P * (PowerSeries.coeff 1 (γ i)) ^ V.l) := by
  have hl := V.l_prime.two_le
  have hγ0 : ∀ j, PowerSeries.constantCoeff (γ j) = 0 := fun j => (hγ j).1
  have hγI : ∀ j, IntS V (γ j) := fun j => FirstVanishing.intS_cv (hγ j).2
  have hG : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => γ q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hγ0 q.2
  have hγ0' : ∀ j, MvPowerSeries.constantCoeff (γ j) = 0 := hγ0
  obtain ⟨D1, hD1def⟩ : ∃ D1 : PS C 1 dd, ∀ μ, MvPowerSeries.coeff μ D1 =
      if (∃ i, ¬ V.l ∣ μ ((0 : Fin 1), i)) then MvPowerSeries.coeff μ P else 0 :=
    ⟨fun μ => if (∃ i, ¬ V.l ∣ μ ((0 : Fin 1), i)) then MvPowerSeries.coeff μ P else 0, fun μ => rfl⟩
  obtain ⟨D3, hD3def⟩ : ∃ D3 : PS C 1 dd, D3 = ∑ i, MvPowerSeries.monomial (Finsupp.single ((0 : Fin 1), i) V.l)
      (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) V.l) P) := ⟨_, rfl⟩
  have hD1 : MMS V D1 := fun μ => by
    rw [hD1def]
    split_ifs with h
    · exact hfrob μ h
    · exact mm_zero
  have hsq : ∀ (s : Fin 1 × Fin dd), s = ((0 : Fin 1), s.2) := fun s => Prod.ext (Subsingleton.elim _ _) rfl
  have hD2 : Agr (2 * V.l) (P - D1 - D3) 0 := by
    intro μ hμ
    rw [map_sub, map_sub, map_zero, hD1def, hD3def, map_sum]
    simp only [MvPowerSeries.coeff_monomial]
    by_cases hex : ∃ i, ¬ V.l ∣ μ ((0 : Fin 1), i)
    · rw [if_pos hex, sub_self, zero_sub, neg_eq_zero]
      refine Finset.sum_eq_zero fun i _ => if_neg ?_
      rintro rfl
      obtain ⟨i', hi'⟩ := hex
      apply hi'
      rw [Finsupp.single_apply]
      split_ifs
      · exact dvd_refl _
      · exact dvd_zero _
    · rw [if_neg hex, sub_zero]
      push Not at hex
      have hdiv : ∀ s, V.l ∣ μ s := fun s => by rw [hsq s]; exact hex s.2
      rcases FirstVanishing.divisible_small μ hdiv hμ with h0 | ⟨s, hs⟩
      · subst h0
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hPz, zero_sub, neg_eq_zero]
        refine Finset.sum_eq_zero fun i _ => if_neg ?_
        intro h
        have := congrArg (fun f : Fin 1 × Fin dd →₀ ℕ => f ((0 : Fin 1), i)) h
        simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.single_eq_same] at this
        omega
      · subst hs
        rw [Finset.sum_eq_single s.2, if_pos (by rw [← hsq s]), ← hsq s, sub_self]
        · intro i _ hi
          rw [if_neg]
          intro h
          apply hi
          have := (Finsupp.single_left_inj (by omega : V.l ≠ 0)).1 h
          rw [this]
        · intro h
          exact absurd (Finset.mem_univ _) h
  have hz : MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (0 : PS C 1 dd) = 0 := by
    rw [← MvPowerSeries.coe_substAlgHom hG, map_zero]
  have hsplit : P = D1 + (P - D1 - D3) + D3 := by ring
  have hdeg : (Finsupp.single () V.l).degree < 2 * V.l := by
    rw [Finsupp.degree_single]
    omega
  have hA2 := (agr_subst_right (a := fun q : Fin 1 × Fin dd => γ q.2) (fun q => hγ0' q.2) hD2)
    (Finsupp.single () V.l) hdeg
  rw [hz, map_zero] at hA2
  have hA2' : PowerSeries.coeff V.l (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (P - D1 - D3)) = 0 :=
    hA2
  have hB1' : MMS V (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) D1) :=
    MMS.subst (a := fun q : Fin 1 × Fin dd => γ q.2) (fun q => hγ0' q.2) (fun q => hγI q.2) hD1
  have hB1 : V.MM (PowerSeries.coeff V.l (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) D1)) :=
    hB1' (Finsupp.single () V.l)
  have hD3 : MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) D3 =
      ∑ i, MvPowerSeries.C (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) V.l) P) * γ i ^ V.l := by
    rw [hD3def, ← MvPowerSeries.coe_substAlgHom hG, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MvPowerSeries.coe_substAlgHom hG, MvPowerSeries.subst_monomial hG, Finsupp.prod_single_index (by simp)]
    rfl
  have hfr : ∀ i, V.MM (PowerSeries.coeff V.l (γ i ^ V.l) - (PowerSeries.coeff 1 (γ i)) ^ V.l) := by
    intro i
    have h := mms_pow_frobTw (hγI i) (Finsupp.single () V.l)
    rw [map_sub, coeff_frobTw, if_pos (fun s => by simp)] at h
    have e : (Finsupp.single () V.l).mapRange (fun n => n / V.l) (Nat.zero_div V.l) = Finsupp.single () 1 := by
      rw [Finsupp.mapRange_single, Nat.div_self (by omega)]
    rw [e] at h
    exact h
  have eP : MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) P =
      MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) D1 +
        MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (P - D1 - D3) +
          MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) D3 := by
    conv_lhs => rw [hsplit]
    rw [MvPowerSeries.subst_add hG, MvPowerSeries.subst_add hG]
  rw [eP, map_add, map_add, hA2', add_zero, hD3, map_sum]
  have e : ∀ (a : C) (s t : Fin dd → C),
      a + ∑ i, s i - ∑ i, t i = a + ∑ i, (s i - t i) := fun a s t => by
    rw [Finset.sum_sub_distrib]
    ring
  rw [e]
  refine mm_add hB1 (mm_sum _ _ fun i _ => ?_)
  rw [show PowerSeries.coeff V.l (MvPowerSeries.C (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) V.l) P) *
      γ i ^ V.l) = MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) V.l) P * PowerSeries.coeff V.l (γ i ^ V.l) from
    MvPowerSeries.coeff_C_mul _ _ _, ← mul_sub]
  exact mm_mul_ge' (hP _) (hfr i)

theorem coeff_l_frob (P : PS C 1 dd) (hP : IntS V P)
    (hfrob : ∀ μ : Fin 1 × Fin dd →₀ ℕ, (∃ i, ¬ V.l ∣ μ ((0 : Fin 1), i)) → V.MM (MvPowerSeries.coeff μ P))
    {γ : Fin dd → PowerSeries C} (hγ : IsCv V γ) :
    V.MM (PowerSeries.coeff V.l (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) P) -
      ∑ i, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) V.l) P * (PowerSeries.coeff 1 (γ i)) ^ V.l) := by
  have hl := V.l_prime.two_le
  have hγ0 : ∀ j, PowerSeries.constantCoeff (γ j) = 0 := fun j => (hγ j).1
  have hG : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => γ q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hγ0 q.2
  set c := MvPowerSeries.constantCoeff P with hc
  have hP' : IntS V (P - MvPowerSeries.C c) := ZeroPointGroupLaw.intS_sub' hP (fun μ => by
    rw [MvPowerSeries.coeff_C]
    split_ifs
    · rw [hc, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact hP 0
    · exact VF.Ge.zero 0)
  have hPz' : MvPowerSeries.constantCoeff (P - MvPowerSeries.C c) = 0 := by
    rw [map_sub, MvPowerSeries.constantCoeff_C, hc, sub_self]
  have hne : ∀ μ : Fin 1 × Fin dd →₀ ℕ, (∃ i, ¬ V.l ∣ μ ((0 : Fin 1), i)) → μ ≠ 0 := by
    rintro μ ⟨i, hi⟩ rfl
    exact hi (dvd_zero _)
  have hfrob' : ∀ μ : Fin 1 × Fin dd →₀ ℕ, (∃ i, ¬ V.l ∣ μ ((0 : Fin 1), i)) →
      V.MM (MvPowerSeries.coeff μ (P - MvPowerSeries.C c)) := fun μ hμ => by
    rw [map_sub, MvPowerSeries.coeff_C, if_neg (hne μ hμ), sub_zero]
    exact hfrob μ hμ
  have h := coeff_l_frob0 _ hP' hPz' hfrob' hγ
  have hs : ∀ i, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) V.l) (P - MvPowerSeries.C c) =
      MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) V.l) P := fun i => by
    rw [map_sub, MvPowerSeries.coeff_C, if_neg (by simp; omega), sub_zero]
  simp only [hs] at h
  have hsub : MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (P - MvPowerSeries.C c) =
      MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) P - MvPowerSeries.C c := by
    rw [MvPowerSeries.subst_sub hG, MvPowerSeries.subst_C]
  have hC0 : PowerSeries.coeff V.l (MvPowerSeries.C c : PowerSeries C) = 0 := by
    change MvPowerSeries.coeff (Finsupp.single () V.l) (MvPowerSeries.C c) = 0
    rw [MvPowerSeries.coeff_C, if_neg (Finsupp.single_ne_zero.2 (by omega))]
  rw [hsub, map_sub, hC0, sub_zero] at h
  exact h

theorem v_one_sub {m : C} (hm : V.MM m) : V.v (1 - m) = 0 := by
  have hm0 : (0 : WithTop ℝ) < V.v m := hm
  have hge : (0 : WithTop ℝ) ≤ V.v (1 - m) := by
    have h := V.v.map_add 1 (-m)
    rw [V.v.map_one, V.v.map_neg, ← sub_eq_add_neg] at h
    exact le_trans (le_min le_rfl hm0.le) h
  apply le_antisymm _ hge
  by_contra h
  push Not at h
  have h1 := mm_add (show V.MM (1 - m) from h) hm
  rw [sub_add_cancel] at h1
  have h2 : (0 : WithTop ℝ) < V.v (1 : C) := h1
  rw [V.v.map_one] at h2
  exact lt_irrefl _ h2

theorem curve_coefficient_linear_term (Y : FBChart C V O dd) {γ : Fin dd → PowerSeries C} (hγ : IsCv V γ) {U : Fin dd → C}
    (hL : Y.LgLin γ U) (v : Fin dd → C) (hv : ∀ i, V.Ge 0 (v i)) :
    V.MM ((V.l : C) * PowerSeries.coeff V.l (alongCv γ (un1 (Y.sgP v))) - Y.aLin U v) := by
  have hl := V.l_prime.two_le
  have hγ0 : ∀ j, PowerSeries.constantCoeff (γ j) = 0 := fun j => (hγ j).1
  have hγ0' : ∀ j, MvPowerSeries.constantCoeff (γ j) = 0 := hγ0
  have hγI : ∀ j, IntS V (γ j) := fun j => FirstVanishing.intS_cv (hγ j).2
  have hG : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => γ q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hγ0 q.2
  have hu1 := first_unit_series_integral C V O dd Y

  have hSI : IntS V (Sv Y v) := fun μ => by
    show V.Ge 0 (∑ j, v j * MvPowerSeries.coeff (io0 μ + Finsupp.single ((1 : Fin 2), j) 1) Y.u1)
    exact VF.Ge.sum fun j _ => (hv j).mul_int (hu1 _)
  have hSF : ∀ μ : Fin 1 × Fin dd →₀ ℕ, (∃ i, ¬ V.l ∣ μ ((0 : Fin 1), i)) →
      V.MM (MvPowerSeries.coeff μ (Sv Y v)) := by
    rintro μ ⟨i, hi⟩
    show V.MM (∑ j, v j * MvPowerSeries.coeff (io0 μ + Finsupp.single ((1 : Fin 2), j) 1) Y.u1)
    refine mm_sum _ _ fun j _ => mm_mul_ge' (hv j) (first_unit_series_frobenius C V O dd Y _ ⟨i, ?_⟩)
    rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (by simp), add_zero]
    unfold io0
    rw [show ((0 : Fin 2), i) = (fun q : Fin 1 × Fin dd => ((0 : Fin 2), q.2)) ((0 : Fin 1), i) from rfl,
      Finsupp.mapDomain_apply zero_axis_embedding_injective]
    exact hi

  have hA := coeff_l_frob (Sv Y v) hSI hSF hγ
  simp only [LogarithmSeriesLinearTerm.coeff1_of_lgLin Y hγ hL] at hA
  have haL : Y.aLin U v = ∑ i, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) V.l) (Sv Y v) * U i ^ V.l := by
    have e1 : ∀ j, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (Y.aOf U) =
        ∑ i, U i ^ V.l * MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), i) V.l + Finsupp.single ((1 : Fin 2), j) 1)
          Y.u1 := fun j => by
      show ∑ i, U i ^ V.l * MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), i) V.l +
        (Finsupp.single ((0 : Fin 1), j) 1).mapDomain (fun q : Fin 1 × Fin dd => ((1 : Fin 2), q.2))) Y.u1 = _
      rw [Finsupp.mapDomain_single]
    have e2 : ∀ i, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) V.l) (Sv Y v) =
        ∑ j, v j * MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), i) V.l + Finsupp.single ((1 : Fin 2), j) 1)
          Y.u1 := fun i => by
      show ∑ j, v j * MvPowerSeries.coeff (io0 (Finsupp.single ((0 : Fin 1), i) V.l) +
        Finsupp.single ((1 : Fin 2), j) 1) Y.u1 = _
      unfold io0
      rw [Finsupp.mapDomain_single]
    unfold FBChart.aLin
    simp only [e1, e2, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [← haL] at hA

  set s := PowerSeries.coeff V.l (alongCv γ (un1 (Y.sgP v))) with hs
  have hLγ0 : ∀ k, MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (mulL Y.B.G.F V.l k)) = 0 :=
    fun k => MvPowerSeries.constantCoeff_subst_eq_zero hG (fun q => hγ0 q.2) (FirstUnitSeriesIntegrality.multiplication_constantCoeff_zero Y.B.G V.l k)
  have hM : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => mulL Y.B.G.F V.l q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => FirstUnitSeriesIntegrality.multiplication_constantCoeff_zero Y.B.G V.l q.2
  have hSg : MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (Sv Y v) =
      (V.l : C) • alongCv γ (un1 (Y.sgP v)) -
        alongCv (fun k => MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (mulL Y.B.G.F V.l k))
          (un1 (Y.sgP v)) := by
    rw [Sv_eq, MvPowerSeries.subst_sub hG, MvPowerSeries.subst_smul hG, eval_single_eq_subst,
      MvPowerSeries.subst_comp_subst_apply hM hG]
    unfold alongCv
    rw [subst_singlePointUncurry hγ0, subst_singlePointUncurry hLγ0]

  have hX0 : ∀ (a : C), MvPowerSeries.constantCoeff (a • (MvPowerSeries.X () : PowerSeries C)) = 0 := by
    intro a
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.constantCoeff_X, mul_zero]
  have hcl : ∀ j, MvPowerSeries.constantCoeff (alongCv γ (un1 (Y.lg j))) = 0 := fun j =>
    MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero hγ0) hγ0 (LogarithmSeriesLinearTerm.lg0 Y j)
  have hclL : ∀ j, MvPowerSeries.constantCoeff ((V.l : C) • alongCv γ (un1 (Y.lg j))) = 0 := fun j => by
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, hcl j, mul_zero]
  have hE : MvPowerSeries.HasSubst (fun k => un1 (Y.ex k)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => by rw [constantCoeff_uncurry, Y.ex_const]
  set Φ := MvPowerSeries.subst (fun k => un1 (Y.ex k)) (un1 (Y.sgP v)) with hΦ
  have eLγ : (fun k => MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (mulL Y.B.G.F V.l k)) =
      fun k => MvPowerSeries.subst (fun j => (V.l : C) • alongCv γ (un1 (Y.lg j))) (un1 (Y.ex k)) := by
    funext k
    rw [← LogarithmSeriesLinearTerm.ex_lg_at' Y _ hLγ0 k]
    simp only [LogarithmSeriesLinearTerm.lg_mulCv' Y hγ0 V.l]
  have eγ : γ = fun k => MvPowerSeries.subst (fun j => alongCv γ (un1 (Y.lg j))) (un1 (Y.ex k)) := by
    funext k
    exact (LogarithmSeriesLinearTerm.ex_lg_at' Y γ hγ0 k).symm
  have h1 : alongCv (fun k => MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (mulL Y.B.G.F V.l k))
      (un1 (Y.sgP v)) = MvPowerSeries.subst (fun j => (V.l : C) • alongCv γ (un1 (Y.lg j))) Φ := by
    rw [eLγ, hΦ, MvPowerSeries.subst_comp_subst_apply hE (MvPowerSeries.hasSubst_of_constantCoeff_zero hclL)]
    rfl
  have h2 : alongCv γ (un1 (Y.sgP v)) = MvPowerSeries.subst (fun j => alongCv γ (un1 (Y.lg j))) Φ := by
    conv_lhs => rw [eγ]
    rw [hΦ, MvPowerSeries.subst_comp_subst_apply hE (MvPowerSeries.hasSubst_of_constantCoeff_zero hcl)]
    rfl
  have hdeg : (Finsupp.single () V.l).degree < V.l ^ 2 := by
    rw [Finsupp.degree_single]
    nlinarith
  have a1 := agr_subst_left (a := fun j => (V.l : C) • alongCv γ (un1 (Y.lg j)))
    (b := fun j => ((V.l : C) * U j) • (MvPowerSeries.X () : PowerSeries C)) hclL (fun j => hX0 _)
    (fun j => by
      have := FirstVanishing.Agr.smul (hL j) (V.l : C)
      rwa [smul_smul] at this) Φ _ hdeg
  have a2 := agr_subst_left (a := fun j => alongCv γ (un1 (Y.lg j)))
    (b := fun j => U j • (MvPowerSeries.X () : PowerSeries C)) hcl (fun j => hX0 _) (fun j => hL j) Φ _ hdeg
  change PowerSeries.coeff V.l _ = PowerSeries.coeff V.l _ at a1 a2
  have hσl : PowerSeries.coeff V.l (alongCv (fun k => MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2)
      (mulL Y.B.G.F V.l k)) (un1 (Y.sgP v))) = (V.l : C) ^ V.l * s := by
    rw [h1, a1, FirstVanishing.coeff_subst_scale, ← a2, ← h2]

  have hT : PowerSeries.coeff V.l (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (Sv Y v)) =
      (V.l : C) * s - (V.l : C) ^ V.l * s := by
    rw [hSg, map_sub, map_smul, hσl, smul_eq_mul]
  have hTI' : IntS V (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (Sv Y v)) :=
    intS_subst (a := fun q : Fin 1 × Fin dd => γ q.2) (fun q => hγ0' q.2) (fun q => hγI q.2) hSI
  have hTI : V.Ge 0 (PowerSeries.coeff V.l (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (Sv Y v))) :=
    hTI' (Finsupp.single () V.l)
  rw [hT] at hA hTI
  obtain ⟨m, hm⟩ : ∃ m, V.l = m + 2 := ⟨V.l - 2, by omega⟩
  have hmm : V.MM ((V.l : C) ^ (m + 1)) := by
    rw [pow_succ']
    exact mm_l_mul (VF.Ge.pow (ge_natCast V.l) m)
  have hv1 := v_one_sub hmm
  have hne : (1 - (V.l : C) ^ (m + 1)) ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hv1
    exact WithTop.top_ne_zero hv1
  have els : (V.l : C) * s = ((V.l : C) * s - (V.l : C) ^ V.l * s) * (1 - (V.l : C) ^ (m + 1))⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hne, hm]
    ring
  have hls : V.Ge 0 ((V.l : C) * s) := by
    rw [els]
    refine hTI.mul_int ?_
    unfold VF.Ge
    rw [AddValuation.map_inv, hv1]
    simp
  have hll : V.MM ((V.l : C) ^ V.l * s) := by
    have e5 : (V.l : C) ^ V.l = (V.l : C) ^ (m + 1) * (V.l : C) := by
      rw [← pow_succ]
      congr 1
    rw [e5, mul_assoc]
    exact mm_mul_ge hmm hls
  have e : (V.l : C) * s - Y.aLin U v = ((V.l : C) * s - (V.l : C) ^ V.l * s - Y.aLin U v) + (V.l : C) ^ V.l * s := by
    ring
  rw [e]
  exact mm_add hA hll

end ZeroAxisEmbedding

theorem curve_linear_term_unconditional : CurveLinearTermCondition := by
  intro C _ _ V O _ _ dd Y γ U hγ hL v hv
  exact ZeroAxisEmbedding.curve_coefficient_linear_term Y hγ hL v hv

end Formalism.L2.FormalSeriesBounds
