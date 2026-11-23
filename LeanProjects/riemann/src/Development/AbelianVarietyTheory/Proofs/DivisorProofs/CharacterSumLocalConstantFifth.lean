import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantFourth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantSecondStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntAtNatCast
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SumModGPeriodValues

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ColNorms.Unfold

open GlobalTheory.TopStep GlobalTheory.LastSteps GlobalTheory.PadicUnfold GlobalTheory.PadicUnfold.Period

section Count

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)}

theorem dvd_of_intAt_div (hq : (Formalism.L2.Col.qOf P).Prime) (d : ℕ) :
    ∀ i : ℕ, IntAt P ((i : E) / (Formalism.L2.Col.qOf P : E) ^ d) → Formalism.L2.Col.qOf P ^ d ∣ i := by
  have hq0 : (Formalism.L2.Col.qOf P : E) ≠ 0 := qOf_ne_zero
  induction d with
  | zero => intro i _; simp
  | succ d ih =>
    intro i hi
    have h1 : IntAt P ((i : E) / (Formalism.L2.Col.qOf P : E)) := by
      convert (intAt_pow (intAt_nat (P := P) (Formalism.L2.Col.qOf P)) d).mul hi using 1
      field_simp
      ring
    have h2 := redP_eq_zero_of_div h1
    have h3 := reduction_coe P ((i : ℕ) : 𝓞 E)
    rw [map_natCast, h2] at h3
    have h4 : ((i : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.Quotient.eq_zero_iff_mem.1 h3.symm
    have h5 : Formalism.L2.Col.qOf P ∣ i := by
      by_contra hn
      obtain ⟨a, b, hab⟩ : IsCoprime ((Formalism.L2.Col.qOf P : ℕ) : 𝓞 E) ((i : ℕ) : 𝓞 E) :=
        Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd hq).2 hn)
      exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
        (hab ▸ add_mem (Ideal.mul_mem_left _ _ qOf_mem) (Ideal.mul_mem_left _ _ h4)))
    obtain ⟨j, rfl⟩ := h5
    rw [pow_succ']
    refine Nat.mul_dvd_mul_left _ (ih j ?_)
    convert hi using 1
    push_cast
    field_simp
    ring

open Classical in

theorem card_vals_le (hq : (Formalism.L2.Col.qOf P).Prime) (A B c : ℕ) :
    ((LocE.valsQ E (Formalism.L2.Col.qOf P) A B).filter fun a => IntAt P ((Formalism.L2.Col.qOf P : E) ^ c * a)).card ≤
      Formalism.L2.Col.qOf P ^ (B + c) := by
  have hq0 : (Formalism.L2.Col.qOf P : E) ≠ 0 := qOf_ne_zero
  rcases le_total A c with h | h
  · refine (Finset.card_filter_le _ _).trans (Finset.card_image_le.trans ?_)
    rw [Finset.card_range]
    exact Nat.pow_le_pow_right hq.pos (by omega)
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    refine le_trans (Finset.card_le_card (t := (Finset.range (Formalism.L2.Col.qOf P ^ (B + c))).image
      fun j : ℕ => (j : E) / (Formalism.L2.Col.qOf P : E) ^ c) fun a ha => ?_) (Finset.card_image_le.trans (by rw [Finset.card_range]))
    obtain ⟨ha, hi⟩ := Finset.mem_filter.1 ha
    obtain ⟨i, hr, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨j, rfl⟩ := dvd_of_intAt_div hq d i (by
      convert hi using 1
      rw [pow_add]
      field_simp)
    refine Finset.mem_image.2 ⟨j, Finset.mem_range.2 ?_, ?_⟩
    · have := Finset.mem_range.1 hr
      rw [show c + d + B = d + (B + c) by ring, pow_add] at this
      exact lt_of_mul_lt_mul_left this (Nat.zero_le _)
    · push_cast
      rw [pow_add]
      field_simp

end Count

section Unfolding

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

omit [StarRing E] in
theorem intAt_zpow_mono {a : E} {u v : ℤ} (h : u ≤ v) (ha : IntAt P (a * (Formalism.L2.Col.qOf P : E) ^ u)) :
    IntAt P (a * (Formalism.L2.Col.qOf P : E) ^ v) := by
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, v = u + d := ⟨(v - u).toNat, by omega⟩
  rw [zpow_add₀ qOf_ne_zero, zpow_natCast, ← mul_assoc]
  exact ha.mul (intAt_pow (intAt_nat _) _)

theorem unfolding_smallHomFunction_levelPrime_bounded (hq : (Formalism.L2.Col.qOf P).Prime) {n' c' n c : ℕ} (hc : c' = c + 1) (A B : ℕ) (psi : E → K)
    (hpsi : ∀ a, IntAt P ((Formalism.L2.Col.qOf P : E) * a) → psi a ^ Formalism.L2.Col.qOf P = 1)
    (Φ : Loc.SF E K (n' + c') (n + c))
    (hΦ : LocSmall (Formalism.L2.Col.qOf P) (LocE.lamY P (Formalism.L2.Col.qOf P) n' c' fun i => i + 1)
      (LocE.lamY P (Formalism.L2.Col.qOf P) n c fun i => i + 1) Φ 1) :
    LocSmall (Formalism.L2.Col.qOf P) (stdAt E n' P) (stdAt E n P)
      (Loc.E1 psi (LocE.valsQ E (Formalism.L2.Col.qOf P) A B) (((Formalism.L2.Col.qOf P : K) ^ B)⁻¹) Φ)
      ((Formalism.L2.Col.qOf P : ℝ) ^ (c' * ((n + c) * (n' + c')))) := by
  classical
  subst hc
  have hent : ∀ y, Φ y ≠ 0 → ∀ (l : Fin (n + c)) (l' : Fin (n' + (c + 1))), IntAt P (y (Pi.single l' 1) l *
      (Formalism.L2.Col.qOf P : E) ^ (LocE.scE n' (fun i => i + 1) l'.1 - LocE.scE n (fun i => i + 1) l.1)) :=
    fun y hy => mem_homS_sclLat.1 (hΦ.1 y hy)
  refine ⟨fun x hx y hy => ?_, fun x z hz => ?_, fun σ x => ?_⟩
  · obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul hx)
    refine mem_stdAt.2 fun l => ?_
    rw [apply_eq_sum]
    refine intAt_sum _ fun j _ => (mem_stdAt.1 hy j).mul ?_
    have h := hent _ (left_ne_zero_of_mul ht) (Fin.castAdd c l) (Fin.castAdd (c + 1) j)
    have hj := j.2
    rw [linearMap_unfolding_apply_single, dif_neg (by unfold Loc.IsFree; simp only [Fin.val_castAdd]; omega), dif_pos (by simp),
      dif_pos (by simp)] at h
    simpa [LocE.scE] using h
  · unfold Loc.E1
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [periodXX1_add_smul, chArg_add, chArg_smul_extZero, add_zero, hΦ.2.1]
    refine mem_homS_sclLat.2 fun l l' => ?_
    rw [extZero_single]
    split_ifs with hs hl
    · simpa [LocE.scE, hs, hl] using mem_stdAt.1 (hz _ (single_mem_stdAt ⟨l'.1, hs⟩)) ⟨l.1, hl⟩
    · simpa using intAt_zero
    · simpa using intAt_zero
  · set q := Formalism.L2.Col.qOf P with hqdef
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.one_le
    set F := Fintype.card (Loc.FC n' (c + 1) n c) with hF
    have hFle : F ≤ (n + c) * (n' + (c + 1)) := by
      refine (Fintype.card_subtype_le _).trans ?_
      simp
    set V := (LocE.valsQ E q A B).filter fun a => IntAt P ((q : E) ^ (c + 1) * a) with hV
    have hsum : ∑ t ∈ Fintype.piFinset fun _ : Loc.FC n' (c + 1) n c => LocE.valsQ E q A B,
        Φ (Loc.xx1 x t) * psi (-Loc.chArg (Loc.xx1 x t)) = ∑ t ∈ Fintype.piFinset fun _ : Loc.FC n' (c + 1) n c => V,
        Φ (Loc.xx1 x t) * psi (-Loc.chArg (Loc.xx1 x t)) := by
      symm
      refine Finset.sum_subset (Fintype.piFinset_subset _ _ fun _ => Finset.filter_subset _ _) fun t ht hn => ?_
      by_contra h0
      refine hn (Fintype.mem_piFinset.2 fun p => Finset.mem_filter.2 ⟨Fintype.mem_piFinset.1 ht p, ?_⟩)
      have h := hent _ (left_ne_zero_of_mul h0) p.1.1 p.1.2
      rw [linearMap_unfolding_apply_single, dif_pos p.2] at h
      have h' := intAt_zpow_mono (v := ((c + 1 : ℕ) : ℤ)) (by
        have := p.1.2.2
        unfold LocE.scE
        split_ifs <;> push_cast <;> omega) h
      rwa [zpow_natCast, mul_comm] at h'
    have hterm : ∀ y, ‖σ (Φ y * psi (-Loc.chArg y))‖ ≤ 1 := by
      intro y
      by_cases h0 : Φ y = 0
      · simp [h0]
      have h1 : IntAt P ((q : E) * -Loc.chArg y) := by
        rw [mul_neg, chArg_eq, Finset.mul_sum]
        refine intAt_neg (intAt_sum _ fun i _ => ?_)
        have h := hent y h0 ⟨n + i.1, by omega⟩ ⟨n' + i.1 + 1, by omega⟩
        have h' := intAt_zpow_mono (v := 1) (by
          unfold LocE.scE
          dsimp only
          rw [if_neg (by omega), if_neg (by omega)]
          omega) h
        rwa [zpow_one, mul_comm] at h'
      have h2 : ‖σ (psi (-Loc.chArg y))‖ ^ q = 1 := by rw [← norm_pow, ← map_pow, hpsi _ h1, map_one, norm_one]
      rw [map_mul, norm_mul, (pow_eq_one_iff_of_nonneg (norm_nonneg _) hq.ne_zero).1 h2, mul_one]
      exact hΦ.2.2 σ y
    unfold Loc.E1
    rw [hsum, map_mul, norm_mul, map_pow, map_inv₀, map_pow, map_natCast, norm_pow, norm_inv, norm_pow, Complex.norm_natCast,
      map_sum]
    have hb : ‖∑ t ∈ Fintype.piFinset fun _ : Loc.FC n' (c + 1) n c => V,
        σ (Φ (Loc.xx1 x t) * psi (-Loc.chArg (Loc.xx1 x t)))‖ ≤ ((q : ℝ) ^ (B + (c + 1))) ^ F := by
      refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ 1 fun t _ => hterm _).trans ?_)
      rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, nsmul_eq_mul, mul_one, Nat.cast_pow]
      refine pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ _
      have hc : V.card ≤ q ^ (B + (c + 1)) := card_vals_le hq A B (c + 1)
      exact_mod_cast hc
    refine (mul_le_mul_of_nonneg_left hb (by positivity)).trans ?_
    rw [← mul_pow, pow_add, inv_mul_cancel_left₀ (by positivity), ← pow_mul]
    exact pow_le_pow_right₀ hq1 (Nat.mul_le_mul_left _ hFle)

end Unfolding

section Index

theorem relIndex_le_card {G T : Type} [Group G] [Finite T] (H M : Subgroup G) (f : G → T)
    (hf : ∀ a ∈ M, ∀ b ∈ M, f a = f b → a⁻¹ * b ∈ H) : H.relIndex M ≤ Nat.card T := by
  refine Nat.card_le_card_of_injective (fun z : M ⧸ H.subgroupOf M => f z.out.1) fun z w h => ?_
  rw [← z.out_eq, ← w.out_eq]
  exact QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 (hf _ z.out.2 _ w.out.2 h))

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem relIndex_le (hq : ((Formalism.L2.Col.qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (k₀ rS r t n c : ℕ)
    (h : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) (hh : h ∈ stabL E _ (LocE.lamY P (Formalism.L2.Col.qOf P) n c fun i => i + 1)) :
    (Loc.Cbe (LocE.JGsym P (Formalism.L2.Col.qOf P) k₀ rS r t n c) h ⊓ Loc.N1 E n c).relIndex
      (Loc.N1 E n c ⊓ stabL E _ (LocE.lamY P (Formalism.L2.Col.qOf P) n c fun i => i + 1)) ≤
        Formalism.L2.Col.qOf P ^ ((n + c) * (n + c)) := by
  have hfin : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  have hq0 : (Formalism.L2.Col.qOf P : E) ≠ 0 := qOf_ne_zero
  refine (relIndex_le_card _ _ (fun (g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) (p : Fin (n + c) × Fin (n + c)) =>
    redP P (g (Pi.single p.2 1) p.1 * (Formalism.L2.Col.qOf P : E) ^
      (LocE.scE n (fun i => i + 1) p.2.1 - LocE.scE n (fun i => i + 1) p.1.1))) fun a ha b hb hab => ?_).trans (le_of_eq ?_)
  · have hm := mul_mem (inv_mem ha) hb
    refine ⟨⟨hm.1.1, ?_⟩, hm.1⟩
    have hd : ((Formalism.L2.Col.qOf P : E)⁻¹ • (b.toLinearMap - a.toLinearMap)) ∈
        homS (LocE.lamY P (Formalism.L2.Col.qOf P) n c fun i => i + 1) (LocE.lamY P (Formalism.L2.Col.qOf P) n c fun i => i + 1) := by
      refine mem_homS_sclLat.2 fun l l' => ?_
      have h1 := mem_homS_sclLat.1 (show a.toLinearMap ∈ homS _ _ from fun y hy => (ha.2 y).2 hy) l l'
      have h2 := mem_homS_sclLat.1 (show b.toLinearMap ∈ homS _ _ from fun y hy => (hb.2 y).2 hy) l l'
      have h3 := intAt_div_of_redP hq (intAt_sub h2 h1) (by
        rw [reduction_sub h2 h1, sub_eq_zero]
        exact (congrFun hab (l, l')).symm)
      convert h3 using 1
      simp only [LinearMap.smul_apply, LinearMap.sub_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring
    have hc0 : ∀ x ∈ LocE.lamY P (Formalism.L2.Col.qOf P) n c fun i => i + 1, (Formalism.L2.Col.qOf P : E)⁻¹ • ((a⁻¹ * b) x - x) ∈
        LocE.lamY P (Formalism.L2.Col.qOf P) n c fun i => i + 1 := by
      intro x hx
      refine (ha.2 _).1 ?_
      rw [map_smul, map_sub, show a ((a⁻¹ * b) x) = b x from LinearEquiv.apply_symm_apply _ _]
      exact hd x hx
    have e : (MulAut.conj h⁻¹).toMonoidHom (a⁻¹ * b) = h⁻¹ * (a⁻¹ * b) * h := by simp
    show (MulAut.conj h⁻¹).toMonoidHom (a⁻¹ * b) ∈ LocE.JGsym P (Formalism.L2.Col.qOf P) k₀ rS r t n c
    rw [e]
    have hs := mul_mem (mul_mem (inv_mem hh) hm.2) hh
    have hc := GlobalTheory.CongLevel.conj_cong (Formalism.L2.Col.qOf P) _ _ h hh hc0
    refine ⟨hs, GlobalTheory.CongLevel.mem_flagU (Formalism.L2.Col.qOf P) _ _ _ _ _ (fun s => ?_) (fun s x hx => ?_) (fun s => ?_) _ hs hc⟩
    · exact GlobalTheory.CongLevel.sclLat_le P _ hq0 _ _ _
    · exact GlobalTheory.CongLevel.smul_mem_sclLat P _ hq0 _ _ _ x hx
    · exact GlobalTheory.CongLevel.bvec_mem P _ hq0 _ _ _
  · rw [Nat.card_fun, Nat.card_prod, Nat.card_eq_fintype_card (α := Fin (n + c)), Fintype.card_fin]
    rfl

theorem norm_volN_inv_le {k K : Type} [CommRing k] [Field K] {n c : ℕ}
    (C M : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k))) (σ : K →+* ℂ) :
    ‖σ (Loc.volN K C M)⁻¹‖ ≤ ((C ⊓ Loc.N1 k n c).relIndex M : ℕ) := by
  unfold Loc.volN
  rw [inv_div, map_div₀, map_natCast, map_natCast, norm_div, Complex.norm_natCast, Complex.norm_natCast]
  rcases Nat.eq_zero_or_pos (M.relIndex (C ⊓ Loc.N1 k n c)) with h | h
  · simp [h]
  · exact div_le_self (Nat.cast_nonneg _) (by exact_mod_cast h)

end Index

theorem rank_le (R : Ranks) {j : ℕ} (hj : j ≤ R.m) : R.N j + cOf R j ≤ R.N R.m := by
  unfold Ranks.N cOf
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hj
  have : d ≤ d * (R.t + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have h2 : R.m * (R.t + 1) = j * (R.t + 1) + d * (R.t + 1) := by rw [hd, add_mul]
  omega

end GlobalTheory.ColNorms.Unfold
