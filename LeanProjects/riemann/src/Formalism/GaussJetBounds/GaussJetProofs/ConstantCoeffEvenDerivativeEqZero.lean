import Formalism.GaussJetBounds.GaussJetProofs.LogarithmWeightComparison

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds MvPowerSeries

theorem asmS_rho_pos {l : ℕ} (hl : l.Prime) : 0 < rho l := by
  unfold rho
  have h2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
  apply div_pos one_pos
  nlinarith

theorem lemmaSt_of (hG : GenLogWeight.{u, 0}) (hB : LogBridges.{u}) : LemmaSt.{u} := by
  intro K _ _ _ l d _ hl hpi g hg0 hgl x
  have hb := (hB K l d 0 0).1
  exact hG K l hl hpi (V2 d) (fun y => (y.1, y.2 - 2)) g hg0 (fun x => by rw [← hb x]; exact hgl x) x

theorem asmS_integral_sub_one {K : Type u} [NormedField K] {ι : Type} {pi ρ : ℝ} (h0 : 0 < pi)
    (h1 : pi ≤ 1) (hρ : 0 ≤ ρ) {E : MvPowerSeries ι K} (hE : Integral E)
    (hc : constantCoeff E = 1) : WtGe pi (fun _ => ρ) ρ (E - 1) := by
  classical
  intro n
  unfold MonoWtGe
  by_cases hn : n = 0
  · subst hn
    have h00 : coeff 0 (E - 1) = 0 := by
      rw [map_sub, coeff_zero_eq_constantCoeff_apply, hc, coeff_one, if_pos rfl, sub_self]
    rw [h00, norm_zero]
    exact (Real.rpow_pos_of_pos h0 _).le
  · obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hn (Finsupp.ext h)
    have hd : ρ ≤ dot n (fun _ => ρ) := by
      unfold dot Finsupp.sum
      have hmem : i ∈ n.support := Finsupp.mem_support_iff.mpr hi
      have h1' : (1 : ℝ) ≤ n i := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hi
      calc ρ ≤ (n i : ℝ) * ρ := by nlinarith
        _ ≤ ∑ x ∈ n.support, (n x : ℝ) * ρ :=
          Finset.single_le_sum (f := fun x => (n x : ℝ) * ρ)
            (fun x _ => mul_nonneg (Nat.cast_nonneg _) hρ) hmem
    have hc1 : coeff n (E - 1) = coeff n E := by
      rw [map_sub, coeff_one, if_neg hn, sub_zero]
    rw [hc1]
    exact (hE n).trans (Real.one_le_rpow_of_pos_of_le_one_of_nonpos h0 h1 (by linarith))

theorem asmS_cc_be {K : Type u} [Field K] {d : ℕ} [NeZero d] {be : MvPowerSeries (ZMod d) K}
    (h : NoLowBidegree be) : constantCoeff be = 0 := by
  by_contra hne
  have := (h 0 (by rwa [coeff_zero_eq_constantCoeff_apply])).1
  simp [degE] at this

theorem asmS_cc_subst {K : Type u} [Field K] {d : ℕ} [NeZero d] {be : MvPowerSeries (ZMod d) K}
    (hbe0 : constantCoeff be = 0) (a : ZMod d → MvPowerSeries (V2 d) K)
    (ha : ∀ s, constantCoeff (a s) = 0) : constantCoeff (subst a be) = 0 := by
  have ha' : HasSubst a := hasSubst_of_constantCoeff_zero ha
  rw [constantCoeff_subst ha']
  apply finsum_eq_zero_of_forall_eq_zero
  intro n
  by_cases hn : n = 0
  · subst hn
    rw [coeff_zero_eq_constantCoeff_apply, hbe0, zero_smul]
  · obtain ⟨s, hs⟩ : ∃ s, n s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hn (Finsupp.ext h)
    have hp : constantCoeff (n.prod fun s e => a s ^ e) = 0 := by
      simp only [Finsupp.prod, map_prod]
      apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs)
      rw [map_pow, ha s, zero_pow hs]
    rw [hp, smul_zero]

theorem constantCoeff_evenDerivative_eq_zero {K : Type u} [Field K] {d : ℕ} [NeZero d] {be : MvPowerSeries (ZMod d) K}
    (hbe0 : constantCoeff be = 0) : constantCoeff (de1 be) = 0 := by
  have c0 : constantCoeff (subst (s0 (K := K) (d := d)) be) = 0 :=
    asmS_cc_subst hbe0 _ (fun s => by simp [s0])
  have c1 : constantCoeff (subst (s1 (K := K) (d := d)) be) = 0 :=
    asmS_cc_subst hbe0 _ (fun s => by simp only [s1]; split_ifs <;> simp)
  have c2 : constantCoeff (subst (s2 (K := K) (d := d)) be) = 0 :=
    asmS_cc_subst hbe0 _ (fun s => by simp only [s2]; split_ifs <;> simp)
  simp only [de1, map_sub, c0, c1, c2, sub_zero]

theorem constantCoeff_oddDerivative_eq_zero {K : Type u} [Field K] {d : ℕ} [NeZero d] {be : MvPowerSeries (ZMod d) K}
    (hbe0 : constantCoeff be = 0) : constantCoeff (de2 be) = 0 := by
  have c0 : constantCoeff (subst (s0 (K := K) (d := d)) be) = 0 :=
    asmS_cc_subst hbe0 _ (fun s => by simp [s0])
  have c1 : constantCoeff (subst (s1' (K := K) (d := d)) be) = 0 :=
    asmS_cc_subst hbe0 _ (fun s => by simp only [s1']; split_ifs <;> simp)
  have c2 : constantCoeff (subst (s2' (K := K) (d := d)) be) = 0 :=
    asmS_cc_subst hbe0 _ (fun s => by simp only [s2']; split_ifs <;> simp)
  simp only [de2, map_sub, c0, c1, c2, sub_zero]

theorem asmS_diff (hGW : GenLogWeight.{u, 0}) (hGI : GenLogInverse.{u, 0}) (hB : LogBridges.{u})
    (hSW : SubstWt.{u, 0, 0}) (hQ : Quant.{u}) (hLS : LogStep.{u, 0})
    {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K] {l d : ℕ} [NeZero d]
    (hl : l.Prime) (hd : 2 ≤ d) (hde : Even d) (hpi : ‖(l : K)‖ < 1)
    {K0 : Subfield K} (hK0 : Unram l K0) (D : MvPowerSeries (V2 d) K)
    (hD0 : constantCoeff D = 0) (hK : ∀ n, coeff n (mvExp D) ∈ K0)
    (hcong : ∀ n : V2 d →₀ ℕ, coeff n (mvExp D) ≠ 0 →
      ((l ^ d - 1 : ℕ) : ℤ) ∣ ∑ x ∈ n.support, (n x : ℤ) * lw l x.2)
    (hEi : Integral (subst (letterLog (K := K) l) (mvExp D)))
    (hEc : constantCoeff (subst (letterLog (K := K) l) (mvExp D)) = 1) :
    WtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) D := by
  have hl0 : (l : K) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne_zero
  have hpi0 : 0 < ‖(l : K)‖ := norm_pos_iff.mpr hl0
  have hρ : 0 ≤ rho l := (asmS_rho_pos hl).le
  have hLL : ∀ x : V2 d, letterLog (K := K) l x = genLog l (fun y : V2 d => (y.1, y.2 - 2)) x :=
    (hB K l d 0 0).1

  obtain ⟨g, hg0, hgl, -⟩ := hGI K l hl (V2 d) (fun y : V2 d => (y.1, y.2 - 2))
  have hgl' : ∀ x, subst g (letterLog (K := K) l x) = X x := fun x => by rw [hLL x]; exact hgl x
  have hgw : ∀ x, WtGe ‖(l : K)‖ (fun _ => rho l) (rho l) (g x) :=
    lemmaSt_of hGW hB K l d hl hpi g hg0 hgl'
  have hE1 := asmS_integral_sub_one hpi0 hpi.le hρ hEi hEc
  have hW := hSW K ‖(l : K)‖ hpi0 hpi (V2 d) (V2 d) g (fun _ => rho l) (fun _ => rho l) (rho l) _
    hg0 hgw hE1

  have hLL0 : ∀ x, constantCoeff (letterLog (K := K) l x) = 0 := fun x => by
    rw [← coeff_zero_eq_constantCoeff_apply]
    show letterLog (K := K) l x 0 = 0
    unfold letterLog
    refine Finset.sum_eq_zero fun e _ => if_neg ?_
    intro h
    have h' := congrArg (fun f : V2 d →₀ ℕ => f (x.1, x.2 - 2 * (e : ZMod d))) h
    simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.single_eq_same] at h'
    exact pow_ne_zero _ (pow_ne_zero _ hl.ne_zero) h'.symm
  have hLa : HasSubst (letterLog (K := K) l : V2 d → MvPowerSeries (V2 d) K) :=
    hasSubst_of_constantCoeff_zero hLL0
  have hga : HasSubst g := hasSubst_of_constantCoeff_zero hg0
  have hcomp : subst g (subst (letterLog (K := K) l) (mvExp D)) = mvExp D := by
    rw [subst_comp_subst_apply hLa hga, show (fun s => subst g (letterLog (K := K) l s)) = X from
      funext hgl', subst_self]
    rfl
  have hsub1 : subst g (subst (letterLog (K := K) l) (mvExp D) - 1) = mvExp D - 1 := by
    rw [← coe_substAlgHom hga, map_sub, map_one, coe_substAlgHom, hcomp]
  rw [hsub1] at hW

  have hQ' : WtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) (mvExp D - 1) := by
    intro n
    by_cases hz : coeff n (mvExp D - 1) = 0
    · unfold MonoWtGe
      rw [hz, norm_zero]
      exact (Real.rpow_pos_of_pos hpi0 _).le
    have hmem : coeff n (mvExp D - 1) ∈ K0 := by
      rw [map_sub, coeff_one]
      split_ifs
      · exact K0.sub_mem (hK n) K0.one_mem
      · exact K0.sub_mem (hK n) K0.zero_mem
    have hdiv : ((l ^ d - 1 : ℕ) : ℤ) ∣ ∑ x ∈ n.support, (n x : ℤ) * lw l x.2 := by
      by_cases hn : n = 0
      · subst hn
        simp
      · apply hcong
        intro h0
        apply hz
        rw [map_sub, coeff_one, if_neg hn, h0, sub_zero]
    exact hQ K l d hl hd hde hpi hpi0 K0 hK0 _ hmem n hdiv (hW n)
  exact hLS K l hl hpi (V2 d) _ D hD0 hQ'

theorem lemmaS_of (hGW : GenLogWeight.{u, 0}) (hGI : GenLogInverse.{u, 0}) (hB : LogBridges.{u})
    (hSW : SubstWt.{u, 0, 0}) (hX : ExpDeInv.{u}) (hQ : Quant.{u}) (hLS : LogStep.{u, 0})
    (hBE : BinomExtract.{u}) : LemmaS.{u} := by
  intro K _ _ _ l d _ hl hlo hd hde hpi K0 hK0 ζ hζ be hBh
  obtain ⟨hK, htor, hlow, ⟨hEi1, hEc1⟩, ⟨hEi2, hEc2⟩⟩ := hBh
  have hbe0 := asmS_cc_be hlow
  have hX' := hX K l d hl hd hde K0 ζ hζ be hK htor hbe0
  obtain ⟨hK1, hc1⟩ := hX' (de1 be) (by simp)
  obtain ⟨hK2, hc2⟩ := hX' (de2 be) (by simp)
  have w1 := asmS_diff hGW hGI hB hSW hQ hLS hl hd hde hpi hK0 (de1 be) (constantCoeff_evenDerivative_eq_zero hbe0) hK1 hc1
    hEi1 hEc1
  have w2 := asmS_diff hGW hGI hB hSW hQ hLS hl hd hde hpi hK0 (de2 be) (constantCoeff_oddDerivative_eq_zero hbe0) hK2 hc2
    hEi2 hEc2
  exact hBE K l d hl hlo hd hde hpi ζ hζ be htor hlow w1 w2

end Formalism.DworkPowerSeriesWeights
