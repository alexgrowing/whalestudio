import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.BiextensionPointsOfExpSpec
import Formalism.GaussJetBounds.GaussJetProofs.Transfer

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral mvExp torus entLog thetaZ bSum linSub idM ZV)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog mvExp_add)
open MvPowerSeries
open Pair

namespace BiextensionSums

theorem map_lgF' {K0 K : Type} [Field K0] [Field K] (l : ℕ) (j : K0 →+* K) :
    PowerSeries.map j (lgF K0 l) = lgF K l := by
  ext n
  rw [PowerSeries.coeff_map]
  unfold lgF
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · rw [map_inv₀, map_pow, map_natCast]
  · rw [map_zero]

theorem linSub_idM {K : Type} [Field K] {d N0 N1 : ℕ} [NeZero d] :
    linSub (idM : ZV d N0 N1 → ZV d N0 N1 → K) = X := by
  funext x
  unfold linSub idM
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    rw [if_neg (Ne.symm hy)]
    simp
  · simp

theorem map_sumE {K0 K ι : Type} [Field K0] [Field K] [Fintype ι] {N0 N1 : ℕ} (j : K0 →+* K)
    (be : MvPowerSeries (Fin 2) K0) :
    map j (sumE (ι := ι) (N0 := N0) (N1 := N1) be) = sumE (map j be) := by
  unfold sumE
  rw [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_subst (hasSubst_of_constantCoeff_zero (by intro a; simp))]
  simp only [map_X]

theorem subst_neg' {K ι κ : Type} [Field K] {φ : ι → MvPowerSeries κ K} (hφ : HasSubst φ)
    (f : MvPowerSeries ι K) : subst φ (-f) = -subst φ f := by
  rw [← coe_substAlgHom hφ, map_neg]

theorem subst_map_linEL {K0 K : Type} [NormedField K0] [NormedField K] {d N0 N1 : ℕ} [NeZero d]
    (l : ℕ) (j : K0 →+* K) (σ : K0 →+* K0) (c : K0) (a : Fin N0) (b : Fin N1)
    {g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) K} (hg : HasSubst g)
    (hgE : ∀ y, subst g (entLog (K := K) l y) = X y) :
    subst g (map j (linEL σ c (fun s : ZMod d => entLog (K := K0) l (s, a, b)))) =
      ∑ s : ZMod d, if s.val % 2 = 0 then C (j (σ^[s.val] c)) * X (s, a, b) else 0 := by
  unfold linEL
  rw [map_sum, subst_sum hg]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs
  · rw [map_mul, map_C, Formalism.DworkPowerSeriesWeights.Transfer.map_entLog, subst_mul hg, subst_C, hgE]
  · rw [map_zero, subst_zero' hg]

theorem subst_map_linOL {K0 K : Type} [NormedField K0] [NormedField K] {d N0 N1 : ℕ} [NeZero d]
    (l : ℕ) (j : K0 →+* K) (σ : K0 →+* K0) (c : K0) (a : Fin N0) (b : Fin N1)
    {g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) K} (hg : HasSubst g)
    (hgE : ∀ y, subst g (entLog (K := K) l y) = X y) :
    subst g (map j (linOL σ c (fun s : ZMod d => entLog (K := K0) l (s, a, b)))) =
      ∑ s : ZMod d, if s.val % 2 = 0 then 0 else C (j (σ^[s.val] c)) * X (s, a, b) := by
  unfold linOL
  rw [map_sum, subst_sum hg]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs
  · rw [map_zero, subst_zero' hg]
  · rw [map_mul, map_C, Formalism.DworkPowerSeriesWeights.Transfer.map_entLog, subst_mul hg, subst_C, hgE]

end BiextensionSums

open BiextensionSums

theorem biextension_of_exp_spec (hE : ExpSpec) (hP : BiextensionPointsIntegral) : B0 := by
  intro K0 K _ _ _ _ _ _ l d N0 N1 _ σ j hU hj h2 hd F hF be0 hF1 hF2 ι _ _ om oms hOw hTr ζ hζ
    U0 Φ hU0 hΦ0 hΦ
  have hl : 2 ≤ l := hU.1.two_le
  obtain ⟨Xt, hX, hlog, hS⟩ := hP K0 l d N0 N1 σ hU h2 hd F hF be0 hF1 hF2 ι om oms hOw hTr ζ hζ
  have hR := Formalism.InvariantFactorPaths.G7.Top.simeqRules K (ZV d N0 N1)
  have hs0 : HasSubst Xt := hasSubst_of_constantCoeff_zero fun x => (hX x).1
  obtain ⟨Xp, hXp⟩ : ∃ Xp : Bool × ι × Fin N0 × Fin N1 → MvPowerSeries (ZV d N0 N1) K,
      ∀ x, Xp x = map j (Xt x) := ⟨fun x => map j (Xt x), fun _ => rfl⟩
  have hXp' : (fun x => map j (Xt x)) = Xp := funext fun x => (hXp x).symm
  have h0 : ∀ x, constantCoeff (Xp x) = 0 := fun x => by
    rw [hXp, constantCoeff_map, (hX x).1, map_zero]
  have hi : ∀ x, Integral (Xp x) := fun x => by
    rw [hXp]
    exact Formalism.DworkPowerSeriesWeights.Transfer.integral_map j hj (hX x).2
  have hs : HasSubst Xp := hasSubst_of_constantCoeff_zero h0
  have hE0 : ∀ (a : Fin N0) (b : Fin N1) (s : ZMod d),
      constantCoeff (entLog (K := K0) l (s, a, b)) = 0 :=
    fun a b s => ((letter_shift K0 l d σ hU.1).2.2 N0 N1 a b s).1
  have hE1 : ∀ (a : Fin N0) (b : Fin N1) (s : ZMod d),
      constantCoeff (entLog (K := K) l (s, a, b)) = 0 :=
    fun a b s => ((letter_shift K l d (RingHom.id K) hU.1).2.2 N0 N1 a b s).1
  obtain ⟨bm, hbm⟩ : ∃ bm, bm = map j (beMean (d := d) l σ be0 om oms ζ) := ⟨_, rfl⟩
  obtain ⟨Bt, hBt⟩ : ∃ Bt : MvPowerSeries (ZV d N0 N1) K, Bt = ∑ ab : Fin N0 × Fin N1,
      subst (fun s => entLog (K := K) l (s, ab.1, ab.2)) bm := ⟨_, rfl⟩
  have hmapB : map j (∑ ab : Fin N0 × Fin N1, subst
      (fun s => entLog (K := K0) l (s, ab.1, ab.2)) (beMean (d := d) l σ be0 om oms ζ)) = Bt := by
    rw [map_sum, hBt]
    refine Finset.sum_congr rfl fun ab _ => ?_
    rw [map_subst (hasSubst_of_constantCoeff_zero fun s => hE0 ab.1 ab.2 s), hbm]
    simp only [Formalism.DworkPowerSeriesWeights.Transfer.map_entLog]
  have hS' : Simeq Bt (subst Xp (sumE (map j be0))) := by
    have := (Formalism.InvariantFactorPaths.G7.Top.mapSimeq K0 K _ j hj).1 _ _ hS
    rwa [hmapB, map_subst hs0, map_sumE, hXp'] at this
  have hΦ' := (Formalism.InvariantFactorPaths.G7.Top.simeqRules K (Bool × ι × Fin N0 × Fin N1)).2.2.2.2 _ Φ _ Xp h0 hi hΦ
  have hBΦ : Simeq Bt (subst Xp Φ) := hR.2.2.1 _ _ _ hS' (hR.2.1 _ _ hΦ')
  have hsΦ0 : constantCoeff (subst Xp Φ) = 0 := constantCoeff_subst_eq_zero hs h0 hΦ0
  have hBt0 : constantCoeff Bt = 0 := by
    have := hBΦ.1
    rwa [map_sub, hsΦ0, sub_zero] at this
  have hnB0 : constantCoeff (-Bt) = 0 := by rw [map_neg, hBt0, neg_zero]
  refine ⟨mvExp (Bt - subst Xp Φ) * subst Xp U0,
    Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' hBΦ.2 (Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_subst' h0 hi hU0), ?_⟩
  intro g hg0 hgE
  have hg : HasSubst g := hasSubst_of_constantCoeff_zero hg0
  have hx : ∀ x, subst g (Xp x) = xOfZ l j σ om oms x := by
    intro x
    have ha : constantCoeff (subst g (Xp x)) = 0 := constantCoeff_subst_eq_zero hg hg0 (h0 x)
    have hlg : PowerSeries.subst (subst g (Xp x)) (lgF K l) =
        subst g (map j (PowerSeries.subst (Xt x) (lgF K0 l))) := by
      rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (hX x).1), map_lgF',
        ← hXp, subst_subst1 hg (PowerSeries.HasSubst.of_constantCoeff_zero (h0 x))]
    rw [← exp_log hE hl ha, hlg, hlog]
    unfold xOfZ
    congr 1
    split_ifs
    · exact subst_map_linEL l j σ _ _ _ hg hgE
    · exact subst_map_linOL l j σ _ _ _ hg hgE
  have hmain : subst Xp (mvExp (-Φ) * U0) =
      mvExp (-Bt) * (mvExp (Bt - subst Xp Φ) * subst Xp U0) := by
    rw [subst_mul hs, Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.subst_mvExp' hs (by rw [map_neg, hΦ0, neg_zero]),
      ← mul_assoc, ← mvExp_add hnB0 hBΦ.1, subst_neg' hs]
    congr 2
    ring
  have hgB : subst g Bt = bSum (idM : ZV d N0 N1 → ZV d N0 N1 → K) bm := by
    unfold bSum
    rw [linSub_idM, hBt, subst_sum hg]
    refine Finset.sum_congr rfl fun ab _ => ?_
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun s => hE1 ab.1 ab.2 s) hg]
    simp only [hgE]
  have hxf : xOfZ (d := d) (N0 := N0) (N1 := N1) l j σ om oms = fun x => subst g (Xp x) :=
    funext fun x => (hx x).symm
  unfold thetaInZ thetaZ
  rw [linSub_idM, subst_self, id, ← hbm, ← hgB, hxf, ← subst_comp_subst_apply hs hg, hmain,
    subst_mul hg, Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.subst_mvExp' hg hnB0, subst_neg' hg, neg_smul, one_smul, mul_comm]

end Formalism.L2.Th1.D
