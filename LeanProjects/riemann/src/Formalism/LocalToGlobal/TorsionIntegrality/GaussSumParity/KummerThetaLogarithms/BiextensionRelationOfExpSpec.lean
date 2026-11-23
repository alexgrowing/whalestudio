import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.RelativeThetaFactorization
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.BiextensionOfExpSpec
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.BiextensionPointsOfExpSpec

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral mvExp torus entLog bSum linSub idM ZV serAlong)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog mvExp_add)
open MvPowerSeries
open Pair

namespace BiextensionAlongSeries

section Alg

variable {K : Type} [Field K]

theorem hsX {ι κ : Type} [Finite ι] (e : ι → κ) :
    HasSubst (fun i => (X (e i) : MvPowerSeries κ K)) :=
  hasSubst_of_constantCoeff_zero fun i => constantCoeff_X (e i)

theorem subst_serAlong {ι κ μ : Type} [Finite ι] (e : ι → κ) {Y : κ → MvPowerSeries μ K}
    (hY : HasSubst Y) (f : MvPowerSeries ι K) :
    subst Y (serAlong e f) = subst (fun i => Y (e i)) f := by
  unfold serAlong
  rw [subst_comp_subst_apply (hsX e) hY]
  simp only [subst_X hY]

theorem serAlong_subst {ι κ μ : Type} [Finite κ] (e : κ → μ) {φ : ι → MvPowerSeries κ K}
    (hφ : HasSubst φ) (f : MvPowerSeries ι K) :
    serAlong e (subst φ f) = subst (fun i => serAlong e (φ i)) f := by
  unfold serAlong
  rw [subst_comp_subst_apply hφ (hsX e)]

theorem cc_serAlong {ι κ : Type} [Finite ι] (e : ι → κ) {f : MvPowerSeries ι K}
    (hf : constantCoeff f = 0) : constantCoeff (serAlong e f) = 0 :=
  constantCoeff_subst_eq_zero (hsX e) (fun i => constantCoeff_X (e i)) hf

theorem serAlong_neg {ι κ : Type} [Finite ι] (e : ι → κ) (f : MvPowerSeries ι K) :
    serAlong e (-f) = -serAlong e f :=
  BiextensionSums.subst_neg' (hsX e) f

theorem cc_serAlong_eq {ι κ : Type} [Finite ι] (e : ι → κ) (f : MvPowerSeries ι K) :
    constantCoeff (serAlong e f) = constantCoeff f := by
  have h : f = C (constantCoeff f) + (f - C (constantCoeff f)) := by ring
  have h0 : constantCoeff (f - C (constantCoeff f)) = 0 := by simp
  conv_lhs => rw [h]
  unfold serAlong
  rw [subst_add (hsX e), subst_C, map_add, constantCoeff_C]
  have := cc_serAlong e h0
  unfold serAlong at this
  rw [this, add_zero]

theorem cc_sumE {ι : Type} [Fintype ι] {N0 N1 : ℕ} {be : MvPowerSeries (Fin 2) K}
    (h : constantCoeff be = 0) :
    constantCoeff (sumE (ι := ι) (N0 := N0) (N1 := N1) be) = 0 := by
  unfold sumE
  rw [map_sum]
  refine Finset.sum_eq_zero fun e _ => ?_
  exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (by intro a; simp))
    (by intro a; simp) h

end Alg

section Normed

variable {K : Type} [NormedField K]

theorem integral_serAlong [IsUltrametricDist K] {ι κ : Type} [Finite ι] (e : ι → κ)
    {f : MvPowerSeries ι K} (hf : Integral f) : Integral (serAlong e f) :=
  Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_subst' (fun i => constantCoeff_X (e i))
    (fun i => Formalism.InvariantFactorPaths.G7.TwoS.integral_X (e i)) hf

theorem serAlong_mvExp [CharZero K] {ι κ : Type} [Finite ι] (e : ι → κ) {f : MvPowerSeries ι K}
    (hf : constantCoeff f = 0) : serAlong e (mvExp f) = mvExp (serAlong e f) :=
  Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.subst_mvExp' (hsX e) hf

theorem simeq_serAlong [IsUltrametricDist K] [CharZero K] {ι κ : Type} [Finite ι] (e : ι → κ)
    {f g : MvPowerSeries ι K} (h : Simeq f g) : Simeq (serAlong e f) (serAlong e g) :=
  (Formalism.InvariantFactorPaths.G7.Top.simeqRules K ι).2.2.2.2 κ f g _ (fun i => constantCoeff_X (e i))
    (fun i => Formalism.InvariantFactorPaths.G7.TwoS.integral_X (e i)) h

end Normed

end BiextensionAlongSeries

open BiextensionSums BiextensionAlongSeries

theorem biextension_relation_of_exp_spec (hE : ExpSpec) (hP : BiextensionPointsIntegral) : RelativeThetaFactorization := by
  intro K0 K _ _ _ _ _ _ l d N0 N1 _ σ j hU hj h2 hd F hF be0 hF1 hF2 ι _ _ om oms hOw hTr ζ hζ
    τ _ U0 Φ Ψ hU0 hΦ0 hΦ
  have hl : 2 ≤ l := hU.1.two_le
  obtain ⟨Xt, hX, hlog, hS⟩ := hP K0 l d N0 N1 σ hU h2 hd F hF be0 hF1 hF2 ι om oms hOw hTr ζ hζ
  have hR := Formalism.InvariantFactorPaths.G7.Top.simeqRules K (ZV d N0 N1 ⊕ τ)
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

  have hbe0 : constantCoeff (map j be0) = 0 := by
    rw [constantCoeff_map, ← coeff_zero_eq_constantCoeff_apply, hF1.1 0 (Or.inl rfl), map_zero]
  have hsE0 : constantCoeff (sumE (ι := ι) (N0 := N0) (N1 := N1) (map j be0)) = 0 := cc_sumE hbe0
  have hBt0 : constantCoeff Bt = 0 := by
    have := hS'.1
    rwa [map_sub, constantCoeff_subst_eq_zero hs h0 hsE0, sub_zero] at this
  have hΨ0 : constantCoeff Ψ = 0 := by
    have := hΦ.1
    rwa [map_sub, hΦ0, map_add, cc_serAlong _ hsE0, cc_serAlong_eq, zero_add, zero_sub,
      neg_eq_zero] at this

  obtain ⟨Y, hYl, hYr⟩ : ∃ Y : (Bool × ι × Fin N0 × Fin N1) ⊕ τ → MvPowerSeries (ZV d N0 N1 ⊕ τ) K,
      (∀ x, Y (Sum.inl x) = serAlong Sum.inl (Xp x)) ∧ ∀ y, Y (Sum.inr y) = X (Sum.inr y) :=
    ⟨Sum.elim (fun x => serAlong Sum.inl (Xp x)) (fun y => X (Sum.inr y)), fun _ => rfl,
      fun _ => rfl⟩
  have hY0 : ∀ a, constantCoeff (Y a) = 0 := by
    rintro (x | y)
    · rw [hYl]
      exact cc_serAlong _ (h0 x)
    · rw [hYr, constantCoeff_X]
  have hYi : ∀ a, Integral (Y a) := by
    rintro (x | y)
    · rw [hYl]
      exact integral_serAlong _ (hi x)
    · rw [hYr]
      exact Formalism.InvariantFactorPaths.G7.TwoS.integral_X _
  have hY : HasSubst Y := hasSubst_of_constantCoeff_zero hY0
  have hYinl : ∀ f : MvPowerSeries (Bool × ι × Fin N0 × Fin N1) K,
      subst Y (serAlong Sum.inl f) = serAlong Sum.inl (subst Xp f) := by
    intro f
    rw [subst_serAlong _ hY, serAlong_subst _ hs]
    simp only [hYl]
  have hYinr : ∀ f : MvPowerSeries τ K, subst Y (serAlong Sum.inr f) = serAlong Sum.inr f := by
    intro f
    rw [subst_serAlong _ hY]
    simp only [hYr]
    rfl
  obtain ⟨T, hT⟩ : ∃ T : MvPowerSeries (ZV d N0 N1 ⊕ τ) K,
      T = serAlong Sum.inl Bt + serAlong Sum.inr Ψ := ⟨_, rfl⟩
  have hΦ' := (Formalism.InvariantFactorPaths.G7.Top.simeqRules K ((Bool × ι × Fin N0 × Fin N1) ⊕ τ)).2.2.2.2 _ Φ _ Y
    hY0 hYi hΦ
  rw [subst_add hY, hYinl, hYinr] at hΦ'
  have hTΦ : Simeq T (subst Y Φ) := by
    rw [hT]
    exact hR.2.2.1 _ _ _ (hR.2.2.2.1 _ _ _ _ (simeq_serAlong _ hS') (hR.1 _)) (hR.2.1 _ _ hΦ')
  have hlB0 : constantCoeff (-serAlong (Sum.inl : _ → ZV d N0 N1 ⊕ τ) Bt) = 0 := by
    rw [map_neg, cc_serAlong _ hBt0, neg_zero]
  have hrΨ0 : constantCoeff (-serAlong (Sum.inr : _ → ZV d N0 N1 ⊕ τ) Ψ) = 0 := by
    rw [map_neg, cc_serAlong _ hΨ0, neg_zero]
  have hnT0 : constantCoeff (-T) = 0 := by
    rw [hT, neg_add, map_add, hlB0, hrΨ0, add_zero]
  refine ⟨mvExp (T - subst Y Φ) * subst Y U0,
    Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' hTΦ.2 (Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_subst' hY0 hYi hU0), ?_⟩
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
  have hmain : subst Y (mvExp (-Φ) * U0) =
      mvExp (-T) * (mvExp (T - subst Y Φ) * subst Y U0) := by
    rw [subst_mul hY, Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.subst_mvExp' hY (by rw [map_neg, hΦ0, neg_zero]),
      ← mul_assoc, ← mvExp_add hnT0 hTΦ.1, subst_neg' hY]
    congr 2
    ring
  have hgB : subst g Bt = bSum (idM : ZV d N0 N1 → ZV d N0 N1 → K) bm := by
    unfold bSum
    rw [linSub_idM, hBt, subst_sum hg]
    refine Finset.sum_congr rfl fun ab _ => ?_
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun s => hE1 ab.1 ab.2 s) hg]
    simp only [hgE]
  obtain ⟨G, hGl, hGr, hGdef⟩ : ∃ G : ZV d N0 N1 ⊕ τ → MvPowerSeries (ZV d N0 N1 ⊕ τ) K,
      (∀ x, G (Sum.inl x) = serAlong Sum.inl (g x)) ∧ (∀ y, G (Sum.inr y) = X (Sum.inr y)) ∧
      G = Sum.elim (fun x => serAlong Sum.inl (g x)) (fun y => X (Sum.inr y)) :=
    ⟨Sum.elim (fun x => serAlong Sum.inl (g x)) (fun y => X (Sum.inr y)), fun _ => rfl,
      fun _ => rfl, rfl⟩
  have hG0 : ∀ a, constantCoeff (G a) = 0 := by
    rintro (x | y)
    · rw [hGl]
      exact cc_serAlong _ (hg0 x)
    · rw [hGr, constantCoeff_X]
  have hG : HasSubst G := hasSubst_of_constantCoeff_zero hG0
  have hGinl : ∀ f : MvPowerSeries (ZV d N0 N1) K,
      subst G (serAlong Sum.inl f) = serAlong Sum.inl (subst g f) := by
    intro f
    rw [subst_serAlong _ hG, serAlong_subst _ hg]
    simp only [hGl]
  have hGinr : ∀ f : MvPowerSeries τ K, subst G (serAlong Sum.inr f) = serAlong Sum.inr f := by
    intro f
    rw [subst_serAlong _ hG]
    simp only [hGr]
    rfl
  have hfam : (Sum.elim (fun x => serAlong Sum.inl (xOfZ (d := d) l j σ om oms x))
      (fun y => (X (Sum.inr y) : MvPowerSeries (ZV d N0 N1 ⊕ τ) K))) =
      fun a => subst G (Y a) := by
    funext a
    rcases a with x | y
    · rw [Sum.elim_inl, hYl, hGinl, hx]
    · rw [Sum.elim_inr, hYr, subst_X hG, hGr]
  have hb0 : constantCoeff (-(bSum (idM : ZV d N0 N1 → ZV d N0 N1 → K) bm)) = 0 := by
    rw [← hgB, map_neg, constantCoeff_subst_eq_zero hg hg0 hBt0, neg_zero]
  have hnΨ0 : constantCoeff (-Ψ) = 0 := by rw [map_neg, hΨ0, neg_zero]
  have hGT : subst G (mvExp (-T)) =
      serAlong Sum.inl (mvExp (-(bSum (idM : ZV d N0 N1 → ZV d N0 N1 → K) bm))) *
        serAlong Sum.inr (mvExp (-Ψ)) := by
    rw [Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.subst_mvExp' hG hnT0, subst_neg' hG, hT, subst_add hG, hGinl, hGinr, hgB,
      serAlong_mvExp _ hb0, serAlong_mvExp _ hnΨ0, serAlong_neg, serAlong_neg, neg_add]
    refine mvExp_add ?_ hrΨ0
    rw [← serAlong_neg]
    exact cc_serAlong _ hb0
  rw [hfam, ← subst_comp_subst_apply hY hG, hmain, subst_mul hG, hGT, ← hGdef, ← hbm]
  ring

theorem biextension_relation_holds : RelativeThetaFactorization := biextension_relation_of_exp_spec expSpec biextension_points_integral

end Formalism.L2.Th1.D
