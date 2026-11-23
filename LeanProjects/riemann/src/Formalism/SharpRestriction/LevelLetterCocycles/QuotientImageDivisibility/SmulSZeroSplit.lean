import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.IsExpSmulA
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ZpowNeOneOfClose

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Formalism.MainNotions.N.Pv.LocalLengthBound.Ser

section LemK

variable {LL' : Type} [Field LL'] {V : Type} [AddCommGroup V] [Module LL' V]

theorem smulS_zero_split {Fil : ℤ → Submodule LL' V} (hFa : Antitone Fil) {M : ℤ} {f : ℤ → V}
    (hf : LB M f) (hneg : ∀ k : ℤ, k < 0 → f k ∈ Fil (-k)) (g : PowerSeries LL') :
    smulS g f 0 - PowerSeries.constantCoeff g • f 0 ∈ Fil 1 := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (0 : ℤ) - M < (N + 1 : ℕ) :=
    ⟨(0 - M).toNat, by have := Int.self_le_toNat (0 - M); push_cast; omega⟩
  rw [smulS_eq_sum hf g 0 (N + 1) hN, Finset.sum_range_succ']
  simp only [Nat.cast_zero, sub_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    add_sub_cancel_right]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  have h := hneg ((0 : ℤ) - ((i + 1 : ℕ) : ℤ)) (by push_cast; omega)
  exact hFa (show (1 : ℤ) ≤ -((0 : ℤ) - ((i + 1 : ℕ) : ℤ)) by push_cast; omega) h

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem chi_zpow_ne_one (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (k : ℤ) (hk : k ≠ 0) :
    (algebraMap O LL (W.χΓ W.gam : O)) ^ k ≠ 1 := by
  have hs : W.s = 1 := hA.2.1
  have hg := W.gam_gen
  rw [hs, Nat.cast_one] at hg
  have h1 : (1 : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ W.gam : O) - 1) := le_of_eq hg.symm
  have hne : algebraMap O LL (W.χΓ W.gam : O) ≠ 1 := by
    intro h
    rw [h, sub_self, AddValuation.map_zero] at hg
    exact WithTop.top_ne_coe hg
  have hp3 : 3 ≤ PD.p := by have := PD.hp.two_le; have := hA.2.2; omega
  exact Val.zpow_ne_one_of_close v PD.hp W.v_l hp3 _ h1 hne k hk

theorem lemK_of [NeZero n] (hdom : IsDomain O) (hFr : IsFractionRing O LL)
    (h1 : Formalism.MainNotions.DeltaInvariantLattices.WachLatticeFree W) (h3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W) (h4 : Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W)
    (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hD : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W)
    (hN : GamN W) (hA' : GamA W) (hΓ : GamNΔ W) (hΔ : PtTrans W) : Formalism.MainNotions.RamifiedCoefficientChains.Sh.LemK W := by
  intro hA T hT i ζ hζ x d hDL hd ⟨j, hj⟩
  have hp := p_ne_zero_LL W
  obtain ⟨-, -, hAdd, hO, -, hGam, -⟩ := expRules_of W h4 hN hA' hA T hT i ζ hζ
  have hCr := expCritN_of W hA hdom hFr h1 h3 h4 h5 hD hR hΓ hΔ T hT i ζ hζ x d hDL hd
  have hLv1 : ∀ (z : ↥(W.N T)) (k : ℤ), W.levN T i ζ z k ∈ Formalism.MainNotions.WachCoordinates.FilLev W T i 0 (-k) :=
    (h4 T hT i 0 ζ (by rwa [zero_add, pow_one])).1
  have hFl : Antitone (Formalism.MainNotions.WachCoordinates.FilLev W T i 0) := Formalism.MainNotions.UnusedSlot80.LevR.filLev_anti W T i 0
  have hcoef : ∀ k : ℤ, k ≠ 0 → d k ∈ Formalism.MainNotions.WachCoordinates.FilLev W T i 0 (-k) := by
    intro k hk
    have hE := hO (((PD.p : ℕ) : O) ^ j) _ _ (hAdd _ _ _ _ (hGam x d hd) (hO (-1) x d hd))
    have hz : ((PD.p : ℕ) : O) ^ j • (W.γ T x + (-1 : O) • x) ∈ W.N T := by
      rw [neg_one_smul, ← sub_eq_add_neg]; exact hj
    have huq := congrFun (isExp_unique W T i ζ hE (isExp_self W T i ζ hz)) k
    have hmem := hLv1 ⟨_, hz⟩ k
    rw [← huq] at hmem
    simp only [Pi.add_apply] at hmem
    have e : algebraMap O LL (((PD.p : ℕ) : O) ^ j) •
        ((algebraMap O LL (W.χΓ W.gam : O)) ^ k • d k + algebraMap O LL (-1) • d k) =
        (algebraMap O LL (((PD.p : ℕ) : O) ^ j) * ((algebraMap O LL (W.χΓ W.gam : O)) ^ k - 1)) •
          d k := by
      rw [map_neg, map_one, neg_one_smul, ← sub_eq_add_neg, mul_smul, sub_smul, one_smul]
    have hc0 : algebraMap O LL (((PD.p : ℕ) : O) ^ j) *
        ((algebraMap O LL (W.χΓ W.gam : O)) ^ k - 1) ≠ 0 := by
      refine mul_ne_zero ?_ (sub_ne_zero.2 (chi_zpow_ne_one W hA k hk))
      rw [map_pow, map_natCast]; exact pow_ne_zero _ hp
    rw [e] at hmem
    have := (Formalism.MainNotions.WachCoordinates.FilLev W T i 0 (-k)).smul_mem
      (algebraMap O LL (((PD.p : ℕ) : O) ^ j) * ((algebraMap O LL (W.χΓ W.gam : O)) ^ k - 1))⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at this
  refine ⟨hcoef, fun y hy => ⟨?_, ?_⟩⟩
  · obtain ⟨u, hu, hlq⟩ := (expRing_of W hR hA i ζ hζ).1
    obtain ⟨m, hm⟩ := hd.1
    have hEq := isExp_unique W T i ζ (isExp_self W T i ζ hy) (isExp_smulA W T i ζ hd _)
    have hc := hLv1 ⟨_, hy⟩ (y : ℤ)
    rw [hEq, map_pow, hlq, mul_pow, mul_comm, smulS_mul hm, smulS_X_pow (LB_smulS hm _)] at hc
    simp only [sub_self] at hc
    have hsplit := smulS_zero_split hFl hm (fun k hk => hcoef k (by omega)) (u ^ y)
    have h2 : PowerSeries.constantCoeff (u ^ y) • d 0 ∈ Formalism.MainNotions.WachCoordinates.FilLev W T i 0 (-(y : ℤ)) := by
      have := Submodule.sub_mem _ hc (hFl (show -(y : ℤ) ≤ 1 by omega) hsplit)
      rwa [sub_sub_cancel] at this
    have hcu : PowerSeries.constantCoeff (u ^ y) ≠ 0 := by
      rw [map_pow]
      exact pow_ne_zero _ (PowerSeries.isUnit_iff_constantCoeff.1 hu).ne_zero
    have := (Formalism.MainNotions.WachCoordinates.FilLev W T i 0 (-(y : ℤ))).smul_mem
      (PowerSeries.constantCoeff (u ^ y))⁻¹ h2
    rwa [smul_smul, inv_mul_cancel₀ hcu, one_smul] at this
  · constructor
    · intro hx
      have := (hCr ⟨y, hy⟩).1 hx 0
      simpa using this
    · intro h0
      refine (hCr ⟨y, hy⟩).2 fun k => ?_
      by_cases hk : k = 0
      · subst hk; simpa using h0
      · exact hcoef k hk

end LemK

end Formalism.MainNotions.N.Pv.LocalLengthBound
