import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ImportsAlt
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DivAddLogbLeEightMulErrorScale
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.TruncatedCoefficientPoly
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.RingDataOfCaseAOfP9
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.CmpDSmulLetter

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.DYAa

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17 PowerSeries

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable (W : LocWach PD LL O v n)

theorem phi_smul (T : LocLat G Qp LL O) (a : LetA O n) (x : W.DD T) :
    W.φD T (a • x) = W.φA a • W.φD T x := by
  show W.φD T (a • x) = (letφ W.φ₀ a) • W.φD T x
  rw [← algebraMap_smul W.EE a x, W.φD_smul, W.φE_ext, algebraMap_smul]

variable {W} [IsDomain O] [FiniteDimensional Qp LL]

theorem π₀_letter_ne (hR : Formalism.MainNotions.N.FrobeniusPowerSeries.GS.RD W) (j : ZMod n) : W.π₀ j ≠ 0 := by
  obtain ⟨w, hw⟩ := hR.1
  intro h0
  have h1 : W.π₀ j = (w : LetA O n) j * PowerSeries.X ^ (PD.p - 1) := by
    rw [hw, Pi.mul_apply, Pi.pow_apply]
    rfl
  rw [h1] at h0
  have hu : IsUnit ((w : LetA O n) j) := w.isUnit.map (Pi.evalMonoidHom (fun _ : ZMod n => PowerSeries O) j)
  have hX : (PowerSeries.X : PowerSeries O) ^ (PD.p - 1) ≠ 0 := pow_ne_zero _ PowerSeries.X_ne_zero
  exact hX (hu.mul_right_eq_zero.mp h0)

theorem cancel_π₀ (hR : Formalism.MainNotions.N.FrobeniusPowerSeries.GS.RD W) {x y : LetA O n} (h : W.π₀ * x = W.π₀ * y) : x = y := by
  funext j
  have h' := congrFun h j
  simp only [Pi.mul_apply] at h'
  exact mul_left_cancel₀ (π₀_letter_ne hR j) h'

theorem qA_letter_cc (hR : Formalism.MainNotions.N.FrobeniusPowerSeries.GS.RD W) (j : ZMod n) : constantCoeff (qA W j) = ((PD.p : ℕ) : O) := by
  obtain ⟨w, hw⟩ := hR.1
  have hp2 : 2 ≤ PD.p := PD.hp.two_le
  have h1 : qA W j = (w : LetA O n) j * PowerSeries.X ^ (PD.p - 1) + ((PD.p : ℕ) : PowerSeries O) := by
    show W.π₀ j + (lA W) j = _
    rw [hw, Pi.mul_apply, Pi.pow_apply]
    rfl
  rw [h1, map_add, map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega), mul_zero, zero_add,
    map_natCast]

theorem qA_letter_ne (hR : Formalism.MainNotions.N.FrobeniusPowerSeries.GS.RD W) (j : ZMod n) : qA W j ≠ 0 := by
  intro h
  have hc := qA_letter_cc hR j
  rw [h, map_zero] at hc
  have hv := W.v_l
  have h0 : ((PD.p : ℕ) : LL) = 0 := by
    rw [← map_natCast (algebraMap O LL), ← hc, map_zero]
  rw [h0, AddValuation.map_zero] at hv
  simp at hv

theorem w_mem (hR : Formalism.MainNotions.N.FrobeniusPowerSeries.GS.RD W) :
    ∃ w ∈ W.AΔ, IsUnit w ∧ W.φA W.π₀ = w * W.π₀ * qA W ^ (PD.p - 1) := by
  obtain ⟨w, hw⟩ := hR.2.1
  have hinv : ∀ g, g ∈ W.DelF → g⁻¹ ∈ W.DelF := by
    intro g hg
    obtain ⟨k, hk, hk'⟩ := (W.DelF_def g).1 hg
    exact (W.DelF_def _).2 ⟨k, hk, by rw [inv_pow, hk', inv_one]⟩
  have hmul : ∀ a b, a ∈ W.DelF → b ∈ W.DelF → a * b ∈ W.DelF := by
    intro a b ha hb
    obtain ⟨k, hk, hk'⟩ := (W.DelF_def a).1 ha
    obtain ⟨m, hm, hm'⟩ := (W.DelF_def b).1 hb
    refine (W.DelF_def _).2 ⟨k * m, Nat.mul_pos hk hm, ?_⟩
    rw [mul_pow, pow_mul, hk', one_pow, one_mul, mul_comm k m, pow_mul, hm', one_pow]
  have hπ : ∀ δ ∈ W.DelF, W.γA δ W.π₀ = W.π₀ := by
    intro δ hδ
    funext i
    show W.γ₀ δ W.π₀₁ = W.π₀₁
    unfold Formalism.BasicNotions.LocWach.π₀₁
    rw [map_add, map_sub, map_one, map_natCast, map_sum]
    congr 1
    have hsum : ∀ x ∈ W.DelF, W.γ₀ δ (W.γ₀ x (1 + PowerSeries.X)) = W.γ₀ (δ * x) (1 + PowerSeries.X) := by
      intro x _
      rw [map_mul, AlgHom.mul_apply]
    rw [Finset.sum_congr rfl hsum]
    refine Finset.sum_equiv (Equiv.mulLeft δ) (fun g => ?_) (fun g _ => rfl)
    constructor
    · intro hg
      exact hmul δ g hδ hg
    · intro hg
      have := hmul δ⁻¹ (δ * g) (hinv δ hδ) hg
      rwa [inv_mul_cancel_left] at this
  have hq : ∀ δ ∈ W.DelF, W.γA δ (qA W) = qA W := by
    intro δ hδ
    show W.γA δ (W.π₀ + lA W) = W.π₀ + lA W
    rw [map_add, hπ δ hδ]
    congr 1
    show W.γA δ ((PD.p : ℕ) : LetA O n) = ((PD.p : ℕ) : LetA O n)
    exact map_natCast _ _
  have hc : ∀ δ (a : LetA O n), W.γA δ (W.φA a) = W.φA (W.γA δ a) := by
    intro δ a
    funext i
    show W.γ₀ δ (W.φ₀ (a (i - 1))) = W.φ₀ (W.γ₀ δ (a (i - 1)))
    rw [W.γ₀_comm]
  refine ⟨w, ?_, w.isUnit, hw⟩
  show ∀ δ ∈ W.DelF, W.γA δ (w : LetA O n) = w
  intro δ hδ
  have e1 := congrArg (W.γA δ) hw
  rw [hc, hπ δ hδ, map_mul, map_mul, map_pow, hπ δ hδ, hq δ hδ, hw] at e1
  funext j
  have e2 := congrFun e1 j
  simp only [Pi.mul_apply, Pi.pow_apply] at e2
  have hne : W.π₀ j * qA W j ^ (PD.p - 1) ≠ 0 :=
    mul_ne_zero (π₀_letter_ne hR j) (pow_ne_zero _ (qA_letter_ne hR j))
  apply mul_left_cancel₀ hne
  linear_combination -e2

theorem coord_mod (hR : Formalism.MainNotions.N.FrobeniusPowerSeries.GS.RD W) {T : LocLat G Qp LL O} {i : ZMod n} {d : ℕ} {b : Fin d → W.DD T}
    (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T i b) {x : W.DD T} (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T i x) :
    ∃ (c₀ : Fin d → O) (z : W.DD T), Formalism.MainNotions.LiftingTheory.InNΔi W T i z ∧
      x = Formalism.MainNotions.LiftingTheory.vecB W T b c₀ + W.π₀ • z := by
  obtain ⟨a, ⟨haA, hxa⟩, -⟩ := hb.2 x hx
  choose F hF using fun m => hR.2.2.2 (a m) (haA m).1
  have hs : HasSubst W.π₀₁ := HasSubst.of_constantCoeff_zero' (Formalism.MainNotions.N.FrobeniusPowerSeries.GS.π₀₁_cc hR)
  let c₀ : Fin d → O := fun m => constantCoeff (F m i)
  let g : Fin d → PowerSeries O := fun m => substAlgHom hs (mk fun k => coeff (k + 1) (F m i))
  let a' : Fin d → LetA O n := fun m => Pi.single i (g m)
  have hzero : ∀ m, ∀ j, j ≠ i → a m j = 0 := by
    intro m j hj
    have := congrFun (haA m).2 j
    simp only [Pi.mul_apply, letE, Pi.single_apply, hj, if_false, zero_mul] at this
    exact this.symm
  have key : ∀ m, a m = algebraMap O (LetA O n) (c₀ m) * letE i + W.π₀ * a' m := by
    intro m
    funext j
    by_cases hj : j = i
    · subst hj
      have e1 : a m j = substAlgHom hs (F m j) := by rw [hF m j, coe_substAlgHom]; rfl
      rw [e1]
      conv_lhs => rw [eq_shift_mul_X_add_const (F m j)]
      rw [map_add, map_mul, substAlgHom_X hs]
      have e2 : substAlgHom hs (C (constantCoeff (F m j))) = C (constantCoeff (F m j)) := by
        rw [coe_substAlgHom, subst_C]
        rfl
      rw [e2]
      show _ = (algebraMap O (LetA O n) (c₀ m)) j * (letE (O := O) j : LetA O n) j + W.π₀ j * a' m j
      have e3 : (algebraMap O (LetA O n) (c₀ m)) j = C (c₀ m) := rfl
      simp only [e3, letE, a', g, c₀, Pi.single_eq_same, mul_one]
      show _ = C (constantCoeff (F m j)) + W.π₀₁ * _
      ring
    · simp only [Pi.add_apply, Pi.mul_apply, letE, Pi.single_apply, hj, if_false, mul_zero, a', zero_add, hzero m j hj]
  have h1 : ∀ m, W.π₀ * a' m = a m - algebraMap O (LetA O n) (c₀ m) * letE i := by
    intro m
    rw [key m]
    ring
  refine ⟨c₀, ∑ m, a' m • b m, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact Submodule.sum_mem _ fun m _ => (W.N T).smul_mem _ (hb.1 m).1.1
  · intro δ hδ
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Formalism.MainNotions.N.FrobeniusPowerSeries.GS.γD_smulA, (hb.1 m).1.2 δ hδ]
    congr 1
    apply cancel_π₀ hR
    calc W.π₀ * W.γA δ (a' m) = W.γA δ (W.π₀ * a' m) := by
          rw [map_mul, Formalism.MainNotions.N.FrobeniusPowerSeries.GS.π₀_mem W δ hδ]
      _ = W.γA δ (a m - algebraMap O (LetA O n) (c₀ m) * letE i) := by rw [h1]
      _ = a m - algebraMap O (LetA O n) (c₀ m) * letE i := by
          rw [map_sub, map_mul, (haA m).1 δ hδ, AlgHom.commutes, Formalism.MainNotions.N.FrobeniusPowerSeries.GS.γA_letE]
      _ = W.π₀ * a' m := (h1 m).symm
  · refine ⟨∑ m, a' m • b m, Submodule.sum_mem _ fun m _ => (W.N T).smul_mem _ (hb.1 m).1.1, ?_⟩
    show (letE i : LetA O n) • (∑ m, a' m • b m) = ∑ m, a' m • b m
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_smul]
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj
      simp [letE, a']
    · simp [letE, a', hj]
  · rw [hxa]
    simp only [Formalism.MainNotions.LiftingTheory.vecB]
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hlet : (letE i : LetA O n) • b m = b m := Formalism.MainNotions.N.FrobeniusPowerSeries.TypesD.nl_letter W (hb.1 m).2
    rw [key m, add_smul, mul_smul, hlet, algebraMap_smul, mul_smul]

end Formalism.MainNotions.N.FrobeniusPowerSeries.DYAa
