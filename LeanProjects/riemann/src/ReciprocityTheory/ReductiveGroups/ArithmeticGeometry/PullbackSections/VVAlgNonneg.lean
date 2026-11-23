import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProof

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open Formalism.L2.Pj IsDedekindDomain

theorem vV_alg_nonneg (T : CDVR) (r : T.V) : 0 ≤ vV T.V (algebraMap T.V T.Fr r) := by
  unfold vV valV
  have h := HeightOneSpectrum.valuation_le_one (K := T.Fr) (IsDiscreteValuationRing.maximalIdeal T.V) r
  generalize (HeightOneSpectrum.valuation T.Fr (IsDiscreteValuationRing.maximalIdeal T.V))
    ((algebraMap T.V T.Fr) r) = x at h ⊢
  induction x using WithZero.recZeroCoe with
  | zero => simp
  | coe a =>
    have ha : a ≤ 1 := WithZero.coe_le_one.mp h
    have hl : (↑a : WithZero (Multiplicative ℤ)).log = Multiplicative.toAdd a := by
      simp [WithZero.log]
    rw [hl]
    have h2 : Multiplicative.toAdd a ≤ 0 := ha
    omega

variable {T T' : CDVR} (iT : T.Fr →+* T'.Fr) {e' : ℕ}
  (hv : ∀ a : T.Fr, a ≠ 0 → vV T'.V (iT a) = (e' : ℤ) * vV T.V a)

include hv in
theorem iT_int (r : T.V) : iT (algebraMap T.V T.Fr r) ∈ (algebraMap T'.V T'.Fr).range := by
  have key : ∀ x : T'.Fr, 0 ≤ vV T'.V x → x ∈ (algebraMap T'.V T'.Fr).range := by
    intro x hx
    unfold vV valV at hx
    have hle : (HeightOneSpectrum.valuation T'.Fr (IsDiscreteValuationRing.maximalIdeal T'.V)) x ≤ 1 := by
      generalize (HeightOneSpectrum.valuation T'.Fr (IsDiscreteValuationRing.maximalIdeal T'.V)) x = y at hx ⊢
      induction y using WithZero.recZeroCoe with
      | zero => exact zero_le'
      | coe a =>
        have hl : (↑a : WithZero (Multiplicative ℤ)).log = Multiplicative.toAdd a := by
          simp [WithZero.log]
        rw [hl] at hx
        have h2 : Multiplicative.toAdd a ≤ 0 := by omega
        exact WithZero.coe_le_one.mpr h2
    apply HeightOneSpectrum.mem_integers_of_valuation_le_one
    intro w
    have hw : w = IsDiscreteValuationRing.maximalIdeal T'.V := by
      ext1
      rw [IsLocalRing.eq_maximalIdeal w.isMaximal,
        IsLocalRing.eq_maximalIdeal (IsDiscreteValuationRing.maximalIdeal T'.V).isMaximal]
    rw [hw]
    exact hle
  by_cases hr : algebraMap T.V T.Fr r = 0
  · rw [hr, map_zero]
    exact zero_mem _
  · apply key
    rw [hv _ hr]
    exact mul_nonneg (by positivity) (vV_alg_nonneg T r)

def eqV (T' : CDVR) : T'.V ≃+* (algebraMap T'.V T'.Fr).range :=
  RingEquiv.ofBijective (algebraMap T'.V T'.Fr).rangeRestrict
    ⟨fun a b h => IsFractionRing.injective T'.V T'.Fr (congrArg Subtype.val h),
      (algebraMap T'.V T'.Fr).rangeRestrict_surjective⟩

def phiV : T.V →+* T'.V :=
  (eqV T').symm.toRingHom.comp ((iT.comp (algebraMap T.V T.Fr)).codRestrict _ (iT_int iT hv))

end ReciprocityTheory.ChartRestriction.G.PullbackSections
