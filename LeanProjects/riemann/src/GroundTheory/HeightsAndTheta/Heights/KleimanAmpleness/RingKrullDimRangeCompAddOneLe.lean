import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLastTail
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocalRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver chartRingOver mConeMapOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim ringKrullDim_eq_of_relDim)

noncomputable section

section RangeDim

variable {F A T T' : Type*} [CommRing F] [CommRing A] [CommRing T] [CommRing T'] [Algebra F A] [Algebra F T]
  [Algebra F T']

def rangeCompMap (φ : A →ₐ[F] T) (ψ : T →ₐ[F] T') : φ.range →ₐ[F] (ψ.comp φ).range :=
  (ψ.comp φ.range.val).codRestrict _ (by rintro ⟨_, a, rfl⟩; exact ⟨a, rfl⟩)

theorem rangeCompMap_surjective (φ : A →ₐ[F] T) (ψ : T →ₐ[F] T') :
    Function.Surjective (rangeCompMap φ ψ) := by
  rintro ⟨_, a, rfl⟩
  exact ⟨⟨φ a, a, rfl⟩, rfl⟩

theorem ringKrullDim_range_comp_add_one_le [IsDomain T] (φ : A →ₐ[F] T) (ψ : T →ₐ[F] T') (a : A)
    (ha : φ a ≠ 0) (hψ : ψ (φ a) = 0) :
    ringKrullDim (ψ.comp φ).range + 1 ≤ ringKrullDim φ.range := by
  let r : φ.range := ⟨φ a, a, rfl⟩
  have hr : r ∈ nonZeroDivisors φ.range :=
    mem_nonZeroDivisors_of_ne_zero fun h => ha (congrArg Subtype.val h)
  let χ := (rangeCompMap φ ψ).toRingHom
  have hχr : ∀ b ∈ Ideal.span {r}, χ b = 0 := by
    intro b hb
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hb
    rw [map_mul]
    have : χ r = 0 := Subtype.ext hψ
    rw [this, mul_zero]
  have h1 := ringKrullDim_le_of_surjective _
    (Ideal.Quotient.lift_surjective_of_surjective _ hχr (rangeCompMap_surjective φ ψ))
  exact (add_le_add h1 le_rfl).trans (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr)

end RangeDim

section Chart

variable {F : Type} [Field F] {K : Type} [DecidableEq K] {ι : K → Type} {Ω : Type} [Field Ω]
  [Algebra F Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k)

def partDehom (s : Finset K) : MvPolynomial (Σ k, ι k) F →ₐ[F] MvPolynomial K Ω :=
  aeval fun p => if p.1 ∈ s then C (y p / y ⟨p.1, c p.1⟩) else C (y p) * X p.1

def subst1 (k : K) : MvPolynomial K Ω →ₐ[F] MvPolynomial K Ω :=
  (aeval fun j => if j = k then C (y ⟨k, c k⟩)⁻¹ else X j : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω).restrictScalars F

theorem subst1_comp {s : Finset K} {k : K} (hk : k ∉ s) :
    (subst1 (F := F) y c k).comp (partDehom y c s) = partDehom y c (insert k s) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨j, i⟩
  simp only [partDehom, subst1, AlgHom.comp_apply, aeval_X, Finset.mem_insert]
  by_cases hj : j ∈ s
  · have : j ≠ k := fun h => hk (h ▸ hj)
    simp [hj]
  · by_cases hjk : j = k
    · subst hjk
      simp only [hj, if_false, if_true, AlgHom.restrictScalars_apply, map_mul, aeval_C, aeval_X]
      rw [div_eq_mul_inv, C_mul]
      simp
    · simp [hj, hjk]

theorem partDehom_empty : partDehom (F := F) y c ∅ = mConeMapOver F y := by
  apply MvPolynomial.algHom_ext
  intro p
  simp [partDehom, mConeMapOver]

theorem ringKrullDim_partDehom_insert (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {s : Finset K} {k : K} (hk : k ∉ s) :
    ringKrullDim (partDehom (F := F) y c (insert k s)).range + 1 ≤ ringKrullDim (partDehom (F := F) y c s).range := by
  have key := ringKrullDim_range_comp_add_one_le (partDehom (F := F) y c s) (subst1 y c k) (X ⟨k, c k⟩ - 1) ?_ ?_
  · rwa [subst1_comp y c hk] at key
  · intro h
    have h' := congrArg constantCoeff h
    simp [partDehom, hk] at h'
  · rw [← AlgHom.comp_apply, subst1_comp y c hk]
    simp [partDehom, hc k]

theorem chartRingOver_eq_range [Fintype K] :
    chartRingOver F y c = (((aeval fun _ => (0 : Ω) : MvPolynomial K Ω →ₐ[Ω] Ω).restrictScalars F).comp
      (partDehom (F := F) y c Finset.univ)).range := by
  rw [chartRingOver, Algebra.adjoin_range_eq_range_aeval]
  congr 1
  apply MvPolynomial.algHom_ext
  intro p
  simp [partDehom]

end Chart

theorem le_zero_of_add_natCast_le {d : WithBot ℕ∞} {n : ℕ} (h : d + n ≤ n) : d ≤ 0 := by
  induction d using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => exact absurd h (by norm_cast)
    | coe e =>
      have h' : ((e + n : ℕ) : WithBot ℕ∞) ≤ ((n : ℕ) : WithBot ℕ∞) := by exact_mod_cast h
      have h'' : e + n ≤ n := by exact_mod_cast h'
      have : e = 0 := by omega
      subst this
      simp

theorem PointChartField.full : PointChartField.Statement := by
  intro F _ K _ _ ι Ω _ _ y hdim c hc
  have h0 : ringKrullDim (partDehom (F := F) y c ∅).range = (Fintype.card K : WithBot ℕ∞) := by
    rw [partDehom_empty, ← ringKrullDim_eq_of_ringEquiv (Ideal.quotientKerEquivRange _).toRingEquiv]
    have := ringKrullDim_eq_of_relDim (Q := mIdealOver F y) (m := 0) hdim
    rw [Nat.zero_add] at this
    exact this
  have hstep : ∀ s : Finset K,
      ringKrullDim (partDehom (F := F) y c s).range + (s.card : WithBot ℕ∞) ≤ Fintype.card K := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [h0]
    | insert k s hk ih =>
      rw [Finset.card_insert_of_notMem hk, Nat.cast_add, Nat.cast_one, add_comm ((s.card : ℕ) : WithBot ℕ∞) 1,
        ← add_assoc]
      exact (add_le_add (ringKrullDim_partDehom_insert y c hc hk) le_rfl).trans ih
  have hu := hstep Finset.univ
  rw [Finset.card_univ] at hu
  have hle : ringKrullDim (chartRingOver F y c) ≤ 0 := by
    rw [chartRingOver_eq_range]
    exact (ringKrullDim_le_of_surjective _ (rangeCompMap_surjective _ _)).trans (le_zero_of_add_natCast_le hu)
  have : Ring.KrullDimLE 0 (chartRingOver F y c) := Ring.krullDimLE_iff.mpr (by simpa using hle)
  exact Ring.KrullDimLE.isField_of_isDomain

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
