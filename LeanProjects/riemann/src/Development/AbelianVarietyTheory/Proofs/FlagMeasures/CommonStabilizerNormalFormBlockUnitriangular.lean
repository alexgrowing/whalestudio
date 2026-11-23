import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormFlagZeroMiddleInverseMinorOrthogonal
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MapConjLebesgueCommonStabilizerNormalForm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerSetEqRangeNormalFormStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerHaarUnimodularNormalStatement

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.StabNormal

variable {k r : ℕ}

theorem xstJ_self : XstJ k r r = Xst k r := by
  unfold XstJ Xst
  congr 1
  ext v
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.1, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨a, a.2⟩, rfl⟩

theorem isNormal0_iff {β : Fin r → ℕ} {g : Mat k r} (z' : Fin (2 * r + k + 1) → ℂ) :
    IsNormal0 k r le_rfl β 1 (g *ᵥ z') z' g ↔ IsNormal k r β g := by
  constructor
  · rintro ⟨hg, -, -, -, -, hX, -, hB⟩
    refine ⟨hg, fun a => ?_, hB⟩
    rw [← xstJ_self]
    exact hX a a.2
  · rintro ⟨hg, hX, hB⟩
    refine ⟨hg, by simp, by simp, hB.1, fun a b hb => absurd b.2 (not_lt.2 hb), fun a _ => ?_,
      fun a ha => absurd a.2 (not_lt.2 ha), hB⟩
    rw [xstJ_self]
    exact hX a

theorem pTop_self (q : PTop k r r) : pTop k r r q = 1 := by
  have h1 : (fun a : Fin r => if h : r ≤ a.val then q.1 ⟨a, h⟩ else 0) = 0 :=
    funext fun a => dif_neg (not_le.2 a.2)
  have h2 : (fun p : UT r => if h : r ≤ p.1.1.val then q.2.1 ⟨p, h⟩ else 0) = 0 :=
    funext fun p => dif_neg (not_le.2 p.1.1.2)
  have h3 : (fun a : Fin r => if h : r ≤ a.val then q.2.2 ⟨a, h⟩ else 0) = 0 :=
    funext fun a => dif_neg (not_le.2 a.2)
  have hs : skewM (0 : UT r → ℂ) (0 : Fin r → ℝ) = 0 := by
    ext a b
    simp only [skewM]
    split_ifs <;> simp
  show pEl k r (fun a : Fin r => if h : r ≤ a.val then q.1 ⟨a, h⟩ else 0)
      (skewM (fun p : UT r => if h : r ≤ p.1.1.val then q.2.1 ⟨p, h⟩ else 0)
        (fun a : Fin r => if h : r ≤ a.val then q.2.2 ⟨a, h⟩ else 0)) = 1
  rw [h1, h2, h3, hs]
  exact Rad.pEl_zero

theorem rEl_self (β : Fin r → ℕ) (q : (UTin β → ℂ) × PTop k r r) : rEl k r r β q = uEmb k r (upperIn β q.1) := by
  show uEmb k r (upperIn β q.1) * pTop k r r q.2 = _
  rw [pTop_self, mul_one]

theorem range_rEl (β : Fin r → ℕ) :
    Set.range (rEl k r r β) = Set.range fun x : UTin β → ℂ => uEmb k r (upperIn β x) := by
  ext m
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q.1, (rEl_self β q).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨(x, 0), rEl_self β (x, 0)⟩

theorem volume_pTop : (volume : Measure (PTop k r r)) Set.univ = 1 := by
  haveI : IsEmpty {a : Fin r // r ≤ a.val} := ⟨fun a => absurd a.2 (not_le.2 a.1.2)⟩
  haveI : IsEmpty {p : UT r // r ≤ p.1.1.val} := ⟨fun p => absurd p.2 (not_le.2 p.1.1.1.2)⟩
  rw [← Set.univ_prod_univ, Measure.volume_eq_prod, Measure.prod_prod, ← Set.univ_prod_univ,
    Measure.volume_eq_prod, Measure.prod_prod]
  simp [volume_pi, Measure.pi_univ]

theorem lebesgueCommonStabilizerNormalForm_full_eq (β : Fin r → ℕ) : lebR0 k r r β = lebR k r β := by
  have hc : Continuous fun x : UTin β → ℂ => Matrix.of.symm (uEmb k r (upperIn β x)) := by
    have h := (RConj.continuous_rEl (k := k) (r := r) r β).comp
      (continuous_id.prodMk (continuous_const : Continuous fun _ : UTin β → ℂ => (0 : PTop k r r)))
    refine continuous_pi fun i => continuous_pi fun j => ?_
    have := h.matrix_elem i j
    simpa [Function.comp_def, rEl_self] using this
  have hf : (fun q : (UTin β → ℂ) × PTop k r r => Matrix.of.symm (rEl k r r β q)) =
      (fun x : UTin β → ℂ => Matrix.of.symm (uEmb k r (upperIn β x))) ∘ Prod.fst := by
    funext q
    simp [rEl_self]
  rw [lebR0, lebR, hf, ← Measure.map_map hc.measurable measurable_fst, Measure.volume_eq_prod,
    Measure.map_fst_prod, volume_pTop, one_smul]

theorem tz_last : 0 < Tz k r (bvec (wI k r (Fin.last k))) := by
  have hv : (wI k r (Fin.last k)).val = r + k := rfl
  have hH : Hpk k r (wI k r (Fin.last k)) (wI k r (Fin.last k)) = -1 := by
    unfold Hpk
    rw [hv]
    simp
  have he : herm (Hpk k r) (bvec (wI k r (Fin.last k))) (bvec (wI k r (Fin.last k))) =
      Hpk k r (wI k r (Fin.last k)) (wI k r (Fin.last k)) := by
    simp [herm, bvec, Matrix.mulVec_single, dotProduct, Pi.single_apply]
  unfold Tz
  rw [he, hH]
  norm_num

theorem stabiliser_normal : ∀ (k r : ℕ) (g₀ : Mat k r) (β : Fin r → ℕ), IsNormal k r β g₀ → Rset k r g₀ = Set.range (fun x : UTin β → ℂ => uEmb k r (upperIn β x)) ∧ IsClosedSub k r (Rset k r g₀) ∧ IsHaarOn (Rset k r g₀) (lebR k r β) ∧ IsUnimod (Rset k r g₀) (lebR k r β) ∧ IsNormal k r β g₀⁻¹ ∧ (lebR k r β).map (conjM g₀) = lebR k r β := by
  intro k r g₀ β hN
  obtain ⟨w, hw⟩ : ∃ w : Fin (2 * r + k + 1) → ℂ, w = bvec (wI k r (Fin.last k)) := ⟨_, rfl⟩
  have h0 : IsNormal0 k r le_rfl β 1 (g₀ *ᵥ w) w g₀ := (isNormal0_iff w).2 hN
  have hwW : inWb k r w := hw ▸ NfMid.inWb_bvec _
  have hzW : inWb k r (g₀ *ᵥ w) := NfMid.inWb_mulVec h0 hwW
  have hT : 0 < Tz k r (g₀ *ᵥ w) := by
    rw [← NfMid.tz_eq h0, hw]
    exact tz_last
  obtain ⟨hR, hC⟩ := GlobalTheory.T.commonStabilizerSet_eq_range_normalForm k r r le_rfl (g₀ *ᵥ w) w g₀ β 1 hzW hwW hT h0
  obtain ⟨hH, hU⟩ := GlobalTheory.T.stabilizer_haar_unimodular_normal k r r le_rfl (g₀ *ᵥ w) w g₀ β 1 hzW hwW hT h0
  have hM := RConj.lebR0_map_conjM_eq_of_isNormalZero k r r le_rfl (g₀ *ᵥ w) w g₀ β 1 hzW hwW hT h0
  rw [lebesgueCommonStabilizerNormalForm_full_eq] at hH hU hM
  rw [range_rEl] at hR
  refine ⟨hR, hC, hH, hU, ?_, hM⟩
  have hi := NfMid.isNormal0_inv h0
  rw [inv_one] at hi
  have hback : g₀⁻¹ *ᵥ (g₀ *ᵥ w) = w := NfMid.inv_mul_vec hN.1 w
  have hi' : IsNormal0 k r le_rfl β 1 (g₀⁻¹ *ᵥ (g₀ *ᵥ w)) (g₀ *ᵥ w) g₀⁻¹ := by
    rw [hback]
    exact hi
  exact (isNormal0_iff (g₀ *ᵥ w)).1 hi'

end GlobalTheory.Amp.StabNormal
