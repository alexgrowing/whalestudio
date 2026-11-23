import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylCellStabilizerMeasureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusConjugationWeylCell
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCompactSecondCountable
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactUnitaryIntegralPoints

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG
open scoped NNReal ENNReal

noncomputable section

namespace GlobalTheory

namespace GKConjScale

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem v_eq_ofAdd_ordL {x : L} (hx : x ≠ 0) :
    Valued.v x = ((Multiplicative.ofAdd (-ordL x) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  have h : Valued.v x ≠ 0 := by simpa using hx
  unfold ordL
  rw [dif_neg h, neg_neg, ofAdd_toAdd, WithZero.coe_unzero]

theorem coe_mul_le_iff (g h : Multiplicative ℤ) (x : WithZero (Multiplicative ℤ)) :
    (g : WithZero (Multiplicative ℤ)) * x ≤ h ↔ x ≤ ((g⁻¹ * h : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  constructor
  · intro H
    calc x = ((g⁻¹ : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) * (g * x) := by
          rw [← mul_assoc, ← WithZero.coe_mul, inv_mul_cancel, WithZero.coe_one, one_mul]
      _ ≤ ((g⁻¹ : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) * h := by gcongr
      _ = _ := by rw [WithZero.coe_mul]
  · intro H
    calc (g : WithZero (Multiplicative ℤ)) * x ≤ g * ((g⁻¹ * h : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
          by gcongr
      _ = h := by rw [WithZero.coe_mul, ← mul_assoc, ← WithZero.coe_mul, mul_inv_cancel, WithZero.coe_one, one_mul]

variable {n : ℕ}

theorem inv_offdiag {σ : L →+* L} (t : GU σ n)
    (ht : ∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) (i j : Fin n) (hij : i ≠ j) :
    (((t⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0 := by
  rw [Subgroup.coe_inv, (GlobalTheory.LGrp.mem_GU_iff σ n _).1 t.2 i j,
    ht _ _ (fun h => hij (Fin.rev_injective h).symm), map_zero]

open GlobalTheory.WeylCell in

theorem conjScale : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 →
    Even n → ∀ (y : GU σ n), y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ [MeasurableSpace (cellU y)] [BorelSpace (cellU y)] (μ : Measure (cellU y)) [μ.IsHaarMeasure],
    μ ((KU σ n).subgroupOf (cellU y)) = 1 → ∀ (t : GU σ n),
    (∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) →
    (∀ F : GU σ n → ℂ, ∫ u : cellU y, F (t⁻¹ * u * t) ∂μ =
        (q : ℂ) ^ (-2 * ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k))) *
          ∫ u : cellU y, F u ∂μ) ∧
    ∀ F : GU σ n → ENNReal, ∫⁻ u : cellU y, F (t⁻¹ * u * t) ∂μ =
        (q : ENNReal) ^ (-2 * ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k))) *
          ∫⁻ u : cellU y, F u ∂μ := by
  intro L _ _ _ _ ϖ σ q hU n k hk hn y hyK hy _ _ μ _ hμ t ht
  haveI : SecondCountableTopology L := (GlobalTheory.LineUMod.locCompact_secondCountable hU).2
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) L) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → L))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) L)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) L)).symm.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin n) L) := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : SecondCountableTopology (GU σ n) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SecondCountableTopology (cellU y) := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨hKo, hKc⟩ := GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU L ϖ σ q n hU
  haveI : LocallyCompactSpace (cellU y) := by
    have hN : IsClosed (cellU y : Set (GU σ n)) := (isClosed_cell _).preimage continuous_subtype_val
    have h1 : IsOpen ((KU σ n).subgroupOf (cellU y) : Set (cellU y)) := hKo.preimage continuous_subtype_val
    have h2 : IsCompact ((KU σ n).subgroupOf (cellU y) : Set (cellU y)) :=
      hN.isClosedEmbedding_subtypeVal.isCompact_preimage hKc
    exact h2.locallyCompactSpace_of_mem_nhds_of_group (h1.mem_nhds (one_mem _))
  have htinv := inv_offdiag t ht
  have hdc := (GlobalTheory.WeylCell.diagConjU L σ n y _ hy t ht).2
  have hdc' := (GlobalTheory.WeylCell.diagConjU L σ n y _ hy t⁻¹ htinv).2
  let c : cellU y ≃* cellU y :=
    { toFun := fun u => ⟨t⁻¹ * u * t, hdc u u.2⟩
      invFun := fun u => ⟨t * u * t⁻¹, by simpa using hdc' u u.2⟩
      left_inv := fun u => Subtype.ext (by simp [mul_assoc])
      right_inv := fun u => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hc : Continuous c :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  have hc' : Continuous c.symm :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  haveI : (μ.map c).IsHaarMeasure := MulEquiv.isHaarMeasure_map μ c hc hc'
  have hE : MeasurableEmbedding c := (Homeomorph.mk c.toEquiv hc hc').measurableEmbedding

  set T : Matrix (Fin n) (Fin n) L := ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hTd
  set a : Fin n := lo k with ha
  set r : ℤ := ordL (T a a) with hr
  have hσv : ∀ x, Valued.v (σ x) = Valued.v x := hU.2.1
  have hprod : σ (T a.rev a.rev) * T a a = 1 := by
    have hu := (GlobalTheory.LGrp.mem_GU_iff σ n (t : GL (Fin n) L)).1 t.2 a a
    have h := congrFun (congrFun (Units.inv_mul (t : GL (Fin n) L)) a) a
    rw [Matrix.mul_apply, Finset.sum_eq_single a] at h
    · rw [← hu, h, Matrix.one_apply_eq]
    · intro b _ hb; exact mul_eq_zero_of_right _ (ht b a hb)
    · simp
  have ha0 : T a a ≠ 0 := right_ne_zero_of_mul_eq_one hprod
  have hva : Valued.v (T a a) = ((Multiplicative.ofAdd (-r) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
    v_eq_ofAdd_ordL ha0
  have hva' : Valued.v (T a.rev a.rev) = ((Multiplicative.ofAdd r : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    have h := congrArg Valued.v hprod
    rw [map_mul, hσv, map_one, hva] at h
    rw [eq_inv_of_mul_eq_one_left h, ← WithZero.coe_inv, ← ofAdd_neg, neg_neg]

  let S : ℤ → Set (cellU y) := fun j => {u : cellU y |
    Valued.v ((((u : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a.rev) ≤
      ((Multiplicative.ofAdd j : Multiplicative ℤ) : WithZero (Multiplicative ℤ))}
  have hsh : ∀ j : ℤ, MeasurableSet (S j) ∧ μ (S j) = (q : ENNReal) ^ j := GlobalTheory.T.weyl_cell_stabilizer_measure L ϖ σ q hU n k hk hn y hyK hy μ hμ
  have hpre : c ⁻¹' S 0 = S (-2 * r) := by
    ext u
    simp only [S, Set.mem_preimage, Set.mem_setOf_eq]
    show Valued.v (((((t : GL (Fin n) L))⁻¹ * ((u : GU σ n) : GL (Fin n) L) * (t : GL (Fin n) L) : GL (Fin n) L) :
      Matrix (Fin n) (Fin n) L) a a.rev) ≤ _ ↔ _
    rw [gl_conj_apply_of_offdiag ht, map_mul, map_mul, map_inv₀, ← hTd, hva, hva', ← WithZero.coe_inv,
      mul_right_comm, ← WithZero.coe_mul, coe_mul_le_iff]
    have e : ((Multiplicative.ofAdd (-r))⁻¹ * Multiplicative.ofAdd r)⁻¹ * Multiplicative.ofAdd (0 : ℤ) =
        (Multiplicative.ofAdd (-2 * r) : Multiplicative ℤ) := by
      apply Multiplicative.toAdd.injective
      simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd]
      ring
    rw [e]
  have hq0 : q ≠ 0 := by have := hU.2.2.2.2.2.1; omega
  set Q : ℝ≥0 := (q : ℝ≥0) ^ (-2 * r) with hQd
  have hQ : (Q : ℝ≥0∞) = (q : ℝ≥0∞) ^ (-2 * r) := by
    rw [hQd, ENNReal.coe_zpow (by exact_mod_cast hq0)]
    simp
  have hmap : μ.map c (S 0) = (q : ℝ≥0∞) ^ (-2 * r) := by
    rw [Measure.map_apply hE.measurable (hsh 0).1, hpre, (hsh _).2]
  have hS0 : μ (S 0) = 1 := by rw [(hsh 0).2, zpow_zero]
  have e := Measure.isMulLeftInvariant_eq_smul (μ.map c) μ
  have hfac : Measure.haarScalarFactor (μ.map c) μ = Q := by
    have h := congrArg (fun ν : Measure (cellU y) => ν (S 0)) e
    simp only [Measure.smul_apply, hS0, hmap, ENNReal.smul_def, smul_eq_mul, mul_one] at h
    exact ENNReal.coe_injective (h.symm.trans hQ.symm)
  have hmu : μ.map c = Q • μ := e.trans (by rw [hfac])
  refine ⟨fun F => ?_, fun F => ?_⟩
  · refine (hE.integral_map (fun v : cellU y => F v)).symm.trans ?_
    rw [hmu, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
    congr 1
    rw [hQd]
    push_cast
    rfl
  · refine (hE.lintegral_map (fun v : cellU y => F v)).symm.trans ?_
    rw [hmu, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul, hQ]

end GKConjScale

end GlobalTheory
