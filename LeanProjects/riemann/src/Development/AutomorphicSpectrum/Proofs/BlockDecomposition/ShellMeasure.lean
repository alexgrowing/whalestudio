import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemShellUIffDepth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylCellStabilizerMeasure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalWeylCellTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusConjugationWeylCell
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylCellStabilizerMeasureTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCellUAbsorbUnip
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell
open scoped NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.InvStep

open GlobalTheory.ShellU GlobalTheory.GKConjScale GlobalTheory.UnipShiftU

theorem shell_measure' : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 →
    Even n → ∀ (y : GU σ n), y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ [MeasurableSpace (cellU y)] [BorelSpace (cellU y)] (μ : Measure (cellU y)) [μ.IsHaarMeasure],
    μ ((KU σ n).subgroupOf (cellU y)) = 1 → ∀ (j : ℤ),
    MeasurableSet {u : cellU y | Valued.v ((((u : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev) ≤
        ((Multiplicative.ofAdd j : Multiplicative ℤ) : WithZero (Multiplicative ℤ))} ∧
    μ {u : cellU y | Valued.v ((((u : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev) ≤
        ((Multiplicative.ofAdd j : Multiplicative ℤ) : WithZero (Multiplicative ℤ))} = (q : ENNReal) ^ j := by
  intro L _ _ _ ϖ σ q hU n k hk hn y hyK hy _ _ μ _ hμ j
  have hidx := relIndex_antiBall hU
  obtain ⟨-, -, -, hv, -, hq2, -⟩ := hU
  have haa : lo k ≠ (lo k).rev := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_rev, Fin.coe_castLE] at this
    have := k.2
    omega
  have hshape := cellU_rankOne_shape L σ n k hk hn y hy
  set a := lo k with ha
  let M : cellU y → Matrix (Fin n) (Fin n) L := fun u => (((u : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
  let c : cellU y → L := fun u => M u a a.rev
  have hstr : ∀ u : cellU y, M u = 1 + Matrix.single a a.rev (c u) := by
    intro u
    ext i l
    rw [Matrix.add_apply, Matrix.single_apply]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      rw [Matrix.one_apply_ne haa, zero_add]
    · rw [add_zero]
      exact (hshape u).1 u.2 i l (fun h' => h ⟨h'.1.symm, h'.2.symm⟩)
  have hprod : ∀ b d : L, (1 + Matrix.single a a.rev b) * (1 + Matrix.single a a.rev d) =
      1 + Matrix.single a a.rev (b + d) := by
    intro b d
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.single_mul_single_of_ne _ _ _ _ haa.symm,
      Matrix.single_add]
    simp only [Matrix.one_mul, Matrix.mul_one, add_zero]
    abel
  have hent : ∀ b : L, (1 + Matrix.single a a.rev b : Matrix (Fin n) (Fin n) L) a a.rev = b := by
    intro b
    rw [Matrix.add_apply, Matrix.one_apply_ne haa, Matrix.single_apply_same, zero_add]
  have hM : ∀ u w : cellU y, M (u * w) = M u * M w := fun u w => rfl
  have hmul : ∀ u w : cellU y, c (u * w) = c u + c w := by
    intro u w
    show M (u * w) a a.rev = c u + c w
    rw [hM, hstr u, hstr w, hprod, hent]
  have hone : c 1 = 0 := Matrix.one_apply_ne haa
  have hinv : ∀ u, c u⁻¹ = -c u := fun u => by
    have := hmul u⁻¹ u
    rw [inv_mul_cancel, hone] at this
    linear_combination -this
  have hanti : ∀ u, σ (c u) = -c u := fun u => by
    have := (LGrp.mem_GU_iff σ n _).1 (u : GU σ n).2 a a.rev
    rw [Fin.rev_rev] at this
    rw [← hinv]
    exact this.symm
  have hsurj : ∀ b : L, σ b = -b → ∃ u : cellU y, c u = b := by
    intro b hb
    let g : GL (Fin n) L := ⟨1 + Matrix.single a a.rev b, 1 + Matrix.single a a.rev (-b),
      by rw [hprod]; simp, by rw [hprod]; simp⟩
    have hg : g ∈ GU σ n := by
      rw [LGrp.mem_GU_iff]
      intro i l
      show (1 + Matrix.single a a.rev (-b) : Matrix (Fin n) (Fin n) L) i l =
        σ ((1 + Matrix.single a a.rev b : Matrix (Fin n) (Fin n) L) l.rev i.rev)
      rw [Matrix.add_apply, Matrix.add_apply, map_add, Matrix.one_apply, Matrix.one_apply, Matrix.single_apply,
        Matrix.single_apply, apply_ite σ, apply_ite σ, map_one, map_zero, hb]
      congr 1
      · exact if_congr (by rw [Fin.rev_inj, eq_comm]) rfl rfl
      · refine if_congr ?_ rfl rfl
        rw [Fin.rev_inj, and_comm, Fin.rev_eq_iff]
    refine ⟨⟨⟨g, hg⟩, (hshape _).2 fun i l h => ?_⟩, hent b⟩
    show (1 + Matrix.single a a.rev b : Matrix (Fin n) (Fin n) L) i l = _
    rw [Matrix.add_apply, Matrix.single_apply, if_neg (fun h' => h ⟨h'.1.symm, h'.2.symm⟩), add_zero]
  let φ : cellU y →* Multiplicative L :=
    { toFun := fun u => Multiplicative.ofAdd (c u)
      map_one' := by simp only [hone]; rfl
      map_mul' := fun u w => by simp only [hmul]; rfl }
  let H : ℤ → Subgroup (cellU y) := fun j => (AddSubgroup.toSubgroup (antiBall σ j)).comap φ
  have memH : ∀ j (u : cellU y), u ∈ H j ↔ Valued.v (c u) ≤ WithZero.exp j := by
    intro j u
    show (c u) ∈ antiBall σ j ↔ _
    rw [mem_antiBall]
    exact ⟨fun h => h.2, fun h => ⟨hanti u, h⟩⟩
  have hset : ∀ j, (H j : Set (cellU y)) = c ⁻¹' {x : L | Valued.v x ≤ WithZero.exp j} :=
    fun j => Set.ext (memH j)
  have hc : Continuous c :=
    (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)).matrix_elem a a.rev
  have hm : ∀ j, MeasurableSet (H j : Set (cellU y)) := fun j => by
    rw [hset]
    exact ((isOpen_ball hv j).preimage hc).measurableSet
  have hle : ∀ j, H j ≤ H (j + 1) := fun j u hu =>
    (memH _ _).2 (((memH _ _).1 hu).trans (WithZero.exp_le_exp.2 (by omega)))
  have hi : ∀ j, (H j).relIndex (H (j + 1)) = q := fun j => by
    show ((AddSubgroup.toSubgroup (antiBall σ j)).comap φ).relIndex
      ((AddSubgroup.toSubgroup (antiBall σ (j + 1))).comap φ) = q
    rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self, AddSubgroup.relIndex_toSubgroup, hidx]
    intro b hb
    obtain ⟨u, hu⟩ := hsurj (Multiplicative.toAdd b) hb.1
    exact ⟨u, congrArg Multiplicative.ofAdd hu⟩
  have hint : ∀ u : cellU y, Valued.v (c u) ≤ 1 → ∀ i l, M u i l ∈ intL L := by
    intro u hu i l
    rw [hstr u, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    refine add_mem ?_ ?_ <;> split_ifs
    · exact one_mem _
    · exact zero_mem _
    · exact hu
    · exact zero_mem _
  have hH0 : H 0 = (KU σ n).subgroupOf (cellU y) := by
    ext u
    rw [memH, WithZero.exp_zero, Subgroup.mem_subgroupOf, ← SetLike.mem_coe, LFun.IntPtsUnitary.coe_KU,
      LFun.IntPtsUnitary.coe_GLint]
    constructor
    · intro h
      exact ⟨hint u h, hint u⁻¹ (by rwa [hinv, Valuation.map_neg])⟩
    · intro h
      exact h.1 a a.rev
  have hfin := measure_chain μ H (q := q) (by omega) hm hle hi (by rw [hH0]; exact hμ) j
  have hmj := hm j
  rw [hset] at hfin hmj
  exact ⟨hmj, hfin⟩

theorem conjScale' : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
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
  intro L _ _ _ ϖ σ q hU n k hk hn y hyK hy _ _ μ _ hμ t ht
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
  have hsh : ∀ j : ℤ, MeasurableSet (S j) ∧ μ (S j) = (q : ENNReal) ^ j := shell_measure' L ϖ σ q hU n k hk hn y hyK hy μ hμ
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

theorem shiftCore (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (q : ℕ) (n : ℕ)
    (a a' : Fin n) (hrev : a.rev = a') (haa : a'.val = a.val + 1) {m : ℕ} (α : Fin m → ℂ) (φ : GU σ n → ℂ)
    (hφ : ∀ b g : GU σ n, IsBorelU b → φ (b * g) = chiDeltaU q α b * φ g) (y : GU σ n) (hy : IsWeylRep (Equiv.swap a a') (y : GL (Fin n) L))
    (ν : GU σ n) (hν : IsUnipU ν) :
    ∃ u' ∈ cellU y, ∀ u ∈ cellU y, ∀ g : GU σ n, φ (y⁻¹ * u * ν * g) = φ (y⁻¹ * (u' * u) * g) := by
  have hne : a ≠ a' := fun e => by have := congrArg Fin.val e; omega
  have hlt : a < a' := by rw [Fin.lt_iff_val_lt_val]; omega
  have hrev' : a'.rev = a := by rw [← hrev, Fin.rev_rev]
  have hνB : (ν : GL (Fin n) L) ∈ unipB L (Fin n) := (mem_unipB L).2 ⟨hν.1, hν.2⟩
  set c : L := ((ν : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a' with hc
  have hσc : σ c = -c := by
    have h := (GlobalTheory.LGrp.mem_GU_iff σ n (ν : GL (Fin n) L)).1 ν.2 a a'
    rw [hrev', hrev, unipB_inv_apply_succ hνB haa] at h
    exact h.symm
  let T : GL (Fin n) L := ⟨Matrix.transvection a a' c, Matrix.transvection a a' (-c),
    (Matrix.transvection_mul_transvection_same a a' hne c (-c)).trans (by rw [add_neg_cancel, Matrix.transvection_zero]),
    (Matrix.transvection_mul_transvection_same a a' hne (-c) c).trans (by rw [neg_add_cancel, Matrix.transvection_zero])⟩
  have hTapp : ∀ (d : L) (i j : Fin n), Matrix.transvection a a' d i j =
      (if i = j then 1 else 0) + (if i = a ∧ j = a' then d else 0) := by
    intro d i j
    exact transvection_apply' a a' d i j
  have hT : ∀ i j, (T : Matrix (Fin n) (Fin n) L) i j =
      (if i = j then 1 else 0) + (if i = a ∧ j = a' then c else 0) := hTapp c
  have hTi : ∀ i j, ((T⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
      (if i = j then 1 else 0) + (if i = a ∧ j = a' then -c else 0) := hTapp (-c)
  have hTG : T ∈ GU σ n := by
    rw [GlobalTheory.LGrp.mem_GU_iff]
    intro i j
    rw [hTi, hT]
    have e1 : j.rev = i.rev ↔ i = j := by rw [Fin.rev_inj]; exact eq_comm
    have e2 : (j.rev = a ∧ i.rev = a') ↔ (i = a ∧ j = a') := by
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by rw [← Fin.rev_rev i, h2, hrev'], by rw [← Fin.rev_rev j, h1, hrev]⟩
      · rintro ⟨rfl, rfl⟩
        exact ⟨hrev', hrev⟩
    simp only [e1, e2]
    split_ifs with h1 h2 <;> simp_all
  have hTB : T ∈ unipB L (Fin n) := by
    refine (mem_unipB L).2 ⟨fun i j h => ?_, fun i => ?_⟩
    · rw [hT, if_neg (ne_of_lt h).symm, if_neg (fun e => by obtain ⟨rfl, rfl⟩ := e; exact absurd h (not_lt.2 hlt.le)), add_zero]
    · rw [hT, if_pos rfl, if_neg (fun h => hne (h.1.symm.trans h.2)), add_zero]
  have hback : ∀ i j, Equiv.swap a a' i = a → Equiv.swap a a' j = a' → i = a' ∧ j = a := by
    intro i j h1 h2
    exact ⟨by rw [← Equiv.swap_apply_self a a' i, h1, Equiv.swap_apply_left],
      by rw [← Equiv.swap_apply_self a a' j, h2, Equiv.swap_apply_right]⟩
  refine ⟨⟨T, hTG⟩, ?_, ?_⟩
  · show T ∈ cell (y : GL (Fin n) L)
    rw [mem_cell]
    refine ⟨hTB, mem_unipBLower.2 ⟨fun i j hij => ?_, fun i => ?_⟩⟩
    · rw [Units.val_mul, Units.val_mul, conj_apply hy, hT,
        if_neg (fun e => (ne_of_lt hij) ((Equiv.injective _) e)),
        if_neg (fun e => by
          obtain ⟨h1, h2⟩ := hback i j e.1 e.2
          rw [h1, h2] at hij
          exact absurd hij (not_lt.2 hlt.le))]
      simp
    · rw [Units.val_mul, Units.val_mul, conj_apply hy, hT, if_pos rfl,
        if_neg (fun h => hne (h.1.symm.trans h.2)), add_zero, mul_one, inv_mul_diag hy]
  · intro u hu g
    have huB : (u : GL (Fin n) L) ∈ unipB L (Fin n) := (mem_cell.1 hu).1
    set N : GL (Fin n) L := (u : GL (Fin n) L) * ν * (u : GL (Fin n) L)⁻¹ * T⁻¹ with hN
    have hNB : N ∈ unipB L (Fin n) :=
      mul_mem (mul_mem (mul_mem huB hνB) (inv_mem huB)) (inv_mem hTB)
    have hNa : (N : Matrix (Fin n) (Fin n) L) a a' = 0 := by
      rw [hN, unipB_mul_apply_succ (mul_mem (mul_mem huB hνB) (inv_mem huB)) (inv_mem hTB) haa,
        unipB_mul_apply_succ (mul_mem huB hνB) (inv_mem huB) haa, unipB_mul_apply_succ huB hνB haa,
        unipB_inv_apply_succ hTB haa, unipB_inv_apply_succ huB haa, hT, if_neg hne, if_pos ⟨rfl, rfl⟩]
      ring
    let b : GU σ n := y⁻¹ * u * ν * u⁻¹ * (⟨T, hTG⟩ : GU σ n)⁻¹ * y
    have hbG : (b : GL (Fin n) L) = (y : GL (Fin n) L)⁻¹ * N * y := by
      simp only [b, hN, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hbv : ∀ i j, ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
        ((y⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i (Equiv.swap a a' i) *
          (N : Matrix (Fin n) (Fin n) L) (Equiv.swap a a' i) (Equiv.swap a a' j) *
          ((y : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (Equiv.swap a a' j) j := by
      intro i j
      rw [hbG, Units.val_mul, Units.val_mul, conj_apply hy]
    have hbB : IsBorelU b := by
      intro i j hji
      rw [hbv]
      suffices h0 : (N : Matrix (Fin n) (Fin n) L) (Equiv.swap a a' i) (Equiv.swap a a' j) = 0 by
        rw [h0, mul_zero, zero_mul]
      rcases lt_trichotomy (Equiv.swap a a' i) (Equiv.swap a a' j) with h | h | h
      · obtain ⟨h1, h2⟩ := swap_inversion haa h (by rwa [Equiv.swap_apply_self, Equiv.swap_apply_self])
        rw [h1, h2]
        exact hNa
      · exact absurd ((Equiv.injective _) h) (ne_of_lt hji).symm
      · exact ((mem_unipB L).1 hNB).1 _ _ h
    have hbd : ∀ i, ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = 1 := by
      intro i
      rw [hbv, ((mem_unipB L).1 hNB).2, mul_one, inv_mul_diag hy]
    have hchi : chiDeltaU q α b = 1 := by
      unfold chiDeltaU
      apply Finset.prod_eq_one
      intro i _
      split_ifs
      · rw [hbd, ordL_one]
        simp
      · rfl
    have e : ∀ w : GU σ n, y⁻¹ * u * ν * g = (y⁻¹ * u * ν * u⁻¹ * w⁻¹ * y) * (y⁻¹ * (w * u) * g) :=
      fun w => by group
    have key := hφ b (y⁻¹ * (⟨T, hTG⟩ * u) * g) hbB
    rw [hchi, one_mul] at key
    rw [e ⟨T, hTG⟩]
    exact key

theorem shiftEven (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (q : ℕ) (n : ℕ)
    (k : Fin (n / 2)) (hk : ¬ k.val + 1 < n / 2) (hn : Even n) {m : ℕ} (α : Fin m → ℂ) (φ : GU σ n → ℂ)
    (hφ : ∀ b g : GU σ n, IsBorelU b → φ (b * g) = chiDeltaU q α b * φ g) (y : GU σ n)
    (hy : IsWeylRep (simpleU k) (y : GL (Fin n) L)) (ν : GU σ n) (hν : IsUnipU ν) :
    ∃ u' ∈ cellU y, ∀ u ∈ cellU y, ∀ g : GU σ n, φ (y⁻¹ * u * ν * g) = φ (y⁻¹ * (u' * u) * g) := by
  have hs : simpleU k = Equiv.swap (lo k) (lo k).rev := by simp only [simpleU, if_neg hk]
  rw [hs] at hy
  have haa : ((lo k).rev).val = (lo k).val + 1 := by
    obtain ⟨m, hm⟩ := hn
    have := k.2
    simp only [Fin.val_rev, lo, Fin.coe_castLE]
    omega
  exact shiftCore L σ q n (lo k) (lo k).rev rfl haa α φ hφ y hy ν hν

theorem shiftOdd : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ (α : Fin (n / 2) → ℂ) (φ : GU σ n → ℂ), (∀ b g : GU σ n, IsBorelU b → φ (b * g) = chiDeltaU q α b * φ g) →
    ∀ n' : GU σ n, IsUnipU n' → ∃ p : cellU y, ∀ (u : cellU y) (x : GU σ n),
      φ (y⁻¹ * (u : GU σ n) * n' * x) = φ (y⁻¹ * ((u * p : cellU y) : GU σ n) * x) := by
  intro L _ _ _ ϖ σ q hq n k hk hn y hyK hy α φ hφ n' hn'
  have hcell := mem_cellU_last_iff L ϖ σ q hq n k hk hn y hyK hy
  have hw : simpleU k = Equiv.swap (lo k) (lo k).rev := by simp [simpleU, hk]
  have hA := val_rev_lo_of_last k hk hn
  have hnB : (n' : GL (Fin n) L) ∈ unipB L (Fin n) := (mem_unipB L).2 hn'
  let p₀ : GU σ n := ⟨blockKeepGL (lo k) (lo k).rev _ hnB, blockKeepGL_mem_GU _ _ hnB n'.2⟩
  have hp₀ : ((p₀ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      blockKeep (lo k) (lo k).rev ((n' : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := rfl
  have hp : p₀ ∈ cellU y := by
    refine (hcell p₀).2 ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j hij hor => ?_⟩
    · rw [hp₀]; unfold blockKeep
      split_ifs
      · exact hn'.1 i j hij
      · exact Matrix.one_apply_ne hij.ne'
    · rw [hp₀]; unfold blockKeep
      split_ifs
      · exact hn'.2 i
      · exact Matrix.one_apply_eq i
    · rw [hp₀]; unfold blockKeep
      rw [if_neg, Matrix.one_apply_ne hij.ne]
      rintro ⟨⟨h1, -⟩, -, h2⟩
      rcases hor with h | h
      · exact absurd h1 (not_le.2 h)
      · exact absurd h2 (not_le.2 h)
  refine ⟨⟨p₀, hp⟩, fun u x => ?_⟩
  have hkeep : ∀ v : GU σ n, v ∈ cellU y →
      blockKeep (lo k) (lo k).rev ((v : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
        ((v : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := fun v hv =>
    blockKeep_eq_self _ _ _ ((hcell v).1 hv).1.1 ((hcell v).1 hv).1.2 ((hcell v).1 hv).2
  have hB : ∀ v : GU σ n, v ∈ cellU y → (v : GL (Fin n) L) ∈ unipB L (Fin n) := fun v hv =>
    (mem_unipB L).2 ((hcell v).1 hv).1
  set c : GU σ n := (u : GU σ n) * p₀ with hc
  have hcc : c ∈ cellU y := mul_mem u.2 hp
  set M : GU σ n := (u : GU σ n) * n' * c⁻¹ with hM
  have hMB : (M : GL (Fin n) L) ∈ unipB L (Fin n) :=
    mul_mem (mul_mem (hB _ u.2) hnB) (hB _ (inv_mem hcc))
  have hM1 : blockKeep (lo k) (lo k).rev ((M : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := by
    have e1 : ((M : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
        (((u : GU σ n) : GL (Fin n) L) * (n' : GL (Fin n) L) : GL (Fin n) L) *
          (((c⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := rfl
    rw [e1, blockKeep_mul _ _ _ _ ((mem_unipB L).1 (mul_mem (hB _ u.2) hnB)).1
      ((mem_unipB L).1 (hB _ (inv_mem hcc))).1, Units.val_mul,
      blockKeep_mul _ _ _ _ ((mem_unipB L).1 (hB _ u.2)).1 hn'.1, hkeep _ u.2, hkeep _ (inv_mem hcc), ← hp₀,
      ← Units.val_mul, ← Units.val_mul]
    have e2 : ((u : GU σ n) : GL (Fin n) L) * (p₀ : GL (Fin n) L) * ((c⁻¹ : GU σ n) : GL (Fin n) L) =
        ((c * c⁻¹ : GU σ n) : GL (Fin n) L) := rfl
    rw [e2, mul_inv_cancel]
    rfl
  set g : GU σ n := y⁻¹ * M * y with hg
  have hgv : (g : GL (Fin n) L) = (y : GL (Fin n) L)⁻¹ * (M : GL (Fin n) L) * (y : GL (Fin n) L) := rfl
  have hgB : IsBorelU g := by
    intro i j hij
    rw [hgv, GKFactor.weylRep_conj_apply hy]
    have hz : ((M : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (simpleU k i) (simpleU k j) = 0 := by
      rcases lt_or_gt_of_ne (fun e : simpleU k i = simpleU k j => hij.ne' ((simpleU k).injective e)) with hl | hl
      · have hno := (swap_lt_swap_iff_of_add_two (lo k) (lo k).rev _ _ hA hl).not.1 (by
          rw [hw, Equiv.swap_apply_self, Equiv.swap_apply_self]; exact not_lt.2 hij.le)
        rw [not_or, not_lt, not_lt] at hno
        have := congrFun (congrFun hM1 (simpleU k i)) (simpleU k j)
        unfold blockKeep at this
        rw [if_pos ⟨⟨hno.1, hl.le.trans hno.2⟩, hno.1.trans hl.le, hno.2⟩, Matrix.one_apply_ne hl.ne] at this
        exact this
      · exact ((mem_unipB L).1 hMB).1 _ _ hl
    rw [hz, mul_zero, zero_mul]
  have hgd : ∀ i, ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = 1 := by
    intro i
    rw [hgv, GKFactor.weylRep_conj_apply hy, ((mem_unipB L).1 hMB).2, mul_one, GKFactor.weylRep_inv_mul_diag hy]
  have ho : ordL (1 : L) = 0 := by
    unfold ordL
    split_ifs with h
    · rfl
    · have : WithZero.unzero h = 1 := by
        apply WithZero.coe_injective
        rw [WithZero.coe_unzero, map_one]; rfl
      rw [this]; simp
  have hchi : chiDeltaU q α g = 1 := by
    unfold chiDeltaU
    refine Finset.prod_eq_one fun i _ => ?_
    split_ifs
    · rw [hgd, ho]; simp
    · rfl
  have h := hφ g (y⁻¹ * c * x) hgB
  rw [hchi, one_mul] at h
  have e : y⁻¹ * (u : GU σ n) * n' * x = g * (y⁻¹ * c * x) := by
    rw [hg, hM]; group
  rw [e, h]
  rfl

end GlobalTheory.CompanionTheory.InvStep

end
