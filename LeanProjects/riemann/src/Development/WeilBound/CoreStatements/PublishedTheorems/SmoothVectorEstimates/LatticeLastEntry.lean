import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.MirabolicColumnBlock
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsOpenKerFinIdele

noncomputable section

open MeasureTheory Matrix GlobalTheory.CuspGeneric Topology
open scoped ContDiff

set_option linter.unusedSectionVars false

namespace PositivityTheory.jumpWindows

namespace LatticeLastEntry

open ValuativeRel

section Ring

variable {R : Type} [CommRing R] {a m : ℕ}

def t0 (hk : m + 1 < a) : UnipotentBlockColumnIndex a (m + 1) (m + 1) :=
  ⟨(⟨m, by omega⟩, ⟨m + 1, hk⟩), Nat.lt_succ_self m, le_rfl, le_rfl⟩

def rowOf (hk : m + 1 < a) (h : GL (Fin a) R) : UnipotentBlockColumnIndex a (m + 1) (m + 1) → R :=
  fun t => h.val ⟨m, by omega⟩ t.1.1

def dotp {ι : Type} [Fintype ι] (ξ y : ι → R) : R := ∑ t, ξ t * y t

theorem dotp_add {ι : Type} [Fintype ι] (ξ y y' : ι → R) : dotp ξ (y + y') = dotp ξ y + dotp ξ y' := by
  simp [dotp, mul_add, Finset.sum_add_distrib]

theorem dotp_sub_left {ι : Type} [Fintype ι] (ξ ξ' y : ι → R) : dotp (ξ - ξ') y = dotp ξ y - dotp ξ' y := by
  simp [dotp, sub_mul, Finset.sum_sub_distrib]

theorem dotp_single {ι : Type} [Fintype ι] [DecidableEq ι] (t : ι) (y : ι → R) : dotp (Pi.single t 1) y = y t := by
  simp [dotp, Pi.single_apply, ite_mul]

theorem lastE_eq (hk : m + 1 < a) (y : UnipotentBlockColumnIndex a (m + 1) (m + 1) → R) : lastE (m + 1) y = y (t0 hk) := by
  unfold lastE
  rw [Finset.sum_eq_single (t0 hk)]
  · simp [t0]
  · intro t _ ht
    rw [if_neg]
    intro e
    apply ht
    have hc : t.1.2 = ⟨m + 1, hk⟩ := Fin.ext (le_antisymm t.2.2.2 t.2.2.1)
    apply Subtype.ext
    apply Prod.ext
    · exact Fin.ext (by simp [t0]; omega)
    · exact hc
  · intro h; exact absurd (Finset.mem_univ _) h

theorem blkU_apply {r k : ℕ} (y : UnipotentBlockColumnIndex a r k → R) (t : UnipotentBlockColumnIndex a r k) : (blkU y).val t.1.1 t.1.2 = y t := by
  change (1 + posM Subtype.val y : Matrix (Fin a) (Fin a) R) t.1.1 t.1.2 = y t
  rw [Matrix.add_apply, posM, Matrix.sum_apply, Finset.sum_eq_single t]
  · rw [Matrix.one_apply_ne, Matrix.single_apply_same, zero_add]
    intro e
    have h1 := t.2.1
    have h2 := t.2.2.1
    rw [e] at h1
    omega
  · intro s _ hs
    rw [Matrix.single_apply_of_ne]
    rintro ⟨e1, e2⟩
    exact hs (Subtype.ext (Prod.ext e1 e2))
  · simp

theorem blkU_injective {r k : ℕ} : Function.Injective (blkU : (UnipotentBlockColumnIndex a r k → R) → GL (Fin a) R) := by
  intro y y' e
  funext t
  rw [← blkU_apply y t, ← blkU_apply y' t, e]

theorem rowOf_one (hk : m + 1 < a) : rowOf hk (1 : GL (Fin a) R) = Pi.single (t0 hk) 1 := by
  funext t
  have hc : t.1.2 = ⟨m + 1, hk⟩ := Fin.ext (le_antisymm t.2.2.2 t.2.2.1)
  by_cases ht : t = t0 hk
  · subst ht; simp [rowOf, t0]
  · rw [Pi.single_eq_of_ne ht]
    simp only [rowOf, Units.val_one]
    rw [Matrix.one_apply_ne]
    intro e
    apply ht
    apply Subtype.ext
    apply Prod.ext
    · exact e.symm
    · exact hc

theorem key (hS : MirabolicColumnBlock) (hk : m + 1 < a) (χ : AddChar R ℂ) {X : Type} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (GL (Fin a) R) X) (Y : Submodule ℂ X) (hY : ∀ g, ∀ x ∈ Y, ρ g x ∈ Y)
    (Λ : X →ₗ[ℂ] ℂ) (hΛ : ∀ x ∈ Y, ∀ y : UnipotentBlockColumnIndex a (m + 1) (m + 1) → R,
      Λ (ρ (blkU y) x) = χ (lastE (m + 1) y) * Λ x)
    (h : GL (Fin a) R) (hh : GlobalTheory (m + 1) h) (x : X) (hx : x ∈ Y) (y : UnipotentBlockColumnIndex a (m + 1) (m + 1) → R) :
    Λ (ρ h (ρ (blkU y) x)) = χ (dotp (rowOf hk h) y) * Λ (ρ h x) := by
  obtain ⟨y', e1, e2⟩ := (hS R a (m + 1)).2.2.2.2.2.2.2 h hh y
  have h1 : ρ h (ρ (blkU y) x) = ρ (blkU y') (ρ h x) := by
    rw [← Module.End.mul_apply, ← map_mul, e1, map_mul, Module.End.mul_apply]
  rw [h1, hΛ _ (hY h x hx) y', lastE_eq hk, e2]
  rfl

end Ring

section Fld

variable {F : Type} [Field F] {a m : ℕ}

def extR (hk : m + 1 < a) (ξ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → F) : Fin a → F :=
  fun j => if hj : (j : ℕ) < m + 1 then ξ ⟨(j, ⟨m + 1, hk⟩), hj, le_rfl, le_rfl⟩ else 0

def sMat (hk : m + 1 < a) (ξ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → F) : Matrix (Fin a) (Fin a) F :=
  Matrix.updateRow 1 ⟨m, by omega⟩ (extR hk ξ)

theorem det_sMat (hk : m + 1 < a) (ξ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → F) : (sMat hk ξ).det = ξ (t0 hk) := by
  rw [Matrix.det_of_isLowerTriangular]
  · rw [Finset.prod_eq_single (⟨m, by omega⟩ : Fin a)]
    · simp [sMat, extR, t0]
    · intro i _ hi
      simp [sMat, Matrix.updateRow_ne hi]
    · simp
  · intro i j hij
    have hij' : i < j := hij
    by_cases hi : i = ⟨m, by omega⟩
    · have hj : ¬ ((j : ℕ) < m + 1) := by
        have := Fin.lt_def.1 hij'
        rw [hi] at this
        simp at this
        omega
      rw [hi]
      simp [sMat, extR, hj]
    · simp [sMat, Matrix.updateRow_ne hi, Matrix.one_apply_ne (ne_of_lt hij')]

open Classical in

def sM (hk : m + 1 < a) (ξ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → F) : GL (Fin a) F :=
  if hξ : ξ (t0 hk) ≠ 0 then
    ((Matrix.isUnit_iff_isUnit_det _).2 (by rw [det_sMat]; exact isUnit_iff_ne_zero.2 hξ)).unit
  else 1

theorem sM_val (hk : m + 1 < a) (ξ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → F) (hξ : ξ (t0 hk) ≠ 0) :
    (sM hk ξ).val = sMat hk ξ := by
  simp [sM, hξ]

theorem sM_e (hk : m + 1 < a) : sM hk (Pi.single (t0 hk) (1 : F)) = 1 := by
  have h1 : (Pi.single (t0 hk) (1 : F) : UnipotentBlockColumnIndex a (m + 1) (m + 1) → F) (t0 hk) ≠ 0 := by simp
  apply Units.ext
  rw [sM_val hk _ h1, Units.val_one, sMat]
  have : extR hk (Pi.single (t0 hk) (1 : F)) = (1 : Matrix (Fin a) (Fin a) F) ⟨m, by omega⟩ := by
    funext j
    simp only [extR, Matrix.one_apply]
    by_cases hj : (j : ℕ) < m + 1
    · rw [dif_pos hj, Pi.single_apply]
      congr 1
      simp only [t0, Subtype.ext_iff, Prod.ext_iff, Fin.ext_iff, and_true, eq_iff_iff]
      omega
    · rw [dif_neg hj, if_neg]
      intro e
      rw [← e] at hj
      simp at hj
  rw [this, Matrix.updateRow_eq_self]

theorem blk_sM (hk : m + 1 < a) (ξ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → F) : GlobalTheory (m + 1) (sM hk ξ) := by
  intro i j hij
  by_cases hξ : ξ (t0 hk) ≠ 0
  · rw [sM_val hk ξ hξ, sMat]
    by_cases hi : i = ⟨m, by omega⟩
    · have hj : ¬ ((j : ℕ) < m + 1) := by
        rw [hi] at hij
        simp at hij
        omega
      have hmj : (⟨m, by omega⟩ : Fin a) ≠ j := by
        intro e
        rw [← e] at hj
        simp at hj
      rw [hi, Matrix.updateRow_self, extR, dif_neg hj, Matrix.one_apply_ne hmj]
    · rw [Matrix.updateRow_ne hi]
  · simp [sM, hξ]

theorem mir_mul (hk : m + 1 < a) (h : GL (Fin a) F) (hh : GlobalTheory (m + 1) h) (hξ : rowOf hk h (t0 hk) ≠ 0) :
    Mir m (h * (sM hk (rowOf hk h))⁻¹) := by
  set M := sM hk (rowOf hk h) with hM
  intro i j hij
  rw [Units.val_mul]
  rcases hij with hi | hj
  · have hrow : ∀ l, h.val i l = M.val i l := by
      intro l
      by_cases him : (i : ℕ) = m
      · have hi' : i = ⟨m, by omega⟩ := Fin.ext him
        rw [hM, sM_val hk _ hξ, sMat, hi', Matrix.updateRow_self, extR]
        by_cases hl : (l : ℕ) < m + 1
        · rw [dif_pos hl]
          rfl
        · rw [dif_neg hl]
          rw [hh _ _ (Or.inr (by omega)), Matrix.one_apply_ne]
          intro e
          rw [← e] at hl
          simp at hl
      · rw [hh _ _ (Or.inl (by omega)), blk_sM hk _ _ _ (Or.inl (by omega))]
    have : (h.val * M⁻¹.val) i j = (M.val * M⁻¹.val) i j := by
      simp only [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hrow l]
    rw [this, Units.mul_inv]
  · have hj' : m + 1 ≤ (j : ℕ) := hj
    have hcol : ∀ l, M⁻¹.val l j = (1 : Matrix (Fin a) (Fin a) F) l j := by
      intro l
      have h1 : (M⁻¹.val * M.val) l j = (M⁻¹.val * (1 : Matrix (Fin a) (Fin a) F)) l j := by
        simp only [Matrix.mul_apply]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [blk_sM hk _ p j (Or.inr hj')]
      rw [Units.inv_mul, Matrix.mul_one] at h1
      exact h1.symm
    have : (h.val * M⁻¹.val) i j = (h.val * (1 : Matrix (Fin a) (Fin a) F)) i j := by
      simp only [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hcol l]
    rw [this, Matrix.mul_one, hh _ _ (Or.inr hj')]

theorem contOn_sM [TopologicalSpace F] [IsTopologicalDivisionRing F] (hk : m + 1 < a) :
    ContinuousOn (sM hk) {ξ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → F | ξ (t0 hk) ≠ 0} := by
  have hc : Continuous (sMat hk : (UnipotentBlockColumnIndex a (m + 1) (m + 1) → F) → Matrix (Fin a) (Fin a) F) := by
    refine continuous_matrix fun i j => ?_
    simp only [sMat, Matrix.updateRow_apply, extR]
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
    · exact continuous_const
  have hi : Continuous fun x : {ξ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → F | ξ (t0 hk) ≠ 0} => (sMat hk x.1)⁻¹ := by
    rw [continuous_iff_continuousAt]
    intro x
    have h1 : ContinuousAt Inv.inv (sMat hk x.1) := by
      refine continuousAt_matrix_inv _ ?_
      rw [det_sMat, Ring.inverse_eq_inv']
      exact continuousAt_inv₀ x.2
    exact (h1.comp hc.continuousAt).comp continuous_subtype_val.continuousAt
  rw [continuousOn_iff_continuous_domRestrict]
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine (hc.comp continuous_subtype_val).congr fun x => ?_
    exact (sM_val hk x.1 x.2).symm
  · refine hi.congr fun x => ?_
    show _ = ((sM hk x.1)⁻¹ : GL (Fin a) F).val
    rw [Matrix.coe_units_inv, sM_val hk x.1 x.2]

end Fld

section Val

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem isOpen_le {γ : ValueGroupWithZero F} (hγ : γ ≠ 0) : IsOpen {x : F | valuation F x ≤ γ} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 γ hγ, fun z hz => ?_⟩
  have hz' : valuation F (z - x) < γ := by simpa using hz
  have h1 : valuation F z ≤ max (valuation F (z - x)) (valuation F x) := by
    simpa using (valuation F).map_add (z - x) x
  exact h1.trans (max_le hz'.le hx)

theorem isOpen_ne_zero : IsOpen {x : F | x ≠ 0} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 (valuation F x) (by simpa using hx), fun z hz hz0 => ?_⟩
  simp [hz0] at hz

theorem exists_le_sub {W : Set F} (hW : W ∈ 𝓝 (0 : F)) :
    ∃ r : F, r ≠ 0 ∧ {x : F | valuation F x ≤ valuation F r} ⊆ W := by
  obtain ⟨γ, hγ, hsub⟩ := (IsValuativeTopology.hasBasis_nhds_zero' F).mem_iff.mp hW
  obtain ⟨r0, hr0⟩ := ValuativeRel.valuation_surjective γ
  obtain ⟨π, hπ0, hπ1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation F)
  have hr0' : r0 ≠ 0 := by
    rintro rfl
    exact hγ (by rw [← hr0, map_zero])
  refine ⟨r0 * π, mul_ne_zero hr0' hπ0, fun x hx => hsub ?_⟩
  have hlt : valuation F (r0 * π) < γ := by
    rw [map_mul, hr0]
    exact mul_lt_of_lt_one_right (zero_lt_iff.2 hγ) hπ1
  exact lt_of_le_of_lt hx hlt

variable {ι : Type} [Fintype ι]

def lat (γ : ValueGroupWithZero F) : AddSubgroup (ι → F) where
  carrier := {y | ∀ t, valuation F (y t) ≤ γ}
  add_mem' := by
    intro y y' hy hy' t
    exact ((valuation F).map_add _ _).trans (max_le (hy t) (hy' t))
  zero_mem' := by intro t; simp
  neg_mem' := by intro y hy t; simpa using hy t

theorem mem_lat {γ : ValueGroupWithZero F} {y : ι → F} : y ∈ (lat γ : AddSubgroup (ι → F)) ↔ ∀ t, valuation F (y t) ≤ γ :=
  Iff.rfl

theorem isCompact_lat (γ : ValueGroupWithZero F) : IsCompact ((lat γ : AddSubgroup (ι → F)) : Set (ι → F)) := by
  have e : ((lat γ : AddSubgroup (ι → F)) : Set (ι → F)) = Set.univ.pi (fun _ => {x : F | valuation F x ≤ γ}) := by
    ext y
    simp [mem_lat]
  rw [e]
  exact isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall F γ

theorem isOpen_lat {γ : ValueGroupWithZero F} (hγ : γ ≠ 0) : IsOpen ((lat γ : AddSubgroup (ι → F)) : Set (ι → F)) := by
  have e : ((lat γ : AddSubgroup (ι → F)) : Set (ι → F)) = Set.univ.pi (fun _ => {x : F | valuation F x ≤ γ}) := by
    ext y
    simp [mem_lat]
  rw [e]
  exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_le hγ

theorem exists_lat {W : Set (ι → F)} (hW : W ∈ 𝓝 (0 : ι → F)) (t : ι) :
    ∃ r : F, r ≠ 0 ∧ ((lat (valuation F r) : AddSubgroup (ι → F)) : Set (ι → F)) ⊆ W := by
  rw [nhds_pi, Filter.mem_pi'] at hW
  obtain ⟨I, s, hs, hsW⟩ := hW
  have hs' : ∀ i, ∃ r : F, r ≠ 0 ∧ {x : F | valuation F x ≤ valuation F r} ⊆ s i := fun i =>
    exists_le_sub (hs i)
  choose r hr0 hrs using hs'
  have : Nonempty ι := ⟨t⟩
  obtain ⟨i0, hi0⟩ := Finite.exists_min (fun i => valuation F (r i))
  refine ⟨r i0, hr0 i0, fun y hy => hsW fun i _ => hrs i ((hy i).trans (hi0 i))⟩

theorem finite_quot {γ δ : ValueGroupWithZero F} (hδ : δ ≠ 0) :
    Finite ((lat γ : AddSubgroup (ι → F)) ⧸ (lat δ : AddSubgroup (ι → F)).addSubgroupOf (lat γ)) := by
  have : CompactSpace (lat γ : AddSubgroup (ι → F)) := isCompact_iff_compactSpace.mp (isCompact_lat γ)
  apply AddSubgroup.quotient_finite_of_isOpen
  exact (isOpen_lat hδ).preimage continuous_subtype_val

theorem ann [DecidableEq ι] (χ : AddChar F ℂ) (x0 : F) (hx0 : χ x0 ≠ 1) (ε : F) (hε : ε ≠ 0)
    (Γ : ValueGroupWithZero F) (hΓ : valuation F (x0 / ε) ≤ Γ) (ζ : ι → F)
    (hζ : ∀ y ∈ (lat Γ : AddSubgroup (ι → F)), χ (dotp ζ y) = 1) : ζ ∈ (lat (valuation F ε) : AddSubgroup (ι → F)) := by
  intro t
  by_contra hlt
  rw [not_le] at hlt
  have hz : ζ t ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hlt
    exact not_lt_zero hlt
  have hv : valuation F (x0 / ζ t) ≤ valuation F (x0 / ε) := by
    have e1 : x0 / ζ t = (x0 / ε) * (ε / ζ t) := by field_simp
    rw [e1, map_mul]
    refine mul_le_of_le_one_right' ?_
    rw [map_div₀]
    exact (div_le_one₀ (lt_of_le_of_lt zero_le hlt)).2 hlt.le
  have hy : (Pi.single t (x0 / ζ t) : ι → F) ∈ (lat Γ : AddSubgroup (ι → F)) := by
    intro s
    by_cases hs : s = t
    · subst hs; simpa using hv.trans hΓ
    · simp [hs]
  have h1 := hζ _ hy
  have h2 : dotp ζ (Pi.single t (x0 / ζ t)) = x0 := by
    simp [dotp, Pi.single_apply]
    field_simp
  rw [h2] at h1
  exact hx0 h1

end Val

theorem sum_zero {G : Type} [AddCommGroup G] (L L0 : AddSubgroup G) [Fintype (L ⧸ L0.addSubgroupOf L)]
    (f : G → ℂ) (hadd : ∀ x y, f (x + y) = f x * f y) (h0 : ∀ y ∈ L0, f y = 1) (y1 : G) (hy1 : y1 ∈ L)
    (hf1 : f y1 ≠ 1) : ∑ q : L ⧸ L0.addSubgroupOf L, f ((Quotient.out q : L) : G) = 0 := by
  have hwd : ∀ x x' : L, (QuotientAddGroup.mk x : L ⧸ L0.addSubgroupOf L) = QuotientAddGroup.mk x' →
      f (x : G) = f (x' : G) := by
    intro x x' hx
    rw [QuotientAddGroup.eq] at hx
    have hm : ((-x + x' : L) : G) ∈ L0 := AddSubgroup.mem_addSubgroupOf.1 hx
    have e : (x' : G) = (x : G) + ((-x + x' : L) : G) := by simp
    rw [e, hadd, h0 _ hm, mul_one]
  have hout : ∀ x : L ⧸ L0.addSubgroupOf L, (QuotientAddGroup.mk (Quotient.out x) : L ⧸ L0.addSubgroupOf L) = x :=
    fun x => Quotient.out_eq x
  set q1 : L ⧸ L0.addSubgroupOf L := QuotientAddGroup.mk ⟨y1, hy1⟩ with hq1
  have hs : (∑ q : L ⧸ L0.addSubgroupOf L, f ((Quotient.out q : L) : G)) * f y1 =
      ∑ q : L ⧸ L0.addSubgroupOf L, f ((Quotient.out q : L) : G) := by
    rw [Finset.sum_mul]
    refine Fintype.sum_equiv (Equiv.addRight q1) _ _ fun q => ?_
    have e1 : f ((Quotient.out (q + q1) : L) : G) = f (((Quotient.out q : L) + ⟨y1, hy1⟩ : L) : G) := by
      apply hwd
      rw [QuotientAddGroup.mk_add, hout, hout]
    rw [Equiv.coe_addRight, e1, AddSubgroup.coe_add, hadd]
  have h2 : (∑ q : L ⧸ L0.addSubgroupOf L, f ((Quotient.out q : L) : G)) * (1 - f y1) = 0 := by
    rw [mul_sub, mul_one, hs, sub_self]
  exact (mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 (Ne.symm hf1))

end LatticeLastEntry

open LatticeLastEntry ValuativeRel in
theorem lattice_open_last_entry : MirabolicColumnBlock → S9 := by
  intro hS F _ _ _ _ a m hk χ hχc hχ1 X _ _ ρ U hU
  classical
  obtain ⟨x0, hx0⟩ := hχ1
  obtain ⟨e, he⟩ : ∃ e : UnipotentBlockColumnIndex a (m + 1) (m + 1) → F, e = Pi.single (t0 hk) 1 := ⟨_, rfl⟩
  have he1 : sM hk e = 1 := by rw [he]; exact sM_e hk
  have hrow1 : rowOf hk (1 : GL (Fin a) F) = e := by rw [he]; exact rowOf_one hk
  have hdot : ∀ y, dotp e y = y (t0 hk) := by intro y; rw [he]; exact dotp_single _ y
  have he0 : e (t0 hk) ≠ 0 := by simp [he]
  have hW0 : {y : UnipotentBlockColumnIndex a (m + 1) (m + 1) → F | blkU y ∈ U ∧ ‖χ (y (t0 hk)) - 1‖ < 1 / 2} ∈
      𝓝 (0 : UnipotentBlockColumnIndex a (m + 1) (m + 1) → F) := by
    refine Filter.inter_mem ?_ ?_
    · have hc : Continuous (blkU : (UnipotentBlockColumnIndex a (m + 1) (m + 1) → F) → GL (Fin a) F) := continuous_posU (isNil_blk a (m + 1) (m + 1))
      refine hc.continuousAt.preimage_mem_nhds ?_
      have h1 : (blkU (0 : UnipotentBlockColumnIndex a (m + 1) (m + 1) → F) : GL (Fin a) F) = 1 := posU_zero (isNil_blk a (m + 1) (m + 1))
      rw [h1]; exact hU
    · have ho : IsOpen {y : UnipotentBlockColumnIndex a (m + 1) (m + 1) → F | ‖χ (y (t0 hk)) - 1‖ < 1 / 2} :=
        isOpen_lt ((hχc.comp (continuous_apply (t0 hk))).sub continuous_const).norm continuous_const
      exact ho.mem_nhds (by simp)
  obtain ⟨d, hd0, hd⟩ := exists_lat hW0 (t0 hk)
  have hopen : IsOpen {ξ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → F | ξ (t0 hk) ≠ 0} :=
    isOpen_ne_zero.preimage (continuous_apply (t0 hk))
  have hW1 : (fun ζ => e + ζ) ⁻¹' ({ξ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → F | ξ (t0 hk) ≠ 0} ∩ sM hk ⁻¹' U) ∈
      𝓝 (0 : UnipotentBlockColumnIndex a (m + 1) (m + 1) → F) := by
    have hca : ContinuousAt (sM hk) e := (contOn_sM hk).continuousAt (hopen.mem_nhds he0)
    have h1 : sM hk ⁻¹' U ∈ 𝓝 e := hca.preimage_mem_nhds (by rw [he1]; exact hU)
    refine (continuous_const_add e).continuousAt.preimage_mem_nhds ?_
    rw [add_zero]; exact Filter.inter_mem (hopen.mem_nhds he0) h1
  obtain ⟨ε, hε0, hε⟩ := exists_lat hW1 (t0 hk)
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : ValueGroupWithZero F, Γ = max (valuation F d) (valuation F (x0 / ε)) := ⟨_, rfl⟩
  have hdΓ : valuation F d ≤ Γ := hΓ ▸ le_max_left _ _
  have hxΓ : valuation F (x0 / ε) ≤ Γ := hΓ ▸ le_max_right _ _
  obtain ⟨L, hL⟩ : ∃ L : AddSubgroup (UnipotentBlockColumnIndex a (m + 1) (m + 1) → F), L = lat Γ := ⟨_, rfl⟩
  obtain ⟨L0, hL0⟩ : ∃ L0 : AddSubgroup (UnipotentBlockColumnIndex a (m + 1) (m + 1) → F), L0 = lat (valuation F d) := ⟨_, rfl⟩
  have hd0' : valuation F d ≠ 0 := by simpa using hd0
  have : Finite (L ⧸ L0.addSubgroupOf L) := by rw [hL, hL0]; exact finite_quot hd0'
  let _ : Fintype (L ⧸ L0.addSubgroupOf L) := Fintype.ofFinite _
  have hχ0 : ∀ y ∈ L0, χ (y (t0 hk)) = 1 := by
    intro y hy
    refine GlobalTheory.CuspRep.eq_one_of_pow_near fun n => ?_
    rw [← AddChar.map_nsmul_eq_pow]
    have hn : n • y ∈ L0 := L0.nsmul_mem hy n
    rw [hL0] at hn
    exact (hd hn).2
  have hU0 : ∀ y ∈ L0, blkU y ∈ U := fun y hy => (hd (hL0 ▸ hy)).1
  let P1 : (UnipotentBlockColumnIndex a (m + 1) (m + 1) → F) → Prop := fun ξ => ∀ y ∈ L, χ (dotp (ξ - e) y) = 1
  have hP1 : ∀ ξ, P1 ξ → ξ (t0 hk) ≠ 0 ∧ sM hk ξ ∈ U ∧
      ξ - e ∈ (lat (valuation F ε) : AddSubgroup (UnipotentBlockColumnIndex a (m + 1) (m + 1) → F)) := by
    intro ξ hξ
    have hm := ann χ x0 hx0 ε hε0 Γ hxΓ (ξ - e) (fun y hy => hξ y (hL ▸ hy))
    have h2 := hε hm
    have h3 : e + (ξ - e) = ξ := by abel
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq, h3] at h2
    exact ⟨h2.1, h2.2, hm⟩
  let N : ℝ := (Fintype.card (L ⧸ L0.addSubgroupOf L) : ℝ)
  let T : Finset (GL (Fin a) F) := Finset.univ.image fun q : L ⧸ L0.addSubgroupOf L =>
    blkU ((Quotient.out q : L) : UnipotentBlockColumnIndex a (m + 1) (m + 1) → F)
  let c : GL (Fin a) F → ℂ := fun g => χ (-(g.val (t0 hk).1.1 (t0 hk).1.2))
  let η : GL (Fin a) F → ℂ := fun h => ((if GlobalTheory (m + 1) h ∧ P1 (rowOf hk h) then N else 0 : ℝ) : ℂ)
  let r : GL (Fin a) F → GL (Fin a) F := fun h =>
    if GlobalTheory (m + 1) h ∧ P1 (rowOf hk h) then h * (sM hk (rowOf hk h))⁻¹ else 1
  have hblk1 : GlobalTheory (m + 1) (1 : GL (Fin a) F) := fun i j _ => rfl
  have hP1one : P1 (rowOf hk (1 : GL (Fin a) F)) := by
    intro y _
    rw [hrow1, sub_self]
    simp [dotp]
  have hN : N ≠ 0 := by
    simp only [N]; exact_mod_cast Fintype.card_ne_zero
  have hc1 : ∀ y, c (blkU y) = χ (-(y (t0 hk))) := by
    intro y; simp only [c]; rw [blkU_apply]
  refine ⟨T, c, η, r, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [η, if_pos (And.intro hblk1 hP1one)]; exact_mod_cast hN
  · simp only [r, if_pos (And.intro hblk1 hP1one)]; rw [hrow1, he1]; simp
  · intro h hh hη
    have hc : GlobalTheory (m + 1) h ∧ P1 (rowOf hk h) := by
      by_contra hc; exact hη (by simp [η, hc])
    simp only [r, if_pos hc]
    exact mir_mul hk h hh (hP1 _ hc.2).1
  · intro h
    refine ⟨if GlobalTheory (m + 1) h ∧ P1 (rowOf hk h) then N else 0, ?_, rfl⟩
    split_ifs
    · exact Nat.cast_nonneg _
    · exact le_rfl
  · refine ⟨(fun ζ => sM hk (e + ζ)) '' (lat (valuation F ε) : AddSubgroup (UnipotentBlockColumnIndex a (m + 1) (m + 1) → F)),
      ?_, ?_, ?_, ?_⟩
    · refine (isCompact_lat _).image_of_continuousOn ?_
      refine (contOn_sM hk).comp (continuous_const_add e).continuousOn ?_
      intro ζ hζ; exact (hε hζ).1
    · rintro _ ⟨ζ, hζ, rfl⟩; exact (hε hζ).2
    · rintro _ ⟨ζ, hζ, rfl⟩; exact blk_sM hk _
    · intro h hh hη
      have hc : GlobalTheory (m + 1) h ∧ P1 (rowOf hk h) := by
        by_contra hc; exact hη (by simp [η, hc])
      refine ⟨sM hk (rowOf hk h), ⟨rowOf hk h - e, (hP1 _ hc.2).2.2, ?_⟩, ?_⟩
      · show sM hk (e + (rowOf hk h - e)) = _
        congr 1; abel
      · simp only [r, if_pos hc]
        exact (inv_mul_cancel_right _ _).symm
  · intro v hv Y hY hvY Λ hΛ h hh
    have hsum : Λ (ρ h (∑ t ∈ T, c t • ρ t v)) =
        (∑ q : L ⧸ L0.addSubgroupOf L,
          χ (dotp (rowOf hk h - e) ((Quotient.out q : L) : UnipotentBlockColumnIndex a (m + 1) (m + 1) → F))) * Λ (ρ h v) := by
      rw [Finset.sum_image]
      · rw [map_sum, map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [map_smul, map_smul, smul_eq_mul, key hS hk χ ρ Y hY Λ hΛ h hh v hvY, hc1, dotp_sub_left, hdot,
          sub_eq_neg_add, AddChar.map_add_eq_mul, mul_assoc]
      · intro q _ q' _ hqq
        exact Quotient.out_injective (Subtype.ext (blkU_injective hqq))
    by_cases hc : GlobalTheory (m + 1) h ∧ P1 (rowOf hk h)
    · have hall : ∀ q : L ⧸ L0.addSubgroupOf L,
          χ (dotp (rowOf hk h - e) ((Quotient.out q : L) : UnipotentBlockColumnIndex a (m + 1) (m + 1) → F)) = 1 :=
        fun q => hc.2 _ (Quotient.out q).2
      have hfix : ρ h v = ρ (h * (sM hk (rowOf hk h))⁻¹) v := by
        conv_lhs => rw [show h = h * (sM hk (rowOf hk h))⁻¹ * sM hk (rowOf hk h) from (inv_mul_cancel_right _ _).symm]
        rw [map_mul, Module.End.mul_apply, hv _ (hP1 _ hc.2).2.1]
      rw [hsum]
      simp only [hall, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, η, r, if_pos hc, N]
      rw [hfix]
      push_cast
      rfl
    · have hηh : η h = 0 := by simp [η, hc]
      rw [hsum, hηh, zero_mul]
      have hP1' : ¬ P1 (rowOf hk h) := fun h1 => hc ⟨hh, h1⟩
      by_cases hP0 : ∀ y ∈ L0, χ (dotp (rowOf hk h) y) = 1
      · simp only [P1, not_forall] at hP1'
        obtain ⟨y1, hy1, hf1⟩ := hP1'
        rw [sum_zero L L0 (fun y => χ (dotp (rowOf hk h - e) y)) ?_ ?_ y1 hy1 hf1, zero_mul]
        · intro y y'
          rw [dotp_add, AddChar.map_add_eq_mul]
        · intro y hy
          rw [dotp_sub_left, hdot, sub_eq_add_neg, AddChar.map_add_eq_mul, hP0 y hy, AddChar.map_neg_eq_inv,
            hχ0 y hy]
          simp
      · push Not at hP0
        obtain ⟨y0, hy0, hne⟩ := hP0
        have h0 : Λ (ρ h v) = 0 := by
          have h1 := key hS hk χ ρ Y hY Λ hΛ h hh v hvY y0
          rw [hv _ (hU0 y0 hy0)] at h1
          have h2 : (1 - χ (dotp (rowOf hk h) y0)) * Λ (ρ h v) = 0 := by
            rw [sub_mul, one_mul, ← h1, sub_self]
          rcases mul_eq_zero.1 h2 with h3 | h3
          · exact absurd (sub_eq_zero.1 h3).symm hne
          · exact h3
        rw [h0, mul_zero]

end PositivityTheory.jumpWindows

end
