import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NormalRepresentationLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagPartMulDiagPart

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice

namespace GlobalTheory.StepData.NormalForm

section Plain
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

end Plain

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem _root_.GlobalTheory.StepData.NormalForm.exists_valuation_eq_zpow {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k)
    (d : kˣ) : ∃ e : ℤ, valuation k (d : k) = valuation k (ϖ : k) ^ e := by
  set φ := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  have hu0 : φ (uniformizer k) ≠ 0 := by
    rw [ne_eq, map_eq_zero]; exact (uniformizer_pos).ne'
  have hu1 : φ (uniformizer k) < 1 := by
    rw [← map_one φ]; exact φ.strictMono uniformizer_lt_one
  obtain ⟨a, ha⟩ := WithZero.ne_zero_iff_exists.mp hu0
  have ha1 : a.toAdd < 0 := by
    rw [← ha] at hu1
    exact_mod_cast hu1
  have ha2 : -1 ≤ a.toAdd := by
    have h1 : φ.symm ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) < 1 := by
      rw [← map_one φ.symm]
      exact φ.symm.strictMono
        (by exact_mod_cast (show (Multiplicative.ofAdd (-1 : ℤ)) < 1 by decide))
    have h2 := le_uniformizer_iff.mpr h1
    have h3 := φ.strictMono.monotone h2
    simp only [OrderMonoidIso.apply_symm_apply, ← ha] at h3
    exact_mod_cast h3
  have ha3 : a = Multiplicative.ofAdd (-1 : ℤ) := by
    apply Multiplicative.toAdd.injective; simp; omega
  have hd0 : φ (valuation k (d : k)) ≠ 0 := by
    rw [ne_eq, map_eq_zero, map_eq_zero]; exact d.ne_zero
  obtain ⟨b, hb⟩ := WithZero.ne_zero_iff_exists.mp hd0
  have hz : φ (uniformizer k ^ (-b.toAdd)) = φ (uniformizer k) ^ (-b.toAdd) := map_zpow₀ φ _ _
  have key : φ (valuation k (d : k)) = φ (valuation k (ϖ : k) ^ (-b.toAdd)) := by
    rw [hϖ, hz, ← ha, ← hb, ha3, ← WithZero.coe_zpow]
    congr 1
    apply Multiplicative.toAdd.injective
    simp
  exact ⟨-b.toAdd, φ.injective key⟩

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private lemma latOf_mul_of_mem_KO' {K : Type} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] {Y : Type} [Fintype Y] [DecidableEq Y]
    (x w : GL Y K) (hw : w ∈ _root_.GlobalTheory.SplitWeil.KO K Y) :
    _root_.GlobalTheory.StepData.latOf (x * w) = _root_.GlobalTheory.StepData.latOf x := by
  rw [_root_.GlobalTheory.StepData.mem_KO] at hw
  apply le_antisymm
  · rw [_root_.GlobalTheory.StepData.latOf_le_iff]
    simpa [← mul_assoc] using hw.1
  · rw [_root_.GlobalTheory.StepData.latOf_le_iff]
    simpa [mul_assoc] using hw.2

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem _root_.GlobalTheory.StepData.NormalForm.normalFormModN : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], _root_.GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.NormalFormModN k := by
  intro k _ _ _ _ ϖ hϖ n _ _ c h
  obtain ⟨b, hbT, w, hw, rfl⟩ := _root_.GlobalTheory.SplitWeil.iwasawa_blockTriangular k (n ⊕ Fin c)
    (Sum.elim (fun _ => 0) (fun i => (i : ℕ) + 1)) h
  have hbP : (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).BlockTriangular
      (_root_.GlobalTheory.RootEx.lev 1) := by
    intro i j hij
    apply hbT
    unfold _root_.GlobalTheory.RootEx.lev at hij
    rcases i with i | i <;> rcases j with j | j <;> simp at hij ⊢ <;> omega
  obtain ⟨u', hu', m, hm0, hmb, hbum⟩ := _root_.GlobalTheory.RootEx.BlockLevi.exists_unip_mul_levi k n c 1 b hbP
  have h21 : (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₂₁ = 0 := by
    ext i j
    exact hbT (by simp)
  have hT : ((b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₂₂).BlockTriangular id := by
    intro i j hij
    exact hbT (by simp only [Sum.elim_inr]; exact Nat.succ_lt_succ hij)
  have hdet : (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).det ≠ 0 := b.det_ne_zero
  have hbB := fromBlocks_toBlocks (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
  rw [← hbB, h21, det_fromBlocks_zero₂₁, det_of_upperTriangular hT] at hdet
  have hG : (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₁₁.det ≠ 0 := left_ne_zero_of_mul hdet
  have ht : ∀ i : Fin c, (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inr i) (Sum.inr i) ≠ 0 :=
    fun i => Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hdet) i (Finset.mem_univ i)
  set g : GL n k := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hG with hg
  have hgv : (g : Matrix n n k) = (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₁₁ := rfl
  choose e he using fun i => _root_.GlobalTheory.StepData.NormalForm.exists_valuation_eq_zpow hϖ (Units.mk0 _ (ht i))
  set z : n → k := fun r => if hc : 0 < c then
    (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inl r) (Sum.inr ⟨0, hc⟩) *
      ((b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inr ⟨0, hc⟩) (Sum.inr ⟨0, hc⟩))⁻¹ else 0 with hz
  set εv : n ⊕ Fin c → kˣ := Sum.elim (fun _ => 1) (fun i => Units.mk0 _ (ht i) * ϖ ^ (-e i)) with hεv
  have hϖ0 : (ϖ : k) ≠ 0 := ϖ.ne_zero
  have key : m = _root_.GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.nfBasis ϖ g e z * _root_.GlobalTheory.SplitFlip.diagGL εv := by
    clear hbum hu' hbP hdet hbB hw hT h21 hϖ he
    ext r s
    rw [Units.val_mul, _root_.GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.nfBasis_val, _root_.GlobalTheory.SplitFlip.diagGL_val,
      mul_diagonal]
    rcases r with r | i <;> rcases s with s | j
    · rw [hmb _ _ (by simp [_root_.GlobalTheory.RootEx.lev])]
      simp [hεv, hgv, toBlocks₁₁]
    · by_cases hj : (j : ℕ) = 0
      · rw [hmb _ _ (by simp [_root_.GlobalTheory.RootEx.lev, hj])]
        have hc : 0 < c := j.pos
        have hj' : j = ⟨0, hc⟩ := Fin.ext hj
        subst hj'
        simp only [fromBlocks_apply₁₂, of_apply, hj, if_true, hz, dif_pos hc, hεv, Sum.elim_inr,
          Units.val_mul, Units.val_mk0, Units.val_zpow_eq_zpow_val, _root_.zpow_neg,
          Units.val_inv_eq_inv_val]
        have := ht ⟨0, hc⟩
        field_simp
      · rw [hm0 _ _ (by simp [_root_.GlobalTheory.RootEx.lev]; omega)]
        simp [hj]
    · by_cases hi : (i : ℕ) = 0
      · rw [hmb _ _ (by simp [_root_.GlobalTheory.RootEx.lev, hi])]
        simp only [fromBlocks_apply₂₁, Matrix.zero_apply, zero_mul]
        exact hbT (by simp)
      · rw [hm0 _ _ (by simp [_root_.GlobalTheory.RootEx.lev]; omega)]
        rw [fromBlocks_apply₂₁, Matrix.zero_apply, zero_mul]
    · by_cases hij : i = j
      · subst hij
        have := ht i
        rw [hmb _ _ rfl]
        simp only [fromBlocks_apply₂₂, diagonal_apply_eq, hεv, Sum.elim_inr,
          Units.val_mul, Units.val_mk0, Units.val_zpow_eq_zpow_val, _root_.zpow_neg,
          Units.val_inv_eq_inv_val]
        field_simp
      · rw [hm0 _ _ (by simp [_root_.GlobalTheory.RootEx.lev]; omega)]
        simp [diagonal_apply_ne _ hij]
  have hεinv : (_root_.GlobalTheory.SplitFlip.diagGL εv)⁻¹ = _root_.GlobalTheory.SplitFlip.diagGL εv⁻¹ := by
    apply inv_eq_of_mul_eq_one_right
    ext i j
    rw [Units.val_mul, _root_.GlobalTheory.SplitFlip.diagGL_val, _root_.GlobalTheory.SplitFlip.diagGL_val,
      diagonal_mul_diagonal, Units.val_one]
    simp [diagonal_apply, one_apply]
  have hv0 : valuation k (ϖ : k) ≠ 0 := (map_ne_zero _).mpr hϖ0
  have hval : ∀ i, valuation k (εv i : k) = 1 := by
    rintro (i | i)
    · simp [hεv]
    · have hei := he i
      rw [Units.val_mk0] at hei
      simp only [hεv, Sum.elim_inr, Units.val_mul, Units.val_mk0, Units.val_zpow_eq_zpow_val,
        map_mul, map_zpow₀]
      rw [hei, ← zpow_add₀ hv0, add_neg_cancel, zpow_zero]
  have hε : _root_.GlobalTheory.SplitFlip.diagGL εv ∈ _root_.GlobalTheory.SplitWeil.KO k (n ⊕ Fin c) := by
    rw [_root_.GlobalTheory.SplitFlip.mem_KO_iff]
    constructor
    · intro i j
      rw [_root_.GlobalTheory.SplitFlip.diagGL_val, diagonal_apply]
      split_ifs
      · rw [Valuation.mem_integer_iff, hval]
      · exact zero_mem _
    · intro i j
      rw [hεinv, _root_.GlobalTheory.SplitFlip.diagGL_val, diagonal_apply]
      split_ifs
      · rw [Valuation.mem_integer_iff, Pi.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, hval,
          inv_one]
      · exact zero_mem _
  refine ⟨u'⁻¹, inv_mem hu', g, e, z, ?_, ?_⟩
  · have hub : u'⁻¹ * (b * w) = _root_.GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.nfBasis ϖ g e z * (_root_.GlobalTheory.SplitFlip.diagGL εv * w) := by
      rw [hbum, key]; group
    rw [hub, latOf_mul_of_mem_KO' _ _ (mul_mem hε hw)]
  · rw [latOf_mul_of_mem_KO' _ _ hw]
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.MeetsIn
    intro y
    rw [_root_.GlobalTheory.StepData.mem_latOf, _root_.GlobalTheory.StepData.mem_latOf]
    have h1 : (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) *ᵥ Sum.elim ((↑g⁻¹ : Matrix n n k) *ᵥ y) 0 =
        Sum.elim y 0 := by
      rw [← hbB, h21, fromBlocks_mulVec]
      simp [← hgv, mulVec_mulVec]
    have hv : (↑b⁻¹ : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) *ᵥ Sum.elim y 0 =
        Sum.elim ((↑g⁻¹ : Matrix n n k) *ᵥ y) 0 := by
      rw [← h1, mulVec_mulVec, Units.inv_mul, one_mulVec]
    rw [hv]
    constructor
    · intro H i
      simpa using H (Sum.inl i)
    · rintro H (i | i)
      · simpa using H i
      · simp

end GlobalTheory.StepData.NormalForm
