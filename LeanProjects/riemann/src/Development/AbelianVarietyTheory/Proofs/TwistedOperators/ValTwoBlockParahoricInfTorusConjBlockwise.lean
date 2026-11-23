import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

noncomputable section

namespace GlobalTheory.ParahoricConjBlocks

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_lt_one_iff {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (z : k) :
    valuation k z < 1 ↔ valuation k z ≤ valuation k (ϖ : k) := by
  rw [hϖ, le_uniformizer_iff]

theorem scal₁ {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (y : k) (n : ℤ) :
    (valuation k y ≤ 1 ∧ valuation k (y * (ϖ : k) ^ n) ≤ 1) ↔
      valuation k y ≤ valuation k ((ϖ : k) ^ max 0 (-n)) := by
  have h0 : 0 < valuation k (ϖ : k) := (Valuation.pos_iff _).2 ϖ.ne_zero
  have h1 : valuation k (ϖ : k) ≤ 1 := (hϖ ▸ uniformizer_lt_one).le
  rw [map_mul, map_zpow₀, map_zpow₀, ← le_mul_inv_iff₀ (zpow_pos h0 n), one_mul, ← _root_.zpow_neg]
  rcases le_total 0 n with hn | hn
  · rw [max_eq_left (by omega), zpow_zero]
    have : (1 : ValueGroupWithZero k) ≤ valuation k (ϖ : k) ^ (-n) := by
      simpa using zpow_le_zpow_right_of_le_one₀ h0 h1 (show -n ≤ 0 by omega)
    exact ⟨fun h => h.1, fun h => ⟨h, h.trans this⟩⟩
  · rw [max_eq_right (by omega)]
    have : valuation k (ϖ : k) ^ (-n) ≤ 1 := by
      simpa using zpow_le_zpow_right_of_le_one₀ h0 h1 (show 0 ≤ -n by omega)
    exact ⟨fun h => h.2, fun h => ⟨h.trans this, h⟩⟩

theorem scal₂ {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (y : k) (n : ℤ) :
    (valuation k y < 1 ∧ valuation k ((ϖ : k) ^ (-n) * y) < 1) ↔
      valuation k y ≤ valuation k ((ϖ : k) ^ (1 + max 0 n)) := by
  rw [val_lt_one_iff hϖ, val_lt_one_iff hϖ]
  have h0 : 0 < valuation k (ϖ : k) := (Valuation.pos_iff _).2 ϖ.ne_zero
  have h1 : valuation k (ϖ : k) ≤ 1 := (hϖ ▸ uniformizer_lt_one).le
  rw [map_mul, map_zpow₀, map_zpow₀, mul_comm (valuation k (ϖ : k) ^ (-n)),
    ← le_mul_inv_iff₀ (zpow_pos h0 _), ← _root_.zpow_neg, neg_neg, ← zpow_one_add₀ h0.ne']
  rcases le_total 0 n with hn | hn
  · rw [max_eq_right hn]
    have : valuation k (ϖ : k) ^ (1 + n) ≤ valuation k (ϖ : k) := by
      simpa using zpow_le_zpow_right_of_le_one₀ h0 h1 (show 1 ≤ 1 + n by omega)
    exact ⟨fun h => h.2, fun h => ⟨h.trans this, h⟩⟩
  · rw [max_eq_left hn, add_zero, zpow_one]
    have : valuation k (ϖ : k) ≤ valuation k (ϖ : k) ^ (1 + n) := by
      simpa using zpow_le_zpow_right_of_le_one₀ h0 h1 (show 1 + n ≤ 1 by omega)
    exact ⟨fun h => h.1, fun h => ⟨h, h.trans this⟩⟩

theorem isUnit_det_iff_of_lower {R : Type} [CommRing R] [IsLocalRing R] {A D : Type} [Fintype A] [DecidableEq A]
    [Fintype D] [DecidableEq D] (N : Matrix (A ⊕ D) (A ⊕ D) R)
    (hN : ∀ i j, N (.inr i) (.inl j) ∈ IsLocalRing.maximalIdeal R) :
    IsUnit N.det ↔ IsUnit N.toBlocks₁₁.det ∧ IsUnit N.toBlocks₂₂.det := by
  simp only [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply]
  have e : N.map (IsLocalRing.residue R) = fromBlocks (N.toBlocks₁₁.map (IsLocalRing.residue R))
      (N.toBlocks₁₂.map (IsLocalRing.residue R)) 0 (N.toBlocks₂₂.map (IsLocalRing.residue R)) := by
    ext (i | i) (j | j) <;> simp [IsLocalRing.residue_eq_zero_iff, hN, toBlocks₁₁, toBlocks₁₂, toBlocks₂₂]
  rw [e, det_fromBlocks_zero₂₁, mul_ne_zero_iff]

theorem mem_KO_val_iff {n : Type} [Fintype n] [DecidableEq n] (y : Matrix n n k) :
    y ∈ Units.val '' (KO k n : Set (GL n k)) ↔ (∀ i j, valuation k (y i j) ≤ 1) ∧ valuation k y.det = 1 := by
  have hI := Valuation.integer.integers (valuation k)
  constructor
  · rintro ⟨g, ⟨u, rfl⟩, rfl⟩
    refine ⟨fun i j => (u.val i j).2, ?_⟩
    show valuation k ((algebraMap 𝒪[k] k).mapMatrix u.val).det = 1
    rw [← RingHom.map_det, ← hI.isUnit_iff_valuation_eq_one]
    exact (Matrix.isUnit_iff_isUnit_det _).1 u.isUnit
  · rintro ⟨h1, h2⟩
    let N : Matrix n n 𝒪[k] := fun i j => ⟨y i j, h1 i j⟩
    have hN : (algebraMap 𝒪[k] k).mapMatrix N = y := rfl
    have hu : IsUnit N := by
      rw [Matrix.isUnit_iff_isUnit_det, hI.isUnit_iff_valuation_eq_one, RingHom.map_det, hN]
      exact h2
    exact ⟨Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) hu.unit, ⟨hu.unit, rfl⟩, hN⟩

theorem val_det_iff_of_lower {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (y : Matrix (A ⊕ D) (A ⊕ D) k) (hi : ∀ i j, valuation k (y i j) ≤ 1)
    (hl : ∀ i j, valuation k (y (.inr i) (.inl j)) < 1) :
    valuation k y.det = 1 ↔ valuation k y.toBlocks₁₁.det = 1 ∧ valuation k y.toBlocks₂₂.det = 1 := by
  have hI := Valuation.integer.integers (valuation k)
  let N : Matrix (A ⊕ D) (A ⊕ D) 𝒪[k] := fun i j => ⟨y i j, hi i j⟩
  have hN : (algebraMap 𝒪[k] k).mapMatrix N = y := rfl
  have h11 : (algebraMap 𝒪[k] k).mapMatrix N.toBlocks₁₁ = y.toBlocks₁₁ := by ext; rfl
  have h22 : (algebraMap 𝒪[k] k).mapMatrix N.toBlocks₂₂ = y.toBlocks₂₂ := by ext; rfl
  have key := isUnit_det_iff_of_lower N (fun i j => by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hI.isUnit_iff_valuation_eq_one]
    exact (hl i j).ne)
  rwa [hI.isUnit_iff_valuation_eq_one, hI.isUnit_iff_valuation_eq_one, hI.isUnit_iff_valuation_eq_one,
    RingHom.map_det, RingHom.map_det, RingHom.map_det, hN, h11, h22] at key

theorem mem_parahoric_val_iff {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (y : Matrix (A ⊕ D) (A ⊕ D) k) :
    y ∈ Units.val '' (parahoric k A D : Set (GL (A ⊕ D) k)) ↔
      y.toBlocks₁₁ ∈ Units.val '' (KO k A : Set (GL A k)) ∧ (∀ i j, valuation k (y.toBlocks₁₂ i j) ≤ 1) ∧
      (∀ i j, valuation k (y.toBlocks₂₁ i j) < 1) ∧ y.toBlocks₂₂ ∈ Units.val '' (KO k D : Set (GL D k)) := by
  have step : y ∈ Units.val '' (parahoric k A D : Set (GL (A ⊕ D) k)) ↔
      y ∈ Units.val '' (KO k (A ⊕ D) : Set (GL (A ⊕ D) k)) ∧ ∀ i j, valuation k (y (.inr i) (.inl j)) < 1 := by
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, (mem_parahoric.1 hg).1, rfl⟩, (mem_parahoric.1 hg).2⟩
    · rintro ⟨⟨g, hg, rfl⟩, h⟩
      exact ⟨g, mem_parahoric.2 ⟨hg, h⟩, rfl⟩
  rw [step, mem_KO_val_iff, mem_KO_val_iff, mem_KO_val_iff]
  constructor
  · rintro ⟨⟨hi, hd⟩, hl⟩
    have hd' := (val_det_iff_of_lower y hi hl).1 hd
    exact ⟨⟨fun i j => hi _ _, hd'.1⟩, fun i j => hi _ _, hl, ⟨fun i j => hi _ _, hd'.2⟩⟩
  · rintro ⟨⟨h11, d11⟩, h12, hl, ⟨h22, d22⟩⟩
    have hi : ∀ i j, valuation k (y i j) ≤ 1 := by
      rintro (i | i) (j | j)
      · exact h11 i j
      · exact h12 i j
      · exact (hl i j).le
      · exact h22 i j
    exact ⟨⟨hi, (val_det_iff_of_lower y hi hl).2 ⟨d11, d22⟩⟩, hl⟩

theorem mem_val_map_conj_inf {n : Type} [Fintype n] [DecidableEq n] (K : Subgroup (GL n k)) (t : GL n k)
    (y : Matrix n n k) :
    y ∈ Units.val '' ((K.map (MulAut.conj t).toMonoidHom ⊓ K : Subgroup (GL n k)) : Set (GL n k)) ↔
      y ∈ Units.val '' (K : Set (GL n k)) ∧
        (t⁻¹ : GL n k).val * y * t.val ∈ Units.val '' (K : Set (GL n k)) := by
  constructor
  · rintro ⟨g, ⟨hg1, hg2⟩, rfl⟩
    replace hg1 : g ∈ K.map (MulAut.conj t).toMonoidHom := hg1
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at hg1
    exact ⟨⟨g, hg2, rfl⟩, ⟨_, hg1, by simp⟩⟩
  · rintro ⟨⟨g, hg, rfl⟩, ⟨h, hh, e⟩⟩
    refine ⟨g, ⟨?_, hg⟩, rfl⟩
    show g ∈ K.map (MulAut.conj t).toMonoidHom
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    have : t⁻¹ * g * t = h := Units.ext (by simp [e])
    rwa [this]

theorem val_inv_torusElt {n : Type} [Fintype n] [DecidableEq n] (ϖ : kˣ) (f : n → ℤ) :
    ((torusElt k n ϖ f)⁻¹).val = diagonal fun i => (ϖ : k) ^ (-f i) := by
  have : (torusElt k n ϖ f)⁻¹ = torusElt k n ϖ (-f) := by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv]
    apply Units.ext
    rw [Units.val_mul, val_torusElt, val_torusElt, diagonal_mul_diagonal, Units.val_one, ← diagonal_one]
    congr 1
    funext i
    simp only [Pi.neg_apply, _root_.zpow_neg]
    exact inv_mul_cancel₀ (zpow_ne_zero _ ϖ.ne_zero)
  rw [this, val_torusElt]
  rfl

section conjBlocks
variable {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (e : D → ℤ)
  (x : Matrix (A ⊕ D) (A ⊕ D) k)

theorem conj_apply (i j : A ⊕ D) :
    (((mtor (A := A) ϖ e)⁻¹.val * x * (mtor (A := A) ϖ e).val : Matrix (A ⊕ D) (A ⊕ D) k)) i j =
      (ϖ : k) ^ (-(Sum.elim 0 e i : ℤ)) * x i j * (ϖ : k) ^ (Sum.elim 0 e j : ℤ) := by
  have h1 : ((mtor (A := A) ϖ e)⁻¹.val : Matrix (A ⊕ D) (A ⊕ D) k) =
      diagonal fun i => (ϖ : k) ^ (-(Sum.elim 0 e i : ℤ)) := val_inv_torusElt _ _
  have h2 : ((mtor (A := A) ϖ e).val : Matrix (A ⊕ D) (A ⊕ D) k) =
      diagonal fun i => (ϖ : k) ^ (Sum.elim 0 e i : ℤ) := val_torusElt _ _
  rw [h1, h2, mul_diagonal, diagonal_mul]

theorem conj_toBlocks₁₁ :
    (((mtor (A := A) ϖ e)⁻¹.val * x * (mtor (A := A) ϖ e).val : Matrix (A ⊕ D) (A ⊕ D) k)).toBlocks₁₁ =
      x.toBlocks₁₁ := by
  ext i j
  simp only [toBlocks₁₁, of_apply]
  rw [conj_apply]
  simp

theorem conj_toBlocks₁₂ (i : A) (j : D) :
    (((mtor (A := A) ϖ e)⁻¹.val * x * (mtor (A := A) ϖ e).val : Matrix (A ⊕ D) (A ⊕ D) k)).toBlocks₁₂ i j =
      x.toBlocks₁₂ i j * (ϖ : k) ^ e j := by
  simp only [toBlocks₁₂, of_apply]
  rw [conj_apply]
  simp

theorem conj_toBlocks₂₁ (i : D) (j : A) :
    (((mtor (A := A) ϖ e)⁻¹.val * x * (mtor (A := A) ϖ e).val : Matrix (A ⊕ D) (A ⊕ D) k)).toBlocks₂₁ i j =
      (ϖ : k) ^ (-e i) * x.toBlocks₂₁ i j := by
  simp only [toBlocks₂₁, of_apply]
  rw [conj_apply]
  simp

theorem conj_toBlocks₂₂ :
    (((mtor (A := A) ϖ e)⁻¹.val * x * (mtor (A := A) ϖ e).val : Matrix (A ⊕ D) (A ⊕ D) k)).toBlocks₂₂ =
      ((torusElt k D ϖ e)⁻¹.val * x.toBlocks₂₂ * (torusElt k D ϖ e).val : Matrix D D k) := by
  have h1 : ((torusElt k D ϖ e)⁻¹.val : Matrix D D k) = diagonal fun i => (ϖ : k) ^ (-e i) := val_inv_torusElt _ _
  have h2 : ((torusElt k D ϖ e).val : Matrix D D k) = diagonal fun i => (ϖ : k) ^ e i := val_torusElt _ _
  rw [h1, h2]
  ext i j
  rw [mul_diagonal, diagonal_mul]
  simp only [toBlocks₂₂, of_apply]
  rw [conj_apply]
  simp

end conjBlocks

theorem blockset : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ),
    valuation k (ϖ : k) = uniformizer k →
    ∀ (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (e : D → ℤ),
    Units.val '' (((parahoric k A D).map (MulAut.conj (mtor (A := A) ϖ e)).toMonoidHom ⊓ parahoric k A D :
        Subgroup (GL (A ⊕ D) k)) : Set (GL (A ⊕ D) k)) =
      {x | x.toBlocks₁₁ ∈ Units.val '' (KO k A : Set (GL A k)) ∧
        x.toBlocks₁₂ ∈ {y : Matrix A D k | ∀ i j, valuation k (y i j) ≤ valuation k ((ϖ : k) ^ max 0 (-e j))} ∧
        x.toBlocks₂₁ ∈ {y : Matrix D A k | ∀ i j, valuation k (y i j) ≤ valuation k ((ϖ : k) ^ (1 + max 0 (e i)))} ∧
        x.toBlocks₂₂ ∈ Units.val '' (((KO k D).map (MulAut.conj (torusElt k D ϖ e)).toMonoidHom ⊓ KO k D :
          Subgroup (GL D k)) : Set (GL D k))} := by
  intro k _ _ _ _ ϖ hϖ A D _ _ _ _ e
  ext x
  rw [mem_val_map_conj_inf, mem_parahoric_val_iff, mem_parahoric_val_iff, conj_toBlocks₁₁, conj_toBlocks₂₂]
  simp only [conj_toBlocks₁₂, conj_toBlocks₂₁, Set.mem_setOf_eq, mem_val_map_conj_inf, ← scal₁ hϖ, ← scal₂ hϖ,
    forall_and]
  tauto

end GlobalTheory.ParahoricConjBlocks
