import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

noncomputable section

namespace GlobalTheory.SchurExtCpt

open Matrix

section Mat

variable {R : Type} [CommRing R] {m r : ℕ}

theorem eqv_symm_inl_val (a : Fin (m + 1)) : (((eqv m r).symm (Sum.inl a)) : ℕ) = a := by simp [eqv]

theorem eqv_symm_inr_val (b : Fin (r + 1)) : (((eqv m r).symm (Sum.inr b)) : ℕ) = m + 1 + b := by simp [eqv]

theorem unblk_mul (P Q : Matrix (Fin (m + 1) ⊕ Fin (r + 1)) (Fin (m + 1) ⊕ Fin (r + 1)) R) :
    unblk P * unblk Q = unblk (P * Q) := by
  unfold unblk; exact Matrix.submatrix_mul_equiv P Q _ _ _

theorem unblk_one : (unblk (1 : Matrix (Fin (m + 1) ⊕ Fin (r + 1)) (Fin (m + 1) ⊕ Fin (r + 1)) R)) = 1 := by
  unfold unblk; exact Matrix.submatrix_one_equiv _

theorem fromBlocks_decomp {a b : ℕ} (A : Matrix (Fin a) (Fin a) R) (B : Matrix (Fin a) (Fin b) R)
    (C : Matrix (Fin b) (Fin a) R) (D : Matrix (Fin b) (Fin b) R) (uA cA : Matrix (Fin a) (Fin a) R)
    (uD cD : Matrix (Fin b) (Fin b) R) (hD : IsUnit D.det) (hA : uA * cA = A - B * D⁻¹ * C) (hD' : uD * cD = D) :
    fromBlocks uA (B * D⁻¹ * uD) 0 uD * fromBlocks cA 0 (cD * (D⁻¹ * C)) cD = fromBlocks A B C D := by
  rw [fromBlocks_multiply]
  have h1 : B * D⁻¹ * uD * (cD * (D⁻¹ * C)) = B * D⁻¹ * C := by
    rw [Matrix.mul_assoc (B * D⁻¹) uD, ← Matrix.mul_assoc uD, hD', Matrix.mul_nonsing_inv_cancel_left _ _ hD]
  have h2 : B * D⁻¹ * uD * cD = B := by
    rw [Matrix.mul_assoc (B * D⁻¹) uD, hD', Matrix.nonsing_inv_mul_cancel_right _ _ hD]
  have h3 : uD * (cD * (D⁻¹ * C)) = C := by
    rw [← Matrix.mul_assoc, hD', Matrix.mul_nonsing_inv_cancel_left _ _ hD]
  simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, h1, h2, h3, hD', hA, sub_add_cancel]

end Mat

variable {E : Type} [Field E] [NumberField E] {m r : ℕ}

def gEl (a : GA E (m + 1)) (d : GA E (r + 1)) (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E)) : GA E (m + r + 1 + 1) where
  val := unblk (fromBlocks (a : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) 0 ((d : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) * Y) d)
  inv := unblk (fromBlocks ((a⁻¹ : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) 0
    (-(Y * ((a⁻¹ : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)))) ((d⁻¹ : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)))
  val_inv := by
    rw [unblk_mul, fromBlocks_multiply, ← unblk_one, ← fromBlocks_one]
    congr 1
    simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, Units.mul_inv, Matrix.mul_neg, Matrix.mul_assoc,
      add_neg_cancel, neg_zero]
  inv_val := by
    rw [unblk_mul, fromBlocks_multiply, ← unblk_one, ← fromBlocks_one]
    congr 1
    simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, Units.inv_mul, Matrix.neg_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc ((d⁻¹ : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) (d : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)),
      Matrix.mul_one, Matrix.one_mul, neg_add_cancel]

theorem coe_gEl (a : GA E (m + 1)) (d : GA E (r + 1)) (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E)) :
    ((gEl a d Y : GA E (m + r + 1 + 1)) : Matrix _ _ (Ad E)) =
      unblk (fromBlocks (a : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) 0 ((d : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) * Y) d) := rfl

theorem continuous_gEl :
    Continuous fun z : GA E (m + 1) × GA E (r + 1) × Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E) => gEl z.1 z.2.1 z.2.2 := by
  rw [Units.continuous_iff]
  have ha : Continuous fun z : GA E (m + 1) × GA E (r + 1) × Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E) =>
      ((z.1 : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) := Units.continuous_val.comp continuous_fst
  have ha' : Continuous fun z : GA E (m + 1) × GA E (r + 1) × Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E) =>
      ((z.1⁻¹ : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) := Units.continuous_coe_inv.comp continuous_fst
  have hd : Continuous fun z : GA E (m + 1) × GA E (r + 1) × Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E) =>
      ((z.2.1 : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) :=
    Units.continuous_val.comp (continuous_fst.comp continuous_snd)
  have hd' : Continuous fun z : GA E (m + 1) × GA E (r + 1) × Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E) =>
      ((z.2.1⁻¹ : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) :=
    Units.continuous_coe_inv.comp (continuous_fst.comp continuous_snd)
  have hY : Continuous fun z : GA E (m + 1) × GA E (r + 1) × Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E) => z.2.2 :=
    continuous_snd.comp continuous_snd
  have h0 : Continuous fun _ : GA E (m + 1) × GA E (r + 1) × Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E) =>
      (0 : Matrix (Fin (m + 1)) (Fin (r + 1)) (Ad E)) := continuous_const
  constructor
  · exact (Continuous.matrix_fromBlocks ha h0 (hd.matrix_mul hY) hd).matrix_submatrix _ _
  · exact (Continuous.matrix_fromBlocks ha' h0 (hY.matrix_mul ha').neg hd').matrix_submatrix _ _

theorem mem_NA_of_blocks (uA : GA E (m + 1)) (uD : GA E (r + 1)) (huA : uA ∈ GlobalTheory.JSW.NA E (m + 1))
    (huD : uD ∈ GlobalTheory.JSW.NA E (r + 1)) (X : Matrix (Fin (m + 1)) (Fin (r + 1)) (Ad E)) (u : GA E (m + r + 1 + 1))
    (hu : (u : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) =
      unblk (fromBlocks (uA : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) X 0 (uD : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)))) :
    u ∈ GlobalTheory.JSW.NA E (m + r + 1 + 1) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩ <;> rw [hu]
  · obtain ⟨x, rfl⟩ := (eqv m r).symm.surjective i
    obtain ⟨y, rfl⟩ := (eqv m r).symm.surjective j
    simp only [unblk, submatrix_apply, Equiv.apply_symm_apply]
    rw [Fin.lt_iff_val_lt_val] at hij
    rcases x with a | a <;> rcases y with b | b
    · simp only [eqv_symm_inl_val] at hij
      rw [fromBlocks_apply₁₁]; exact huA.1 a b (Fin.lt_iff_val_lt_val.2 hij)
    · simp only [eqv_symm_inl_val, eqv_symm_inr_val] at hij
      exact absurd hij (by have := a.isLt; omega)
    · rw [fromBlocks_apply₂₁, Matrix.zero_apply]
    · simp only [eqv_symm_inr_val] at hij
      rw [fromBlocks_apply₂₂]; exact huD.1 a b (Fin.lt_iff_val_lt_val.2 (by omega))
  · obtain ⟨x, rfl⟩ := (eqv m r).symm.surjective i
    simp only [unblk, submatrix_apply, Equiv.apply_symm_apply]
    rcases x with a | a
    · rw [fromBlocks_apply₁₁]; exact huA.2 a
    · rw [fromBlocks_apply₂₂]; exact huD.2 a

variable [IsTotallyComplex E]

def adOf (z : (Fin (r + 1) → Fin (m + 1) → Cinf E) × (Fin (r + 1) → Fin (m + 1) → Af E)) :
    Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E) :=
  fun i j => ((infEq E (z.1 i j), z.2 i j) : InfiniteAdeleRing E × Af E)

theorem continuous_adOf : Continuous (adOf (E := E) (m := m) (r := r)) := by
  refine continuous_matrix fun i j => ?_
  exact ((continuous_infEq E).comp ((continuous_apply j).comp ((continuous_apply i).comp continuous_fst))).prodMk
    ((continuous_apply j).comp ((continuous_apply i).comp continuous_snd))

end GlobalTheory.SchurExtCpt

open Matrix GlobalTheory.SchurExtCpt in

theorem GlobalTheory.SchurExtCpt.exists_compact_support : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S, β h ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * h ∈ C) → (∃ C : Set (GA E (r + 1)), IsCompact C ∧ ∀ p, b₁ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (r + 1), u⁻¹ * p ∈ C) → HasCompactSupport χ → ∃ C : Set (GA E (m + r + 1 + 1)), IsCompact C ∧ ∀ p ∈ GlobalTheory.JSW.mirS E S (m + r + 1), schurF β b₁ χ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (m + r + 1 + 1), u⁻¹ * p ∈ C := by
  intro E _ _ _ m r S β b₁ χ ⟨Cβ, hCβ, hβ⟩ ⟨C₁, hC₁, hb⟩ hχ
  let K : Set (Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E)) := adOf ''
    (tsupport χ ×ˢ Set.univ.pi fun _ => Set.univ.pi fun _ =>
      (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (Af E)))
  have hK : IsCompact K := (hχ.isCompact.prod (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    GroundTheory.Global.isCompact_integralFiniteAdeles E)).image continuous_adOf
  refine ⟨(fun z : GA E (m + 1) × GA E (r + 1) × Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E) => gEl z.1 z.2.1 z.2.2) ''
    (Cβ ×ˢ C₁ ×ˢ K), (hCβ.prod (hC₁.prod hK)).image continuous_gEl, ?_⟩
  intro p hp hF
  by_cases hD : IsUnit (Dof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det
  swap
  · exact absurd (by unfold schurF; rw [if_neg hD]) hF
  unfold schurF at hF
  rw [if_pos hD] at hF
  obtain ⟨⟨⟨-, h2⟩, h3⟩, h4⟩ := (mul_ne_zero_iff.1 hF) |>.imp (mul_ne_zero_iff.1) id |>.imp (fun h => h.imp mul_ne_zero_iff.1 id) id

  have hdet : IsUnit (Scof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det := by
    haveI : Invertible (blk (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).toBlocks₂₂ :=
      Matrix.invertibleOfIsUnitDet _ hD
    have he : (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).det =
        (Dof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det *
          (Scof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det := by
      rw [← Matrix.det_submatrix_equiv_self (eqv m r).symm (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))]
      change (blk (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det = _
      rw [← Matrix.fromBlocks_toBlocks (blk (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))),
        Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]
      rfl
    have hu := Matrix.isUnits_det_units p
    rw [he] at hu
    exact isUnit_of_mul_isUnit_right hu

  have hsup : mkGL (Scof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) ∈ GlobalTheory.JSW.supS E (m + 1) S := by
    intro w hw
    have hpw := congrArg Units.val (hp.1 w hw)
    apply Units.ext
    change (mkGL (Scof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)).map ((pLoc E w).comp (pFin E)) = 1
    change (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map ((pLoc E w).comp (pFin E)) = 1 at hpw
    rw [coe_mkGL hdet]
    have hbl : (blk (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map ((pLoc E w).comp (pFin E)) = 1 := by
      rw [show (blk (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map ((pLoc E w).comp (pFin E)) =
        blk ((p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map ((pLoc E w).comp (pFin E))) from rfl, hpw]
      exact Matrix.submatrix_one_equiv _
    have hA : (Aof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map ((pLoc E w).comp (pFin E)) = 1 := by
      rw [show (Aof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map ((pLoc E w).comp (pFin E)) =
        ((blk (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map ((pLoc E w).comp (pFin E))).toBlocks₁₁ from rfl,
        hbl, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₁]
    have hB : (Bof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map ((pLoc E w).comp (pFin E)) = 0 := by
      rw [show (Bof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map ((pLoc E w).comp (pFin E)) =
        ((blk (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map ((pLoc E w).comp (pFin E))).toBlocks₁₂ from rfl,
        hbl, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₂]
    unfold Scof
    rw [Matrix.map_sub _ (map_sub ((pLoc E w).comp (pFin E))), Matrix.map_mul, Matrix.map_mul, hA, hB]
    simp
  obtain ⟨uA, huA, hcA⟩ := hβ _ hsup h2
  obtain ⟨uD, huD, hcD⟩ := hb _ h3

  have hY : Yof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) ∈ K := by
    unfold chiF at h4
    obtain ⟨h41, h42⟩ := mul_ne_zero_iff.1 h4
    have hint : ∀ i j, pFin E (Yof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) ∈
        GroundTheory.Global.integralFiniteAdeles (𝓞 E) E := by
      by_contra hc
      rw [if_neg hc] at h42
      exact h42 rfl
    refine ⟨(fun i j => pInf E (Yof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j),
      fun i j => pFin E (Yof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j)), ⟨subset_tsupport _ ?_, ?_⟩, ?_⟩
    · intro h
      apply h41
      rw [h]
      simp
    · simp only [Set.mem_univ_pi]
      exact fun i j => hint i j
    · funext i j
      refine ad_ext ?_ rfl
      show (infEq E).symm (infEq E _) = _
      exact RingEquiv.symm_apply_apply _ _
  refine ⟨p * (gEl (uA⁻¹ * mkGL (Scof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))))
    (uD⁻¹ * mkGL (Dof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))))
    (Yof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))))⁻¹, ?_, ⟨(_, _, _), ⟨hcA, hcD, hY⟩, ?_⟩⟩
  · refine mem_NA_of_blocks uA uD huA huD (Bof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) *
      (Dof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)))⁻¹ * (uD : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E))) _ ?_
    have hpU : (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) =
        unblk (fromBlocks (uA : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Bof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) *
          (Dof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)))⁻¹ * (uD : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E))) 0
          (uD : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E))) *
        ((gEl (uA⁻¹ * mkGL (Scof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))))
          (uD⁻¹ * mkGL (Dof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))))
          (Yof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) : GA E (m + r + 1 + 1)) :
            Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) := by
      rw [coe_gEl, unblk_mul]
      conv_lhs => rw [← unblk_blk (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))]
      congr 1
      rw [← Matrix.fromBlocks_toBlocks (blk (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)))]
      refine (fromBlocks_decomp _ _ _ _ _ _ _ _ hD ?_ ?_).symm
      · rw [← Units.val_mul, mul_inv_cancel_left, coe_mkGL hdet]; try rfl
      · rw [← Units.val_mul, mul_inv_cancel_left, coe_mkGL hD]; try rfl
    rw [Units.val_mul, Units.mul_inv_eq_iff_eq_mul]
    exact hpU
  · rw [_root_.mul_inv_rev, inv_inv, inv_mul_cancel_right]
    rfl
