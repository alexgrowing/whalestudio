import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace DeterminantHeight

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem dt_eq (g : GA E k) :
    Dt g = (GroundTheory.Global.IdeleGroup.ideleModule E (AdelicGLn.det E k g) : ℝ) := rfl

theorem dt_maxCompact {κ : GA E k} (hκ : κ ∈ maxCompact) : Dt κ = 1 := by
  rw [dt_eq]; exact mem_normOneGL.1 (maxCompact_le_normOneGL hκ)

theorem dt_diag (γ : GL (Fin k) E) : Dt (AdelicGLn.diagonal E k γ) = 1 := by
  rw [dt_eq]; exact mem_normOneGL.1 (rationalGL_le_normOneGL ⟨γ, rfl⟩)

theorem dt_mul (g h : GA E k) : Dt (g * h) = Dt g * Dt h := by
  rw [dt_eq, dt_eq, dt_eq, map_mul, map_mul, Positive.val_mul]

theorem adeleAbs_pos {b : GA E k} (hb : b ∈ adelicBorel) (i : Fin k) :
    0 < adeleAbs ((b : Matrix (Fin k) (Fin k) (Ad E)) i i) := by
  rw [← IsUnit.unit_spec (isUnit_apply_self_of_mem_adelicBorel hb i), adeleAbs_units]
  exact (GroundTheory.Global.IdeleGroup.ideleModule E _).2

theorem dt_borel {b : GA E k} (hb : b ∈ adelicBorel) :
    Dt b = ∏ i, adeleAbs ((b : Matrix (Fin k) (Fin k) (Ad E)) i i) := by
  have hu : ∀ i, IsUnit ((b : Matrix (Fin k) (Fin k) (Ad E)) i i) :=
    isUnit_apply_self_of_mem_adelicBorel hb
  have hdet : AdelicGLn.det E k b = ∏ i, (hu i).unit := by
    ext
    rw [AdelicGLn.coe_det, Matrix.det_of_isUpperTriangular hb, Units.coe_prod]
    simp
  rw [dt_eq, hdet, map_prod (GroundTheory.Global.IdeleGroup.ideleModule E), coe_finset_prod_pos]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← adeleAbs_units, IsUnit.unit_spec]

theorem height_last {b : GA E k} (hb : b ∈ adelicBorel) (L : Fin k) (hL : (L : ℕ) + 1 = k) :
    height b (Pi.single L 1) = adeleAbs ((b : Matrix (Fin k) (Fin k) (Ad E)) L L) := by
  have hu := isUnit_apply_self_of_mem_adelicBorel hb L
  have hrow : ratVec (Pi.single L (1 : E)) ᵥ* (b : Matrix (Fin k) (Fin k) (Ad E)) =
      Pi.single L ((b : Matrix (Fin k) (Fin k) (Ad E)) L L) := by
    have : ratVec (Pi.single L (1 : E)) = Pi.single L (1 : Ad E) := by
      ext l
      by_cases hl : l = L
      · subst hl; simp [ratVec]
      · simp [ratVec, Pi.single_eq_of_ne hl]
    rw [this, single_one_vecMul]
    ext l
    by_cases hl : l = L
    · subst hl; simp [Matrix.row]
    · have hlt : l < L := lt_of_le_of_ne (Fin.le_iff_val_le_val.2 (by omega)) hl
      simp [Matrix.row, Pi.single_eq_of_ne hl, hb hlt]
  rw [Reduction.height, hrow, ← IsUnit.unit_spec hu, adelicNorm_single_units, adeleAbs_units]

end DeterminantHeight

theorem minkowski_bound_of : D0 → MinkowskiBoundAlt := by
  intro _ E _ _ _ k hk
  obtain ⟨t₀, ht₀, hred⟩ := GroundTheory.Automorphic.Reduction.exists_reduced (K := E)
  set s : ℝ := min t₀ 1 with hs
  have hs0 : 0 < s := lt_min ht₀ one_pos
  have hs1 : s ≤ 1 := min_le_right _ _
  refine ⟨(s ^ k)⁻¹, fun g => ?_⟩
  obtain ⟨γ, b, hb, κ, hκ, heq, hr⟩ := hred k g
  set L : Fin k := ⟨k - 1, by omega⟩ with hLdef
  have hL : (L : ℕ) + 1 = k := by simp [L]; omega
  set a : Fin k → ℝ := fun i => adeleAbs ((b : Matrix (Fin k) (Fin k) (Ad E)) i i) with hadef
  have ha : ∀ i, 0 < a i := fun i => DeterminantHeight.adeleAbs_pos hb i
  refine ⟨Pi.single L 1 ᵥ* (γ : Matrix (Fin k) (Fin k) E), ?_, ?_⟩
  · intro h
    have h2 := congrArg (fun y => y ᵥ* ((γ⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E)) h
    simp only [vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one,
      zero_vecMul] at h2
    have := congrFun h2 L
    simp at this
  · have hH : Reduction.height g (Pi.single L 1 ᵥ* (γ : Matrix (Fin k) (Fin k) E)) = a L := by
      rw [← height_diagonal_mul, heq, height_mul_maxCompact _ hκ, DeterminantHeight.height_last hb L hL]
    have hD : Dt g = ∏ i, a i := by
      have h1 : Dt (AdelicGLn.diagonal E k γ * g) = Dt g := by
        rw [DeterminantHeight.dt_mul, DeterminantHeight.dt_diag, one_mul]
      rw [← h1, heq, DeterminantHeight.dt_mul, DeterminantHeight.dt_maxCompact hκ, mul_one, DeterminantHeight.dt_borel hb]
    have hchain : ∀ d : ℕ, ∀ i : Fin k, (i : ℕ) + d = k - 1 → s ^ d * a L ≤ a i := by
      intro d
      induction d with
      | zero =>
        intro i hi
        have : i = L := Fin.ext (by simp [L]; omega)
        subst this; simp
      | succ d ih =>
        intro i hi
        have hi' : (i : ℕ) + 1 < k := by omega
        have h1 := ih ⟨(i : ℕ) + 1, hi'⟩ (by simp; omega)
        have h2 := hr i ⟨(i : ℕ) + 1, hi'⟩ rfl
        calc s ^ (d + 1) * a L = s * (s ^ d * a L) := by ring
          _ ≤ s * a ⟨(i : ℕ) + 1, hi'⟩ := mul_le_mul_of_nonneg_left h1 hs0.le
          _ ≤ t₀ * a ⟨(i : ℕ) + 1, hi'⟩ := mul_le_mul_of_nonneg_right (min_le_left _ _) (ha _).le
          _ ≤ a i := h2
    have hlow : ∀ i, s ^ k * a L ≤ a i := fun i =>
      (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hs0.le hs1 (by omega : k - 1 - (i : ℕ) ≤ k))
        (ha L).le).trans (hchain (k - 1 - (i : ℕ)) i (by omega))
    have hsa : 0 < s ^ k * a L := mul_pos (pow_pos hs0 k) (ha L)
    have hprod : (s ^ k * a L) ^ k ≤ Dt g := by
      rw [hD]
      calc (s ^ k * a L) ^ k = ∏ _i : Fin k, s ^ k * a L := by simp
        _ ≤ ∏ i, a i := Finset.prod_le_prod (fun _ _ => hsa.le) (fun i _ => hlow i)
    have hDt : 0 < Dt g := by rw [hD]; exact Finset.prod_pos fun i _ => ha i
    have hDpos : 0 < Dt g ^ ((k : ℝ)⁻¹) := Real.rpow_pos_of_pos hDt _
    have hDk : (Dt g ^ ((k : ℝ)⁻¹)) ^ k = Dt g := Real.rpow_inv_natCast_pow hDt.le (by omega)
    have hle : s ^ k * a L ≤ Dt g ^ ((k : ℝ)⁻¹) :=
      (pow_le_pow_iff_left₀ hsa.le hDpos.le (by omega : k ≠ 0)).1 (hprod.trans hDk.ge)
    have hsk : 0 < s ^ k := pow_pos hs0 k
    rw [ht, hH, div_le_iff₀ hDpos, inv_mul_eq_div, le_div_iff₀ hsk]
    linarith

end PositivityTheory.AdelicQuotientData

end
