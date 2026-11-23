import Mathlib
import GroundTheory.AutomorphicForms.ReductionLocalVolumeTorus
import GroundTheory.AutomorphicForms.RealIwasawaIntegration

open MeasureTheory Measure Set Matrix
open scoped NNReal ENNReal

namespace GroundTheory.Automorphic

noncomputable section

namespace Reduction

variable {𝕜 : Type*} [RCLike 𝕜] {m : ℕ}

variable (m) in

def expPosDiag : (Fin (m + 1) → ℝ) ≃ₜ PosDiag (Fin (m + 1)) where
  toFun x := ⟨fun i => Real.exp (x i), fun i => Real.exp_pos _⟩
  invFun a := fun i => Real.log (a.1 i)
  left_inv x := by funext i; simp
  right_inv a := by apply Subtype.ext; funext i; simp [Real.exp_log (a.2 i)]
  continuous_toFun :=
    Continuous.subtype_mk (continuous_pi fun i => Real.continuous_exp.comp (continuous_apply i)) _
  continuous_invFun := continuous_pi fun i =>
    Real.continuousOn_log.comp_continuous ((continuous_apply i).comp continuous_subtype_val)
      fun a => (a.2 i).ne'

variable (𝕜 m) in

def expDiag : (Fin (m + 1) → ℝ) ≃ₜ diagPosSubgroup (Fin (m + 1)) 𝕜 :=
  (expPosDiag m).trans diagPosHomeomorph

theorem coe_expDiag (x : Fin (m + 1) → ℝ) :
    ((expDiag 𝕜 m x : diagPosSubgroup (Fin (m + 1)) 𝕜) : GL (Fin (m + 1)) 𝕜) =
      diagPosOf ⟨fun i => Real.exp (x i), fun i => Real.exp_pos _⟩ := rfl

theorem expDiag_add (x y : Fin (m + 1) → ℝ) :
    expDiag 𝕜 m (x + y) = expDiag 𝕜 m x * expDiag 𝕜 m y := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_expDiag, coe_diagPosOf, diagonal_mul_diagonal,
    Pi.add_apply, Real.exp_add, RCLike.ofReal_mul]

variable [MeasurableSpace (GL (Fin (m + 1)) 𝕜)] [BorelSpace (GL (Fin (m + 1)) 𝕜)]

theorem isHaarMeasure_map_expDiag :
    (Measure.map (expDiag 𝕜 m) (volume : Measure (Fin (m + 1) → ℝ))).IsHaarMeasure := by
  have hmeas : Measurable (expDiag 𝕜 m) := (expDiag 𝕜 m).continuous.measurable
  have h1 : IsFiniteMeasureOnCompacts (Measure.map (expDiag 𝕜 m) (volume : Measure (Fin (m + 1) → ℝ))) := by
    refine ⟨fun C hC => ?_⟩
    rw [Measure.map_apply hmeas hC.isClosed.measurableSet]
    rw [← (expDiag 𝕜 m).image_symm]
    exact (hC.image (expDiag 𝕜 m).symm.continuous).measure_lt_top
  have h2 : (Measure.map (expDiag 𝕜 m) (volume : Measure (Fin (m + 1) → ℝ))).IsMulLeftInvariant := by
    refine ⟨fun a => ?_⟩
    obtain ⟨z, rfl⟩ := (expDiag 𝕜 m).surjective a
    rw [Measure.map_map (measurable_const_mul _) hmeas]
    have : (fun x => expDiag 𝕜 m z * x) ∘ expDiag 𝕜 m = expDiag 𝕜 m ∘ (fun x => z + x) := by
      funext x; simp [expDiag_add]
    rw [this, ← Measure.map_map hmeas (measurable_const_add z), map_add_left_eq_self]
  have h3 : (Measure.map (expDiag 𝕜 m) (volume : Measure (Fin (m + 1) → ℝ))).IsOpenPosMeasure := by
    refine ⟨fun U hU hne => ?_⟩
    rw [Measure.map_apply hmeas hU.measurableSet]
    exact (hU.preimage (expDiag 𝕜 m).continuous).measure_ne_zero volume
      (hne.preimage (expDiag 𝕜 m).surjective)
  exact {}

section Coordinates

variable {n : ℕ}

theorem ANK_unique {a a' : diagPosSubgroup (Fin n) 𝕜} {u u' : upperUnipotentSubgroup (Fin n) 𝕜}
    {k k' : unitaryGroup (Fin n) 𝕜}
    (h : (a : GL (Fin n) 𝕜) * u * Unitary.toUnits k = (a' : GL (Fin n) 𝕜) * u' * Unitary.toUnits k') :
    a = a' ∧ u = u' := by
  set x : GL (Fin n) 𝕜 := ((a' : GL (Fin n) 𝕜) * u')⁻¹ * ((a : GL (Fin n) 𝕜) * u) with hx
  have hxB : x ∈ upperPosSubgroup (Fin n) 𝕜 :=
    mul_mem (inv_mem (mul_mem (diagPosSubgroup_le_upperPosSubgroup a'.2)
      (upperUnipotentSubgroup_le_upperPosSubgroup u'.2)))
      (mul_mem (diagPosSubgroup_le_upperPosSubgroup a.2)
        (upperUnipotentSubgroup_le_upperPosSubgroup u.2))
  have hxK : x = Unitary.toUnits k' * (Unitary.toUnits k)⁻¹ := by
    rw [hx, inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]
  have hxU : (x : Matrix (Fin n) (Fin n) 𝕜) ∈ unitaryGroup (Fin n) 𝕜 := by
    rw [hxK, ← map_inv, ← map_mul]
    exact (k' * k⁻¹).2
  have hx1 : x = 1 := Units.ext (eq_one_of_mem_unitaryGroup_of_isUpperTriangular hxU hxB.1 hxB.2)
  have hau : (a : GL (Fin n) 𝕜) * u = a' * u' := by
    rw [hx, inv_mul_eq_one] at hx1
    exact hx1.symm
  have hdiag : ∀ (c : diagPosSubgroup (Fin n) 𝕜) (v : upperUnipotentSubgroup (Fin n) 𝕜) (i : Fin n),
      (((c : GL (Fin n) 𝕜) * v : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜) i i =
        ((c : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜) i i := fun c v i => by
    rw [Units.val_mul, eq_diagonal_of_mem_diagPos c.2, diagonal_mul, v.2.2 i, mul_one,
      diagonal_apply_eq]
  have haa : a = a' := by
    apply Subtype.ext
    apply Units.ext
    rw [eq_diagonal_of_mem_diagPos a.2, eq_diagonal_of_mem_diagPos a'.2]
    congr 1
    funext i
    rw [← hdiag a u i, ← hdiag a' u' i, hau]
  refine ⟨haa, ?_⟩
  subst haa
  exact Subtype.ext (mul_left_cancel hau)

def unipotentPart (b : Matrix (Fin n) (Fin n) 𝕜) : StrictUpperIndex (Fin n) → 𝕜 :=
  fun p => b p.1.1 p.1.2 / b p.1.2 p.1.2

theorem apply_self_ne_zero_of_isUpperTriangular {b : GL (Fin n) 𝕜}
    (hb : (b : Matrix (Fin n) (Fin n) 𝕜).IsUpperTriangular) (i : Fin n) :
    (b : Matrix (Fin n) (Fin n) 𝕜) i i ≠ 0 := by
  have hdet : (b : Matrix (Fin n) (Fin n) 𝕜).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 b.isUnit).ne_zero
  rw [det_of_isUpperTriangular hb] at hdet
  exact Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ i)

theorem unipotentOfCoords_unipotentPart_mul {b : GL (Fin n) 𝕜}
    (hb : (b : Matrix (Fin n) (Fin n) 𝕜).IsUpperTriangular) :
    ((unipotentOfCoords (unipotentPart (b : Matrix (Fin n) (Fin n) 𝕜)) : GL (Fin n) 𝕜) :
      Matrix (Fin n) (Fin n) 𝕜) * diagonal (fun i => (b : Matrix (Fin n) (Fin n) 𝕜) i i) =
      (b : Matrix (Fin n) (Fin n) 𝕜) := by
  ext i j
  rw [mul_diagonal, coe_unipotentOfCoords, Matrix.add_apply, one_apply, strictUpperMatrix_apply]
  by_cases hij : i = j
  · subst hij; simp
  · by_cases h : i < j
    · simp only [hij, h, if_false, dite_true, zero_add, unipotentPart]
      rw [div_mul_cancel₀ _ (apply_self_ne_zero_of_isUpperTriangular hb j)]
    · simp only [hij, h, if_false, dite_false, add_zero, zero_mul]
      exact (hb (lt_of_le_of_ne (not_lt.1 h) (Ne.symm hij))).symm

def phaseUnitary (τ : Fin n → 𝕜) (hτ : ∀ i, τ i ≠ 0) : unitaryGroup (Fin n) 𝕜 :=
  ⟨diagonal fun i => τ i / (‖τ i‖ : 𝕜), by
    rw [Matrix.mem_unitaryGroup_iff']
    rw [star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    have h0 : (‖τ i‖ : 𝕜) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 (hτ i)).ne'
    simp only [Pi.star_apply, star_div₀, RCLike.star_def, RCLike.conj_ofReal]
    rw [div_mul_div_comm, RCLike.conj_mul, div_eq_one_iff_eq (mul_ne_zero h0 h0)]
    ring⟩

variable [MeasurableSpace (GL (Fin n) 𝕜)] [BorelSpace (GL (Fin n) 𝕜)]

theorem exists_ANK_of_siegel {b : GL (Fin n) 𝕜} (hb : (b : Matrix (Fin n) (Fin n) 𝕜).IsUpperTriangular)
    (r : PosDiag (Fin n)) (k₀ : unitaryGroup (Fin n) 𝕜) :
    ∃ (a : diagPosSubgroup (Fin n) 𝕜) (u : upperUnipotentSubgroup (Fin n) 𝕜)
      (k : unitaryGroup (Fin n) 𝕜),
      b * diagPosOf r * Unitary.toUnits k₀ =
        (a : GL (Fin n) 𝕜) * (u : GL (Fin n) 𝕜) * Unitary.toUnits k ∧
      (∀ i, ((a : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜) i i =
        ((‖(b : Matrix (Fin n) (Fin n) 𝕜) i i‖ * r.1 i : ℝ) : 𝕜)) ∧
      diagConj a u = unipotentCoordsHomeomorph (unipotentPart (b : Matrix (Fin n) (Fin n) 𝕜)) := by
  have hb0 := apply_self_ne_zero_of_isUpperTriangular hb
  set ar : PosDiag (Fin n) := ⟨fun i => ‖(b : Matrix (Fin n) (Fin n) 𝕜) i i‖ * r.1 i,
    fun i => mul_pos (norm_pos_iff.2 (hb0 i)) (r.2 i)⟩ with har
  set a : diagPosSubgroup (Fin n) 𝕜 := diagPosHomeomorph ar with ha
  set nU : upperUnipotentSubgroup (Fin n) 𝕜 :=
    unipotentCoordsHomeomorph (unipotentPart (b : Matrix (Fin n) (Fin n) 𝕜)) with hnU
  set φ := phaseUnitary (fun i => (b : Matrix (Fin n) (Fin n) 𝕜) i i) hb0 with hφ
  refine ⟨a, diagConj a⁻¹ nU, φ * k₀, ?_, fun i => ?_, ?_⟩
  · have hkey : b * diagPosOf r =
        (nU : GL (Fin n) 𝕜) * (a : GL (Fin n) 𝕜) * Unitary.toUnits φ := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, Units.val_mul, hnU, coe_unipotentCoordsHomeomorph, ha,
        coe_diagPosHomeomorph, coe_diagPosOf, coe_diagPosOf, Unitary.val_toUnits_apply,
        show ((φ : unitaryGroup (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜) =
          diagonal fun i => (b : Matrix (Fin n) (Fin n) 𝕜) i i /
            (‖(b : Matrix (Fin n) (Fin n) 𝕜) i i‖ : 𝕜) from rfl]
      conv_lhs => rw [← unipotentOfCoords_unipotentPart_mul hb]
      rw [mul_assoc, mul_assoc, diagonal_mul_diagonal, diagonal_mul_diagonal]
      congr 2
      funext i
      have h0 : (‖(b : Matrix (Fin n) (Fin n) 𝕜) i i‖ : 𝕜) ≠ 0 := by
        exact_mod_cast (norm_pos_iff.2 (hb0 i)).ne'
      rw [har]
      push_cast
      field_simp
    rw [hkey, map_mul]
    change (nU : GL (Fin n) 𝕜) * (a : GL (Fin n) 𝕜) * Unitary.toUnits φ * Unitary.toUnits k₀ =
      (a : GL (Fin n) 𝕜) * ((a : GL (Fin n) 𝕜)⁻¹ * (nU : GL (Fin n) 𝕜) * (a : GL (Fin n) 𝕜)⁻¹⁻¹) *
        (Unitary.toUnits φ * Unitary.toUnits k₀)
    group
  · rw [ha, coe_diagPosHomeomorph, coe_diagPosOf, diagonal_apply_eq]
  · apply Subtype.ext
    rw [coe_diagConj, coe_diagConj]
    simp only [Subgroup.coe_inv]
    group

end Coordinates

theorem norm_det_unitary {n : ℕ} (k : unitaryGroup (Fin n) 𝕜) :
    ‖(k : Matrix (Fin n) (Fin n) 𝕜).det‖ = 1 := by
  have h : star (k : Matrix (Fin n) (Fin n) 𝕜) * k = 1 := k.2.1
  have h2 := congrArg Matrix.det h
  rw [det_mul, det_one, star_eq_conjTranspose, det_conjTranspose, RCLike.star_def, RCLike.conj_mul]
    at h2
  have h3 : ‖(k : Matrix (Fin n) (Fin n) 𝕜).det‖ ^ 2 = 1 := by exact_mod_cast h2
  nlinarith [norm_nonneg (k : Matrix (Fin n) (Fin n) 𝕜).det]

theorem norm_det_siegel {n : ℕ} {b : GL (Fin n) 𝕜}
    (hb : (b : Matrix (Fin n) (Fin n) 𝕜).IsUpperTriangular) (r : PosDiag (Fin n))
    (k : unitaryGroup (Fin n) 𝕜) :
    ‖((b * diagPosOf r * Unitary.toUnits k : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜).det‖ =
      ∏ i, (‖(b : Matrix (Fin n) (Fin n) 𝕜) i i‖ * r.1 i) := by
  rw [Units.val_mul, Units.val_mul, det_mul, det_mul, norm_mul, norm_mul,
    det_of_isUpperTriangular hb, coe_diagPosOf, det_diagonal, Unitary.val_toUnits_apply,
    norm_det_unitary, mul_one, norm_prod, norm_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [RCLike.norm_ofReal, abs_of_pos (r.2 i)]

section Main

variable {m : ℕ}

def chamberGL (t : ℝ) : Set (GL (Fin (m + 1)) 𝕜) :=
  (fun r => diagPosOf r) '' {r : PosDiag (Fin (m + 1)) | ∀ l : Fin m, t * r.1 l.succ ≤ r.1 l.castSucc}

theorem isClosed_chamberGL (t : ℝ) : IsClosed (chamberGL (𝕜 := 𝕜) (m := m) t) := by
  set C : Set (GL (Fin (m + 1)) 𝕜) :=
    {g | ∀ i j, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) i j =
        if i = j then ((RCLike.re ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) i i) : ℝ) : 𝕜) else 0} ∩
      {g | ∀ i, 0 ≤ RCLike.re ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) i i)} ∩
      {g | ∀ l : Fin m, t * RCLike.re ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) l.succ l.succ) ≤
        RCLike.re ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) l.castSucc l.castSucc)} with hC
  have hent : ∀ i j, Continuous fun g : GL (Fin (m + 1)) 𝕜 =>
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) i j := fun i j =>
    (continuous_apply_apply i j).comp (Units.continuous_val (M := Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜))
  have hCc : IsClosed C := by
    refine IsClosed.inter (IsClosed.inter ?_ ?_) ?_
    · simp only [setOf_forall]
      refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq (hent i j) ?_
      split_ifs
      · exact RCLike.continuous_ofReal.comp (RCLike.continuous_re.comp (hent i i))
      · exact continuous_const
    · simp only [setOf_forall]
      exact isClosed_iInter fun i => isClosed_le continuous_const (RCLike.continuous_re.comp (hent i i))
    · simp only [setOf_forall]
      exact isClosed_iInter fun l => isClosed_le (continuous_const.mul
        (RCLike.continuous_re.comp (hent _ _))) (RCLike.continuous_re.comp (hent _ _))
  convert hCc using 1
  ext g
  constructor
  · rintro ⟨r, hr, rfl⟩
    refine ⟨⟨fun i j => ?_, fun i => ?_⟩, fun l => ?_⟩
    · rw [coe_diagPosOf, diagonal_apply]
      split_ifs with h
      · subst h; simp
      · rfl
    · simpa using (r.2 i).le
    · simpa using hr l
  · rintro ⟨⟨h1, h2⟩, h3⟩
    set d : Fin (m + 1) → ℝ := fun i => RCLike.re ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) i i)
    have hg : (g : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) = diagonal fun i => (d i : 𝕜) := by
      ext i j
      rw [h1 i j, diagonal_apply]
    have hdet : (g : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
    rw [hg, det_diagonal] at hdet
    have hd : ∀ i, 0 < d i := fun i => lt_of_le_of_ne (h2 i) (fun h => by
      apply Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ i)
      rw [← h]; simp)
    refine ⟨⟨d, hd⟩, fun l => h3 l, Units.ext ?_⟩
    rw [coe_diagPosOf, hg]

variable [MeasurableSpace (GL (Fin (m + 1)) 𝕜)] [BorelSpace (GL (Fin (m + 1)) 𝕜)]

def siegelGL (ω : Set (GL (Fin (m + 1)) 𝕜)) (t c₁ c₂ : ℝ) : Set (GL (Fin (m + 1)) 𝕜) :=
  {g | c₁ ≤ ‖(g : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜).det‖ ∧
    ‖(g : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜).det‖ ≤ c₂ ∧
    ∃ b ∈ ω, ∃ r : PosDiag (Fin (m + 1)), (∀ l : Fin m, t * r.1 l.succ ≤ r.1 l.castSucc) ∧
      ∃ k : unitaryGroup (Fin (m + 1)) 𝕜, g = b * diagPosOf r * Unitary.toUnits k}

open scoped Pointwise in
theorem isClosed_siegelGL {ω : Set (GL (Fin (m + 1)) 𝕜)} (hω : IsCompact ω) (t c₁ c₂ : ℝ) :
    IsClosed (siegelGL ω t c₁ c₂) := by
  have hdet : Continuous fun g : GL (Fin (m + 1)) 𝕜 => ‖(g : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜).det‖ :=
    (Continuous.matrix_det (Units.continuous_val (M := Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜))).norm
  set Kset : Set (GL (Fin (m + 1)) 𝕜) := Set.range fun k : unitaryGroup (Fin (m + 1)) 𝕜 => Unitary.toUnits k
  have hK : IsCompact Kset := isCompact_range continuous_unitary_toUnits
  have h1 : IsClosed (ω * chamberGL (𝕜 := 𝕜) (m := m) t) :=
    (isClosed_chamberGL t).smul_left_of_isCompact hω
  have h2 : IsClosed ((ω * chamberGL (𝕜 := 𝕜) (m := m) t) * Kset) := by
    have : (ω * chamberGL (𝕜 := 𝕜) (m := m) t) * Kset =
        (Kset⁻¹ * (ω * chamberGL (𝕜 := 𝕜) (m := m) t)⁻¹)⁻¹ := by
      rw [_root_.mul_inv_rev, inv_inv, inv_inv]
    rw [this]
    exact (h1.inv.smul_left_of_isCompact hK.inv).inv
  have : siegelGL ω t c₁ c₂ =
      {g : GL (Fin (m + 1)) 𝕜 | c₁ ≤ ‖(g : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜).det‖} ∩
      {g : GL (Fin (m + 1)) 𝕜 | ‖(g : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜).det‖ ≤ c₂} ∩
      ((ω * chamberGL (𝕜 := 𝕜) (m := m) t) * Kset) := by
    ext g
    constructor
    · rintro ⟨ha, hb, b, hbω, r, hr, k, rfl⟩
      exact ⟨⟨ha, hb⟩, _, ⟨b, hbω, _, ⟨r, hr, rfl⟩, rfl⟩, _, ⟨k, rfl⟩, rfl⟩
    · rintro ⟨⟨ha, hb⟩, _, ⟨b, hbω, _, ⟨r, hr, rfl⟩, rfl⟩, _, ⟨k, rfl⟩, rfl⟩
      exact ⟨ha, hb, b, hbω, r, hr, k, rfl⟩
  rw [this]
  exact ((isClosed_le continuous_const hdet).inter (isClosed_le hdet continuous_const)).inter h2

theorem measure_siegelGL_lt_top [MeasurableSpace (unitaryGroup (Fin (m + 1)) 𝕜)]
    [BorelSpace (unitaryGroup (Fin (m + 1)) 𝕜)] (μ : Measure (GL (Fin (m + 1)) 𝕜))
    (hANK : ∀ (μK : Measure (unitaryGroup (Fin (m + 1)) 𝕜)) [μK.IsHaarMeasure]
      (μA : Measure (diagPosSubgroup (Fin (m + 1)) 𝕜)) [μA.IsHaarMeasure]
      (μN : Measure (upperUnipotentSubgroup (Fin (m + 1)) 𝕜)) [μN.IsHaarMeasure],
      ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ f : GL (Fin (m + 1)) 𝕜 → ℝ≥0∞, Measurable f →
        ∫⁻ g, f g ∂μ = c * ∫⁻ a, ∫⁻ u, ∫⁻ k, f (a * u * Unitary.toUnits k) ∂μK ∂μN ∂μA)
    {ω : Set (GL (Fin (m + 1)) 𝕜)} (hω : IsCompact ω)
    (hωB : ∀ b ∈ ω, (b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜).IsUpperTriangular)
    {t c₁ c₂ : ℝ} (ht : 0 < t) (hc₁ : 0 < c₁) :
    μ (siegelGL ω t c₁ c₂) < ⊤ := by
  classical
  have hent : ∀ i j, Continuous fun g : GL (Fin (m + 1)) 𝕜 =>
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) i j := fun i j =>
    (continuous_apply_apply i j).comp (Units.continuous_val (M := Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜))
  have hb0 : ∀ b ∈ ω, ∀ i, (b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) i i ≠ 0 := fun b hb i =>
    apply_self_ne_zero_of_isUpperTriangular (hωB b hb) i

  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 < M ∧ ∀ b ∈ ω, ∀ l : Fin m,
      ‖(b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) l.succ l.succ‖ ≤
        M * ‖(b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) l.castSucc l.castSucc‖ := by
    have hcont : ContinuousOn (fun b : GL (Fin (m + 1)) 𝕜 => ∑ l : Fin m,
        ‖(b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) l.succ l.succ‖ /
          ‖(b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) l.castSucc l.castSucc‖) ω :=
      continuousOn_finset_sum _ fun l _ => ContinuousOn.div (hent _ _).norm.continuousOn
        (hent _ _).norm.continuousOn fun b hb => norm_ne_zero_iff.2 (hb0 b hb _)
    obtain ⟨B, hB⟩ := hω.exists_bound_of_continuousOn hcont
    refine ⟨max B 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun b hb l => ?_⟩
    have hpos : 0 < ‖(b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) l.castSucc l.castSucc‖ :=
      norm_pos_iff.2 (hb0 b hb _)
    rw [← div_le_iff₀ hpos]
    calc _ ≤ ∑ l : Fin m, ‖(b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) l.succ l.succ‖ /
          ‖(b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) l.castSucc l.castSucc‖ :=
          Finset.single_le_sum (f := fun l => ‖(b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) l.succ l.succ‖ /
            ‖(b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) l.castSucc l.castSucc‖)
            (fun _ _ => by positivity) (Finset.mem_univ l)
      _ ≤ B := (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hB b hb)
      _ ≤ max B 1 := le_max_left _ _
  set s : ℝ := t / M with hs
  have hs0 : 0 < s := div_pos ht hM0

  set Vset : Set (StrictUpperIndex (Fin (m + 1)) → 𝕜) :=
    (fun b : GL (Fin (m + 1)) 𝕜 => unipotentPart (b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜)) '' ω
    with hVset
  have hVc : IsCompact Vset := hω.image_of_continuousOn (continuousOn_pi.2 fun p =>
    ContinuousOn.div (hent _ _).continuousOn (hent _ _).continuousOn fun b hb => hb0 b hb _)
  set Nc : Set (upperUnipotentSubgroup (Fin (m + 1)) 𝕜) := unipotentCoordsHomeomorph '' Vset
    with hNc
  have hNcc : IsCompact Nc := hVc.image unipotentCoordsHomeomorph.continuous
  have hNcm : MeasurableSet Nc := hNcc.isClosed.measurableSet

  set R : Set (diagPosSubgroup (Fin (m + 1)) 𝕜) := {a |
    (∀ l : Fin m, s * RCLike.re (((a : GL (Fin (m + 1)) 𝕜) : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) l.succ l.succ) ≤
      RCLike.re (((a : GL (Fin (m + 1)) 𝕜) : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) l.castSucc l.castSucc)) ∧
    c₁ ≤ ∏ i, RCLike.re (((a : GL (Fin (m + 1)) 𝕜) : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) i i) ∧
    ∏ i, RCLike.re (((a : GL (Fin (m + 1)) 𝕜) : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) i i) ≤ c₂} with hR
  have hentA : ∀ i j, Continuous fun a : diagPosSubgroup (Fin (m + 1)) 𝕜 =>
      RCLike.re (((a : GL (Fin (m + 1)) 𝕜) : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) i j) := fun i j =>
    RCLike.continuous_re.comp ((hent i j).comp continuous_subtype_val)
  have hRc : IsClosed R := by
    rw [hR]
    simp only [Set.setOf_and]
    refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_)
    · simp only [setOf_forall]
      exact isClosed_iInter fun l => isClosed_le (continuous_const.mul (hentA _ _)) (hentA _ _)
    · exact isClosed_le continuous_const (continuous_finsetProd _ fun i _ => hentA i i)
    · exact isClosed_le (continuous_finsetProd _ fun i _ => hentA i i) continuous_const
  have hRm : MeasurableSet R := hRc.measurableSet

  have hpt : ∀ (a : diagPosSubgroup (Fin (m + 1)) 𝕜) (u : upperUnipotentSubgroup (Fin (m + 1)) 𝕜)
      (k : unitaryGroup (Fin (m + 1)) 𝕜),
      (siegelGL ω t c₁ c₂).indicator (1 : GL (Fin (m + 1)) 𝕜 → ℝ≥0∞)
        ((a : GL (Fin (m + 1)) 𝕜) * (u : GL (Fin (m + 1)) 𝕜) * Unitary.toUnits k) ≤
        R.indicator (1 : diagPosSubgroup (Fin (m + 1)) 𝕜 → ℝ≥0∞) a *
          Nc.indicator (1 : upperUnipotentSubgroup (Fin (m + 1)) 𝕜 → ℝ≥0∞) (diagConj a u) := by
    intro a u k
    by_cases hS : (a : GL (Fin (m + 1)) 𝕜) * (u : GL (Fin (m + 1)) 𝕜) * Unitary.toUnits k ∈
      siegelGL ω t c₁ c₂
    swap
    · rw [indicator_of_notMem hS]; exact zero_le
    obtain ⟨hd1, hd2, b, hbω, r, hr, k₀, hg⟩ := hS
    obtain ⟨a', u', k', heq', hdiag', hconj'⟩ := exists_ANK_of_siegel (hωB b hbω) r k₀
    obtain ⟨rfl, rfl⟩ := ANK_unique (hg.trans heq')
    have hre : ∀ i, RCLike.re (((a : GL (Fin (m + 1)) 𝕜) : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) i i) =
        ‖(b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) i i‖ * r.1 i := fun i => by
      rw [hdiag' i, RCLike.ofReal_re]
    have hdet := norm_det_siegel (hωB b hbω) r k₀
    rw [hg, hdet] at hd1 hd2
    have haR : a ∈ R := by
      refine ⟨fun l => ?_, ?_, ?_⟩
      · rw [hre, hre]
        have h1 := hM b hbω l
        have h2 := hr l
        have hb1 : 0 ≤ ‖(b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) l.castSucc l.castSucc‖ := norm_nonneg _
        have hr1 := (r.2 l.succ).le
        calc s * (‖(b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) l.succ l.succ‖ * r.1 l.succ)
            ≤ s * (M * ‖(b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) l.castSucc l.castSucc‖ * r.1 l.succ) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hr1) hs0.le
          _ = ‖(b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) l.castSucc l.castSucc‖ * (t * r.1 l.succ) := by
              rw [hs]; field_simp
          _ ≤ ‖(b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) l.castSucc l.castSucc‖ * r.1 l.castSucc :=
              mul_le_mul_of_nonneg_left h2 hb1
      · simp only [hre]; exact hd1
      · simp only [hre]; exact hd2
    have hnc : diagConj a u ∈ Nc := by
      rw [hconj']
      exact ⟨_, ⟨b, hbω, rfl⟩, rfl⟩
    rw [indicator_of_mem (show _ ∈ siegelGL ω t c₁ c₂ from ⟨by rw [hg, hdet]; exact hd1,
      by rw [hg, hdet]; exact hd2, b, hbω, r, hr, k₀, hg⟩), indicator_of_mem haR,
      indicator_of_mem hnc]
    simp

  set μK : Measure (unitaryGroup (Fin (m + 1)) 𝕜) := Measure.haar with hμK
  set μN : Measure (upperUnipotentSubgroup (Fin (m + 1)) 𝕜) := Measure.haar with hμN
  haveI := isHaarMeasure_map_expDiag (𝕜 := 𝕜) (m := m)
  set μA : Measure (diagPosSubgroup (Fin (m + 1)) 𝕜) :=
    Measure.map (expDiag 𝕜 m) (volume : Measure (Fin (m + 1) → ℝ)) with hμA
  obtain ⟨c, -, hc⟩ := hANK μK μA μN
  have hSm : MeasurableSet (siegelGL ω t c₁ c₂) := (isClosed_siegelGL hω t c₁ c₂).measurableSet
  rw [← lintegral_indicator_one hSm, hc _ (measurable_one.indicator hSm)]
  refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
  have hK : μK univ < ⊤ := isCompact_univ.measure_lt_top
  have hNcfin : μN Nc < ⊤ := hNcc.measure_lt_top
  set δi : diagPosSubgroup (Fin (m + 1)) 𝕜 → ℝ≥0∞ :=
    fun a => ((iwasawaDelta (a : GL (Fin (m + 1)) 𝕜) : ℝ≥0∞))⁻¹ with hδi
  have hinner : ∀ a : diagPosSubgroup (Fin (m + 1)) 𝕜,
      ∫⁻ u, ∫⁻ k, (siegelGL ω t c₁ c₂).indicator (1 : GL (Fin (m + 1)) 𝕜 → ℝ≥0∞)
        ((a : GL (Fin (m + 1)) 𝕜) * (u : GL (Fin (m + 1)) 𝕜) * Unitary.toUnits k) ∂μK ∂μN ≤
      μK univ * μN Nc * R.indicator δi a := by
    intro a
    have hpre : μN (diagConj a ⁻¹' Nc) = δi a * μN Nc := by
      rw [← Measure.map_apply (continuous_diagConj a).measurable hNcm, map_diagConj_haar,
        Measure.smul_apply, smul_eq_mul]
    calc ∫⁻ u, ∫⁻ k, (siegelGL ω t c₁ c₂).indicator (1 : GL (Fin (m + 1)) 𝕜 → ℝ≥0∞)
          ((a : GL (Fin (m + 1)) 𝕜) * (u : GL (Fin (m + 1)) 𝕜) * Unitary.toUnits k) ∂μK ∂μN
        ≤ ∫⁻ u, ∫⁻ _k, R.indicator (1 : diagPosSubgroup (Fin (m + 1)) 𝕜 → ℝ≥0∞) a *
            Nc.indicator (1 : upperUnipotentSubgroup (Fin (m + 1)) 𝕜 → ℝ≥0∞) (diagConj a u) ∂μK ∂μN :=
          lintegral_mono fun u => lintegral_mono fun k => hpt a u k
      _ = ∫⁻ u, (R.indicator (1 : diagPosSubgroup (Fin (m + 1)) 𝕜 → ℝ≥0∞) a * μK univ) *
            (diagConj a ⁻¹' Nc).indicator (1 : upperUnipotentSubgroup (Fin (m + 1)) 𝕜 → ℝ≥0∞) u ∂μN := by
          refine lintegral_congr fun u => ?_
          rw [lintegral_const]
          simp only [indicator, mem_preimage, Pi.one_apply]
          split_ifs <;> ring
      _ = (R.indicator (1 : diagPosSubgroup (Fin (m + 1)) 𝕜 → ℝ≥0∞) a * μK univ) *
            μN (diagConj a ⁻¹' Nc) := by
          rw [lintegral_const_mul _ (measurable_one.indicator
            (hNcm.preimage (continuous_diagConj a).measurable)),
            lintegral_indicator_one (hNcm.preimage (continuous_diagConj a).measurable)]
      _ = μK univ * μN Nc * R.indicator δi a := by
          rw [hpre]
          simp only [indicator, Pi.one_apply]
          split_ifs <;> ring
  calc ∫⁻ a, ∫⁻ u, ∫⁻ k, (siegelGL ω t c₁ c₂).indicator (1 : GL (Fin (m + 1)) 𝕜 → ℝ≥0∞)
        ((a : GL (Fin (m + 1)) 𝕜) * (u : GL (Fin (m + 1)) 𝕜) * Unitary.toUnits k) ∂μK ∂μN ∂μA
      ≤ ∫⁻ a, μK univ * μN Nc * R.indicator δi a ∂μA := lintegral_mono hinner
    _ = μK univ * μN Nc * ∫⁻ a, R.indicator δi a ∂μA := by
        refine lintegral_const_mul _ (Measurable.indicator ?_ hRm)
        exact (ENNReal.continuous_coe.comp continuous_iwasawaDelta_diagPos).measurable.inv
    _ < ⊤ := by
        refine ENNReal.mul_lt_top (ENNReal.mul_lt_top hK hNcfin) ?_
        have hmeasF : Measurable (R.indicator δi) :=
          (ENNReal.continuous_coe.comp continuous_iwasawaDelta_diagPos).measurable.inv.indicator hRm
        have he : (1 : ℝ) ≤ (Module.finrank ℝ 𝕜 : ℝ) := Nat.one_le_cast.2 Module.finrank_pos
        rw [hμA, lintegral_map hmeasF (expDiag 𝕜 m).continuous.measurable]
        refine lt_of_le_of_lt (lintegral_mono fun x => ?_)
          (lintegral_chamber_lt_top m he (Real.log s) (Real.log c₁) (Real.log c₂))
        by_cases hx : expDiag 𝕜 m x ∈ R
        · have hre : ∀ i, RCLike.re ((((expDiag 𝕜 m x : diagPosSubgroup (Fin (m + 1)) 𝕜) :
              GL (Fin (m + 1)) 𝕜) : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) i i) = Real.exp (x i) :=
            fun i => by rw [coe_expDiag, coe_diagPosOf, diagonal_apply_eq, RCLike.ofReal_re]
          have hx' := hx
          obtain ⟨h1, h2, h3⟩ := hx
          simp only [hre] at h1 h2 h3
          rw [← Real.exp_sum] at h2 h3
          have hc₂ : 0 < c₂ := lt_of_lt_of_le (Real.exp_pos _) h3
          have hmem : x ∈ {x : Fin (m + 1) → ℝ | (∀ l : Fin m, Real.log s ≤ x l.castSucc - x l.succ) ∧
              Real.log c₁ ≤ ∑ i, x i ∧ ∑ i, x i ≤ Real.log c₂} := by
            refine ⟨fun l => ?_, (Real.log_le_iff_le_exp hc₁).2 h2,
              (Real.le_log_iff_exp_le hc₂).2 h3⟩
            rw [Real.log_le_iff_le_exp hs0, Real.exp_sub, le_div_iff₀ (Real.exp_pos _)]
            exact h1 l
          rw [indicator_of_mem hx', indicator_of_mem hmem]
          apply le_of_eq
          rw [hδi]
          dsimp only
          rw [coe_expDiag]
          have hD : ((iwasawaDelta (diagPosOf ⟨fun i => Real.exp (x i), fun i => Real.exp_pos _⟩ :
              GL (Fin (m + 1)) 𝕜) : ℝ)) = Real.exp ((Module.finrank ℝ 𝕜 : ℝ) *
                ∑ p : StrictUpperIndex (Fin (m + 1)), (x p.1.1 - x p.1.2)) := by
            rw [iwasawaDelta_diagPosOf, Finset.mul_sum, Real.exp_sum]
            refine Finset.prod_congr rfl fun p _ => ?_
            rw [← Real.exp_sub, ← Real.exp_nat_mul]
          rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_inv_of_pos (by rw [hD]; exact Real.exp_pos _),
            hD, ← Real.exp_neg]
        · rw [indicator_of_notMem hx]; exact zero_le

end Main

end Reduction

end

end GroundTheory.Automorphic
