import Development.WeilBound.ThetaLifts.LocalTheory.SplitInv
import Development.WeilBound.ThetaLifts.ConeHypotheses.PureEqPureA
import Development.WeilBound.ThetaLifts.CartanFactorisation.ExistsPureML
import Development.WeilBound.ThetaLifts.LatticeBasics.LeviEx

noncomputable section

namespace PositivityTheory.ThKG.Loc

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Levi

variable {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁}

theorem mat_mul (g h : UA σ W.J) : mat (g * h) = mat g * mat h := rfl

theorem mat_one : mat (1 : UA σ W.J) = 1 := rfl

theorem mat_inv_mul (g : UA σ W.J) : mat g⁻¹ * mat g = 1 := by rw [← mat_mul, inv_mul_cancel, mat_one]

theorem mat_mul_inv (g : UA σ W.J) : mat g * mat g⁻¹ = 1 := by rw [← mat_mul, mul_inv_cancel, mat_one]

theorem levi_mul {t t' : (AE F E)ˣ} {h h' : UA σ W₁.J} {m m' : UA σ W.J} (a : IsLevi H' t h m) (b : IsLevi H' t' h' m') :
    IsLevi H' (t * t') (h * h') (m * m') := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mat_mul, ← Matrix.mulVec_mulVec, b.1, Matrix.mulVec_smul, a.1, smul_smul, Units.val_mul, mul_comm]
  · rw [mat_mul, ← Matrix.mulVec_mulVec, b.2.1, Matrix.mulVec_smul, a.2.1, smul_smul, ← map_mul, ← Units.val_mul, mul_inv_rev]
  · rw [mat_mul, Matrix.mul_assoc, b.2.2, ← Matrix.mul_assoc, a.2.2, Matrix.mul_assoc, mat_mul]

theorem levi_inv {t : (AE F E)ˣ} {h : UA σ W₁.J} {m : UA σ W.J} (a : IsLevi H' t h m) : IsLevi H' t⁻¹ h⁻¹ m⁻¹ := by
  refine ⟨?_, ?_, ?_⟩
  · have : mat m⁻¹ *ᵥ (mat m *ᵥ incV F H'.x) = incV F H'.x := by rw [Matrix.mulVec_mulVec, mat_inv_mul, Matrix.one_mulVec]
    rw [a.1, Matrix.mulVec_smul] at this
    conv_rhs => rw [← this]
    rw [smul_smul, Units.inv_mul, one_smul]
  · have : mat m⁻¹ *ᵥ (mat m *ᵥ incV F H'.y) = incV F H'.y := by rw [Matrix.mulVec_mulVec, mat_inv_mul, Matrix.one_mulVec]
    rw [a.2.1, Matrix.mulVec_smul] at this
    conv_rhs => rw [← this]
    rw [smul_smul, ← map_mul, inv_inv, Units.mul_inv, map_one, one_smul]
  · calc mat m⁻¹ * incM F H'.ι = mat m⁻¹ * (incM F H'.ι * mat h) * mat h⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, mat_mul_inv, Matrix.mul_one]
      _ = _ := by rw [← a.2.2, ← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]

theorem unip_conj {h : UA σ W₁.J} {m : UA σ W.J} (a : IsLevi H' 1 h m) {u} (hu : u ∈ unip σ W H') :
    m * u * m⁻¹ ∈ unip σ W H' := by
  induction hu using Subgroup.closure_induction with
  | mem u hu =>
    have b := levi_inv a
    refine Subgroup.subset_closure ⟨?_, fun z => ?_⟩
    · rw [mat_mul, mat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, b.1, inv_one, Units.val_one, one_smul, hu.1, a.1,
        Units.val_one, one_smul]
    · obtain ⟨c, hc⟩ := hu.2 (mat h⁻¹ *ᵥ z)
      refine ⟨c, ?_⟩
      rw [mat_mul, mat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec z, b.2.2,
        ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_add, Matrix.mulVec_smul, a.1, Units.val_one, one_smul,
        Matrix.mulVec_mulVec, a.2.2, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec z, mat_mul_inv, Matrix.one_mulVec]
  | one => simpa using one_mem _
  | mul x y _ _ hx hy => have := mul_mem hx hy; simpa [mul_assoc] using this
  | inv x _ hx => have := inv_mem hx; simpa [mul_assoc] using this

theorem law_par {χ : Chr F E} {z : ℝ} {T : UA σ W.J → ℂ} (hl : HasLaw W₁ H' χ z T)
    (hi : ∀ u ∈ unip σ W H', ∀ h, T (u * h) = T h)
    {t} {h₁ h' : UA σ W₁.J} {m u m' l : UA σ W.J} (a : IsLevi H' t h₁ m) (hu : u ∈ unip σ W H') (b : IsLevi H' 1 h' m') (c : IsLevi H' 1 (h' * h₁) l) :
    T (m' * (u * m)) = (χ t : ℂ) * (((absE F E t : ℝ) ^ z : ℝ) : ℂ) * T l := by
  have e : m' * (u * m) = (m' * u * m'⁻¹) * ((m' * m * l⁻¹) * l) := by group
  have k := levi_mul (levi_mul b a) (levi_inv c)
  rw [one_mul, inv_one, mul_one, mul_inv_cancel] at k
  rw [e, hi _ (unip_conj b hu), hl t _ k]

theorem at_mul_left {R : Type} [Zero R] {ev : AF F → R} {a b c : Type} [Fintype b] (A : Matrix a b (AE F E))
    {Z : Matrix b c (AE F E)} (h : At ev Z) : At ev (A * Z) := fun u hu => by
  rw [← Matrix.mul_smul, h u hu, Matrix.mul_zero]

theorem at_mul_right {R : Type} [Zero R] {ev : AF F → R} {a b c : Type} [Fintype b] {Z : Matrix a b (AE F E)}
    (h : At ev Z) (A : Matrix b c (AE F E)) : At ev (Z * A) := fun u hu => by
  rw [← Matrix.smul_mul, h u hu, Matrix.zero_mul]

theorem uat_mul {R : Type} [Zero R] {ev : AF F → R} {g h : UA σ W.J} (a : g ∈ UAt σ W ev) (b : h ∈ UAt σ W ev) :
    g * h ∈ UAt σ W ev := fun u hu => by
  have e : mat (g * h) - 1 = (mat g - 1) * mat h + (mat h - 1) := by rw [mat_mul, Matrix.sub_mul, Matrix.one_mul]; abel
  rw [e, smul_add, at_mul_right a _ u hu, b u hu, add_zero]

theorem uat_inv {R : Type} [Zero R] {ev : AF F → R} {g : UA σ W.J} (a : g ∈ UAt σ W ev) : g⁻¹ ∈ UAt σ W ev := fun u hu => by
  have e : mat g⁻¹ - 1 = -(mat g⁻¹ * (mat g - 1)) := by rw [Matrix.mul_sub, mat_inv_mul, Matrix.mul_one, neg_sub]
  rw [e, smul_neg, at_mul_left _ a u hu, neg_zero]

theorem uat_one {R : Type} [Zero R] {ev : AF F → R} : (1 : UA σ W.J) ∈ UAt σ W ev := fun u _ => by
  rw [mat_one, sub_self, smul_zero]

theorem uat_closure {R : Type} [Zero R] {ev : AF F → R} {g : UA σ W.J} (h : g ∈ Subgroup.closure (UAt σ W ev)) :
    g ∈ UAt σ W ev := by
  induction h using Subgroup.closure_induction with
  | mem u hu => exact hu
  | one => exact uat_one
  | mul x y _ _ hx hy => exact uat_mul hx hy
  | inv x _ hx => exact uat_inv hx

theorem det_of_sig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨rfl, A, hA⟩ := h
  intro h0
  let e : Fin (r + s) ≃ Fin r ⊕ Fin s := finSumFinEquiv.symm
  have e1 : (A.submatrix e.symm id)ᵀ * M.submatrix e.symm e.symm * (A.submatrix e.symm id).map star =
      Matrix.fromBlocks 1 0 0 (-1) := by
    rw [← hA, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv]
    rfl
  have e2 := congrArg Matrix.det e1
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_submatrix_equiv_self, h0, Matrix.det_fromBlocks_zero₂₁] at e2
  simp [Matrix.det_neg] at e2
  exact pow_ne_zero _ (by norm_num) e2.symm

theorem det_skew {B : Base F E} {r s : ℕ} (h : W.IsSkew σ B r s) : W.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  intro h0
  apply det_of_sig (h.sig w)
  rw [Matrix.det_smul]
  have : (W.J.map (B.emb w).1).det = (B.emb w).1 W.J.det := ((B.emb w).1.map_det W.J).symm
  rw [this, h0, map_zero, mul_zero]

theorem levi_at {B : Base F E} {i₀ i₁ r s : ℕ} (hH : H'.IsAdapted σ B W W₁ i₀ i₁) (hW : W₁.IsSkew σ B r s) {R : Type} [Zero R]
    {ev : AF F → R} {t} {h₁ : UA σ W₁.J} {m : UA σ W.J} (a : IsLevi H' t h₁ m) (hm : m ∈ UAt σ W ev) : h₁ ∈ UAt σ W₁ ev := by
  have hd : IsUnit W₁.Jᵀ.det := by rw [Matrix.det_transpose]; exact (det_skew hW).isUnit
  let P : Matrix (Fin d₁) (Fin d) E := W₁.Jᵀ⁻¹ * ((H'.ι.map σ)ᵀ * W.Jᵀ)
  have hP : P * H'.ι = 1 := by
    have := congrArg Matrix.transpose hH.gram
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at this
    rw [Matrix.mul_assoc, Matrix.mul_assoc, this, Matrix.nonsing_inv_mul _ hd]
  have hP' : incM F P * incM F H'.ι = 1 := by
    rw [← GlobalTheory.ThK.Dbl.incM_mul, hP]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have e : mat h₁ - 1 = incM F P * ((mat m - 1) * incM F H'.ι) := by
    rw [Matrix.sub_mul, a.2.2, Matrix.one_mul, Matrix.mul_sub, ← Matrix.mul_assoc, hP', Matrix.one_mul]
  show At ev _
  rw [e]
  exact at_mul_left _ (at_mul_right hm _)

theorem levi_t_one {B : Base F E} {i₀ i₁ : ℕ} (hH : H'.IsAdapted σ B W W₁ i₀ i₁) {t} {h₁ : UA σ W₁.J}
    (a : IsLevi H' t h₁ (1 : UA σ W.J)) : t = 1 := by
  have h1 := a.1
  rw [mat_one, Matrix.one_mulVec] at h1
  let y : Fin d → E := W.J *ᵥ fun i => σ (H'.y i)
  have h2 : incV F H'.x ⬝ᵥ incV F y = 1 := by
    have := congrArg (inclR (F := F) (E := E) (AF F)) hH.xy
    simpa [form, dotProduct, incV, map_sum, y] using this
  have h3 := congrArg (· ⬝ᵥ incV F y) h1
  simp only [smul_dotProduct, h2, smul_eq_mul, mul_one] at h3
  exact Units.ext h3.symm

end Levi

end PositivityTheory.ThKG.Loc

end
