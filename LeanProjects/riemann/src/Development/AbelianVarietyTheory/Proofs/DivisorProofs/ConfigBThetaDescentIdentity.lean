import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsJacMapZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryMatrixSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterComponentSmoothUnitaryConduct
import Development.AutomorphicArithmetic.LocalEmbeddings.OppLagr
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalFieldNormValuation

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.JacGeom

section Algebra

open Matrix

variable {K : Type} [CommRing K] {D M : Type} [Fintype D] [DecidableEq D] [Fintype M] [DecidableEq M]

theorem adj_intertwine {I : Type} [Fintype I] [DecidableEq I] (e : I ≃ D) {J A B : Matrix D D K} {P Q : Matrix D I K}
    {Γ Γ' N N' N₀ : Matrix I I K} (hG : Pᵀ * J * Q = Γ) (hΓ : Γ' * Γ = 1) (hN : N * N₀ = 1) (hU : Aᵀ * J * B = J)
    (hA : A * P = P * N) (hN' : Nᵀ * Γ * N' = Γ) : B * Q = Q * N' := by
  have h1 : Q * (Γ' * Pᵀ * J) = 1 := (Matrix.mul_eq_one_comm_of_equiv e).1 (by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Pᵀ, hG, hΓ])
  have h2 : Nᵀ * (Pᵀ * J * (B * Q)) = Nᵀ * (Γ * N') := by
    rw [← Matrix.mul_assoc Nᵀ Γ, hN', ← hG]
    conv_rhs => rw [← hU]
    simp only [← Matrix.mul_assoc, ← Matrix.transpose_mul, hA]
  have h3 : Pᵀ * J * (B * Q) = Γ * N' := by
    have := congrArg (fun Z => N₀ᵀ * Z) h2
    simpa only [← Matrix.mul_assoc N₀ᵀ Nᵀ, ← Matrix.transpose_mul, hN, Matrix.transpose_one, Matrix.one_mul] using this
  calc B * Q = Q * (Γ' * Pᵀ * J) * (B * Q) := by rw [h1, Matrix.one_mul]
    _ = Q * Γ' * (Pᵀ * J * (B * Q)) := by simp only [Matrix.mul_assoc]
    _ = Q * N' := by rw [h3, Matrix.mul_assoc, ← Matrix.mul_assoc Γ', hΓ, Matrix.one_mul]

def gram (J₁ : Matrix M M K) : Matrix (Fin 1 ⊕ M ⊕ Fin 1) (Fin 1 ⊕ M ⊕ Fin 1) K :=
  fromBlocks 0 (fromCols 0 1) (fromRows 0 (-1)) (fromBlocks J₁ 0 0 0)

omit [Fintype M] [DecidableEq M] in
theorem fromCols_zero_fromRows (A : Matrix M (Fin 1) K) (C : Matrix (Fin 1) (Fin 1) K) :
    fromCols (0 : Matrix (M ⊕ Fin 1) M K) (fromRows A C) = fromBlocks 0 A 0 C := by
  ext (i | i) (j | j) <;> rfl

theorem gram_inv {J₁ J₁' : Matrix M M K} (h : J₁' * J₁ = 1) :
    fromBlocks 0 (fromCols 0 (-1)) (fromRows 0 1) (fromBlocks J₁' 0 0 0) * gram J₁ = 1 := by
  simp [gram, fromBlocks_multiply, fromCols_mul_fromRows, fromCols_mul_fromBlocks, fromBlocks_mul_fromRows,
    fromCols_zero_fromRows, fromBlocks_add, h, fromBlocks_one]

omit [DecidableEq M] in
theorem gram_levi {J₁ g g' : Matrix M M K} (h : gᵀ * J₁ * g' = J₁) (x y : Kˣ) :
    (fromBlocks (of fun _ _ => (x : K)) 0 0 (fromBlocks g 0 0 (of fun _ _ => (y : K))))ᵀ * gram J₁ *
      fromBlocks (of fun _ _ => ((y⁻¹ : Kˣ) : K)) 0 0 (fromBlocks g' 0 0 (of fun _ _ => ((x⁻¹ : Kˣ) : K))) = gram J₁ := by
  have e : ∀ i j, ∑ k, (∑ l, g l i * J₁ l k) * g' k j = J₁ i j := fun i j => by
    simpa [Matrix.mul_apply] using congrFun (congrFun h i) j
  ext (i | i | i) (j | j | j) <;> simp [gram, Matrix.mul_apply, Fintype.sum_sum_type, e, Matrix.one_apply,
    Fin.fin_one_eq_zero]

theorem gram_unip {J₁ J₁' : Matrix M M K} (h : J₁ * J₁' = 1) (X : Matrix (Fin 1) (M ⊕ Fin 1) K) (Y : Matrix M (Fin 1) K) :
    ∃ (X' : Matrix (Fin 1) (M ⊕ Fin 1) K) (Y' : Matrix M (Fin 1) K),
      (fromBlocks 1 X 0 (fromBlocks 1 Y 0 1))ᵀ * gram J₁ * fromBlocks 1 X' 0 (fromBlocks 1 Y' 0 1) = gram J₁ := by
  obtain ⟨X₁, X₂, rfl⟩ : ∃ X₁ X₂, X = fromCols X₁ X₂ := ⟨_, _, (fromCols_toCols X).symm⟩
  refine ⟨fromCols (Yᵀ * J₁) (X₂ᵀ - Yᵀ * X₁ᵀ), -(J₁' * X₁ᵀ), ?_⟩
  simp [gram, fromBlocks_multiply, fromBlocks_transpose, transpose_fromCols, fromCols_mul_fromRows, fromCols_mul_fromBlocks,
    fromBlocks_mul_fromRows, fromCols_zero_fromRows, fromBlocks_add, Matrix.mul_assoc, ← Matrix.mul_assoc J₁, h]

def frame (x : D → K) (ι : Matrix D M K) (y : D → K) : Matrix D (Fin 1 ⊕ M ⊕ Fin 1) K :=
  of fun r => Sum.elim (fun _ => x r) (Sum.elim (ι r) fun _ => y r)

omit [Fintype D] [DecidableEq D] [DecidableEq M] in
theorem frame_mulVec (x : D → K) (ι : Matrix D M K) (y : D → K) (p : Fin 1 → K) (z : M → K) (q : Fin 1 → K) :
    frame x ι y *ᵥ Sum.elim p (Sum.elim z q) = p 0 • x + ι *ᵥ z + q 0 • y := by
  funext r
  simp [frame, mulVec, dotProduct, Fintype.sum_sum_type, mul_comm, add_assoc]

omit [DecidableEq D] in
theorem cols_unip {g : Matrix D D K} {x y : D → K} {ι : Matrix D M K} {X : Matrix (Fin 1) (M ⊕ Fin 1) K}
    {Y : Matrix M (Fin 1) K} (h : g * frame x ι y = frame x ι y *
      (fromBlocks 1 X 0 (fromBlocks 1 Y 0 1) : Matrix (Fin 1 ⊕ M ⊕ Fin 1) (Fin 1 ⊕ M ⊕ Fin 1) K)) :
    g *ᵥ x = x ∧ ∀ z, ∃ a : K, g *ᵥ (ι *ᵥ z) = ι *ᵥ z + a • x := by
  have k : ∀ p z, g *ᵥ (p • x + ι *ᵥ z) = (p + (X *ᵥ Sum.elim z 0) 0) • x + ι *ᵥ z := fun p z => by
    have := congrArg (· *ᵥ Sum.elim (fun _ => p) (Sum.elim z 0)) h
    simpa [← mulVec_mulVec, fromBlocks_mulVec, frame_mulVec] using this
  refine ⟨?_, fun z => ⟨(X *ᵥ Sum.elim z 0) 0, ?_⟩⟩
  · simpa using k 1 0
  · simpa [add_comm] using k 0 z

omit [DecidableEq D] [DecidableEq M] in
theorem cols_levi {g : Matrix D D K} {x y : D → K} {ι : Matrix D M K} {s s' : K} {g₁ : Matrix M M K}
    (h : g * frame x ι y = frame x ι y * (fromBlocks (of fun _ _ => s) 0 0 (fromBlocks g₁ 0 0 (of fun _ _ => s')) :
      Matrix (Fin 1 ⊕ M ⊕ Fin 1) (Fin 1 ⊕ M ⊕ Fin 1) K)) :
    g *ᵥ x = s • x ∧ g *ᵥ y = s' • y ∧ g * ι = ι * g₁ := by
  refine ⟨funext fun r => ?_, funext fun r => ?_, Matrix.ext fun r j => ?_⟩
  · have := congrFun (congrFun h r) (.inl 0)
    rw [Matrix.mul_apply, Matrix.mul_apply] at this
    simpa [frame, Matrix.mul_apply, mulVec, dotProduct, Fintype.sum_sum_type, mul_comm] using this
  · have := congrFun (congrFun h r) (.inr (.inr 0))
    rw [Matrix.mul_apply, Matrix.mul_apply] at this
    simpa [frame, Matrix.mul_apply, mulVec, dotProduct, Fintype.sum_sum_type, mul_comm] using this
  · have := congrFun (congrFun h r) (.inr (.inl j))
    rw [Matrix.mul_apply, Matrix.mul_apply] at this
    simpa [frame, Matrix.mul_apply, mulVec, dotProduct, Fintype.sum_sum_type] using this

end Algebra

section Adelic

open Matrix GlobalTheory.SplitGLLift GlobalTheory.KSplit
open GlobalTheory.Div.CoordOpp (piW_cA incM_map_piW unit_map)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}

theorem eq_zero_of_at (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) {z : AE F E} (hz : At (evFin F v) z) (h1 : piW t z = 0)
    (h2 : piW (t.comp σ) z = 0) : z = 0 := by
  obtain ⟨a1, a2⟩ := at_evFin_iff.1 hz
  refine GlobalTheory.Doubling.adele_ext (fun w => by rw [a1, map_zero]) fun w => ?_
  by_cases e : w = v
  · subst e
    exact split_ext h t (by rw [map_zero, map_zero]; exact h1) (by rw [map_zero, map_zero]; exact h2)
  · rw [a2 w e, map_zero]

theorem adelic_intertwine (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) {D I : Type} [Fintype D] [DecidableEq D] [Fintype I]
    [DecidableEq I] {g : Matrix D D (AE F E)} {P : Matrix D I E} {N : Matrix I I (AE F E)} (hg : At (evFin F v) (g - 1))
    (hN : At (evFin F v) (N - 1)) (h1 : g.map (piW t) * P.map t = P.map t * N.map (piW t))
    (h2 : g.map (piW (t.comp σ)) * P.map (t.comp σ) = P.map (t.comp σ) * N.map (piW (t.comp σ))) :
    g * incM F P = incM F P * N := by
  have hz : At (evFin F v) (g * incM F P - incM F P * N) := fun u hu => by
    rw [show g * incM F P - incM F P * N = (g - 1) * incM F P - incM F P * (N - 1) by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]; abel,
      smul_sub, ← Matrix.smul_mul, ← Matrix.mul_smul, hg u hu, hN u hu, Matrix.zero_mul, Matrix.mul_zero, sub_zero]
  have k : ∀ τ : E →ₐ[F] Fv F v, g.map (piW τ) * P.map τ = P.map τ * N.map (piW τ) → ∀ i j,
      piW τ ((g * incM F P - incM F P * N) i j) = 0 := fun τ e i j => by
    rw [← incM_map_piW, ← Matrix.map_mul, ← Matrix.map_mul] at e
    rw [Matrix.sub_apply, map_sub, sub_eq_zero]
    exact congrFun (congrFun e i) j
  rw [← sub_eq_zero]
  ext i j
  exact eq_zero_of_at h t (fun u hu => congrFun (congrFun (hz u hu) i) j) (k _ h1 i j) (k _ h2 i j)

def idl (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) : (Fv F v)ˣ × (Fv F v)ˣ →* (AE F E)ˣ :=
  (Units.map (oneAdd (liftPair h t))).comp MulEquiv.prodUnits.symm.toMonoidHom

theorem idl_val (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (x y : (Fv F v)ˣ) :
    (idl h t (x, y) : AE F E) = 1 + liftPair h t ((x : Fv F v) - 1, (y : Fv F v) - 1) := rfl

theorem piW_idl (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (x y : (Fv F v)ˣ) : piW t (idl h t (x, y) : AE F E) = x := by
  rw [idl_val, map_add, map_one, piW_liftPair, add_sub_cancel]

theorem piW_comp_idl (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (x y : (Fv F v)ˣ) :
    piW (t.comp σ) (idl h t (x, y) : AE F E) = y := by
  rw [idl_val, map_add, map_one, piW_comp_liftPair, add_sub_cancel]

theorem at_idl (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (x y : (Fv F v)ˣ) :
    At (evFin F v) ((idl h t (x, y) : AE F E) - 1) := by
  rw [idl_val, add_sub_cancel_left]; exact at_liftPair h t _

theorem cA_idl (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (x y : (Fv F v)ˣ) :
    cA σ (idl h t (x, y) : AE F E) = idl h t (y, x) := by
  rw [idl_val, idl_val, map_add, map_one, cA_liftPair]; rfl

theorem chr_idl (h : IsCMExt F E σ) (χ : Chr F E) (t : E →ₐ[F] Fv F v) (x y : (Fv F v)ˣ) :
    (χ (idl h t (x, y)) : ℂ) = (chrW χ t x : ℂ) * (chrW χ (t.comp σ) y : ℂ) := by
  have e1 := GlobalTheory.ChrLocal.chrW_piW_eq F E σ h χ v t (idl h t (x, 1)) (at_idl h t _ _) (piW_comp_idl h t _ _)
  have e2 := GlobalTheory.ChrLocal.chrW_piW_eq F E σ h χ v (t.comp σ) (idl h t (1, y)) (at_idl h t _ _)
    (by rw [GlobalTheory.OppLagr.comp_comp h]; exact piW_idl h t _ _)
  rw [show Units.map (piW t).toMonoidHom (idl h t (x, 1)) = x from Units.ext (piW_idl h t _ _)] at e1
  rw [show Units.map (piW (t.comp σ)).toMonoidHom (idl h t (1, y)) = y from Units.ext (piW_comp_idl h t _ _)] at e2
  rw [e1, e2, show (x, y) = (x, 1) * (1, y) by simp, map_mul, map_mul, Circle.coe_mul]
  rfl

theorem absE_idl (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (x y : (Fv F v)ˣ) :
    (absE F E (idl h t (x, y)) : ℝ) = GlobalTheory.SplitWeil.nabs (Fv F v) x * GlobalTheory.SplitWeil.nabs (Fv F v) y := by
  have hN : ∀ z : Fv F v ⊗[F] E, Algebra.norm (Fv F v) z = splitProj t z * splitProj (t.comp σ) z := fun z => by
    have := congrArg (splitProj t) (GlobalTheory.Doubling.algebraMap_norm_eq h z)
    rw [AlgHom.commutes, map_mul, ← splitProj_comp] at this
    exact this
  rw [absE_of_mem (v := v) (mem_idelesAt.2 (at_idl h t x y)), GlobalTheory.Doubling.absEv_apply, coe_nnnorm, hN, norm_mul,
    ← ((GlobalTheory.CompletionNorm.norm_nabs_valuation F v).1 x).1, ← ((GlobalTheory.CompletionNorm.norm_nabs_valuation F v).1 y).1]
  exact congrArg₂ (fun p q : Fv F v => ‖p‖ * ‖q‖) (piW_idl h t x y) (piW_comp_idl h t x y)

theorem char_idl (h : IsCMExt F E σ) (χ : Chr F E) {m : ℕ}
    (hχ : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m) (t : E →ₐ[F] Fv F v) (x y : (Fv F v)ˣ) (a : ℕ) :
    (χ (idl h t (x, y⁻¹)) : ℂ) * (((absE F E (idl h t (x, y⁻¹)) : ℝ) ^ ((a : ℝ) / 2) : ℝ) : ℂ) =
      (chrW χ t x : ℂ) * GlobalTheory.SplitFlip.apow x ((a : ℂ) / 2) * ((chrW χ t y : ℂ) * GlobalTheory.SplitFlip.apow y (-(a : ℂ) / 2)) := by
  rw [chr_idl, absE_idl, GlobalTheory.OppLagr.chrW_comp h χ hχ, MonoidHom.inv_apply, map_inv, inv_inv, ← GlobalTheory.SplitWeil.nabs_mul,
    Complex.ofReal_cpow (GlobalTheory.SplitWeil.nabs_pos _ _).le, neg_div, ← GlobalTheory.SplitFlip.apow_inv]
  have := GlobalTheory.SplitFlip.apow_mul x y⁻¹ ((a : ℂ) / 2)
  rw [GlobalTheory.SplitFlip.apow] at this
  push_cast
  rw [this]
  ring

variable {B : Base F E} {d m r s r₁ s₁ i₀ i₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E m} {H : Plane E d m}

omit [NumberField E] in
theorem form_skew (hσ : ∀ x, σ (σ x) = x) {J : Matrix (Fin d) (Fin d) E} (hJ : ∀ i j, σ (J j i) = -J i j) (x y : Fin d → E) :
    form σ J y x = -σ (form σ J x y) := by
  simp only [form, dotProduct, mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem gram_frame (hB : B.IsGood σ) (hW : W.IsSkew σ B r s) (hA : H.IsAdapted σ B W W₁ i₀ i₁) :
    (frame H.x H.ι H.y)ᵀ * W.J * (frame H.x H.ι H.y).map σ = gram W₁.J := by
  have hs := form_skew (GlobalTheory.OppLagr.conj_conj hB.cm) hW.skew
  have o : ∀ j, form σ W.J (fun r => H.ι r j) H.x = 0 ∧ form σ W.J (fun r => H.ι r j) H.y = 0 := fun j => by
    have := hA.orth (Pi.single j 1)
    rwa [Matrix.mulVec_single_one] at this
  have g := hA.gram
  rw [Matrix.mul_assoc] at g ⊢
  ext (i | i | i) (j | j | j)
  · exact hA.xx
  · exact (hs (fun r => H.ι r j) H.x).trans (by rw [(o j).1]; simp [gram])
  · exact hA.xy.trans (by simp [gram, Subsingleton.elim i j])
  · exact (o i).1
  · exact congrFun (congrFun g i) j
  · exact (o i).2
  · exact (hs H.x H.y).trans (by rw [hA.xy]; simp [gram, Subsingleton.elim i j])
  · exact (hs (fun r => H.ι r j) H.y).trans (by rw [(o j).2]; simp [gram])
  · exact hA.yy

theorem gram_frame_map (hB : B.IsGood σ) (hW : W.IsSkew σ B r s) (hA : H.IsAdapted σ B W W₁ i₀ i₁) (t : E →ₐ[F] Fv F v) :
    ((frame H.x H.ι H.y).map t)ᵀ * W.J.map t * (frame H.x H.ι H.y).map (t.comp σ) = gram (W₁.J.map t) := by
  have := congrArg (fun Z => Z.map (t : E →+* Fv F v)) (gram_frame hB hW hA)
  simp only [Matrix.map_mul, Matrix.transpose_map] at this
  refine this.trans ?_
  ext (i | i | i) (j | j | j) <;> simp [gram, Matrix.one_apply, Fin.fin_one_eq_zero]

theorem exists_basis (hB : B.IsGood σ) (hW : W.IsSkew σ B r s) (hW₁ : W₁.IsSkew σ B r₁ s₁)
    (hA : H.IsAdapted σ B W W₁ i₀ i₁) (e : Fin 1 ⊕ Fin m ⊕ Fin 1 ≃ Fin d) (t : E →ₐ[F] Fv F v) :
    ∃ c : GL (Fin d) (Fv F v), ∀ u : GL (Fin d) (Fv F v), ∃ h ∈ UAt σ W (evFin F v), locMat t c h = u ∧
      ∀ N : Matrix _ _ (AE F E), At (evFin F v) (N - 1) → N.map (piW t) = u.val.submatrix e e →
        (u.val.submatrix e e)ᵀ * gram (W₁.J.map t) * N.map (piW (t.comp σ)) = gram (W₁.J.map t) →
        mat h * frame (incV F H.x) (incM F H.ι) (incV F H.y) = frame (incV F H.x) (incM F H.ι) (incV F H.y) * N := by
  have hG := gram_frame_map hB hW hA t
  have hJ : IsUnit (W₁.J.map t).det :=
    isUnit_iff_ne_zero.2 (GlobalTheory.OppLagr.det_map_ne_zero (GlobalTheory.OppLagr.det_ne_zero_skew hW₁) t)
  have hΓ := gram_inv (Matrix.nonsing_inv_mul _ hJ)
  set P := frame H.x H.ι H.y with hP
  generalize fromBlocks _ _ _ _ = Γ' at hΓ
  have hc : IsUnit ((P.map t).submatrix id e.symm) := by
    rw [← Matrix.isUnit_transpose]
    refine IsUnit.of_mul_eq_one ((W.J.map t * P.map (t.comp σ) * Γ').submatrix id e.symm) ?_
    rw [Matrix.transpose_submatrix, ← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, hG, mul_eq_one_comm.1 hΓ, Matrix.submatrix_one_equiv]
  refine ⟨hc.unit, fun u => ?_⟩
  obtain ⟨h, hh, hu⟩ := GlobalTheory.SkewSplitSurj.exists_locMat_eq F E σ B d W r s hB hW v t hc.unit u
  refine ⟨h, hh, hu, fun N hN h1 h2 => ?_⟩
  have a1 : (mat h).map (piW t) * P.map t = P.map t * u.val.submatrix e e := by
    have b1 : (mat h).map (piW t) * hc.unit.val = hc.unit.val * u.val := by
      rw [← hu, locMat_val, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    have b2 : P.map t = hc.unit.val.submatrix id e := by simp
    rw [b2, Matrix.submatrix_mul_equiv, ← b1]
    rfl
  have a2 := adj_intertwine e hG hΓ (N₀ := (u⁻¹).val.submatrix e e)
    (by rw [Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_one_equiv]) (unit_map σ h t) a1 h2
  have a3 : frame (incV F H.x) (incM F H.ι) (incV F H.y) = incM F P := by
    ext r (j | j | j) <;> rfl
  rw [a3]
  exact adelic_intertwine hB.cm t hh hN (by rw [h1]; exact a1) a2

theorem exists_adapted (hB : B.IsGood σ) (hW : W.IsSkew σ B r s) (hW₁ : W₁.IsSkew σ B r₁ s₁)
    (hA : H.IsAdapted σ B W W₁ i₀ i₁) (e : Fin 1 ⊕ Fin m ⊕ Fin 1 ≃ Fin d) (t : E →ₐ[F] Fv F v) :
    ∃ c : GL (Fin d) (Fv F v),
      (∀ (u : GL (Fin d) (Fv F v)) X Y, u.val.submatrix e e = fromBlocks 1 X 0 (fromBlocks 1 Y 0 1) →
        ∃ h ∈ UAt σ W (evFin F v), locMat t c h = u ∧ h ∈ unip σ W H) ∧
      ∀ (u : GL (Fin d) (Fv F v)) (x y : (Fv F v)ˣ) (g : GL (Fin m) (Fv F v)), u.val.submatrix e e =
          fromBlocks (of fun _ _ => (x : Fv F v)) 0 0 (fromBlocks g.val 0 0 (of fun _ _ => (y : Fv F v))) →
        ∃ h ∈ UAt σ W (evFin F v), locMat t c h = u ∧ ∃ h₁ ∈ UAt σ W₁ (evFin F v), locMat t 1 h₁ = g ∧
          IsLevi H (idl hB.cm t (x, y⁻¹)) h₁ h := by
  obtain ⟨c, hc⟩ := exists_basis hB hW hW₁ hA e t
  have hJ : IsUnit (W₁.J.map t).det :=
    isUnit_iff_ne_zero.2 (GlobalTheory.OppLagr.det_map_ne_zero (GlobalTheory.OppLagr.det_ne_zero_skew hW₁) t)
  refine ⟨c, fun u X Y hu => ?_, fun u x y g hu => ?_⟩
  · obtain ⟨h, hh, h1, h2⟩ := hc u
    obtain ⟨X', Y', hX⟩ := gram_unip (Matrix.mul_nonsing_inv _ hJ) X Y
    refine ⟨h, hh, h1, Subgroup.subset_closure (cols_unip (X := of fun i j => liftPair hB.cm t (X i j, X' i j))
      (Y := of fun i j => liftPair hB.cm t (Y i j, Y' i j)) (h2 _ (fun a ha => ?_) ?_ ?_))⟩
    · ext (i | i | i) (j | j | j) <;> simp [Matrix.one_apply, at_liftPair hB.cm t _ a ha]
    · rw [hu]
      ext (i | i | i) (j | j | j) <;> simp [Matrix.one_apply, piW_liftPair, apply_ite (piW t)]
    · rw [hu]
      refine Eq.trans ?_ hX
      congr 1
      ext (i | i | i) (j | j | j) <;> simp [Matrix.one_apply, piW_comp_liftPair, apply_ite (piW (t.comp σ))]
  · obtain ⟨h, hh, h1, h2⟩ := hc u
    obtain ⟨h₁, hh₁, g1⟩ := GlobalTheory.SkewSplitSurj.exists_locMat_eq F E σ B m W₁ r₁ s₁ hB hW₁ v t 1 g
    have g2 : (mat h₁).map (piW t) = g.val := by rw [← g1, locMat_val]; simp
    have si : cA σ ((idl hB.cm t (x, y⁻¹))⁻¹ : (AE F E)ˣ).val = idl hB.cm t (y, x⁻¹) := by
      rw [← map_inv, Prod.inv_mk, inv_inv, cA_idl]
    refine ⟨h, hh, h1, h₁, hh₁, g1, ?_⟩
    rw [IsLevi, si]
    refine cols_levi (h2 _ (fun a ha => ?_) ?_ ?_)
    · have b1 := at_idl hB.cm t x y⁻¹ a ha
      have b2 := at_idl hB.cm t y x⁻¹ a ha
      have b3 := fun i j => congrFun (congrFun (hh₁ a ha) i) j
      ext (i | i | i) (j | j | j)
      all_goals first
        | (simp [Matrix.one_apply, Fin.fin_one_eq_zero, b1, b2]; done)
        | simpa [Matrix.one_apply] using b3 i j
    · rw [hu, ← g2]
      ext (i | i | i) (j | j | j) <;> simp [piW_idl]
    · rw [hu]
      refine Eq.trans ?_ (gram_levi (g' := (mat h₁).map (piW (t.comp σ))) (g2 ▸ unit_map σ h₁ t) x y)
      congr 1
      ext (i | i | i) (j | j | j) <;> simp [piW_comp_idl]

theorem one_mem_UAt (Y : Spc F E d) : (1 : UA σ Y.J) ∈ UAt σ Y (evFin F v) := fun u _ => by
  rw [show mat (1 : UA σ Y.J) = 1 from rfl, sub_self, smul_zero]

theorem isPair_triple {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (h : IsTriple B G X om om') :
    IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) := by
  refine ⟨h.base, h.geo.hV, h.geo.hW, h.geo.hM, h.chars.heckeβ, ⟨?_, fun x => ?_⟩, h.chars.resβ, fun u => ?_, h.weil⟩
  · show Continuous fun x => X.β x / X.α x
    exact h.chars.heckeβ.1.div' h.chars.heckeα.1
  · rw [MonoidHom.div_apply, h.chars.heckeβ.2 x, h.chars.heckeα.2 x, div_one]
  · rw [MonoidHom.div_apply, Circle.coe_div, h.chars.resβ u, h.chars.resα u]
    split_ifs
    · simp
    · rw [div_eq_mul_inv, ← inv_pow, inv_neg_one, ← pow_add]

end Adelic

end GlobalTheory.JacGeom

open GlobalTheory.JacGeom in

theorem GlobalTheory.JacGeom.isJacMap_of_equivariant : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b)
    (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a (b + 2)) (Rf : FinMaps F a (b + 2))
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F a b) (Rf₁ : FinMaps F a b),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∀ (v : Pl F) (t : E →ₐ[F] Fv F v), ∃ (c : GL (Fin (a + (b + 2))) (Fv F v)) (c₁ : GL (Fin (a + b)) (Fv F v)),
        GlobalTheory.KSplit.IsSmU (chrW X.α t) ∧ GlobalTheory.KSplit.IsSmU (chrW X.β t) ∧
        ∀ (eB : Rf.Pi v ≃ₗ[ℂ] GlobalTheory.KSplit.indSp a (b + 2) (chrW X.α t) (chrW X.β t))
          (eS : Rf₁.Pi v ≃ₗ[ℂ] GlobalTheory.KSplit.indSp a b (chrW X.α t) (chrW X.β t)),
          (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + (b + 2)) → Fv F v),
            ∀ φ₁ ∈ SB (Fin a × Fin (a + (b + 2)) → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ →
            ∀ g : GL (Fin (a + (b + 2))) (Fv F v), (eB (Rf.p v φ₁) : GL (Fin (a + (b + 2))) (Fv F v) → ℂ) g =
              (eB (Rf.p v φ) : GL (Fin (a + (b + 2))) (Fv F v) → ℂ) (g * GlobalTheory.KSplit.locMat t c h)) →
          (∀ h ∈ UAt σ G₁.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + b) → Fv F v),
            ∀ φ₁ ∈ SB (Fin a × Fin (a + b) → Fv F v), Acts (evFin F v) (om₁ (1, h)) φ φ₁ →
            ∀ g : GL (Fin (a + b)) (Fv F v), (eS (Rf₁.p v φ₁) : GL (Fin (a + b)) (Fv F v) → ℂ) g =
              (eS (Rf₁.p v φ) : GL (Fin (a + b)) (Fv F v) → ℂ) (g * GlobalTheory.KSplit.locMat t c₁ h)) →
          ∀ φ : Rf.Pi v →ₗ[ℂ] Rf₁.Pi v,
            (∀ u ∈ unip σ G.W H', u ∈ UAt σ G.W (evFin F v) → ∀ ψ ∈ SB (Fin a × Fin (a + (b + 2)) → Fv F v),
              ∀ ψ₁ ∈ SB (Fin a × Fin (a + (b + 2)) → Fv F v), Acts (evFin F v) (om (1, u)) ψ ψ₁ →
                φ (Rf.p v ψ₁) = φ (Rf.p v ψ)) →
            (∀ (s : (AE F E)ˣ) (h₁ : UA σ G₁.W.J) (m : UA σ G.W.J), IsLevi H' s h₁ m → m ∈ UAt σ G.W (evFin F v) →
              h₁ ∈ UAt σ G₁.W (evFin F v) → ∀ ψ ∈ SB (Fin a × Fin (a + (b + 2)) → Fv F v),
              ∀ ψ₁ ∈ SB (Fin a × Fin (a + (b + 2)) → Fv F v), Acts (evFin F v) (om (1, m)) ψ ψ₁ →
              ∀ θ ∈ SB (Fin a × Fin (a + b) → Fv F v), ∀ θ₁ ∈ SB (Fin a × Fin (a + b) → Fv F v),
              Acts (evFin F v) (om₁ (1, h₁)) θ θ₁ → φ (Rf.p v ψ) = Rf₁.p v θ →
                φ (Rf.p v ψ₁) = ((X.β s : ℂ) * (((absE F E s : ℝ) ^ ((a : ℝ) / 2) : ℝ) : ℂ)) • Rf₁.p v θ₁) →
            GlobalTheory.JacLine.IsJacMap a b (chrW X.α t) (chrW X.β t)
              (fun x => (chrW X.β t x : ℂ) * GlobalTheory.SplitFlip.apow x ((a : ℂ) / 2))
              (fun y => (chrW X.β t y : ℂ) * GlobalTheory.SplitFlip.apow y (-(a : ℂ) / 2))
              (eS.toLinearMap ∘ₗ φ ∘ₗ eB.symm.toLinearMap) := by
  intro hK F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁ v t
  have hB := hM.triple.base
  obtain ⟨c, hc1, hc2⟩ := exists_adapted hB hM.triple.geo.hW hM₁.triple.geo.hW hC.hH' (GlobalTheory.JacLine.blk3 a b) t
  refine ⟨c, 1, (GlobalTheory.ChrWLocal.chrW_local F E _ hM.triple.chars.heckeα v t).1,
    (GlobalTheory.ChrWLocal.chrW_local F E _ hM.triple.chars.heckeβ v t).1, fun eB eS heB heS φ hu hl => ?_⟩
  have hx := (GlobalTheory.T.theta_action_exists hK.base F E σ B _ _ _ _ _ _ _ om _ _ _ _ (isPair_triple hM.triple) v).1 1 (one_mem_UAt _)
  have hx₁ := (GlobalTheory.T.theta_action_exists hK.base F E σ B _ _ _ _ _ _ _ om₁ _ _ _ _ (isPair_triple hM₁.triple) v).1 1 (one_mem_UAt _)
  have tr : ∀ h ∈ UAt σ G.W (evFin F v), ∀ f f₁ : GlobalTheory.KSplit.indSp a (b + 2) (chrW X.α t) (chrW X.β t),
      (∀ g, (f₁ : GL (Fin (a + (b + 2))) (Fv F v) → ℂ) g =
        (f : GL (Fin (a + (b + 2))) (Fv F v) → ℂ) (g * GlobalTheory.KSplit.locMat t c h)) →
      ∃ ψ ∈ SB (Fin a × Fin (a + (b + 2)) → Fv F v), ∃ ψ₁ ∈ SB (Fin a × Fin (a + (b + 2)) → Fv F v),
        Acts (evFin F v) (om (1, h)) ψ ψ₁ ∧ eB.symm f = Rf.p v ψ ∧ eB.symm f₁ = Rf.p v ψ₁ := by
    intro h hh f f₁ hf
    obtain ⟨ψ, hψ, e⟩ : eB.symm f ∈ (SB _).map (Rf.p v) := (hM.fin.onto v).symm ▸ Submodule.mem_top
    obtain ⟨ψ₁, ⟨hψ₁, H₁⟩, -⟩ := hx h hh ψ hψ
    refine ⟨ψ, hψ, ψ₁, hψ₁, H₁, e.symm, ?_⟩
    rw [LinearEquiv.symm_apply_eq]
    refine Subtype.ext (funext fun g => ?_)
    rw [heB h hh ψ hψ ψ₁ hψ₁ H₁, e, LinearEquiv.apply_symm_apply, hf]
  refine ⟨fun u Xm Ym hU f f₁ hf => ?_, fun m x y g hm f f₁ hf k => ?_⟩
  · obtain ⟨h, hh, rfl, hn⟩ := hc1 u Xm Ym hU
    obtain ⟨ψ, hψ, ψ₁, hψ₁, H₁, e, e₁⟩ := tr h hh f f₁ hf
    show eS (φ (eB.symm f₁)) = eS (φ (eB.symm f))
    rw [e, e₁, hu h hn hh ψ hψ ψ₁ hψ₁ H₁]
  · obtain ⟨h, hh, rfl, h₁, hh₁, rfl, hL⟩ := hc2 m x y g hm
    obtain ⟨ψ, hψ, ψ₁, hψ₁, H₁, e, e₁⟩ := tr h hh f f₁ hf
    obtain ⟨θ, hθ, eθ⟩ : φ (Rf.p v ψ) ∈ (SB _).map (Rf₁.p v) := (hM₁.fin.onto v).symm ▸ Submodule.mem_top
    obtain ⟨θ₁, ⟨hθ₁, H₂⟩, -⟩ := hx₁ h₁ hh₁ θ hθ
    show (eS (φ (eB.symm f₁)) : GL (Fin (a + b)) (Fv F v) → ℂ) k =
      _ * (eS (φ (eB.symm f)) : GL (Fin (a + b)) (Fv F v) → ℂ) _
    rw [e, e₁, hl _ h₁ h hL hh hh₁ ψ hψ ψ₁ hψ₁ H₁ θ hθ θ₁ hθ₁ H₂ eθ.symm, ← eθ, map_smul, Submodule.coe_smul,
      Pi.smul_apply, smul_eq_mul, heS h₁ hh₁ θ hθ θ₁ hθ₁ H₂, char_idl hB.cm X.β hM.triple.chars.resβ]

end
