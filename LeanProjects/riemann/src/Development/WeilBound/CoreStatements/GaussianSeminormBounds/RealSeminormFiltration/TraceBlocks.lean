import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGrpDataMapHaar
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLieG
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLieH
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLieI

noncomputable section

open scoped TensorProduct Matrix Classical Real SchwartzMap
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift Complex

namespace PositivityTheory.RL.Up

section Mat

variable {β ι : Type} [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι]

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem exp_conj' (C : Matrix β ι ℂ) (C' : Matrix ι β ℂ) (h1 : C * C' = 1) (h2 : C' * C = 1) (Y : Matrix ι ι ℂ) :
    NormedSpace.exp (C * Y * C') = C * NormedSpace.exp Y * C' := by
  have : CompleteSpace (Matrix ι ι ℂ) := FiniteDimensional.complete ℝ _
  let φ : Matrix ι ι ℂ →+* Matrix β β ℂ :=
    { toFun := fun X => C * X * C'
      map_one' := by rw [Matrix.mul_one, h1]
      map_mul' := fun X X' => by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc C', h2, Matrix.one_mul]
      map_zero' := by simp
      map_add' := fun X X' => by rw [Matrix.mul_add, Matrix.add_mul] }
  exact (NormedSpace.map_exp φ ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const) Y).symm

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem exp_blocks (Z Z' : Matrix β β ℂ) :
    NormedSpace.exp (Matrix.fromBlocks Z 0 0 Z') = Matrix.fromBlocks (NormedSpace.exp Z) 0 0 (NormedSpace.exp Z') := by
  have : CompleteSpace (Matrix β β ℂ) := FiniteDimensional.complete ℝ _
  have : @CompleteSpace (Matrix β β ℂ × Matrix β β ℂ) PseudoMetricSpace.toUniformSpace := FiniteDimensional.complete ℝ _
  let φ : Matrix β β ℂ × Matrix β β ℂ →+* Matrix (β ⊕ β) (β ⊕ β) ℂ :=
    { toFun := fun X => Matrix.fromBlocks X.1 0 0 X.2
      map_one' := Matrix.fromBlocks_one
      map_mul' := fun X X' => by simp [Matrix.fromBlocks_multiply]
      map_zero' := Matrix.fromBlocks_zero
      map_add' := fun X X' => by simp [Matrix.fromBlocks_add] }
  have := NormedSpace.map_exp φ (continuous_fst.matrix_fromBlocks continuous_const continuous_const continuous_snd) (Z, Z')
  refine this.symm.trans ?_
  show Matrix.fromBlocks _ 0 0 _ = _
  rw [Prod.fst_exp, Prod.snd_exp]
  rfl

theorem trace_blocks (Z Z' : Matrix β β ℂ) : (Matrix.fromBlocks Z 0 0 Z').trace = Z.trace + Z'.trace := by
  simp [Matrix.trace]

theorem iff_K {b : ℂ} {M : Matrix β β ℂ} (hu : IsUnit ((b • M).map star).det) (g : Matrix β β ℂ) :
    gᴴ * (b • M).map star * g = (b • M).map star ↔ gᵀ * M * g.map star = M := by
  rcases isEmpty_or_nonempty β with h | h
  · exact iff_of_true (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  have hb : b ≠ 0 := fun e => by
    rw [e, zero_smul, Matrix.map_zero _ (star_zero _), Matrix.det_zero] at hu
    exact not_isUnit_zero hu
  have e : gᴴ * (b • M).map star * g = (b • (gᵀ * M * g.map star)).map star := by
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, map_star_mul, map_star_mul]
    congr 1
    ext i j
    simp
  rw [e, (Matrix.map_injective star_injective).eq_iff, (smul_right_injective _ hb).eq_iff]

theorem frame_K {R S : ℕ} {H : Matrix β β ℂ} {C : Matrix β (Ix R S) ℂ} (h : IsFrame H C) :
    (H.map star)ᴴ = H.map star ∧ IsUnit (H.map star).det := by
  obtain ⟨C', h1, h2⟩ := frame_inv h
  have e : H.map star = C'ᴴ * Jm R S * C' := by
    rw [← Jm_map_star, ← h.1, map_star_mul, map_star_mul, show Cᵀ.map star = Cᴴ from rfl,
      show (C.map star).map star = C by ext; simp]
    calc _ = (C * C')ᴴ * H.map star * (C * C') := by rw [h1]; simp
      _ = _ := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e]
  refine ⟨by simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Jm_conjTranspose, Matrix.mul_assoc],
    Matrix.isUnit_det_of_left_inverse (B := C * Jm R S * Cᴴ) ?_⟩
  calc _ = C * (Jm R S * (C' * C)ᴴ * Jm R S) * C' := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [h2, Matrix.conjTranspose_one, Matrix.mul_one, Jm_mul_self, Matrix.mul_one, h1]

end Mat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] {P Q R S : ℕ}
  {ψ : AddChar (AF F) ℂ} {τ : ∀ w : InfinitePlace F, EmbOver E w} {JA : Matrix α α (AE F E)} {JB : Matrix β β (AE F E)}
  {d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ} {a b : ℂ} {A : InfinitePlace F → Matrix α (Ix P Q) ℂ}
  {C : InfinitePlace F → Matrix β (Ix R S) ℂ}

theorem sB_frame (h : IsCMExt F E σ) (hfr : Framed τ JA JB a b A C) {u u' : Matrix α β (AE F E)}
    {c c' : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ} (hc : ∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ)
    (hc' : ∀ w, u'.map (piInf (τ w)) = A w * c' w * (C w)ᵀ) :
    sB σ JA JB u u' = ∑ w, 2 * (∑ l, Fock.tw1 (c w) l * star (Fock.tw1 (c' w) l)).im := by
  rw [sB, symp, Fock.trace_trace h τ, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  have e2 := Fock.herm_frame (MA := JA.map (piInf (τ w))) (MB := JB.map (piInf (τ w))) hfr.1 (hfr.2.1 w) (hfr.2.2 w)
    (c w) (c' w)
  simp only [← hc, ← hc', Matrix.map_apply] at e2
  rw [← e2, hTens, neg_one_mul, map_neg, neg_re]
  simp only [map_sum, map_mul, piInf_cA h]
  ring

theorem fock_data (h : IsCMExt F E σ) (hfr : Framed τ JA JB a b A C) {Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ}
    (hΦ : IsFockMap ψ τ d A C Φ) {D : Matrix α β (AE F E) → (SInf F κ →L[ℂ] SInf F κ)}
    (hD : ∀ u, At (evI F) u → ∀ f, SD (fun t => d.rho ψ (realAd F t • u)) f (D u f))
    {γ : Multiplicative ℝ →* UG (cA σ) JB} {Y : InfinitePlace F → Mat R S} (hY : IsGen τ C γ Y) :
    ∃ Z : InfinitePlace F → Matrix β β ℂ, (∀ w, (Z w).trace = (Y w).trace) ∧
      (∀ (t : ℝ) w, ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf (τ w)) = NormedSpace.exp (t • Z w)) ∧
      (∀ (t : ℝ) w, piInf (τ w) ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).det = cexp (t * (Y w).trace)) ∧
      (∀ w, (Y w).trace.re = 0) ∧
      ∃ u v : InfinitePlace F × (Ln P Q R S × Bool) → Matrix α β (AE F E), (∀ j, At (evI F) (u j)) ∧ (∀ j, At (evI F) (v j)) ∧
        (∀ x, At (evI F) x → ∀ w, x.map (piInf (τ w)) * (Z w)ᵀ = ∑ j, sB σ JA JB (v j) x • (u j).map (piInf (τ w))) ∧
        ∀ T, (8 * π * I : ℂ)⁻¹ • ∑ j, (D (u j) (D (v j) (Φ T)) + D (v j) (D (u j) (Φ T))) =
          Φ (sumPl (fun w => fockAct2 P Q R S (Y w)) T) := by
  choose C' h1 h2 using fun w => frame_inv (hfr.2.2 w)
  choose A' a1 a2 using fun w => frame_inv (hfr.2.1 w)
  have hg : ∀ (t : ℝ) w, ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf (τ w)) =
      C w * NormedSpace.exp (t • Y w) * C' w := fun t w => by rw [← hY, Matrix.mul_assoc, h1, Matrix.mul_one]
  have hu : ∀ w, Y w ∈ upq R S := fun w => lie_of_exp _ _ fun t => (frame_iff_smul (hfr.2.2 w) (hY t w)).1 (by
    have := congrArg (fun X : Matrix β β (AE F E) => X.map (piInf (τ w))) (γ (Multiplicative.ofAdd t)).2
    simp only [map_form h] at this
    exact this)
  obtain ⟨L, -, hL, hL'⟩ := exists_lf h τ α β
  let U : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ → Matrix α β (AE F E) := fun w c =>
    L fun w' => A w' * (Pi.single w c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) w' * (C w')ᵀ
  have hU : ∀ w c T, D (U w c) (Φ T) = Φ (atL w (heisOp c) T) := fun w c T => by
    rw [(actsLaws F κ _ _ (Φ _)).2.2.2.2 _ (hD _ (hL _) (Φ T)) (hΦ.2 _ (hL _) _ (hL' _) T)]
    congr 2
    rw [sumPl, Finset.sum_eq_single w (fun w' _ hw => by simp [atL_eq, hw, heisOp]) (by simp), atL_eq, Pi.single_eq_same]
  refine ⟨fun w => C w * Y w * C' w, fun w => by rw [Matrix.trace_mul_cycle, h2, Matrix.one_mul], fun t w => ?_,
    fun t w => ?_, fun w => ?_, fun j => U j.1 (cu (Y j.1) j.2), fun j => U j.1 (cv j.2), fun j => hL _, fun j => hL _,
    fun x hx w => ?_, fun T => ?_⟩
  · rw [hg, ← exp_conj' _ _ (h1 w) (h2 w), Matrix.mul_smul, Matrix.smul_mul]
  · rw [RingHom.map_det, RingHom.mapMatrix_apply, hg, Matrix.det_conj_of_mul_eq_one (h1 w) (h2 w),
      GlobalTheory.DetSqrtCover.det_exp, Matrix.trace_smul, real_smul]
  · rw [Matrix.trace, re_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    have := congrArg Complex.re (upq_entry (hu w) i i)
    rw [eps_sq] at this
    simp at this
    simp
    linarith
  · let c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ := fun w => A' w * x.map (piInf (τ w)) * (C' w)ᵀ
    have hc : ∀ w, x.map (piInf (τ w)) = A w * c w * (C w)ᵀ := fun w => by
      simp only [c, ← Matrix.mul_assoc, a1, Matrix.one_mul]
      rw [Matrix.mul_assoc, ← Matrix.transpose_mul, h1, Matrix.transpose_one, Matrix.mul_one]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single w (fun w' _ hw => by simp [U, hL', hw.symm]) (by simp)]
    have e : ∀ j, sB σ JA JB (U w (cv j)) x = 2 * (∑ l, Fock.tw1 (cv j) l * star (Fock.tw1 (c w) l)).im := fun j => by
      rw [sB_frame h hfr (hL' _) hc, Finset.sum_eq_single w (fun w' _ hw => by simp [hw, Fock.tw1]) (by simp),
        Pi.single_eq_same]
    simp only [e, U, hL', Pi.single_eq_same]
    rw [Finset.sum_congr rfl fun j _ => (by rw [Matrix.mul_smul, Matrix.smul_mul] :
      (2 * (∑ l, Fock.tw1 (cv j) l * star (Fock.tw1 (c w) l)).im) • (A w * cu (Y w) j * (C w)ᵀ) =
        A w * ((2 * (∑ l, Fock.tw1 (cv j) l * star (Fock.tw1 (c w) l)).im) • cu (Y w) j) * (C w)ᵀ),
      ← Matrix.sum_mul, ← Matrix.mul_sum, ← expand, hc]
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (C w)ᵀ, ← Matrix.transpose_mul, h2, Matrix.transpose_one, Matrix.one_mul]
  · simp only [hU, ← map_add, ← map_sum, ← map_smul]
    congr 1
    rw [Fintype.sum_prod_type, sumPl, LinearMap.sum_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [atL_eq, ← fock_eq (hu w)]
    simp only [map_smul, map_sum, map_add, atL_mul, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.add_apply,
      Module.End.mul_apply]

theorem sumPl_add (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ) (L : InfinitePlace F → Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S))
    (s : InfinitePlace F → ℂ) (T : Tens F P Q R S) :
    Φ (sumPl (fun w => L w + s w • 1) T) = Φ (sumPl L T) + (∑ w, s w) • Φ T := by
  simp only [sumPl, atL_eq, map_add, map_smul, atL_one, Finset.sum_add_distrib, ← Finset.sum_smul, LinearMap.add_apply,
    LinearMap.smul_apply, Module.End.one_apply]

theorem exists_dbl {γ γ' : Multiplicative ℝ →* UG (cA σ) JB} (h : γ ∈ RLines σ JB) (h' : γ' ∈ RLines σ JB) :
    ∃ δ ∈ RLines σ (dbl JB), ∀ t, ((δ t).1 : Matrix (β ⊕ β) (β ⊕ β) (AE F E)) =
      Matrix.fromBlocks ((γ t).1 : Matrix β β (AE F E)) 0 0 ((γ' t).1 : Matrix β β (AE F E)) := by
  let φ : Matrix β β (AE F E) × Matrix β β (AE F E) →* Matrix (β ⊕ β) (β ⊕ β) (AE F E) :=
    { toFun := fun X => Matrix.fromBlocks X.1 0 0 X.2
      map_one' := Matrix.fromBlocks_one
      map_mul' := fun X X' => by simp [Matrix.fromBlocks_multiply] }
  let δ0 : Multiplicative ℝ →* GL (β ⊕ β) (AE F E) := (Units.map φ).comp (MulEquiv.prodUnits.symm.toMonoidHom.comp
    (((UG (cA σ) JB).subtype.comp γ).prod ((UG (cA σ) JB).subtype.comp γ')))
  have c1 : Continuous fun t => (γ t).1 := continuous_subtype_val.comp h.1
  have c2 : Continuous fun t => (γ' t).1 := continuous_subtype_val.comp h'.1
  have hc : Continuous δ0 := Units.continuous_iff.2
    ⟨(Units.continuous_val.comp c1).matrix_fromBlocks continuous_const continuous_const (Units.continuous_val.comp c2),
     (Units.continuous_coe_inv.comp c1).matrix_fromBlocks continuous_const continuous_const
      (Units.continuous_coe_inv.comp c2)⟩
  refine ⟨δ0.codRestrict _ fun t => ?_, ⟨hc.subtype_mk _, fun t u hu => ?_⟩, fun t => rfl⟩
  · have e1 : ((γ t).1 : Matrix β β (AE F E))ᵀ * JB * ((γ t).1 : Matrix β β (AE F E)).map (cA σ) = JB := (γ t).2
    have e2 : ((γ' t).1 : Matrix β β (AE F E))ᵀ * JB * ((γ' t).1 : Matrix β β (AE F E)).map (cA σ) = JB := (γ' t).2
    show (Matrix.fromBlocks ((γ t).1 : Matrix β β (AE F E)) 0 0 ((γ' t).1 : Matrix β β (AE F E)))ᵀ * dbl JB *
      (Matrix.fromBlocks ((γ t).1 : Matrix β β (AE F E)) 0 0 ((γ' t).1 : Matrix β β (AE F E))).map (cA σ) = dbl JB
    rw [dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [e1, e2]
  · show u • (Matrix.fromBlocks ((γ t).1 : Matrix β β (AE F E)) 0 0 ((γ' t).1 : Matrix β β (AE F E)) - 1) = 0
    have e1 := h.2 t u hu
    have e2 := h'.2 t u hu
    rw [smul_sub, sub_eq_zero] at e1 e2 ⊢
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, Matrix.fromBlocks_smul, e1, e2]

theorem at_det {g : Matrix β β (AE F E)} (hg : At (evI F) (g - 1)) : At (evI F) (g.det - 1) := fun u hu => by
  let J : Ideal (AE F E) := LinearMap.ker (LinearMap.mul (AE F E) (AE F E) (algebraMap (AF F) (AE F E) u))
  have hJ : ∀ x, x ∈ J ↔ u • x = 0 := fun x => by rw [Algebra.smul_def]; rfl
  rw [← hJ, ← Ideal.Quotient.eq, RingHom.map_det, map_one, ← Matrix.det_one (n := β),
    ← map_one (Ideal.Quotient.mk J).mapMatrix]
  congr 1
  ext i j
  exact Ideal.Quotient.eq.2 ((hJ _).2 (congrFun (congrFun (hg u hu) i) j))

theorem norm_eq_one (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {z : AE F E} (hz : At (evI F) (z - 1))
    (h1 : ∀ w, ‖piInf (τ w) z‖ = 1) : Algebra.norm (AF F) z = 1 := by
  obtain ⟨x, hx⟩ := exists_moved h
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨ρ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact ρ.injective (by rw [h.2.2.2, h.2.2.2, star_star])
  have hy : σ (x - σ x) = -(x - σ x) := by rw [map_sub, hσ, neg_sub]
  have hy0 : x - σ x ≠ 0 := sub_ne_zero.2 hx.symm
  obtain ⟨B, b0, b1⟩ := exists_basis h (β := x - σ x) (by
    rw [hy]
    exact fun e => hy0 (by linear_combination (-1 / 2 : E) * e))
  have hq : IsQuad (cA σ) ((1 : AF F) ⊗ₜ[F] (x - σ x)) :=
    ⟨(IsUnit.mk0 _ hy0).map (Algebra.TensorProduct.includeRight (R := F) (A := AF F)),
      by rw [← TensorProduct.tmul_neg, ← hy]; rfl,
      Algebra.TensorProduct.basis (AF F) B, by rw [Algebra.TensorProduct.basis_apply, b0]; rfl,
      by rw [Algebra.TensorProduct.basis_apply, b1]⟩
  refine hq.algebraMap_injective ?_
  rw [hq.algebraMap_norm, map_one, ← sub_eq_zero]
  refine eq_zero_of_piInf h τ _ (fun u hu => ?_) fun w => ?_
  · have e : z * cA σ z - 1 = (z - 1) * cA σ z + cA σ (z - 1) := by rw [map_sub, map_one]; ring
    rw [e, smul_add, ← smul_mul_assoc, ← map_smul, hz u hu, zero_mul, map_zero, add_zero]
  · rw [map_sub, map_mul, piInf_cA h, map_one, star_def, mul_conj, normSq_eq_norm_sq, h1]
    simp

theorem sB_anti (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (u v : Matrix α β (AE F E)) :
    sB σ JA JB u v = -sB σ JA JB v u := by
  rw [sB, sB, d.form, d.form, ← Fock.evIh_apply, ← Fock.evIh_apply, ← map_neg, ← map_neg, ← map_neg, ← map_neg, neg_neg,
    neg_sub]

theorem sB_neg (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (u v : Matrix α β (AE F E)) :
    sB σ JA JB (-u) v = -sB σ JA JB u v := by
  rw [sB, sB, d.form, d.form, ← Fock.evIh_apply, ← Fock.evIh_apply]
  simp only [map_neg, Prod.fst_neg, Prod.snd_neg, neg_dotProduct, dotProduct_neg, map_sub]
  ring

theorem sB_zero (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (v : Matrix α β (AE F E)) :
    sB σ JA JB 0 v = 0 := by
  have := sB_neg d 0 v
  rw [neg_zero] at this
  linarith

variable {dd : Darboux (symp (R := AF F) (cA σ) (-1) JA (dbl JB)) (κ ⊕ κ)}

theorem sB_dbl (hdd : IsDblCoord (cA σ) (-1) JA JB d dd) (u u' v v' : Matrix α β (AE F E)) :
    sB σ JA (dbl JB) (Matrix.fromCols u u') (Matrix.fromCols v v') = sB σ JA JB u v - sB σ JA JB u' v' := by
  rw [sB, sB, sB, dd.form, d.form, d.form, hdd, hdd, sumElim_dotProduct_sumElim, sumElim_dotProduct_sumElim,
    ← Fock.evIh_apply, ← Fock.evIh_apply, ← Fock.evIh_apply]
  simp only [dotProduct_neg, map_sub, map_add, map_neg]
  ring

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
theorem at_cols {u u' : Matrix α β (AE F E)} (h : At (evI F) u) (h' : At (evI F) u') : At (evI F) (Matrix.fromCols u u') :=
  fun s hs => by
    ext i j
    rcases j with j | j
    · exact congrFun (congrFun (h s hs) i) j
    · exact congrFun (congrFun (h' s hs) i) j

theorem box_D (hdd : IsDblCoord (cA σ) (-1) JA JB d dd) {D Dd} (hD : IsD d D) (hDd : IsD dd Dd) {u : Matrix α β (AE F E)}
    (hu : At (evI F) u) {B : SInf F (κ ⊕ κ)} {f f' : SInf F κ} (hB : ∀ x, B x = f (x ∘ Sum.inl) * f' (x ∘ Sum.inr)) (x) :
    Dd (Matrix.fromCols u 0) B x = D u f (x ∘ Sum.inl) * f' (x ∘ Sum.inr) := by
  let L1 : (κ ⊕ κ → mixedEmbedding.mixedSpace F) →L[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Sum.inl i)
  let L2 : (κ ⊕ κ → mixedEmbedding.mixedSpace F) →L[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Sum.inr i)
  have h1 := ((f.hasFDerivAt (L1 x)).comp x L1.hasFDerivAt).mul ((f'.hasFDerivAt (L2 x)).comp x L2.hasFDerivAt)
  have h2 : fderiv ℝ B x = _ := (congrArg (fderiv ℝ · x) (funext hB)).trans h1.fderiv
  have e1 : L1 (fun i => evI F ((Sum.elim (d.e u).1 0 : κ ⊕ κ → AF F) i)) = fun i => evI F ((d.e u).1 i) := rfl
  have e2 : L2 (fun i => evI F ((Sum.elim (d.e u).1 0 : κ ⊕ κ → AF F) i)) = 0 := funext fun _ => Der.evI_zero
  rw [hDd _ (at_cols hu fun _ _ => smul_zero _), hD u hu, hdd, h2, hB, map_zero]
  simp only [Prod.fst_zero, Prod.snd_zero, neg_zero, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, e1, e2, map_zero, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
    Der.evI_zero, mul_zero, Finset.sum_const_zero, add_zero, smul_eq_mul, Function.comp_apply]
  show _ + f' (x ∘ Sum.inr) * fderiv ℝ f (x ∘ Sum.inl) _ - _ = _
  ring

end PositivityTheory.RL.Up

namespace PositivityTheory.RL

open Up

theorem lieScalar' (hM : GlobalTheory.Published.RealMetaplecticRepresentation) : GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.LieScalar := by
  intro hD F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ om hcm hψ hfr hΦ hom
  obtain ⟨D, hD⟩ := hD F E σ α β κ ψ JA JB d hψ
  obtain ⟨c, hc⟩ := main hM hcm hψ τ (fun w => (b • JB.map (piInf (τ w))).map star)
    (fun w => (frame_K (hfr.2.2 w)).1) (fun w => (frame_K (hfr.2.2 w)).2) (fun w => iff_K (frame_K (hfr.2.2 w)).2) hom
    (D := D) fun u hu f => (hD u hu f).2
  refine ⟨c, fun γ hγ Y hY T => ?_⟩
  obtain ⟨Z, tr, hZ, -, -, u, v, hu, hv, huv, hq⟩ := fock_data hcm hfr hΦ (fun u hu f => (hD u hu f).1) hY
  have := hc γ hγ Z hZ _ u v hu hv huv (Φ T)
  simp only [tr, hq] at this
  rw [sumPl_add]
  exact this

theorem lieSecond' (hM : GlobalTheory.Published.RealMetaplecticRepresentation) : GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.LieSecond := by
  intro hD0 F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ om χ m hcm hψ hfr hΦ hW hm γ hγ Y hY T
  obtain ⟨hom, dd, omd, hdd, ⟨-, homd, hS⟩, hres⟩ := hW
  obtain ⟨D, hD⟩ := hD0 F E σ α β κ ψ JA JB d hψ
  obtain ⟨Dd, hDd⟩ := hD0 F E σ α (β ⊕ β) (κ ⊕ κ) ψ JA (dbl JB) dd hψ
  have iD : IsD d D := fun u hu f => (hD u hu f).2
  have iDd : IsD dd Dd := fun u hu f => (hDd u hu f).2
  obtain ⟨c, hc⟩ := main hM hcm hψ τ (fun w => (b • JB.map (piInf (τ w))).map star)
    (fun w => (frame_K (hfr.2.2 w)).1) (fun w => (frame_K (hfr.2.2 w)).2) (fun w => iff_K (frame_K (hfr.2.2 w)).2) hom iD
  have eK : ∀ w, (b • (dbl JB).map (piInf (τ w))).map star = Matrix.fromBlocks ((b • JB.map (piInf (τ w))).map star) 0 0
      (-(b • JB.map (piInf (τ w))).map star) := fun w => by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [dbl]
  have uK : ∀ w, IsUnit ((b • (dbl JB).map (piInf (τ w))).map star).det := fun w => by
    rw [eK, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]
    exact (frame_K (hfr.2.2 w)).2.mul ((isUnit_one.neg.pow _).mul (frame_K (hfr.2.2 w)).2)
  obtain ⟨c', hc'⟩ := main hM hcm hψ τ (fun w => (b • (dbl JB).map (piInf (τ w))).map star)
    (fun w => by
      simp only [eK, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_neg, Matrix.conjTranspose_zero,
        (frame_K (hfr.2.2 w)).1]) uK (fun w => iff_K (uK w)) homd iDd
  obtain ⟨Z, tr, hZ, hdet, hre, u, v, hu, hv, huv, hq⟩ := fock_data hcm hfr hΦ (fun u hu f => (hD u hu f).1) hY
  have split : ∀ x : Matrix α (β ⊕ β) (AE F E), At (evI F) x → ∃ x₁ x₂, At (evI F) x₁ ∧ At (evI F) x₂ ∧
      x = Matrix.fromCols x₁ x₂ := fun x hx =>
    ⟨x.toCols₁, x.toCols₂, fun s hs => congrArg Matrix.toCols₁ (hx s hs), fun s hs => congrArg Matrix.toCols₂ (hx s hs),
      (Matrix.fromCols_toCols x).symm⟩
  have z0 : At (evI F) (0 : Matrix α β (AE F E)) := fun _ _ => smul_zero _
  have step2 : ∑ w, c w * (Y w).trace = ∑ w, c' w * (Y w).trace := by
    obtain ⟨δ, hδ, hδ'⟩ := exists_dbl hγ (γ' := 1) ⟨continuous_const, fun t s _ => by simp⟩
    obtain ⟨f, B, r, hB, hf, -, -, hr0⟩ := exists_box F κ
    obtain ⟨g, hg, y, hy⟩ := SeminormBoundRestriction.exists_SB (F := F) (κ := κ)
    let x := SeminormBoundRestriction.pt (0 : κ → mixedEmbedding.mixedSpace F) y
    have h1 := hc' δ hδ (fun w => Matrix.fromBlocks (Z w) 0 0 0) (fun t w => by
      rw [hδ', Matrix.fromBlocks_map, hZ, Matrix.fromBlocks_smul, smul_zero, exp_blocks, NormedSpace.exp_zero]
      simp) _ (fun j => Matrix.fromCols (u j) 0) (fun j => Matrix.fromCols (v j) 0) (fun j => at_cols (hu j) z0)
      (fun j => at_cols (hv j) z0) (fun x hx w => by
        obtain ⟨x₁, x₂, h₁, h₂, rfl⟩ := split x hx
        simp only [sB_dbl hdd, sB_zero d, sub_zero, Matrix.fromBlocks_transpose, Matrix.fromCols_map,
          Matrix.fromCols_mul_fromBlocks, Matrix.transpose_zero, Matrix.mul_zero, add_zero, huv x₁ h₁]
        ext i j
        rcases j with j | j <;> simp [Matrix.sum_apply]) B _ (box_SB hg hg) _ (SeminormBoundRestriction.eval_adm (Sum.elim x x))
    have h2 := (hc γ hγ Z hZ _ u v hu hv huv f g hg _ (SeminormBoundRestriction.eval_adm x)).mul_const (pureA F f g x)
    have eB : ∀ (B : SInf F (κ ⊕ κ)), pureA F B (boxFun g g) (Sum.elim x x) = B 0 := fun B => by
      have : Sum.elim x x = SeminormBoundRestriction.pt 0 (Sum.elim y y) := funext fun i => by rcases i with i | i <;> rfl
      rw [this, SeminormBoundRestriction.pureA_pt]
      show _ * (g y * g y) = _
      rw [hy, mul_one, mul_one]
    have ef : ∀ f : SInf F κ, pureA F f g x = f 0 := fun f => by rw [SeminormBoundRestriction.pureA_pt, hy, mul_one]
    have e3 : pureA F B (boxFun g g) = boxFun (pureA F f g) (pureA F f g) := by
      funext p
      simp only [pureA, boxFun, hB]
      exact mul_mul_mul_comm _ _ _ _
    have h3 := h1.unique (h2.congr_of_eventuallyEq (.of_forall fun t => by
      show omd _ _ _ = _
      rw [e3, hres (γ (Multiplicative.ofAdd t)) _ (hδ' _) _ (pure_mem f hg) _ (pure_mem f hg)]
      rfl))
    have f0 : f 0 = 1 := by rw [hf, hr0, ofReal_one]
    have bb : ∀ p q : Matrix α β (AE F E), At (evI F) p → At (evI F) q →
        Dd (Matrix.fromCols p 0) (Dd (Matrix.fromCols q 0) B) 0 = D p (D q f) 0 := fun p q hp hq =>
      (box_D hdd iD iDd hp (box_D hdd iD iDd hq hB) 0).trans (by
        show D p (D q f) 0 * f 0 = _
        rw [f0, mul_one])
    have B0 : B 0 = 1 := (hB 0).trans (by
      show f 0 * f 0 = 1
      rw [f0, mul_one])
    simp only [LinearMap.proj_apply, eB, ef, SchwartzMap.add_apply, SchwartzMap.smul_apply, SchwartzMap.sum_apply,
      bb _ _ (hu _) (hv _), bb _ _ (hv _) (hu _), f0, B0, mul_one, smul_eq_mul, add_right_inj, trace_blocks,
      Matrix.trace_zero, add_zero, tr] at h3
    exact h3.symm
  have step1 : ∑ w, c' w * (Y w).trace = ∑ w, (m w : ℂ) / 2 * (Y w).trace := by
    obtain ⟨δ, hδ, hδ'⟩ := exists_dbl hγ hγ
    obtain ⟨l, hl, hinv, B, G, hG, hne⟩ := exists_form F κ ψ
    obtain ⟨T0, hT0⟩ := hl G hG
    have kill : ∀ y, At (evI F) y → ∀ B', T0 (Dd (Matrix.fromCols y y) B') = 0 := fun y hy B' => by
      have h1 := (hDd _ (at_cols hy hy) B').1 G hG l hl
      have e : ∀ t : ℝ, l (dd.rho ψ (realAd F t • Matrix.fromCols y y) (pureA F B' G)) = l (pureA F B' G) := fun t => by
        rw [show realAd F t • Matrix.fromCols y y = Matrix.fromCols (realAd F t • y) (realAd F t • y) by
          ext i j
          rcases j with j | j <;> rfl, Darboux.rho, hdd, hinv _ _ _ (pure_mem B' hG)]
      simp only [e] at h1
      rw [← hT0]
      exact h1.unique (hasDerivAt_const _ _)
    let hf : AF F := realAd F (1 / 2)
    have hh : ∀ j, At (evI F) (hf • u j) := fun j s hs => by rw [smul_comm, hu j s hs, smul_zero]
    have ng : ∀ {p : Matrix α β (AE F E)}, At (evI F) p → At (evI F) (-p) := fun hp s hs => by
      rw [smul_neg, hp s hs, neg_zero]
    have h1 := hc' δ hδ (fun w => Matrix.fromBlocks (Z w) 0 0 (Z w)) (fun t w => by
      rw [hδ', Matrix.fromBlocks_map, hZ, Matrix.fromBlocks_smul, smul_zero, exp_blocks]
      simp) _
      (Sum.elim (fun j => Matrix.fromCols (hf • u j) (hf • u j)) fun j => Matrix.fromCols (hf • u j) (-(hf • u j)))
      (Sum.elim (fun j => Matrix.fromCols (v j) (-v j)) fun j => Matrix.fromCols (v j) (v j))
      (by rintro (j | j); exacts [at_cols (hh j) (hh j), at_cols (hh j) (ng (hh j))])
      (by rintro (j | j); exacts [at_cols (hv j) (ng (hv j)), at_cols (hv j) (hv j)]) (fun x hx w => by
        obtain ⟨x₁, x₂, h₁, h₂, rfl⟩ := split x hx
        simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, sB_dbl hdd, sB_neg d, Matrix.fromBlocks_transpose,
          Matrix.fromCols_map, Matrix.fromCols_mul_fromBlocks, Matrix.transpose_zero, Matrix.mul_zero, add_zero, zero_add,
          huv x₁ h₁, huv x₂ h₂, ← Finset.sum_add_distrib]
        ext i k
        rcases k with k | k <;>
        · simp only [Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Matrix.sum_apply, Matrix.add_apply,
            Matrix.smul_apply, Matrix.map_apply, Matrix.neg_apply, map_neg, hf, Fock.piInf_realAd hcm.1, real_smul]
          refine Finset.sum_congr rfl fun j _ => ?_
          push_cast
          ring) B G hG l hl
    have h2 : ∀ t : ℝ, l (omd (δ (Multiplicative.ofAdd t)) (pureA F B G)) =
        cexp (t * ∑ w, (m w : ℂ) * (Y w).trace) * l (pureA F B G) := fun t => by
      have n1 : ∀ w, ‖cexp (t * (Y w).trace)‖ = 1 := fun w => by simp [norm_exp, hre]
      have ad := at_det (hγ.2 (Multiplicative.ofAdd t))
      rw [hS l hl (fun z φ hφ => by
        rw [show z * (diagCols β : Matrix (β ⊕ β) β (AE F E))ᵀ = Matrix.fromCols z z by
          simp [diagCols, Matrix.transpose_fromRows, Matrix.mul_fromCols], Darboux.rho, hdd, hinv _ _ _ hφ])
        (δ (Multiplicative.ofAdd t)) (γ (Multiplicative.ofAdd t)).1 (by
          rw [hδ']
          simp [diagCols, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul]) _ (pure_mem B hG),
        show Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det (γ (Multiplicative.ofAdd t)).1) = 1
          from Units.ext (norm_eq_one hcm τ ad fun w => (congrArg norm (hdet t w)).trans (n1 w)),
        hm _ ad]
      simp only [Matrix.GeneralLinearGroup.val_det_apply, hdet, n1, map_one, NNReal.coe_one, Real.one_rpow, ofReal_one,
        mul_one, div_one, ← Complex.exp_int_mul, ← Complex.exp_sum, Finset.mul_sum]
      congr 2
      exact Finset.sum_congr rfl fun w _ => by ring
    simp only [h2] at h1
    have h3 := h1.unique ((((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const
      (∑ w, (m w : ℂ) * (Y w).trace)).cexp).mul_const (l (pureA F B G)))
    have t1 : ∀ j, T0 (Dd (Matrix.fromCols (v j) (-v j)) (Dd (Matrix.fromCols (hf • u j) (hf • u j)) B)) =
        2 * π * I * (2 * sB σ JA JB (v j) (hf • u j) : ℝ) * T0 B := fun j => by
      rw [iDd.comm (at_cols (hv j) (ng (hv j))) (at_cols (hh j) (hh j)), map_add, kill _ (hh j), map_smul, sB_dbl hdd,
        sB_neg d, zero_add, smul_eq_mul]
      congr 3
      ring
    have t2 : ∀ j, T0 (Dd (Matrix.fromCols (hf • u j) (-(hf • u j))) (Dd (Matrix.fromCols (v j) (v j)) B)) =
        -(2 * π * I * (2 * sB σ JA JB (v j) (hf • u j) : ℝ) * T0 B) := fun j => by
      rw [iDd.comm (at_cols (hh j) (ng (hh j))) (at_cols (hv j) (hv j)), map_add, kill _ (hv j), map_smul, sB_dbl hdd,
        sB_neg d, zero_add, smul_eq_mul, sB_anti d]
      push_cast
      ring
    rw [hT0] at hne
    simp only [hT0, map_add, map_smul, map_sum, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, kill _ (hh _),
      kill _ (hv _), t1, t2, zero_add, add_zero, Finset.sum_neg_distrib, add_neg_cancel, smul_zero, smul_eq_mul,
      trace_blocks, tr, id, ofReal_zero, zero_mul, Complex.exp_zero, one_mul, ofReal_one, mul_zero] at h3
    have h4 := mul_right_cancel₀ hne h3
    simp only [mul_add, Finset.sum_add_distrib] at h4
    simp only [div_mul_eq_mul_div, ← Finset.sum_div, ← h4]
    ring
  have := hc γ hγ Z hZ _ u v hu hv huv (Φ T)
  simp only [tr, hq, step2, step1] at this
  rw [sumPl_add]
  exact this

theorem lieScalar : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.VacLine → GlobalTheory.RealLift.LieScalar :=
  fun hP hD _ => lieScalar' hP.realMetaplecticRepresentation hD

theorem lieSecond : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.FockEx → GlobalTheory.RealLift.VacLine →
    GlobalTheory.RealLift.LieScalar → GlobalTheory.RealLift.LieSecond :=
  fun hP hD _ _ _ => lieSecond' hP.realMetaplecticRepresentation hD

example : GlobalTheory.RealLift.LieSecond → GlobalTheory.RealLift.LieFirst := lieFirst

end PositivityTheory.RL

end
