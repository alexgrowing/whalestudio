import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct

namespace GlobalTheory.MaxCptConj

section Mat

open scoped ComplexOrder MatrixOrder

variable {n : ℕ}

theorem exists_invariant_posDef {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (f : G →* Matrix (Fin n) (Fin n) ℂ) (hf : Continuous f) :
    ∃ P : Matrix (Fin n) (Fin n) ℂ, P.PosDef ∧ ∀ g, (f g)ᴴ * P * f g = P := by
  borelize G
  let μ₀ : Measure G := Measure.haar
  let μ : Measure G := μ₀.inv
  have hc : ∀ i j, Continuous fun g => ((f g)ᴴ * f g) i j := fun i j =>
    (hf.matrix_conjTranspose.matrix_mul hf).matrix_elem i j
  have hi : ∀ i j, Integrable (fun g => ((f g)ᴴ * f g) i j) μ := fun i j =>
    (hc i j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let P : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => ∫ g, ((f g)ᴴ * f g) i j ∂μ
  have key : ∀ x y : Fin n → ℂ, star x ⬝ᵥ P *ᵥ y = ∫ g, star (f g *ᵥ x) ⬝ᵥ (f g *ᵥ y) ∂μ := fun x y => by
    have e : ∀ g, star (f g *ᵥ x) ⬝ᵥ (f g *ᵥ y) = ∑ i, ∑ j, star x i * (((f g)ᴴ * f g) i j * y j) := fun g => by
      rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, ← dotProduct_mulVec]
      simp only [dotProduct, mulVec, Finset.mul_sum]
    simp only [e]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ((hi i j).mul_const _).const_mul _]
    simp only [dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => ((hi i j).mul_const _).const_mul _]
    simp only [integral_const_mul, integral_mul_const, P, of_apply]
  refine ⟨P, Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_, fun g => ?_⟩
  · ext i j
    simp only [P, conjTranspose_apply, of_apply, RCLike.star_def, ← integral_conj]
    refine integral_congr_ae (.of_forall fun g => ?_)
    exact congrFun (congrFun (isHermitian_conjTranspose_mul_self (f g)) i) j
  · rw [key]
    have e : ∀ g, star (f g *ᵥ x) ⬝ᵥ (f g *ᵥ x) = ((∑ i, ‖(f g *ᵥ x) i‖ ^ 2 : ℝ) : ℂ) := fun g => by
      simp [dotProduct, Complex.conj_mul']
    simp only [e]
    rw [integral_complex_ofReal, Complex.zero_lt_real]
    have hc2 : Continuous fun g => ∑ i, ‖(f g *ᵥ x) i‖ ^ 2 :=
      continuous_finsetSum _ fun i _ => ((continuous_apply i).comp (hf.matrix_mulVec continuous_const)).norm.pow 2
    refine hc2.integral_pos_of_hasCompactSupport_nonneg_nonzero (HasCompactSupport.of_compactSpace _)
      (fun g => by positivity) (x := 1) ?_
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
    simp only [map_one, one_mulVec]
    exact (Finset.sum_pos' (fun _ _ => by positivity) ⟨i, Finset.mem_univ _, by
      have : x i ≠ 0 := hi
      positivity⟩).ne'
  · ext i j
    have e : ∀ Q : Matrix (Fin n) (Fin n) ℂ, Q i j = star (Pi.single i 1 : Fin n → ℂ) ⬝ᵥ Q *ᵥ Pi.single j 1 := fun Q => by
      simp [Pi.star_single]
    rw [e P, e ((f g)ᴴ * P * f g), ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, key, key]
    simp only [mulVec_mulVec, ← map_mul]
    exact integral_mul_right_eq_self (fun a => star (f a *ᵥ Pi.single i 1) ⬝ᵥ (f a *ᵥ Pi.single j 1)) g

theorem exists_isometry_conj {P D : Matrix (Fin n) (Fin n) ℂ} (hP : P.PosDef) (hD : Dᴴ = D) (hDD : D * D = 1) :
    ∃ R : GL (Fin n) ℂ, R.1ᴴ * D * R.1 = D ∧ ∀ s, sᴴ * P * s = P → sᴴ * D * s = D →
      (R.1 * s * (R⁻¹).1)ᴴ * (R.1 * s * (R⁻¹).1) = 1 := by
  have root : ∀ X : Matrix (Fin n) (Fin n) ℂ, 0 ≤ X → IsUnit X → ∃ B : GL (Fin n) ℂ, 0 ≤ B.1 ∧ B.1 * B.1 = X ∧ B.1ᴴ = B.1 ∧
      (B⁻¹).1ᴴ = (B⁻¹).1 := fun X h hu => by
    obtain ⟨B, hB⟩ := (CFC.isUnit_sqrt_iff X h).2 hu
    have h0 : 0 ≤ B.1 := hB ▸ CFC.sqrt_nonneg X
    have h1 : B.1ᴴ = B.1 := (Matrix.nonneg_iff_posSemidef.1 h0).1
    refine ⟨B, h0, hB ▸ CFC.sqrt_mul_sqrt_self X h, h1, ?_⟩
    refine (Units.mul_right_inj B).1 ?_
    have := congrArg conjTranspose B.inv_mul
    rw [conjTranspose_mul, h1, conjTranspose_one] at this
    rw [this, Units.mul_inv]
  have conj : ∀ X t : Matrix (Fin n) (Fin n) ℂ, 0 ≤ X → 0 ≤ tᴴ * X * t := fun X t h =>
    Matrix.nonneg_iff_posSemidef.2 ((Matrix.nonneg_iff_posSemidef.1 h).conjTranspose_mul_mul_same t)
  obtain ⟨B, -, hBB, hB, hBi⟩ := root P hP.posSemidef.nonneg hP.isUnit
  set H := (B⁻¹).1 * D * (B⁻¹).1 with hH
  have hHs : Hᴴ = H := by simp only [hH, conjTranspose_mul, hBi, hD, Matrix.mul_assoc]
  have hDu : IsUnit D := IsUnit.of_mul_eq_one _ hDD
  have hHu : IsUnit H := ((Units.isUnit _).mul hDu).mul (Units.isUnit _)
  set A := CFC.abs H with hA
  have hA0 : 0 ≤ A := CFC.abs_nonneg H
  have hAA : A * A = H * H := by rw [hA, CFC.abs_mul_abs, star_eq_conjTranspose, hHs]
  have hAH : A * H = H * A := (CFC.commute_abs_self H (IsSelfAdjoint.isStarNormal (show star H = H from hHs))).eq
  have hAu : IsUnit A := isUnit_of_mul_isUnit_left (hAA ▸ hHu.mul hHu)
  obtain ⟨R, hR0, hRR, hR, hRi⟩ := root (B.1 * A * B.1) (by simpa only [hB] using conj A B.1 hA0)
    (((Units.isUnit _).mul hAu).mul (Units.isUnit _))
  have hBH : B.1 * H * B.1 = D := by simp only [hH, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul,
    Units.inv_mul_cancel_right]
  have hHi : H * (B.1 * D * B.1) = 1 := by
    simp only [hH, Matrix.mul_assoc, Units.inv_mul_cancel_left]
    rw [← Matrix.mul_assoc D, hDD, Matrix.one_mul, Units.inv_mul]
  have hQ : B.1 * A * B.1 * D * (B.1 * A * B.1) = D := by
    have : A * (B.1 * D * B.1) * A = H := by
      refine hHu.mul_right_inj.1 ?_
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hAH, Matrix.mul_assoc A, hHi, Matrix.mul_one, hAA]
    conv_rhs => rw [← hBH, ← this]
    simp only [Matrix.mul_assoc]
  refine ⟨R, ?_, fun s hs hsD => ?_⟩
  · have h1 : D * R.1 * D = (R⁻¹).1 := by
      refine (CFC.mul_self_eq_mul_self_iff _ _ (by simpa only [hD] using conj R.1 D hR0) ?_).1 ?_
      · simpa only [hRi, Units.inv_mul, Matrix.one_mul] using conj R.1 (R⁻¹).1 hR0
      · refine (Units.mul_right_inj R).1 ((Units.mul_right_inj R).1 ?_)
        rw [← Matrix.mul_assoc R.1 R.1, hRR, Units.mul_inv_cancel_left, Units.mul_inv]
        calc _ = B.1 * A * B.1 * D * (R.1 * (D * D) * R.1) * D := by simp only [Matrix.mul_assoc]
          _ = 1 := by rw [hDD, Matrix.mul_one, hRR, hQ, hDD]
    rw [hR]
    calc R.1 * D * R.1 = R.1 * (D * R.1 * D) * D := by simp only [Matrix.mul_assoc, hDD, Matrix.mul_one]
      _ = D := by rw [h1, Units.mul_inv, Matrix.one_mul]
  · set t := B.1 * s * (B⁻¹).1 with ht
    have hc : ∀ X, tᴴ * X * t = (B⁻¹).1 * (sᴴ * (B.1 * X * B.1) * s) * (B⁻¹).1 := fun X => by
      simp only [ht, conjTranspose_mul, hB, hBi, Matrix.mul_assoc]
    have h1 : tᴴ * t = 1 := by
      have := hc 1
      rwa [Matrix.mul_one, Matrix.mul_one, hBB, hs, ← hBB, Units.inv_mul_cancel_left, Units.mul_inv] at this
    have h2 : tᴴ * H * t = H := by rw [hc, hBH, hsD]
    have h1' : t * tᴴ = 1 := mul_eq_one_comm.1 h1
    have sq : ∀ X, tᴴ * X * t * (tᴴ * X * t) = tᴴ * (X * X) * t := fun X => by
      calc _ = tᴴ * X * (t * tᴴ) * X * t := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [h1']; simp only [Matrix.mul_assoc, Matrix.one_mul]
    have h3 : tᴴ * A * t = A := (CFC.mul_self_eq_mul_self_iff _ _ (conj A t hA0) hA0).1 (by rw [sq, hAA, ← sq, h2])
    have h4 : sᴴ * (B.1 * A * B.1) * s = B.1 * A * B.1 := by
      conv_rhs => rw [← h3, hc]
      simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Units.inv_mul_cancel_right]
    calc _ = (R⁻¹).1 * (sᴴ * (R.1 * R.1) * s) * (R⁻¹).1 := by simp only [conjTranspose_mul, hR, hRi, Matrix.mul_assoc]
      _ = 1 := by rw [hRR, h4, ← hRR, Units.inv_mul_cancel_left, Units.mul_inv]

end Mat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem exists_conj_mem_stabArch (h : IsCMExt F E σ) {w : InfinitePlace F} {c : GL (Fin n) (w.Completion ⊗[F] E)}
    {ε : Fin n → Bool} (hε : Formalism.UG.cT (sigR _ σ) c.1 * JR w.Completion J * c.1 =
      Matrix.diagonal fun i => if ε i then 1 else -1) {K : Subgroup (GAd σ J)} (hK : IsCompact (K : Set (GAd σ J))) :
    ∃ a : GArch σ J w, ∀ k ∈ K, a * projArch σ J w k * a⁻¹ ∈ stabArch σ J w c := by
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  set D : Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E) := Matrix.diagonal fun i => if ε i then 1 else -1 with hD
  have hDD : D * D = 1 := by
    rw [hD, diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; split_ifs <;> simp
  have hcD : Formalism.UG.cT (sigR _ σ) D = D := by
    rw [hD, Formalism.UG.cT, diagonal_map (map_zero _), diagonal_transpose]
    congr 1; funext i; split_ifs <;> simp only [map_one, map_neg]
  let m : GAd σ J →* GL (Fin n) (w.Completion ⊗[F] E) :=
    (MulAut.conj c⁻¹).toMonoidHom.comp ((matHom _ σ J).comp (projArch σ J w))
  have hm : ∀ x, m x = c⁻¹ * matHom _ σ J (projArch σ J w x) * c := fun x => by simp [m]
  let f : GAd σ J →* Matrix (Fin n) (Fin n) ℂ := (infEmb τ).mapMatrix.toMonoidHom.comp ((Units.coeHom _).comp m)
  have hf : Continuous f := by
    have : IsTopologicalRing (w.Completion ⊗[F] E) := GlobalTheory.Doubling.isTopologicalRing_tens
    have e : f = fun x => ((c⁻¹).1 * (matHom _ σ J (projArch σ J w x)).1 * c.1).map (infEmb τ) :=
      funext fun x => congrArg (fun y : GL (Fin n) _ => y.1.map (infEmb τ)) (hm x)
    rw [e]
    exact ((continuous_const.matrix_mul (Units.continuous_val.comp ((isEmbedding_matHom _ σ J).continuous.comp
      (continuous_projArch σ J w)))).matrix_mul continuous_const).matrix_map (GlobalTheory.Orb.continuous_infEmb τ)
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  obtain ⟨P, hP, hPK⟩ := exists_invariant_posDef (f.comp K.subtype) (hf.comp continuous_subtype_val)
  have one : (1 : Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E)).map (infEmb τ) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  obtain ⟨R, hR, hRK⟩ := exists_isometry_conj (D := D.map (infEmb τ)) hP (by rw [← Frames.map_cT_sigR h, hcD])
    (by rw [← Matrix.map_mul, hDD, one])
  let e := RingEquiv.ofBijective _ (infEmb_bijective h τ)
  let r : GL (Fin n) (w.Completion ⊗[F] E) := Formalism.UG.bc e.symm.toRingHom R
  have h1 : r.1.map (infEmb τ) = R.1 := Matrix.ext fun i j => e.apply_symm_apply _
  have h2 : (r⁻¹).1.map (infEmb τ) = (R⁻¹).1 := by
    refine (Units.mul_right_inj R).1 ?_
    rw [Units.mul_inv, ← h1, ← Matrix.map_mul, Units.mul_inv, one]
  have inj := Matrix.map_injective (m := Fin n) (n := Fin n) (infEmb_bijective h τ).1
  have hr : c⁻¹ * (c * r * c⁻¹) * c = r := by group
  refine ⟨⟨c * r * c⁻¹, (conj_mem_UJ hε _).1 (hr.symm ▸ show Formalism.UG.cT _ r.1 * D * r.1 = D from inj ?_)⟩, fun k hk => ?_⟩
  · simp only [Matrix.map_mul, Frames.map_cT_sigR h, h1, hR]
  rw [mem_stabArch]
  change c⁻¹ * (c * r * c⁻¹ * matHom _ σ J (projArch σ J w k) * (c * r * c⁻¹)⁻¹) * c ∈ _
  rw [show ∀ x, c⁻¹ * (c * r * c⁻¹ * x * (c * r * c⁻¹)⁻¹) * c = r * (c⁻¹ * x * c) * r⁻¹ from fun x => by group, ← hm]
  change Formalism.UG.cT _ (r * m k * r⁻¹).1 * 1 * (r * m k * r⁻¹).1 = 1
  have h3 : Formalism.UG.cT (sigR _ σ) (m k).1 * D * (m k).1 = D := hm k ▸ (conj_mem_UJ hε _).2 (projArch σ J w k).2
  have h4 := congrArg (Matrix.map · (infEmb τ)) h3
  simp only [Matrix.map_mul, Frames.map_cT_sigR h] at h4
  refine inj ?_
  simp only [mul_one, Units.val_mul, Matrix.map_mul, Frames.map_cT_sigR h, h1, h2, one]
  exact hRK _ (hPK ⟨k, hk⟩) h4

theorem exists_conj_majCpt (h : IsCMExt F E σ) {c : ∀ w : InfinitePlace F, GL (Fin n) (w.Completion ⊗[F] E)}
    (hc : ∀ w, ∃ ε : Fin n → Bool, Formalism.UG.cT (sigR _ σ) (c w).1 * JR w.Completion J * (c w).1 =
      Matrix.diagonal fun i => if ε i then 1 else -1) {K : Subgroup (GAd σ J)} (hK : IsMaxCpt σ J K) :
    ∃ a ∈ infPts σ J, ∀ k, k ∈ K ↔ a * k * a⁻¹ ∈ majCpt σ J c := by
  choose x hx using fun w => (hc w).elim fun _ hε => exists_conj_mem_stabArch h hε hK.1.2
  let a := ofInf σ J (embArchPi σ J x)
  have ha : a ∈ infPts σ J := mem_infPts.2 (projFin_ofInf _ _ _)
  have hM := (isMaxCpt_majCpt h hc).1
  let K' : Subgroup (GAd σ J) := (majCpt σ J c).comap (MulAut.conj a).toMonoidHom
  have hK' : ∀ k, k ∈ K' ↔ a * k * a⁻¹ ∈ majCpt σ J c := fun k => Iff.rfl
  have hle : K ≤ K' := fun k hk => (hK' k).2 (mem_majCpt.2
    ⟨mul_mem (mul_mem ha (hK.1.1 hk)) (inv_mem ha), fun w => by simpa [a] using hx w k hk⟩)
  refine ⟨a, ha, fun k => ⟨fun hk => hle hk, fun hk => hK.2 (y := K') ⟨fun g hg => ?_, ?_⟩ hle hk⟩⟩
  · simpa [mul_assoc] using mul_mem (mul_mem (inv_mem ha) (hM.1 ((hK' g).1 hg))) ha
  · convert hM.2.image (f := fun g => a⁻¹ * g * a) (by fun_prop) using 1
    ext g
    exact ⟨fun hg => ⟨_, (hK' g).1 hg, by simp [mul_assoc]⟩, fun ⟨y, hy, e⟩ => (hK' g).2 (by simpa [← e, mul_assoc] using hy)⟩

theorem isMaxCpt_conj (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (K₁ K₂ : Subgroup (GAd σ J))
    (h₁ : IsMaxCpt σ J K₁) (h₂ : IsMaxCpt σ J K₂) : ∃ a ∈ infPts σ J, ∀ k, k ∈ K₂ ↔ a * k * a⁻¹ ∈ K₁ := by
  choose c ε hc using Frames.exists_arch_frame h hJ
  obtain ⟨a, ha, e⟩ := exists_conj_majCpt h (fun w => ⟨ε w, hc w⟩) h₁
  obtain ⟨b, hb, e'⟩ := exists_conj_majCpt h (fun w => ⟨ε w, hc w⟩) h₂
  refine ⟨a⁻¹ * b, mul_mem (inv_mem ha) hb, fun k => ?_⟩
  rw [e, e', show a * (a⁻¹ * b * k * (a⁻¹ * b)⁻¹) * a⁻¹ = b * k * b⁻¹ by group]

end GlobalTheory.MaxCptConj

end
