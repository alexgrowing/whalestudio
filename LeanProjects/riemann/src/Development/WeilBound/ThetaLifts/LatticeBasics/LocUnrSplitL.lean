import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegrandEqOnPiece
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocalFieldUniformizerNormProperties
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeneralLinearIntegralCompactOpen
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemIntegralGLIffIntegralUnitDet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeneralLinearUnimodularHaar
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IwasawaDecompositionUpperTriangular

open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL

namespace GlobalTheory.ThK.Dbl.Split

set_option hygiene false in
local notation "𝟙" => (1 : Matrix (Fin n) (Fin n) k)
set_option hygiene false in
local notation "𝟘" => (0 : Matrix (Fin n) (Fin n) k)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {O : Subring k} {ϖ : kˣ}
  {nrm : AbsoluteValue k ℝ} {q n : ℕ}

theorem zeta (h : LF O (ϖ : k) nrm q) {A : kˣ →* ℂ} (hA : ∀ u : kˣ, nrm u = 1 → A u = 1)
    (hb : ∀ i < n, ‖A ϖ‖ * (q : ℝ) ^ i < 1) (κ : Measure (GL (Fin n) k)) [hκ : κ.IsMulLeftInvariant]
    (h1 : κ (GLint O n : Set (GL (Fin n) k)) = 1) :
    IntegrableOn (fun g => A (GeneralLinearGroup.det g)) (Mint O n) κ ∧
      ∫ g in Mint O n, A (GeneralLinearGroup.det g) ∂κ = ∏ i ∈ Finset.range n, (1 - A ϖ * (q : ℂ) ^ i)⁻¹ := by
  classical
  have hq : (0 : ℝ) < q := by exact_mod_cast zero_lt_one.trans (GlobalTheory.CompanionTheory.QL.NormalisedValue.main h).1
  have hϖ : A ϖ ≠ 0 := left_ne_zero_of_mul_eq_one (b := A ϖ⁻¹) (by rw [← map_mul, mul_inv_cancel, map_one])
  let a : Fin n → ℝ := fun i => ((n : ℝ) - 1) / 2 - (i : ℕ)
  have e : ∀ i : Fin n, (q : ℝ) ^ a i * (q : ℝ) ^ (((n : ℝ) - 1) / 2 - 0) = (q : ℝ) ^ (n - 1 - i : ℕ) := fun i => by
    have := i.2
    rw [← Real.rpow_add hq, ← Real.rpow_natCast, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    congr 1; simp only [a]; push_cast; ring
  have := GlobalTheory.CompanionTheory.ZetaSph.zeta_spherical h (fun i x => if hx : x = 0 then 0 else A (Units.mk0 x hx) * (nrm x ^ (-a i) : ℝ))
    (fun i => A ϖ * ((q : ℝ) ^ a i : ℝ)) ⟨fun i => mul_ne_zero hϖ
      (by exact_mod_cast (Real.rpow_pos_of_pos hq _).ne'), fun i x m hx => ?_⟩ (fun g => A (GeneralLinearGroup.det g))
    (fun b hb κ hκ => ?_) κ hκ h1 0 fun i => ?_
  · simp only [Real.rpow_zero, Complex.ofReal_one, mul_one] at this
    refine ⟨this.1, this.2.trans ?_⟩
    rw [← Finset.prod_range_reflect, ← Fin.prod_univ_eq_prod_range fun i => (1 - A ϖ * (q : ℂ) ^ (n - 1 - i))⁻¹]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [mul_assoc, ← Complex.ofReal_mul, e]; simp
  · have h0 : x ≠ 0 := fun h0 => by rw [h0, map_zero] at hx; exact (zpow_pos hq _).ne hx
    have : A (Units.mk0 x h0 * (ϖ ^ m)⁻¹) = 1 := hA _ (by
      simp only [Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul, map_inv₀,
        map_zpow₀, hx, h.nrm_pi, _root_.inv_zpow', ne_eq]
      exact mul_inv_cancel₀ (zpow_pos hq _).ne')
    rw [map_mul, map_inv, map_zpow, mul_inv_eq_one₀ (zpow_ne_zero _ hϖ)] at this
    beta_reduce
    rw [dif_neg h0, this, mul_zpow, hx, ← Complex.ofReal_zpow, ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_mul hq.le,
      ← Real.rpow_mul hq.le]
    congr 3; push_cast; ring
  · have hd : b.1.det = ∏ i, b.1 i i := det_of_upperTriangular hb
    have h0 : ∀ i, b.1 i i ≠ 0 := fun i => Finset.prod_ne_zero_iff.1 (hd.symm.trans_ne b.det_ne_zero) i (Finset.mem_univ _)
    have : GeneralLinearGroup.det b = ∏ i, Units.mk0 _ (h0 i) := Units.ext (by simp [hd])
    beta_reduce
    rw [map_mul, map_mul, hA (GeneralLinearGroup.det κ) ((GlobalTheory.CompanionTheory.QLDet.mem_GLint_iff h n κ).1 hκ).2, mul_one, this, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [dif_neg (h0 i), mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add (nrm.pos (h0 i))]
    simp [a]
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hq.le _), mul_assoc, e]
    exact hb _ (by have := i.2; omega)

def IsGcd (O : Subring k) (g t : GL (Fin n) k) : Prop := ∀ a, a ∈ Mint O n ∧ g⁻¹ * a ∈ Mint O n ↔ t⁻¹ * a ∈ Mint O n

theorem doubling (h : LF O (ϖ : k) nrm q) {A B : kˣ →* ℂ} (hA : ∀ u : kˣ, nrm u = 1 → A u = 1)
    (hB : ∀ u : kˣ, nrm u = 1 → B u = 1) (bA : ∀ i < n, ‖A ϖ‖ * (q : ℝ) ^ i < 1) (bB : ∀ i < n, ‖B ϖ‖ * (q : ℝ) ^ i < 1)
    (bC : ∀ i < n, ‖(A * B) ϖ‖ * (q : ℝ) ^ i < 1) (μ : Measure (GL (Fin n) k)) [μ.IsHaarMeasure]
    (h1 : μ (GLint O n : Set (GL (Fin n) k)) = 1) {φ : GL (Fin n) k → ℂ}
    (hφ : ∀ g, ∃ t, IsGcd O g t ∧ φ g = B (GeneralLinearGroup.det g⁻¹) * (A * B) (GeneralLinearGroup.det t)) :
    Integrable φ μ ∧ (∫ g, φ g ∂μ) * ∏ i ∈ Finset.range n, (1 - (A * B) ϖ * (q : ℂ) ^ i)⁻¹ =
      (∏ i ∈ Finset.range n, (1 - A ϖ * (q : ℂ) ^ i)⁻¹) * ∏ i ∈ Finset.range n, (1 - B ϖ * (q : ℂ) ^ i)⁻¹ := by
  obtain ⟨-, -, _, _, _, hM, -⟩ := GlobalTheory.CompanionTheory.QLTop.gl_topology h n
  obtain ⟨-, _⟩ := (GlobalTheory.CompanionTheory.QL.HaarGL.exists_haar_unimodular h n).2 μ inferInstance
  obtain ⟨iA, zA⟩ := zeta h hA bA μ h1
  obtain ⟨iB, zB⟩ := zeta h hB bB μ h1
  obtain ⟨-, zC⟩ := zeta h (A := A * B) (fun u hu => by simp [hA u hu, hB u hu]) bC μ h1
  rw [← integral_indicator hM.measurableSet] at zA zB zC
  rw [← integrable_indicator_iff hM.measurableSet] at iA iB
  set a := (Mint O n).indicator fun g => A (GeneralLinearGroup.det g)
  set b := (Mint O n).indicator fun g => B (GeneralLinearGroup.det g)
  set Z := ∏ i ∈ Finset.range n, (1 - (A * B) ϖ * (q : ℂ) ^ i)⁻¹
  have hZ : Z ≠ 0 := Finset.prod_ne_zero_iff.2 fun i hi => inv_ne_zero (sub_ne_zero.2 fun e => by
    have := bC i (Finset.mem_range.1 hi)
    rw [← Complex.norm_natCast q, ← norm_pow, ← norm_mul, ← e, norm_one] at this
    exact this.false)
  have key : ∀ g, ∫ x, a x * b (g⁻¹ * x) ∂μ = φ g * Z := fun g => by
    obtain ⟨t, ht, e⟩ := hφ g
    rw [← zC, ← integral_mul_left_eq_self _ t, ← integral_const_mul]
    congr 1; ext x
    have := ht (t * x)
    rw [inv_mul_cancel_left] at this
    by_cases hx : x ∈ Mint O n
    · obtain ⟨h2, h3⟩ := this.2 hx
      simp only [a, b, Set.indicator_of_mem, hx, h2, h3, e, map_mul, MonoidHom.mul_apply]; ring
    · rw [Set.indicator_of_notMem hx, mul_zero]
      by_cases h2 : t * x ∈ Mint O n
      · rw [show b _ = 0 from Set.indicator_of_notMem (fun h3 => hx (this.1 ⟨h2, h3⟩)) _, mul_zero]
      · rw [show a _ = 0 from Set.indicator_of_notMem h2 _, zero_mul]
  let e : GL (Fin n) k × GL (Fin n) k ≃ᵐ GL (Fin n) k × GL (Fin n) k := MeasurableEquiv.shearMulRight _
  have he : MeasurePreserving e (μ.prod μ) (μ.prod μ) := measurePreserving_prod_mul μ μ
  let H : GL (Fin n) k × GL (Fin n) k → ℂ := fun z => a z.1 * b (z.2⁻¹ * z.1)
  have hH : H ∘ e = fun z => a z.1 * b z.2⁻¹ := by ext z; simp [H, e, MeasurableEquiv.shearMulRight]
  have iH : Integrable H (μ.prod μ) :=
    (he.integrable_comp_emb e.measurableEmbedding).1 (hH ▸ iA.mul_prod iB.comp_inv)
  have i2 : Integrable (fun g => φ g * Z) μ := by simpa only [H, key] using iH.integral_prod_right
  refine ⟨(integrable_mul_const_iff hZ.isUnit _).1 i2, ?_⟩
  rw [← integral_mul_const, ← zA, ← zB, ← integral_inv_eq_self b, ← integral_prod_mul, ← hH]
  refine Eq.trans ?_ (he.integral_comp' H).symm
  rw [integral_prod_symm _ iH]
  simp only [H, key]

theorem exists_frame (h : LF O (ϖ : k) nrm q) (g : GL (Fin n) k) : ∃ (t : GL (Fin n) k) (κ : GL (Fin n ⊕ Fin n) k),
    (∀ i j, κ.1 i j ∈ O) ∧ (∀ i j, (κ⁻¹).1 i j ∈ O) ∧ IsGcd O g t ∧
      (κ⁻¹).1 * fromRows 𝟙 𝟙 = fromRows ((g⁻¹).1 * t.1) t.1 := by
  let r := (reindexAlgEquiv k k (finSumFinEquiv (m := n) (n := n))).toMulEquiv
  let N : GL (Fin n ⊕ Fin n) k := ⟨fromBlocks g.1 0 (-g.1) 1, fromBlocks (g⁻¹).1 0 1 1,
    by simp [fromBlocks_multiply], by simp [fromBlocks_multiply]⟩
  obtain ⟨b', hb, κ', hκ, e⟩ := GlobalTheory.CompanionTheory.QL.Iwasawa.exists_upper_mul_int h _ (Units.mapEquiv r N)
  let b := (Units.mapEquiv r).symm b'
  let c := (Units.mapEquiv r).symm κ'
  have e' : N = b * c := by rw [← map_mul, ← e, MulEquiv.symm_apply_apply]
  have c1 : ∀ i j, c.1 i j ∈ O := fun i j => hκ.1 _ _
  have c2 : ∀ i j, (c⁻¹).1 i j ∈ O := fun i j => hκ.2 _ _
  have b0 : b.1.toBlocks₂₁ = 0 := Matrix.ext fun i j => hb (show finSumFinEquiv (.inl j) < finSumFinEquiv (.inr i) by
    simp [Fin.lt_def]; omega)
  have bb : b.1 = fromBlocks b.1.toBlocks₁₁ b.1.toBlocks₁₂ 0 b.1.toBlocks₂₂ := by rw [← b0, fromBlocks_toBlocks]
  have ht : b.1.toBlocks₁₁.det ≠ 0 := left_ne_zero_of_mul (b := b.1.toBlocks₂₂.det) (by rw [← det_fromBlocks_zero₂₁, ← bb]; exact GeneralLinearGroup.det_ne_zero b)
  let t : GL (Fin n) k := GeneralLinearGroup.mkOfDetNeZero _ ht
  have key : (c⁻¹).1 * fromRows 𝟙 𝟘 = fromRows ((g⁻¹).1 * t.1) t.1 := by
    rw [show c⁻¹ = N⁻¹ * b by rw [e']; group, Units.val_mul, Matrix.mul_assoc, bb, fromBlocks_mul_fromRows]
    exact (fromBlocks_mul_fromRows _ _ _ _ _ _).trans (by simp; rfl)
  let C : GL (Fin n ⊕ Fin n) k := ⟨fromBlocks 1 0 1 1, fromBlocks 1 0 (-1) 1,
    by simp [fromBlocks_multiply], by simp [fromBlocks_multiply]⟩
  have o : ∀ i j : Fin n, (1 : Matrix (Fin n) (Fin n) k) i j ∈ O := fun i j => by
    rw [one_apply]; split_ifs; exacts [O.one_mem, O.zero_mem]
  have mul : ∀ {α β γ : Type} [Fintype β] (x : Matrix α β k) (y : Matrix β γ k), (∀ i j, x i j ∈ O) → (∀ i j, y i j ∈ O) →
      ∀ i j, (x * y) i j ∈ O := fun x y hx hy i j => O.sum_mem fun l _ => O.mul_mem (hx i l) (hy l j)
  refine ⟨t, C * c, mul _ _ ?_ c1, ?_, fun a => ?_, ?_⟩
  · rintro (i | i) (j | j); exacts [o i j, O.zero_mem, o i j, o i j]
  · rw [_root_.mul_inv_rev]
    refine mul _ _ c2 ?_
    rintro (i | i) (j | j); exacts [o i j, O.zero_mem, O.neg_mem (o i j), o i j]
  · have k2 : (c⁻¹).1 * fromRows (t⁻¹ * a).1 𝟘 = fromRows (g⁻¹ * a).1 a.1 := by
      have := congrArg (· * (t⁻¹ * a).1) key
      simpa only [Matrix.mul_assoc, fromRows_mul, Matrix.one_mul, Matrix.zero_mul, Units.val_mul,
        Units.mul_inv_cancel_left] using this
    refine ⟨fun ⟨h1, h2⟩ i j => ?_, fun h1 => ?_⟩
    · have := mul c.1 (fromRows (g⁻¹ * a).1 a.1) c1 (by rintro (i | i) j; exacts [h2 i j, h1 i j]) (.inl i) j
      rwa [← k2, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul] at this
    · have := mul _ (fromRows (t⁻¹ * a).1 𝟘) c2 (by rintro (i | i) j; exacts [h1 i j, O.zero_mem])
      rw [k2] at this
      exact ⟨fun i j => this (.inr i) j, fun i j => this (.inl i) j⟩
  · rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, ← key]
    congr 1
    exact (fromBlocks_mul_fromRows _ _ _ _ _ _).trans (by simp)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem exists_dual (J : GL (Fin n) k) {p J₂ : GL (Fin n ⊕ Fin n) k} (hJ : J₂.1 = fromBlocks J.1 0 0 (-J.1)) {t : GL (Fin n) k}
    (h : p.1 * fromRows 𝟙 𝟙 = fromRows 𝟙 𝟙 * t.1) : ∃ t' : GL (Fin n) k,
      (J₂⁻¹).1 * (p⁻¹).1ᵀ * J₂.1 * fromRows 𝟙 𝟙 = fromRows 𝟙 𝟙 * t'.1 ∧
        GeneralLinearGroup.det t' = GeneralLinearGroup.det t * (GeneralLinearGroup.det p)⁻¹ := by
  obtain ⟨A, B, C, D, e⟩ : ∃ A B C D, p.1 = fromBlocks A B C D := ⟨_, _, _, _, (fromBlocks_toBlocks _).symm⟩
  rw [e, fromBlocks_mul_fromRows, fromRows_mul] at h
  simp only [Matrix.mul_one, Matrix.one_mul, fromRows_ext_iff] at h
  have hA : A = t.1 - B := eq_sub_of_add_eq h.1
  have hC : C = t.1 - D := eq_sub_of_add_eq h.2
  have d : p.1.det = t.1.det * (D - B).det := by
    have : p.1 * fromBlocks 𝟙 𝟘 𝟙 𝟙 = fromBlocks 𝟙 𝟘 𝟙 𝟙 * fromBlocks t.1 B 0 (D - B) := by
      simp [e, fromBlocks_multiply, hA, hC]
    simpa [det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂] using congrArg det this
  have hs : (D - B)ᵀ.det ≠ 0 := by
    rw [det_transpose]; exact right_ne_zero_of_mul (d.symm.trans_ne (GeneralLinearGroup.det_ne_zero p))
  let s := GeneralLinearGroup.mkOfDetNeZero _ hs
  have k1 : p.1ᵀ * fromRows 𝟙 (-𝟙) = fromRows 𝟙 (-𝟙) * s.1 := by
    rw [e, fromBlocks_transpose, fromBlocks_mul_fromRows, fromRows_mul, hA, hC]
    change _ = fromRows (𝟙 * (D - B)ᵀ) (-𝟙 * (D - B)ᵀ)
    congr 1 <;> simp [transpose_sub] <;> abel
  have k2 : (p⁻¹).1ᵀ * fromRows 𝟙 (-𝟙) = fromRows 𝟙 (-𝟙) * (s⁻¹).1 := by
    have := congrArg (fun x => (p⁻¹).1ᵀ * x * (s⁻¹).1) k1
    simp only [← Matrix.mul_assoc, ← transpose_mul, Units.mul_inv, transpose_one, Matrix.one_mul] at this
    rw [this, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have k3 : J₂.1 * fromRows 𝟙 𝟙 = fromRows 𝟙 (-𝟙) * J.1 := by rw [hJ, fromBlocks_mul_fromRows, fromRows_mul]; simp
  refine ⟨J⁻¹ * s⁻¹ * J, ?_, Units.ext ?_⟩
  · rw [Matrix.mul_assoc, k3, ← Matrix.mul_assoc, Matrix.mul_assoc (J₂⁻¹).1, k2, Units.val_mul, Units.val_mul,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    congr 2
    have := congrArg (fun x => (J₂⁻¹).1 * x * (J⁻¹).1) k3
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at this
    rw [this, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  · have := GeneralLinearGroup.det_ne_zero t
    have := GeneralLinearGroup.det_ne_zero J
    rw [det_transpose] at hs
    simp only [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, GeneralLinearGroup.val_det_apply, d]
    rw [show s.1.det = (D - B).det from det_transpose _]
    field_simp

end GlobalTheory.ThK.Dbl.Split
