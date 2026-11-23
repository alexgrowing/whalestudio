import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualTr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeEqOfRealUnitaryConj
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LandherrStOfHasseNormSt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension

noncomputable section

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ENNReal Matrix nonZeroDivisors

namespace GlobalTheory.EqCovol.Transport

open GlobalTheory.CovolConj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

section Frames

variable {Ψ : Finset (E →+* ℂ)} {G G' : Matrix (Fin r) (Fin r) E} {u : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ}

omit [IsCMField E] [NumberField E] in
theorem gram_mul' {τ : E →+* ℂ} {v : Matrix (Fin r) (Fin r) ℂ}
    (hu : gram τ G' v = G.map τ) (x : Matrix (Fin r) (Fin r) ℂ) : gram τ G' (v * x) = gram τ G x := by
  rw [CovolConj.gram_eq] at hu
  rw [CovolConj.gram_eq, CovolConj.gram_eq, Matrix.transpose_mul, Matrix.map_mul, ← hu]
  simp only [Matrix.mul_assoc]

omit [IsCMField E] [NumberField E] in
theorem det_ne' {τ : E →+* ℂ} (hG : G.det ≠ 0)
    {v : Matrix (Fin r) (Fin r) ℂ} (hu : gram τ G' v = G.map τ) : v.det ≠ 0 := by
  intro h
  rw [CovolConj.gram_eq] at hu
  have h2 := congrArg Matrix.det hu
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h, zero_mul, zero_mul] at h2
  have h3 : τ G.det = (G.map τ).det := RingHom.map_det τ G
  exact hG ((map_eq_zero τ).1 (h3.trans h2.symm))

omit [IsCMField E] [NumberField E] in
theorem dmin_umul (hu : ∀ τ ∈ Ψ, gram τ G' (u τ) = G.map τ) (x : Frame Ψ r) (τ : Ψ) (i : Fin (r + 1)) :
    dmin G' (umul u x) τ i = dmin G x τ i :=
  congrArg (fun M => lminor M i) (gram_mul' (hu τ.1 τ.2) (mat x τ))

omit [IsCMField E] [NumberField E] in
theorem umul_mem_GG (hG : G.det ≠ 0) (hu : ∀ τ ∈ Ψ, gram τ G' (u τ) = G.map τ) (p : ℕ) (x : Frame Ψ r) :
    umul u x ∈ GG Ψ G' p ↔ x ∈ GG Ψ G p := by
  refine forall_congr' fun τ => and_congr ?_ ?_
  · have : mat (umul u x) τ = u τ.1 * mat x τ := rfl
    rw [this, Matrix.det_mul]
    exact ⟨right_ne_zero_of_mul, mul_ne_zero (det_ne' hG (hu τ.1 τ.2))⟩
  · simp only [dmin_umul hu]

omit [IsCMField E] [NumberField E] in
theorem umul_inj' (hG : G.det ≠ 0) (hu : ∀ τ ∈ Ψ, gram τ G' (u τ) = G.map τ) {x y : Frame Ψ r}
    (h : umul u x = umul u y) : x = y := by
  funext τ
  have h1 : u τ.1 * mat x τ = u τ.1 * mat y τ := congrFun h τ
  have hd : IsUnit (u τ.1).det := isUnit_iff_ne_zero.mpr (det_ne' hG (hu τ.1 τ.2))
  have := congrArg (fun M => (u τ.1)⁻¹ * M) h1
  simp only [Matrix.nonsing_inv_mul_cancel_left _ _ hd] at this
  exact this

omit [IsCMField E] [NumberField E] in
theorem umul_surj (hG : G.det ≠ 0) (hu : ∀ τ ∈ Ψ, gram τ G' (u τ) = G.map τ) (x : Frame Ψ r) :
    ∃ y, x = umul u y := by
  refine ⟨umul (fun τ => (u τ)⁻¹) x, funext fun τ => ?_⟩
  have hd : IsUnit (u τ.1).det := isUnit_iff_ne_zero.mpr (det_ne' hG (hu τ.1 τ.2))
  exact (Matrix.mul_nonsing_inv_cancel_left _ (mat x τ) hd).symm

omit [IsCMField E] [NumberField E] in
theorem umul_lact' {γ γ' : GL (Fin r) E}
    (h : ∀ τ ∈ Ψ, u τ * (γ : Matrix (Fin r) (Fin r) E).map τ =
      (γ' : Matrix (Fin r) (Fin r) E).map τ * u τ) (x : Frame Ψ r) :
    umul u (lact γ x) = lact γ' (umul u x) := by
  funext τ
  show u τ.1 * ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) =
    (γ' : Matrix (Fin r) (Fin r) E).map τ.1 * (u τ.1 * mat x τ)
  rw [← Matrix.mul_assoc, h τ.1 τ.2, Matrix.mul_assoc]

end Frames

def ratio (X Y : Data E r) : E := X.κ0 / Y.κ0

theorem cc_κ (X : Data E r) : cc X.κ0 = -X.κ0 := by
  have h := X.ξ0_im
  unfold cc at h ⊢
  rcases X.κ0_xi with e | e <;> simp [e, h, map_ofNat]

theorem κ_ne (X : Data E r) : X.κ0 ≠ 0 := by
  have h := X.ξ0_ne
  rcases X.κ0_xi with e | e <;> simp [e, h]

theorem ratio_ne (X Y : Data E r) : ratio X Y ≠ 0 := div_ne_zero (κ_ne X) (κ_ne Y)

theorem cc_ratio (X Y : Data E r) : cc (ratio X Y) = ratio X Y := by
  have h := cc_κ X
  have h' := cc_κ Y
  unfold cc at h h' ⊢
  rw [ratio, map_div₀, h, h', neg_div_neg_eq]

theorem ξ_mul_ratio (X Y : Data E r) : Y.ξ0 * ratio X Y = X.ξ0 ∨ Y.ξ0 * ratio X Y = -X.ξ0 := by
  have h := Y.ξ0_ne
  unfold ratio
  rcases X.κ0_xi with e | e <;> rcases Y.κ0_xi with e' | e' <;> rw [e, e']
  · left; field_simp
  · right; field_simp
  · right; field_simp
  · left; field_simp

theorem re_κ (X : Data E r) (τ : E →+* ℂ) : (τ X.κ0).re = 0 := by
  have h := IsCMField.complexEmbedding_complexConj E τ X.κ0
  have h' := cc_κ X
  unfold cc at h'
  rw [h', map_neg] at h
  have := congrArg Complex.re h
  simp at this
  linarith

theorem exists_sq (X Y : Data E r) (hΨ : X.Ψ = Y.Ψ) {τ : E →+* ℂ} (hτ : τ ∈ X.Ψ) :
    ∃ t : ℝ, t ≠ 0 ∧ (t : ℂ) * t * τ (ratio X Y) = 1 := by
  have h1 := X.κ0_sign ⟨τ, hτ⟩
  have h2 := Y.κ0_sign ⟨τ, hΨ ▸ hτ⟩
  dsimp only at h1 h2
  have e1 : τ X.κ0 = (τ X.κ0).im * Complex.I := by
    apply Complex.ext <;> simp [re_κ]
  have e2 : τ Y.κ0 = (τ Y.κ0).im * Complex.I := by
    apply Complex.ext <;> simp [re_κ]
  have hp : 0 < (τ Y.κ0).im / (τ X.κ0).im := div_pos_of_neg_of_neg h2 h1
  refine ⟨Real.sqrt ((τ Y.κ0).im / (τ X.κ0).im), (Real.sqrt_pos.2 hp).ne', ?_⟩
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt hp.le, ratio, map_div₀]
  have n1 : ((τ X.κ0).im : ℂ) ≠ 0 := by exact_mod_cast h1.ne
  have n2 : ((τ Y.κ0).im : ℂ) ≠ 0 := by exact_mod_cast h2.ne
  generalize (τ X.κ0).im = a at *
  generalize (τ Y.κ0).im = b at *
  rw [e1, e2]
  push_cast
  field_simp

omit [IsCMField E] [NumberField E] in
theorem gram_smul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (c : E) (t : ℝ) (Q : Matrix (Fin r) (Fin r) ℂ) :
    gram τ (c • G) ((t : ℂ) • Q) = ((t : ℂ) * t * τ c) • gram τ G Q := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem herm_smul (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    herm (c • G) x y = c * herm G x y := by
  simp only [herm, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem trace_ratio (X Y : Data E r) (a : E) :
    (∃ n : ℤ, Algebra.trace ℚ E (-Y.ξ0 * (ratio X Y * a)) = n) ↔ ∃ n : ℤ, Algebra.trace ℚ E (-X.ξ0 * a) = n := by
  rcases ξ_mul_ratio X Y with e | e
  · rw [← e]; ring_nf
  · have : -Y.ξ0 * (ratio X Y * a) = -(-X.ξ0 * a) := by linear_combination (-a) * e
    rw [this, map_neg]
    exact ⟨fun ⟨n, h⟩ => ⟨-n, by push_cast; linarith⟩, fun ⟨n, h⟩ => ⟨-n, by push_cast; linarith⟩⟩

theorem exists_similitude (H : Host E) (X Y : Data E r) (hΨ : X.Ψ = Y.Ψ) (hp : X.p0 = Y.p0)
    (hX : IsSelfDualTr X) (hY : IsSelfDualTr Y) :
    ∃ P : GL (Fin r) E, ratio X Y • X.Gm = P.1ᵀ * Y.Gm * P.1.map cc := by
  haveI := H.unram
  have hb := inv_ne_zero (mul_ne_zero
    ((FractionalIdeal.spanSingleton_ne_zero_iff (R := 𝓞 E) (P := E)).2 Y.ξ0_ne) (coe_different_ne_zero (E := E)))
  obtain ⟨P, hP0, hP⟩ := GlobalTheory.SelfDualGenus.congr_of_modular (G := Y.Gm) (G' := ratio X Y • X.Gm)
    (L := Y.Λ) (L' := X.Λ) (GlobalTheory.LocalQuad.landherr_of_hasseNormSt GlobalTheory.QNorm.hasseNormSt) GlobalTheory.QNorm.hasseNormSt hb
    (GlobalTheory.SelfDualGenus.cc_mem_inv_mul_different Y.ξ0_im) Y.Gm_herm
    (fun a b => by
      have h1 := cc_ratio X Y
      have h2 := X.Gm_herm a b
      unfold cc at h1 h2 ⊢
      simp only [Matrix.smul_apply, smul_eq_mul, map_mul, h1, h2])
    Y.Gm_det
    (by rw [Matrix.det_smul]; exact mul_ne_zero (pow_ne_zero _ (ratio_ne X Y)) X.Gm_det)
    ⟨Y.Λ_fg, Y.Λ_span⟩ ⟨X.Λ_fg, X.Λ_span⟩
    (fun x => by
      rw [← mem_smul_hermDual_iff hb, ← traceFormDual_eq Y.ξ0_ne]
      exact hY x)
    (fun x => by
      rw [← mem_smul_hermDual_iff hb, ← traceFormDual_eq Y.ξ0_ne, mem_traceFormDual]
      simp only [EFf, herm_smul, trace_ratio]
      exact hX x)
    (GlobalTheory.Published.Landherr.congr_of_signature (X.Ψ : Set (E →+* ℂ))
      (fun τ => by
        by_cases h : ComplexEmbedding.conjugate τ ∈ X.Ψ
        · exact Or.inr h
        · exact Or.inl ((X.cmType τ).2 h))
      fun τ hτ => ⟨X.p0, by rw [hp]; exact Y.signature ⟨τ, hΨ ▸ hτ⟩, by
        obtain ⟨Q, hQ, e⟩ := X.signature ⟨τ, hτ⟩
        obtain ⟨t, ht, h⟩ := exists_sq X Y hΨ hτ
        refine ⟨(t : ℂ) • Q, ?_, ?_⟩
        · rw [Matrix.det_smul]
          exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast ht)) hQ
        · rw [gram_smul, h, one_smul]; exact e⟩)
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero P hP0, hP⟩

def latMap (P : GL (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) : Submodule (𝓞 E) (Fin r → E) :=
  Λ.map ((Matrix.mulVecLin P.1).restrictScalars (𝓞 E))

omit [IsCMField E] [NumberField E] in
theorem mulVec_inj (P : GL (Fin r) E) {x y : Fin r → E} (h : P.1 *ᵥ x = P.1 *ᵥ y) : x = y := by
  have := congrArg (fun v => (P⁻¹).1 *ᵥ v) h
  simpa only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] using this

omit [IsCMField E] [NumberField E] in
theorem mulVec_surj (P : GL (Fin r) E) : Function.Surjective fun x : Fin r → E => P.1 *ᵥ x := fun x =>
  ⟨(P⁻¹).1 *ᵥ x, by simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]⟩

omit [IsCMField E] [NumberField E] in
theorem mem_latMap (P : GL (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (x : Fin r → E) :
    P.1 *ᵥ x ∈ latMap P Λ ↔ x ∈ Λ :=
  ⟨fun ⟨_, hy, e⟩ => mulVec_inj P e ▸ hy, fun h => ⟨x, h, rfl⟩⟩

omit [IsCMField E] [NumberField E] in
theorem latMap_smul (P : GL (Fin r) E) (I : Ideal (𝓞 E)) (Λ : Submodule (𝓞 E) (Fin r → E)) :
    I • latMap P Λ = latMap P (I • Λ) := (Submodule.map_smul'' _ _ _).symm

omit [IsCMField E] [NumberField E] in
theorem conj_mulVec (P γ : GL (Fin r) E) (x : Fin r → E) :
    γ.1 *ᵥ (P.1 *ᵥ x) = P.1 *ᵥ ((P⁻¹ * γ * P).1 *ᵥ x) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
  congr 2
  group

omit [IsCMField E] [NumberField E] in
theorem cong_iff (P γ : GL (Fin r) E) (Λ Λ' : Submodule (𝓞 E) (Fin r → E)) (n : ℕ) :
    (∀ x ∈ latMap P Λ', ∃ y ∈ latMap P Λ, γ.1 *ᵥ x - x = n • y) ↔
      ∀ x ∈ Λ', ∃ y ∈ Λ, (P⁻¹ * γ * P).1 *ᵥ x - x = n • y := by
  rw [(mulVec_surj P).forall]
  refine forall_congr' fun x => imp_congr (mem_latMap P _ x) ?_
  rw [(mulVec_surj P).exists]
  refine exists_congr fun y => and_congr (mem_latMap P _ y) ?_
  rw [conj_mulVec, ← Matrix.mulVec_sub, ← Matrix.mulVec_smul]
  exact ⟨mulVec_inj P, fun h => by rw [h]⟩

section Move

variable (X Y : Data E r) (P : GL (Fin r) E) (hP : ratio X Y • X.Gm = P.1ᵀ * Y.Gm * P.1.map cc)

include hP in
theorem herm_P (x y : Fin r → E) : herm Y.Gm (P.1 *ᵥ x) (P.1 *ᵥ y) = ratio X Y * herm X.Gm x y := by
  rw [GlobalTheory.SelfDualGenus.herm_mulVec, ← hP, herm_smul]

include hP in
theorem isUStab_iff (γ : GL (Fin r) E) :
    IsUStab Y.Gm (latMap P X.Λ) γ ↔ IsUStab X.Gm X.Λ (P⁻¹ * γ * P) := by
  refine and_congr ?_ ?_
  · rw [(mulVec_surj P).forall]
    refine forall_congr' fun x => ?_
    rw [(mulVec_surj P).forall]
    refine forall_congr' fun y => ?_
    rw [conj_mulVec P γ x, conj_mulVec P γ y, herm_P X Y P hP, herm_P X Y P hP, mul_right_inj' (ratio_ne X Y)]
  · rw [(mulVec_surj P).forall]
    refine forall_congr' fun x => ?_
    rw [conj_mulVec, mem_latMap, mem_latMap]

include hP in

theorem exists_isom (hΨ : X.Ψ = Y.Ψ) : ∃ u : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ,
    (∀ τ ∈ X.Ψ, gram τ Y.Gm (u τ) = X.Gm.map τ) ∧
    ∀ γ : GL (Fin r) E, ∀ τ ∈ X.Ψ, u τ * (P⁻¹ * γ * P).1.map τ = γ.1.map τ * u τ := by
  choose! t ht using fun τ (hτ : τ ∈ X.Ψ) => exists_sq X Y hΨ hτ
  refine ⟨fun τ => (t τ : ℂ) • P.1.map τ, fun τ hτ => ?_, fun γ τ _ => ?_⟩
  · have h1 := gram_smul τ Y.Gm 1 (t τ) (P.1.map τ)
    have h2 : (P.1.map τ).map (starRingEnd ℂ) = (P.1.map cc).map τ := by
      ext a b
      exact (IsCMField.complexEmbedding_complexConj E τ _).symm
    rw [one_smul, map_one, mul_one] at h1
    rw [h1, CovolConj.gram_eq, h2, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, ← hP]
    ext a b
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul]
    rw [← mul_assoc, (ht τ hτ).2, one_mul]
  · rw [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.map_mul, ← Matrix.map_mul, ← Units.val_mul, ← Units.val_mul]
    congr 3
    group

include hP in
theorem transv_conj (ξ : Fin r → E) (α : E) :
    transvMat Y.Gm (P.1 *ᵥ ξ) α * P.1 = P.1 * transvMat X.Gm ξ (α * ratio X Y) := by
  have key : ∀ (G : Matrix (Fin r) (Fin r) E) (ξ x : Fin r → E) (α : E),
      transvMat G ξ α *ᵥ x = x + (α * herm G x ξ) • ξ := by
    intro G ξ x α
    funext a
    simp only [transvMat, herm, Matrix.mulVec, dotProduct, Matrix.of_apply, add_mul, Finset.sum_add_distrib,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  refine Matrix.toLin'.injective (LinearMap.ext fun x => ?_)
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, key, key,
    herm_P X Y P hP, Matrix.mulVec_add, Matrix.mulVec_smul, mul_assoc]

theorem exists_den : ∃ d : 𝓞 E, d ≠ 0 ∧
    ∀ x ∈ X.Λ, ∀ y ∈ X.Λ, IsIntegral ℤ ((d : E) * (ratio X Y * herm X.Gm x y)) := by
  obtain ⟨a, b, hb, e⟩ := IsFractionRing.div_surjective (A := 𝓞 E) (ratio X Y)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbE : algebraMap (𝓞 E) E b ≠ 0 := by simpa using hb0
  refine ⟨b * X.den, mul_ne_zero hb0 X.den_ne, fun x hx y hy => ?_⟩
  have : ((b * X.den : 𝓞 E) : E) * (ratio X Y * herm X.Gm x y) =
      algebraMap (𝓞 E) E a * ((X.den : E) * herm X.Gm x y) := by
    rw [← e]
    show algebraMap (𝓞 E) E (b * X.den) * _ = _ * (algebraMap (𝓞 E) E X.den * _)
    rw [map_mul]
    field_simp
  rw [this]
  exact a.isIntegral_coe.mul (X.Λ_int x hx y hy)

variable (hΨ : X.Ψ = Y.Ψ) (hp : X.p0 = Y.p0)

def move : Data E r where
  Ψ := X.Ψ
  cmType := X.cmType
  Gm := Y.Gm
  Gm_herm := Y.Gm_herm
  Gm_det := Y.Gm_det
  p0 := X.p0
  p0_le := X.p0_le
  signature τ := by rw [hp]; exact Y.signature ⟨τ.1, hΨ ▸ τ.2⟩
  Λ := latMap P X.Λ
  Λ_fg := X.Λ_fg.map _
  Λ_span := by
    have : (latMap P X.Λ : Set (Fin r → E)) = Matrix.mulVecLin P.1 '' (X.Λ : Set (Fin r → E)) := rfl
    rw [this, Submodule.span_image, X.Λ_span, Submodule.map_top, LinearMap.range_eq_top]
    exact mulVec_surj P
  den := (exists_den X Y).choose
  den_ne := (exists_den X Y).choose_spec.1
  Λ_int := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have := (exists_den X Y).choose_spec.2 x hx y hy
    rwa [← herm_P X Y P hP] at this
  Γ := X.Γ.comap (MulAut.conj P).symm.toMonoidHom
  Γ_stab γ hγ := (isUStab_iff X Y P hP γ).2 (X.Γ_stab _ hγ)
  Γ_index := by
    classical
    obtain ⟨S, hS⟩ := X.Γ_index
    refine ⟨S.image fun s => P * s * P⁻¹, fun γ hγ => ?_⟩
    obtain ⟨s, hs, h⟩ := hS _ ((isUStab_iff X Y P hP γ).1 hγ)
    refine ⟨_, Finset.mem_image_of_mem _ hs, ?_⟩
    show P⁻¹ * _ * P ∈ X.Γ
    convert h using 1
    group
  Γ_free γ hγ x hx b hb h := by
    obtain ⟨u, hu, hc⟩ := exists_isom X Y P hP hΨ
    obtain ⟨y, rfl⟩ := umul_surj X.Gm_det hu x
    rw [← umul_rmul, ← umul_lact' (hc γ)] at h
    have := X.Γ_free _ hγ y ((umul_mem_GG X.Gm_det hu _ y).1 hx) b hb (umul_inj' X.Gm_det hu h)
    have h2 : P⁻¹ * γ * P = 1 := this
    calc γ = P * (P⁻¹ * γ * P) * P⁻¹ := by group
      _ = 1 := by rw [h2]; group
  χ _ _ := 1
  χ_mul := by simp
  χ_add := by simp
  χ_fin _ := ⟨1, one_pos, by simp⟩
  ξ0 := Y.ξ0
  ξ0_im := Y.ξ0_im
  ξ0_ne := Y.ξ0_ne
  κ0 := Y.κ0
  κ0_xi := Y.κ0_xi
  κ0_sign τ := Y.κ0_sign ⟨τ.1, hΨ ▸ τ.2⟩
  m := X.m
  m_pos := X.m_pos
  transv := by
    rintro _ ⟨ξ, hξ, rfl⟩ h0 s hs hi
    change herm Y.Gm (P.1 *ᵥ ξ) (P.1 *ᵥ ξ) = 0 at h0
    rw [herm_P X Y P hP, mul_eq_zero, or_iff_right (ratio_ne X Y)] at h0
    obtain ⟨γ, hγ, e⟩ := X.transv ξ hξ h0 s hs hi
    refine ⟨P * γ * P⁻¹, ?_, ?_⟩
    · show P⁻¹ * _ * P ∈ X.Γ
      convert hγ using 1
      group
    · have h1 := transv_conj X Y P hP ξ ((X.m : E) * s * Y.κ0)
      rw [mul_assoc _ Y.κ0, ratio, mul_div_cancel₀ _ (κ_ne Y), ← e] at h1
      rw [Units.val_mul, Units.val_mul, ← h1, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      rfl

theorem mem_move (γ : GL (Fin r) E) : γ ∈ (move X Y P hP hΨ hp).Γ ↔ P⁻¹ * γ * P ∈ X.Γ := Iff.rfl

theorem isLevGrp_move {H : Host E} (l : Level H) (h : IsLevGrp l X) : IsLevGrp l (move X Y P hP hΨ hp) := by
  intro γ
  rw [mem_move, h]
  refine and_congr (isUStab_iff X Y P hP γ).symm (and_congr ?_ (cong_iff P γ _ _ _).symm)
  refine (cong_iff P γ _ _ _).symm.trans ?_
  rw [← latMap_smul]
  rfl

theorem isSelfDualTr_move (h : IsSelfDualTr X) : IsSelfDualTr (move X Y P hP hΨ hp) := by
  intro x
  obtain ⟨x, rfl⟩ := mulVec_surj P x
  show P.1 *ᵥ x ∈ latMap P X.Λ ↔ ∀ y ∈ latMap P X.Λ, ∃ n : ℤ,
    Algebra.trace ℚ E (-Y.ξ0 * herm Y.Gm (P.1 *ᵥ x) y) = n
  rw [mem_latMap, h x]
  refine Iff.trans ?_ (mulVec_surj P).forall.symm
  refine forall_congr' fun y => imp_congr (mem_latMap P _ y).symm ?_
  rw [herm_P X Y P hP, trace_ratio]

theorem covol_move : GlobalTheory.TrueCx.covol (move X Y P hP hΨ hp) = GlobalTheory.TrueCx.covol X := by
  obtain ⟨u, hu, hc⟩ := exists_isom X Y P hP hΨ
  have ho := GlobalTheory.TrueCx.isOrth_x0F X
  generalize x0F X = x0 at ho
  obtain ⟨FF, hF⟩ := GlobalTheory.MetricWeightTest.exists_fundSet_orth X ho
  set Z := move X Y P hP hΨ hp with hZ
  have hcpt : ∀ z : V (nd X), rmul (umul u x0) (nmat X z) = umul u (cpt X x0 z) := fun z => (umul_rmul _ _).symm
  have hO : OmF Z (umul u x0) = OmF X x0 := by
    refine Set.ext fun z : V (nd X) => ?_
    show rmul (umul u x0) (nmat X z) ∈ GG X.Ψ Y.Gm X.p0 ↔ cpt X x0 z ∈ X.dom
    rw [hcpt]
    exact umul_mem_GG X.Gm_det hu _ _
  have hD : densF Z (umul u x0) = densF X x0 := by
    refine funext fun z : V (nd X) => ?_
    show ∏ τ : X.Ψ, ∏ i : Fin r, ‖dmin Y.Gm (rmul (umul u x0) (nmat X z)) τ i.castSucc‖ ^ (-2 : ℤ) = _
    simp only [hcpt, dmin_umul hu, densF]
  have hmu : muF Z (umul u x0) = muF X x0 := by
    exact congrArg₂ (fun (O : Set (V (nd X))) (D : V (nd X) → ℝ) =>
      (volume.restrict O).withDensity fun z => ENNReal.ofReal (D z)) hO hD
  have ho' : IsOrth Z (umul u x0) := fun τ => (gram_mul' (hu τ.1 τ.2) (mat x0 τ)).trans (ho τ)
  have hF' : IsFundSet Z (umul u x0) FF := by
    refine ⟨hF.1, hF.2.1.trans hO.ge, ?_, ?_⟩
    · intro (z : V (nd X)) hz (z' : V (nd X)) hz' γ hγ (b : Frame X.Ψ r) hb h
      replace h : rmul (umul u x0) (nmat X z') = lact γ (rmul (rmul (umul u x0) (nmat X z)) b) := h
      rw [hcpt, hcpt] at h
      have h' : umul u (cpt X x0 z') = umul u (lact (P⁻¹ * γ * P) (rmul (cpt X x0 z) b)) := by
        rw [umul_lact' (hc γ), umul_rmul]; exact h
      exact hF.2.2.1 z hz z' hz' _ hγ b hb (umul_inj' X.Gm_det hu h')
    · have : ∀ᵐ z ∂muF X x0, ∃ z' ∈ FF, ∃ γ ∈ Z.Γ, ∃ b ∈ Bor X.Ψ r,
          rmul (umul u x0) (nmat X z) = lact γ (rmul (rmul (umul u x0) (nmat X z')) b) := ?_
      · rw [← hmu] at this
        exact this
      filter_upwards [hF.2.2.2] with z hz
      obtain ⟨z', hz', γ, hγ, b, hb, h⟩ := hz
      have e : P⁻¹ * (P * γ * P⁻¹) * P = γ := by group
      refine ⟨z', hz', P * γ * P⁻¹, (mem_move X Y P hP hΨ hp _).2 (by rwa [e]), b, hb, ?_⟩
      rw [hcpt, hcpt]
      have := umul_lact' (hc (P * γ * P⁻¹)) (rmul (cpt X x0 z') b)
      rw [e, ← h, umul_rmul] at this
      exact this
  rw [(GlobalTheory.TrueCx.covol_eq Z ho' hF').2, (GlobalTheory.TrueCx.covol_eq X ho hF).2]
  exact congrArg (fun m : Measure (V (nd X)) => GlobalTheory.TrueCx.flagConst r ^ X.Ψ.card * (m FF).toReal) hmu

end Move

end GlobalTheory.EqCovol.Transport

open GlobalTheory.EqCovol.Transport in

theorem GlobalTheory.EqCovol.exists_transport : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (r : ℕ) (Y Y' : ReciprocityTheory.ChartRestriction.G.FD.Data E r), (∀ τ : E →+* ℂ, τ ∈ Y.Ψ ↔ τ (H.rt : E) = H.rt0) → Y'.Ψ = Y.Ψ → Y'.p0 = Y.p0 → 1 ≤ Y.p0 → Y.p0 < r → GlobalTheory.EqCovol.IsLevGrp l Y' → GlobalTheory.EqCovol.IsSelfDualTr Y → GlobalTheory.EqCovol.IsSelfDualTr Y' → ∃ Y'' : ReciprocityTheory.ChartRestriction.G.FD.Data E r, Y''.Ψ = Y.Ψ ∧ Y''.Gm = Y.Gm ∧ Y''.ξ0 = Y.ξ0 ∧ Y''.p0 = Y.p0 ∧ GlobalTheory.EqCovol.IsLevGrp l Y'' ∧ GlobalTheory.EqCovol.IsSelfDualTr Y'' ∧ GlobalTheory.TrueCx.covol Y'' = GlobalTheory.TrueCx.covol Y' := by
  intro E _ _ _ H l r Y Y' _ hΨ hp _ _ hl hY hY'
  obtain ⟨P, hP⟩ := exists_similitude H Y' Y hΨ hp hY' hY
  exact ⟨move Y' Y P hP hΨ hp, hΨ, rfl, rfl, hp, isLevGrp_move Y' Y P hP hΨ hp l hl,
    isSelfDualTr_move Y' Y P hP hΨ hp hY', covol_move Y' Y P hP hΨ hp⟩
