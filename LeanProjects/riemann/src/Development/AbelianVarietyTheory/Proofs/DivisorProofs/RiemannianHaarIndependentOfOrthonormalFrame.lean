import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU

noncomputable section
namespace GlobalTheory.FrameIndep
open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD
open scoped InnerProductSpace ComplexConjugate

abbrev cj {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ := A.map (starRingEnd ℂ)

def IsSkew {r : ℕ} (D Y : Matrix (Fin r) (Fin r) ℂ) : Prop := Yᵀ * D + D * cj Y = 0

theorem cj_mul {r : ℕ} (A B : Matrix (Fin r) (Fin r) ℂ) : cj (A * B) = cj A * cj B :=
  Matrix.map_mul

theorem isSkew_conj {r : ℕ} {D D' k l Y : Matrix (Fin r) (Fin r) ℂ} (hlk : l * k = 1) (hkl : k * l = 1)
    (h : kᵀ * D * cj k = D') (hY : IsSkew D' Y) : IsSkew D (k * Y * l) := by
  unfold IsSkew at *
  have e1 : kᵀ * D = D' * cj l := by
    have : cj k * cj l = 1 := by rw [← cj_mul, hkl]; simp
    calc kᵀ * D = kᵀ * D * (cj k * cj l) := by rw [this, Matrix.mul_one]
      _ = D' * cj l := by rw [← h]; simp only [Matrix.mul_assoc]
  have e2 : D * cj k = lᵀ * D' := by
    have : lᵀ * kᵀ = 1 := by rw [← Matrix.transpose_mul, hkl, Matrix.transpose_one]
    calc D * cj k = (lᵀ * kᵀ) * (D * cj k) := by rw [this, Matrix.one_mul]
      _ = lᵀ * D' := by rw [← h]; simp only [Matrix.mul_assoc]
  calc (k * Y * l)ᵀ * D + D * cj (k * Y * l) = lᵀ * (Yᵀ * (kᵀ * D)) + (D * cj k) * cj Y * cj l := by
        simp only [Matrix.transpose_mul, cj_mul, Matrix.mul_assoc]
    _ = lᵀ * (Yᵀ * D' + D' * cj Y) * cj l := by
        rw [e1, e2]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hY]; simp

theorem trace_conj {r : ℕ} {k l Y : Matrix (Fin r) (Fin r) ℂ} (hlk : l * k = 1) :
    (k * Y * l).trace = Y.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hlk, Matrix.one_mul]

theorem trace_conj_mul {r : ℕ} {k l Y Z : Matrix (Fin r) (Fin r) ℂ} (hlk : l * k = 1) :
    ((k * Y * l) * (k * Z * l)).trace = (Y * Z).trace := by
  have : (k * Y * l) * (k * Z * l) = k * (Y * Z) * l := by
    calc (k * Y * l) * (k * Z * l) = k * Y * (l * k) * Z * l := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hlk]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [this, trace_conj hlk]

theorem herm_skew_iff {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (A : Matrix (Fin r) (Fin r) ℂ) :
    (∀ u w, hermC τ G (A *ᵥ u) w + hermC τ G u (A *ᵥ w) = 0) ↔ IsSkew (G.map τ) A := by
  have key : ∀ u w, hermC τ G (A *ᵥ u) w + hermC τ G u (A *ᵥ w) =
      ∑ a, ∑ b, u a * (Aᵀ * G.map τ + G.map τ * cj A) a b * conj (w b) := by
    intro u w
    simp only [hermC, Matrix.mulVec, dotProduct, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, mul_add, add_mul, Finset.sum_add_distrib]
    congr 1
    · refine (Finset.sum_congr rfl fun y _ => Finset.sum_comm).trans (Finset.sum_comm.trans
        (Finset.sum_congr rfl fun x _ => ?_))
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun y _ => by ring
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring
  constructor
  · intro h
    unfold IsSkew
    ext a b
    have := h (Pi.single a 1) (Pi.single b 1)
    rw [key] at this
    simpa [Pi.single_apply] using this
  · intro h u w
    unfold IsSkew at h
    rw [key, h]; simp

theorem gram_eq {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (M : Matrix (Fin r) (Fin r) ℂ) : gram τ G M = Mᵀ * G.map τ * cj M := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]

abbrev sgnMat (r p : ℕ) : Matrix (Fin r) (Fin r) ℂ := Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)

theorem sgn_sq (p a : ℕ) : sgn p a * sgn p a = 1 := by unfold sgn; split_ifs <;> norm_num

theorem sgnMat_mul (r p : ℕ) : sgnMat r p * sgnMat r p = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext a; rw [← Complex.ofReal_mul, sgn_sq]; simp

theorem sgnMat_transpose (r p : ℕ) : (sgnMat r p)ᵀ = sgnMat r p := Matrix.diagonal_transpose _

theorem cj_sgnMat (r p : ℕ) : cj (sgnMat r p) = sgnMat r p := by
  ext a b; by_cases h : a = b <;> simp [h, Matrix.diagonal_apply]

theorem frame_facts {E : Type} [Field E] {r p : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (M : Matrix (Fin r) (Fin r) ℂ) (h : gram τ G M = sgnMat r p) :
    M * M⁻¹ = 1 ∧ M⁻¹ * M = 1 ∧ (M⁻¹)ᵀ * sgnMat r p * cj (M⁻¹) = G.map τ := by
  rw [gram_eq] at h
  have h1 : Mᵀ * (G.map τ * cj M * sgnMat r p) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h, sgnMat_mul]
  have hu : IsUnit M.det := by
    have := Matrix.isUnit_det_of_right_inverse h1
    rwa [Matrix.det_transpose] at this
  have hMi : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hiM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul _ hu
  refine ⟨hMi, hiM, ?_⟩
  have c1 : (M⁻¹)ᵀ * Mᵀ = 1 := by rw [← Matrix.transpose_mul, hMi, Matrix.transpose_one]
  have c2 : cj M * cj (M⁻¹) = 1 := by rw [← cj_mul, hMi]; simp
  rw [← h]
  calc (M⁻¹)ᵀ * (Mᵀ * G.map τ * cj M) * cj M⁻¹ = ((M⁻¹)ᵀ * Mᵀ) * G.map τ * (cj M * cj M⁻¹) := by
        simp only [Matrix.mul_assoc]
    _ = G.map τ := by rw [c1, c2, Matrix.one_mul, Matrix.mul_one]

abbrev WW (ι : Type) [Fintype ι] (r : ℕ) : Type := EuclideanSpace ℂ (ι × Fin r × Fin r)

def blk {ι : Type} [Fintype ι] {r : ℕ} (Y : WW ι r) (t : ι) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b => Y (t, a, b)

def cjW {ι : Type} [Fintype ι] {r : ℕ} (k l : ι → Matrix (Fin r) (Fin r) ℂ) : WW ι r →ₗ[ℝ] WW ι r where
  toFun Y := WithLp.toLp 2 fun i => (k i.1 * blk Y i.1 * l i.1) i.2.1 i.2.2
  map_add' Y Z := by
    ext i
    have : blk (Y + Z) i.1 = blk Y i.1 + blk Z i.1 := by ext a b; simp [blk]
    simp [this, Matrix.mul_add, Matrix.add_mul]
  map_smul' c Y := by
    ext i
    have : blk (c • Y) i.1 = (c : ℂ) • blk Y i.1 := by ext a b; simp [blk]
    simp [this]

theorem blk_cjW {ι : Type} [Fintype ι] {r : ℕ} (k l : ι → Matrix (Fin r) (Fin r) ℂ) (Y : WW ι r) (t : ι) :
    blk (cjW k l Y) t = k t * blk Y t * l t := by
  ext a b; simp [cjW, blk]

theorem cjW_cjW {ι : Type} [Fintype ι] {r : ℕ} {k l : ι → Matrix (Fin r) (Fin r) ℂ} (h : ∀ t, l t * k t = 1)
    (Y : WW ι r) : cjW l k (cjW k l Y) = Y := by
  ext ⟨t, a, b⟩
  have : l t * (k t * blk Y t * l t) * k t = blk Y t := by
    calc _ = (l t * k t) * blk Y t * (l t * k t) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h]; simp
  have h2 : blk (cjW l k (cjW k l Y)) t = blk Y t := by rw [blk_cjW, blk_cjW, this]
  exact congrArg (fun A : Matrix (Fin r) (Fin r) ℂ => A a b) h2

theorem inner_theta {ι : Type} [Fintype ι] {r : ℕ} (d : Fin r → ℝ) (hd : ∀ a, d a * d a = 1) (Y Z : WW ι r)
    (hY : ∀ t, IsSkew (Matrix.diagonal fun a => (d a : ℂ)) (blk Y t)) :
    ⟪cjW (fun _ => Matrix.diagonal fun a => (d a : ℂ)) (fun _ => Matrix.diagonal fun a => (d a : ℂ)) Y, Z⟫_ℝ =
      -(∑ t, (blk Y t * blk Z t).trace).re := by
  have key : ∀ t a b, (starRingEnd ℂ) ((d a : ℂ) * Y (t, a, b) * (d b : ℂ)) = -(Y (t, b, a)) := by
    intro t a b
    have h := congrArg (fun A : Matrix (Fin r) (Fin r) ℂ => A a b) (hY t)
    simp only [IsSkew, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply,
      Matrix.map_apply, blk, Matrix.of_apply, Matrix.zero_apply] at h
    have hb : (d b : ℂ) * d b = 1 := by rw [← Complex.ofReal_mul, hd]; simp
    rw [map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal]
    linear_combination (d b : ℂ) * h - Y (t, b, a) * hb
  have hc : ∀ u w : ℂ, ⟪u, w⟫_ℝ = ((starRingEnd ℂ) u * w).re := fun u w => by
    rw [Complex.inner, mul_comm]
  have hs : ∑ i, (starRingEnd ℂ) (cjW (fun _ => Matrix.diagonal fun a => (d a : ℂ))
      (fun _ => Matrix.diagonal fun a => (d a : ℂ)) Y i) * Z i = -∑ t, (blk Y t * blk Z t).trace := by
    rw [Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Fintype.sum_prod_type]
    have e : ∀ a b, (cjW (fun _ => Matrix.diagonal fun a => (d a : ℂ))
        (fun _ => Matrix.diagonal fun a => (d a : ℂ)) Y) (t, a, b) = (d a : ℂ) * Y (t, a, b) * (d b : ℂ) := by
      intro a b
      simp [cjW, blk, Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [e, key, Matrix.trace, Matrix.diag, Matrix.mul_apply, blk, Matrix.of_apply,
      ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [PiLp.inner_apply]
  simp only [hc]
  rw [← Complex.re_sum, hs, Complex.neg_re]

theorem mem_comap_iff {E : Type} [Field E] [NumberField E] [IsCMField E] {r p : ℕ} {Ψ : Finset (E →+* ℂ)}
    (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (hx : ∀ τ : Ψ, gram τ.1 G (mat x τ) = sgnMat r p)
    (Y : WW Ψ r) :
    Y ∈ (realLie Ψ G).comap (fromFrame x) ↔ ∀ τ : Ψ, (blk Y τ).trace = 0 ∧ IsSkew (sgnMat r p) (blk Y τ) := by
  rw [Submodule.mem_comap]
  show (∀ τ : Ψ, (Matrix.of (fromFrame x Y τ)).trace = 0 ∧ ∀ u w,
    hermC τ.1 G (Matrix.of (fromFrame x Y τ) *ᵥ u) w + hermC τ.1 G u (Matrix.of (fromFrame x Y τ) *ᵥ w) = 0) ↔ _
  refine forall_congr' fun τ => ?_
  obtain ⟨h1, h2, h3⟩ := frame_facts τ.1 G (mat x τ) (hx τ)
  have e : Matrix.of (fromFrame x Y τ) = mat x τ * blk Y τ * (mat x τ)⁻¹ := rfl
  rw [e, herm_skew_iff, trace_conj h2]
  refine and_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
  · have := isSkew_conj h1 h2 h3 h
    have e2 : (mat x τ)⁻¹ * (mat x τ * blk Y τ * (mat x τ)⁻¹) * mat x τ = blk Y τ := by
      calc _ = ((mat x τ)⁻¹ * mat x τ) * blk Y τ * ((mat x τ)⁻¹ * mat x τ) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [h2]; simp
    rwa [e2] at this
  · exact isSkew_conj h2 h1 (by rw [← gram_eq]; exact hx τ) h

theorem det_adjoint_eq {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (A : V →ₗ[ℝ] V) : LinearMap.det (LinearMap.adjoint A) = LinearMap.det A := by
  classical
  let b := stdOrthonormalBasis ℝ V
  rw [← LinearMap.det_toMatrix b.toBasis, ← LinearMap.det_toMatrix b.toBasis A, LinearMap.toMatrix_adjoint,
    Matrix.det_conjTranspose]
  simp

theorem volume_image_of_form {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace V] [BorelSpace V] [MeasurableSpace W] [BorelSpace W]
    (L : V ≃ₗ[ℝ] W) (σ : V →ₗ[ℝ] V) (τ : W →ₗ[ℝ] W) (hσ : ∀ x, σ (σ x) = x) (hτ : ∀ x, τ (τ x) = x)
    (h : ∀ x y, ⟪τ (L x), L y⟫_ℝ = ⟪σ x, y⟫_ℝ) (s : Set V) : volume (L '' s) = volume s := by
  let J : V ≃ₗᵢ[ℝ] W := (stdOrthonormalBasis ℝ V).equiv (stdOrthonormalBasis ℝ W) (finCongr L.finrank_eq)
  let A : V →ₗ[ℝ] V := J.symm.toLinearEquiv.toLinearMap ∘ₗ L.toLinearMap
  let T : V →ₗ[ℝ] V := J.symm.toLinearEquiv.toLinearMap ∘ₗ τ ∘ₗ J.toLinearEquiv.toLinearMap
  have hA : LinearMap.adjoint A ∘ₗ T ∘ₗ A = σ := by
    ext x
    refine ext_inner_right ℝ fun y => ?_
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, ← h]
    simp [A, T]
  have hT : T ∘ₗ T = LinearMap.id := by ext x; simp [T, hτ]
  have hS : σ ∘ₗ σ = LinearMap.id := by ext x; simp [hσ]
  have d1 := congrArg LinearMap.det hA
  have d2 := congrArg LinearMap.det hT
  have d3 := congrArg LinearMap.det hS
  simp only [LinearMap.det_comp, det_adjoint_eq, LinearMap.det_id] at d1 d2 d3
  have d4 : |LinearMap.det A| = 1 := by
    have e : LinearMap.det A ^ 4 = 1 := by
      rw [← d1] at d3
      linear_combination d3 - LinearMap.det A ^ 4 * d2
    have e2 : |LinearMap.det A| ^ 4 = 1 := by rw [← abs_pow, e, abs_one]
    exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) (by norm_num)).1 e2
  have e1 : L '' s = J.symm ⁻¹' (A '' s) := by
    ext w
    simp only [Set.mem_image, Set.mem_preimage, A]
    refine exists_congr fun x => and_congr_right fun _ => ?_
    simp
  rw [e1]
  have := MeasurePreserving.measure_preimage_equiv (f := J.symm.toHomeomorph.toMeasurableEquiv)
    (J.symm.measurePreserving) (A '' s)
  refine this.trans ?_
  rw [Measure.addHaar_image_linearMap, d4]; simp

theorem theta_mem {ι : Type} [Fintype ι] {r p : ℕ} (Y : WW ι r)
    (hY : ∀ t, (blk Y t).trace = 0 ∧ IsSkew (sgnMat r p) (blk Y t)) (t : ι) :
    (blk (cjW (fun _ => sgnMat r p) (fun _ => sgnMat r p) Y) t).trace = 0 ∧
      IsSkew (sgnMat r p) (blk (cjW (fun _ => sgnMat r p) (fun _ => sgnMat r p) Y) t) := by
  rw [blk_cjW]
  refine ⟨by rw [trace_conj (sgnMat_mul r p)]; exact (hY t).1,
    isSkew_conj (sgnMat_mul r p) (sgnMat_mul r p) ?_ (hY t).2⟩
  rw [sgnMat_transpose, cj_sgnMat, sgnMat_mul, Matrix.one_mul]

theorem riemHaar_frame_indep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r p0 p1 : ℕ)
    (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x y : Frame Ψ r), (∀ a b, cc (G a b) = G b a) →
    (∀ τ : Ψ, gram τ.1 G (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) →
    (∀ τ : Ψ, gram τ.1 G (mat y τ) = Matrix.diagonal fun a : Fin r => ((sgn p1 (a : ℕ) : ℝ) : ℂ)) →
    riemHaar Ψ G x = riemHaar Ψ G y := by
  intro E _ _ _ r p0 p1 Ψ G x y _ hx hy
  let k : Ψ → Matrix (Fin r) (Fin r) ℂ := fun τ => (mat x τ)⁻¹ * mat y τ
  let l : Ψ → Matrix (Fin r) (Fin r) ℂ := fun τ => (mat y τ)⁻¹ * mat x τ
  have fx := fun τ : Ψ => frame_facts τ.1 G (mat x τ) (hx τ)
  have fy := fun τ : Ψ => frame_facts τ.1 G (mat y τ) (hy τ)
  have hlk : ∀ τ, l τ * k τ = 1 := fun τ => by
    calc l τ * k τ = (mat y τ)⁻¹ * (mat x τ * (mat x τ)⁻¹) * mat y τ := by simp only [l, k, Matrix.mul_assoc]
      _ = 1 := by rw [(fx τ).1, Matrix.mul_one, (fy τ).2.1]
  have hkl : ∀ τ, k τ * l τ = 1 := fun τ => by
    calc k τ * l τ = (mat x τ)⁻¹ * (mat y τ * (mat y τ)⁻¹) * mat x τ := by simp only [l, k, Matrix.mul_assoc]
      _ = 1 := by rw [(fy τ).1, Matrix.mul_one, (fx τ).2.1]
  have hK : ∀ τ, (k τ)ᵀ * sgnMat r p0 * cj (k τ) = sgnMat r p1 := fun τ => by
    have := hy τ
    rw [gram_eq, ← (fx τ).2.2] at this
    refine Eq.trans ?_ this
    simp only [k, Matrix.transpose_mul, cj_mul, Matrix.mul_assoc]
  have hL : ∀ τ, (l τ)ᵀ * sgnMat r p1 * cj (l τ) = sgnMat r p0 := fun τ => by
    have := hx τ
    rw [gram_eq, ← (fy τ).2.2] at this
    refine Eq.trans ?_ this
    simp only [l, Matrix.transpose_mul, cj_mul, Matrix.mul_assoc]
  have m1 := mem_comap_iff G x hx
  have m2 := mem_comap_iff G y hy
  have hLV : ∀ Y ∈ (realLie Ψ G).comap (fromFrame y), cjW k l Y ∈ (realLie Ψ G).comap (fromFrame x) :=
    fun Y hY => (m1 _).2 fun τ => by
      rw [blk_cjW]
      exact ⟨by rw [trace_conj (hlk τ)]; exact ((m2 Y).1 hY τ).1,
        isSkew_conj (hlk τ) (hkl τ) (hK τ) ((m2 Y).1 hY τ).2⟩
  have hKV : ∀ Y ∈ (realLie Ψ G).comap (fromFrame x), cjW l k Y ∈ (realLie Ψ G).comap (fromFrame y) :=
    fun Y hY => (m2 _).2 fun τ => by
      rw [blk_cjW]
      exact ⟨by rw [trace_conj (hkl τ)]; exact ((m1 Y).1 hY τ).1,
        isSkew_conj (hkl τ) (hlk τ) (hL τ) ((m1 Y).1 hY τ).2⟩
  let L : (realLie Ψ G).comap (fromFrame y) ≃ₗ[ℝ] (realLie Ψ G).comap (fromFrame x) :=
    LinearEquiv.ofLinear ((cjW k l).restrict hLV) ((cjW l k).restrict hKV)
      (by ext1 Y; exact Subtype.ext (cjW_cjW hkl Y.1)) (by ext1 Y; exact Subtype.ext (cjW_cjW hlk Y.1))
  have hθx : ∀ Y ∈ (realLie Ψ G).comap (fromFrame x),
      cjW (fun _ => sgnMat r p0) (fun _ => sgnMat r p0) Y ∈ (realLie Ψ G).comap (fromFrame x) :=
    fun Y hY => (m1 _).2 (theta_mem Y ((m1 Y).1 hY))
  have hθy : ∀ Y ∈ (realLie Ψ G).comap (fromFrame y),
      cjW (fun _ => sgnMat r p1) (fun _ => sgnMat r p1) Y ∈ (realLie Ψ G).comap (fromFrame y) :=
    fun Y hY => (m2 _).2 (theta_mem Y ((m2 Y).1 hY))
  have hvol : ∀ s, volume (L '' s) = volume s :=
    volume_image_of_form L ((cjW _ _).restrict hθy) ((cjW _ _).restrict hθx)
      (fun Y => Subtype.ext (cjW_cjW (fun _ => sgnMat_mul r p1) Y.1))
      (fun Y => Subtype.ext (cjW_cjW (fun _ => sgnMat_mul r p0) Y.1)) (fun a b => by
        simp only [Submodule.coe_inner, LinearMap.restrict_coe_apply]
        change ⟪cjW (fun _ => sgnMat r p0) (fun _ => sgnMat r p0) (cjW k l a.1), cjW k l b.1⟫_ℝ =
          ⟪cjW (fun _ => sgnMat r p1) (fun _ => sgnMat r p1) a.1, b.1⟫_ℝ
        rw [inner_theta (fun a : Fin r => sgn p0 (a : ℕ)) (fun a => sgn_sq p0 a) _ _
            (fun t => ((m1 _).1 (hLV _ a.2) t).2),
          inner_theta (fun a : Fin r => sgn p1 (a : ℕ)) (fun a => sgn_sq p1 a) _ _
            (fun t => ((m2 _).1 a.2 t).2)]
        simp only [blk_cjW, trace_conj_mul (hlk _)])
  have hLm : Measurable (fun Y : (realLie Ψ G).comap (fromFrame y) => L Y) :=
    L.toLinearMap.continuous_of_finiteDimensional.measurable
  have hmap : Measure.map (fun Y : (realLie Ψ G).comap (fromFrame y) => L Y) volume = volume := by
    ext s hs
    rw [Measure.map_apply hLm hs, ← hvol, Set.image_preimage_eq s L.surjective]
  have hfx : Measurable (fun Y : (realLie Ψ G).comap (fromFrame x) => fromFrame x Y.1) :=
    (fromFrame x ∘ₗ ((realLie Ψ G).comap (fromFrame x)).subtype).continuous_of_finiteDimensional.measurable
  have hcomp : (fun Y : (realLie Ψ G).comap (fromFrame x) => fromFrame x Y.1) ∘
      (fun Y : (realLie Ψ G).comap (fromFrame y) => L Y) =
      fun Y : (realLie Ψ G).comap (fromFrame y) => fromFrame y Y.1 := by
    funext Y
    funext τ
    change (mat x τ * blk (cjW k l Y.1) τ * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) =
      mat y τ * blk Y.1 τ * (mat y τ)⁻¹
    rw [blk_cjW]
    calc mat x τ * (k τ * blk Y.1 τ * l τ) * (mat x τ)⁻¹ =
          (mat x τ * (mat x τ)⁻¹) * mat y τ * blk Y.1 τ * (mat y τ)⁻¹ * (mat x τ * (mat x τ)⁻¹) := by
          simp only [k, l, Matrix.mul_assoc]
      _ = _ := by rw [(fx τ).1, Matrix.one_mul, Matrix.mul_one]
  have hlie : riemLie Ψ G x = riemLie Ψ G y := by
    unfold riemLie
    rw [OrthonormalBasis.addHaar_eq_volume, OrthonormalBasis.addHaar_eq_volume, ← hmap,
      Measure.map_map hfx hLm, hcomp]
  unfold riemHaar
  rw [hlie]

end GlobalTheory.FrameIndep
