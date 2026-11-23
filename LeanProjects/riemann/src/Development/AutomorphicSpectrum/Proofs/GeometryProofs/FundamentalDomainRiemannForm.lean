import Mathlib

open MeasureTheory

namespace GlobalTheory.CompanionTheory.Ar.Sl.SelfDualCovol

noncomputable def stdBasis (g : ℕ) : Module.Basis (Σ _ : Fin g, Fin 2) ℝ (Fin g → ℂ) :=
  Pi.basis fun _ => Complex.basisOneI

theorem stdBasis_repr_zero {g : ℕ} (z : Fin g → ℂ) (j : Fin g) :
    (stdBasis g).repr z ⟨j, 0⟩ = (z j).re := by
  simp [stdBasis, Pi.basis_repr]

theorem stdBasis_repr_one {g : ℕ} (z : Fin g → ℂ) (j : Fin g) :
    (stdBasis g).repr z ⟨j, 1⟩ = (z j).im := by
  simp [stdBasis, Pi.basis_repr]

theorem re_dotProduct_star {g : ℕ} (z w : Fin g → ℂ) :
    (z ⬝ᵥ star w).re = ∑ a, (stdBasis g).repr z a * (stdBasis g).repr w a := by
  rw [Fintype.sum_sigma]
  simp only [Fin.sum_univ_two, stdBasis_repr_zero, stdBasis_repr_one, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Complex.mul_re]

theorem volume_fundamentalDomain_stdBasis (g : ℕ) :
    volume.real (ZSpan.fundamentalDomain (stdBasis g)) = 1 := by
  have hset : ZSpan.fundamentalDomain (stdBasis g) =
      Set.pi Set.univ fun _ : Fin g => Complex.reProdIm (Set.Ico 0 1) (Set.Ico 0 1) := by
    ext z
    simp only [ZSpan.mem_fundamentalDomain, Set.mem_pi, Set.mem_univ, true_implies,
      Complex.mem_reProdIm]
    constructor
    · intro h j
      exact ⟨by simpa [stdBasis_repr_zero] using h ⟨j, 0⟩,
        by simpa [stdBasis_repr_one] using h ⟨j, 1⟩⟩
    · rintro h ⟨j, a⟩
      fin_cases a
      · simpa [stdBasis_repr_zero] using (h j).1
      · simpa [stdBasis_repr_one] using (h j).2
  have hsq : volume (Complex.reProdIm (Set.Ico (0 : ℝ) 1) (Set.Ico (0 : ℝ) 1)) = 1 := by
    have h := Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv
      ((Set.Ico (0 : ℝ) 1) ×ˢ (Set.Ico (0 : ℝ) 1))
    have h2 : Complex.measurableEquivRealProd ⁻¹' ((Set.Ico (0 : ℝ) 1) ×ˢ (Set.Ico (0 : ℝ) 1)) =
        Complex.reProdIm (Set.Ico (0 : ℝ) 1) (Set.Ico (0 : ℝ) 1) := by
      ext z
      simp [Complex.mem_reProdIm, Complex.measurableEquivRealProd]
    rw [h2] at h
    rw [h, Measure.volume_eq_prod, Measure.prod_prod]
    simp
  rw [hset, measureReal_def, volume_pi_pi]
  simp [hsq]

theorem det_ne_zero_of_pos {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ}
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) : Hm.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hmv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  have hz : star v ≠ 0 := by simpa using hv
  have := hpos (star v) hz
  simp [hmv] at this

theorem det_gram {g : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Module.Basis ι ℝ (Fin g → ℂ))
    (he : ∀ z w : Fin g → ℂ, (z ⬝ᵥ star w).re = ∑ a, e.repr z a * e.repr w a)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (v : ι → Fin g → ℂ) :
    (Matrix.of fun i j => (v i ⬝ᵥ Hm.mulVec (star (v j))).im).det =
      (e.det v) ^ 2 * Complex.normSq Hm.det := by
  let S : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := (-Complex.I) • Matrix.toLin' Hm.transpose
  let SR : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) := S.restrictScalars ℝ
  let M := LinearMap.toMatrix e e SR
  let P := e.toMatrix v
  have hS : ∀ z w : Fin g → ℂ, (z ⬝ᵥ Hm.mulVec (star w)).im = (S z ⬝ᵥ star w).re := by
    intro z w
    have h1 : z ⬝ᵥ Hm.mulVec (star w) = Hm.transpose.mulVec z ⬝ᵥ star w := by
      rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
    have h2 : S z = (-Complex.I) • Hm.transpose.mulVec z := by
      simp [S]
    rw [h1, h2, smul_dotProduct]
    simp [Complex.mul_re]
  have hM : ∀ z a, e.repr (SR z) a = ∑ c, M a c * e.repr z c := by
    intro z a
    have := LinearMap.toMatrix_mulVec_repr e e SR z
    rw [← this]
    rfl
  have hG : (Matrix.of fun i j => (v i ⬝ᵥ Hm.mulVec (star (v j))).im) =
      P.transpose * M.transpose * P := by
    ext i j
    simp only [Matrix.of_apply, hS, Matrix.mul_apply, Matrix.transpose_apply]
    rw [he]
    have : ∀ a, e.repr (S (v i)) a = ∑ c, M a c * e.repr (v i) c := fun a => hM (v i) a
    simp only [this, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    simp only [P, Module.Basis.toMatrix_apply]
    ring
  have hdetM : M.det = Complex.normSq Hm.det := by
    have h1 : M.det = LinearMap.det SR := LinearMap.det_toMatrix e SR
    have h2 : LinearMap.det SR = Complex.normSq (LinearMap.det S) := by
      rw [show LinearMap.det SR = Algebra.norm ℝ (LinearMap.det S) from
        LinearMap.det_restrictScalars, Algebra.norm_complex_apply]
    rw [h1, h2]
    simp only [S, LinearMap.det_smul, LinearMap.det_toLin', Matrix.det_transpose, map_mul, map_pow]
    simp
  rw [hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose, hdetM,
    Module.Basis.det_apply]
  ring

theorem abs_det_gram_eq_one {V ι : Type*} [AddCommGroup V] [Module ℝ V] [Fintype ι] [DecidableEq ι]
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (bR : Module.Basis ι ℝ V)
    (hdet : (Matrix.of fun i j => E (bR i) (bR j)).det ≠ 0)
    (hint : ∀ i j, ∃ k : ℤ, E (bR i) (bR j) = k)
    (hself : ∀ w, (∀ j, ∃ k : ℤ, E w (bR j) = k) → ∀ i, ∃ k : ℤ, bR.repr w i = k) :
    |(Matrix.of fun i j => E (bR i) (bR j)).det| = 1 := by
  set G : Matrix ι ι ℝ := Matrix.of fun i j => E (bR i) (bR j) with hGdef
  have hunit : IsUnit G.det := isUnit_iff_ne_zero.mpr hdet
  let C : Matrix ι ι ℝ := G⁻¹
  have hCG : C * G = 1 := Matrix.nonsing_inv_mul G hunit
  let w : ι → V := fun i => ∑ k, C i k • bR k
  have hw : ∀ i j, E (w i) (bR j) = (1 : Matrix ι ι ℝ) i j := by
    intro i j
    rw [← hCG, Matrix.mul_apply]
    simp [w, hGdef]
  have hCint : ∀ i k, ∃ n : ℤ, C i k = n := by
    intro i k
    obtain ⟨n, hn⟩ := hself (w i) (fun j => by
      rw [hw, Matrix.one_apply]
      split_ifs
      · exact ⟨1, by simp⟩
      · exact ⟨0, by simp⟩) k
    refine ⟨n, ?_⟩
    rw [← hn]
    simp [w, Finsupp.single_apply]
  choose Cz hCz using hCint
  choose Gz hGz using hint
  have hmul : (Matrix.of Cz) * (Matrix.of Gz) = 1 := by
    have : ((Matrix.of Cz) * (Matrix.of Gz)).map (Int.castRingHom ℝ) = (1 : Matrix ι ι ℤ).map (Int.castRingHom ℝ) := by
      rw [Matrix.map_mul, Matrix.map_one _ (by simp) (by simp), ← hCG]
      congr 1
      · ext i j; simp [hCz]
      · ext i j; simp [hGdef, hGz]
    exact Matrix.map_injective (Int.cast_injective) this
  have hu : IsUnit (Matrix.of Gz).det :=
    IsUnit.of_mul_eq_one _ (by rw [mul_comm, ← Matrix.det_mul, hmul, Matrix.det_one])
  have hGm : G = (Matrix.of Gz).map (Int.castRingHom ℝ) := by
    ext i j; simp [hGdef, hGz]
  have hd : G.det = (((Matrix.of Gz).det : ℤ) : ℝ) := by
    rw [hGm]
    exact ((Int.castRingHom ℝ).map_det _).symm
  rw [hd]
  rcases Int.isUnit_iff.mp hu with h | h <;> simp [h]

noncomputable def imForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) :
    (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun z w => (z ⬝ᵥ Hm.mulVec (star w)).im)
    (fun z z' w => by simp [add_dotProduct])
    (fun c z w => by simp [smul_dotProduct])
    (fun z w w' => by simp [Matrix.mulVec_add, dotProduct_add])
    (fun c z w => by
      have : star (c • w) = c • star w := by ext j; simp
      rw [this, Matrix.mulVec_smul, dotProduct_smul]
      simp)

theorem imForm_apply {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    imForm Hm z w = (z ⬝ᵥ Hm.mulVec (star w)).im := rfl

theorem volume_mul_norm_det_eq_one :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ),
      DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Hm.IsHermitian →
      (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) →
      (∀ l ∈ Λ, ∀ l' ∈ Λ, ∃ k : ℤ, (l ⬝ᵥ Hm.mulVec (star l')).im = k) →
      (∀ w : Fin g → ℂ, (∀ l ∈ Λ, ∃ k : ℤ, (w ⬝ᵥ Hm.mulVec (star l)).im = k) → w ∈ Λ) →
      ∀ Fd : Set (Fin g → ℂ), IsAddFundamentalDomain Λ Fd volume →
        (volume Fd).toReal * ‖Hm.det‖ = 1 := by
  intro g Λ Hm hd hs _ hpos hint hself Fd hFd
  haveI := hd
  haveI : IsZLattice ℝ Λ := ⟨hs⟩
  haveI : Module.Free ℤ Λ := ZLattice.module_free ℝ Λ
  haveI : Module.Finite ℤ Λ := ZLattice.module_finite ℝ Λ
  let e := stdBasis g
  let b0 := Module.Free.chooseBasis ℤ Λ
  let b : Module.Basis (Σ _ : Fin g, Fin 2) ℤ Λ :=
    b0.reindex ((b0.ofZLatticeBasis ℝ Λ).indexEquiv e)
  let bR := b.ofZLatticeBasis ℝ Λ
  have hbR : ∀ i, bR i = (b i : Fin g → ℂ) := fun i => Module.Basis.ofZLatticeBasis_apply ℝ Λ b i
  have hval : (Subtype.val ∘ ⇑b) = ⇑bR := by
    funext i
    exact (hbR i).symm
  have hvol : (volume Fd).toReal = |e.det bR| := by
    have h1 := ZLattice.covolume_eq_measure_fundamentalDomain Λ volume hFd
    have h2 := ZLattice.covolume_eq_det_mul_measureReal Λ volume b e
    rw [volume_fundamentalDomain_stdBasis, mul_one, hval] at h2
    rw [← h2, h1]
    rfl
  have hGdet : (Matrix.of fun i j => imForm Hm (bR i) (bR j)).det =
      (e.det bR) ^ 2 * Complex.normSq Hm.det :=
    det_gram e re_dotProduct_star Hm bR
  have hD : e.det bR ≠ 0 := (e.isUnit_det bR).ne_zero
  have hN : Complex.normSq Hm.det ≠ 0 := by
    simpa using det_ne_zero_of_pos hpos
  have hcomb : ∀ (w : Fin g → ℂ), (∀ j, ∃ k : ℤ, imForm Hm w (bR j) = k) →
      ∀ l ∈ Λ, ∃ k : ℤ, (w ⬝ᵥ Hm.mulVec (star l)).im = k := by
    intro w hw l hl
    choose k hk using hw
    have hl' : l = ∑ j, ((b.repr ⟨l, hl⟩ j : ℤ) : ℝ) • bR j := by
      conv_lhs => rw [← bR.sum_repr l]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show bR.repr l j = _ from Module.Basis.ofZLatticeBasis_repr_apply ℝ Λ b ⟨l, hl⟩ j]
    refine ⟨∑ j, b.repr ⟨l, hl⟩ j * k j, ?_⟩
    rw [← imForm_apply]
    conv_lhs => rw [hl']
    simp [map_sum, hk]
  have hone := abs_det_gram_eq_one (imForm Hm) bR
    (by rw [hGdet]; exact mul_ne_zero (pow_ne_zero 2 hD) hN)
    (fun i j => by
      rw [hbR, hbR]
      exact hint _ (b i).2 _ (b j).2)
    (fun w hw i => by
      have hwΛ : w ∈ Λ := hself w (hcomb w hw)
      exact ⟨b.repr ⟨w, hwΛ⟩ i, Module.Basis.ofZLatticeBasis_repr_apply ℝ Λ b ⟨w, hwΛ⟩ i⟩)
  have hnn : 0 ≤ (e.det bR) ^ 2 * Complex.normSq Hm.det :=
    mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)
  rw [hGdet, abs_of_nonneg hnn, Complex.normSq_eq_norm_sq] at hone
  rw [hvol]
  have h0 : 0 ≤ |e.det bR| * ‖Hm.det‖ := by positivity
  refine (pow_eq_one_iff_of_nonneg h0 two_ne_zero).mp ?_
  rw [mul_pow, sq_abs]
  exact hone

end GlobalTheory.CompanionTheory.Ar.Sl.SelfDualCovol
