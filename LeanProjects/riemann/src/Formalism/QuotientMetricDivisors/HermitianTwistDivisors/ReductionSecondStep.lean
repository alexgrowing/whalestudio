import Mathlib
import Formalism.QuotientMetricDivisors.ProdFormula
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.HermitianLattices.HermitianLatticesProofs.IndexBasic
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ProdFormula
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.LcvBasis
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.IdxChange
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ImageLcv
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.RatHerm
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.LocBasis

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.DivisionValues

namespace StepBAux

section Gram

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def cvec {d : ℕ} (σ : K →+* ℂ) (x : Fin d → K) : Fin d → ℂ := fun i => σ (x i)

def met {d : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (v : InfinitePlace K) :
    Matrix (Fin d) (Fin d) ℂ :=
  ((X v)⁻¹).conjTranspose * (X v)⁻¹

def fmat {d m : ℕ} (σ : K →+* ℂ) (e : Fin m → Fin d → K) : Matrix (Fin d) (Fin m) ℂ :=
  Matrix.of fun i a => σ (e a i)

theorem majAt_eq {d : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (v : InfinitePlace K)
    (x y : Fin d → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) X v x y =
      star (cvec v.embedding x) ⬝ᵥ (met X v *ᵥ cvec v.embedding y) := by
  have hv : ∀ z : Fin d → K, Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin d)) v z = cvec v.embedding z := by
    intro z; funext i; simp [Formalism.HermitianLatticesTheory.vecAt, cvec]
  have h1 : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) X v x y =
      star ((X v)⁻¹ *ᵥ cvec v.embedding x) ⬝ᵥ ((X v)⁻¹ *ᵥ cvec v.embedding y) := by
    simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, hv, dotProduct, Pi.star_apply]
  rw [h1, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, met]

theorem gram_eq_fmat {d m : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (v : InfinitePlace K) (e : Fin m → Fin d → K) :
    gram X v e = (fmat v.embedding e)ᴴ * met X v * fmat v.embedding e := by
  ext a c
  simp only [gram, Formalism.HN.gramPl, Matrix.of_apply, majAt_eq]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, fmat, Matrix.of_apply, dotProduct,
    Matrix.mulVec, cvec, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem fmat_change {d m : ℕ} (σ : K →+* ℂ) (e : Fin m → Fin d → K)
    (γ : Matrix (Fin m) (Fin m) K) :
    fmat σ (fun i => ∑ k, γ k i • e k) = fmat σ e * γ.map σ := by
  ext j i
  simp only [fmat, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem gram_change {d m : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (v : InfinitePlace K) (e : Fin m → Fin d → K) (γ : Matrix (Fin m) (Fin m) K) :
    (gram X v (fun i => ∑ k, γ k i • e k)).det =
      star (v.embedding γ.det) * v.embedding γ.det * (gram X v e).det := by
  have hγ : (γ.map v.embedding).det = v.embedding γ.det := (RingHom.map_det _ _).symm
  rw [gram_eq_fmat, gram_eq_fmat, fmat_change, Matrix.conjTranspose_mul]
  have : (γ.map v.embedding)ᴴ * (fmat v.embedding e)ᴴ * met X v *
      (fmat v.embedding e * γ.map v.embedding) =
      (γ.map v.embedding)ᴴ * ((fmat v.embedding e)ᴴ * met X v * fmat v.embedding e) *
        γ.map v.embedding := by
    simp only [Matrix.mul_assoc]
  rw [this, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hγ]
  ring

theorem gram_det_real {d m : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (v : InfinitePlace K) (e : Fin m → Fin d → K) :
    (gram X v e).det = (((gram X v e).det.re : ℝ) : ℂ) := by
  have h := Formalism.HN.HeightGram.norm_det_gramPl (Pi.basisFun K (Fin d)) X v e
  have hg : gram X v e = Formalism.HN.gramPl (Pi.basisFun K (Fin d)) X v e := rfl
  rw [← hg] at h
  have him : (gram X v e).det.im = 0 := by
    rw [← Complex.abs_re_eq_norm, h, abs_of_nonneg]
    rw [← h]; exact norm_nonneg _
  exact Complex.ext (by simp) (by simp [him])

theorem gram_re_ne [IsTotallyComplex K] {d : ℕ}
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (hX : ∀ v, IsUnit (X v).det)
    (e : Fin d → Fin d → K) (he : LinearIndependent K e) (v : InfinitePlace K) :
    (gram X v e).det.re ≠ 0 := by
  obtain ⟨h1, -⟩ := Formalism.HN.height_gram_determinant K (Fin d → K) (Fin d) (Pi.basisFun K (Fin d)) X hX d e he
  obtain ⟨-, -, hpos⟩ := Formalism.HN.place_lattice_structure K (Fin d → K) (Fin d) (Pi.basisFun K (Fin d)) X hX
    (Submodule.span (𝓞 K) (Set.range e)) (Submodule.fg_span (Set.finite_range e))
  rw [h1] at hpos
  exact (Finset.prod_ne_zero_iff.mp hpos.ne') v (Finset.mem_univ v)

theorem gram_ne [IsTotallyComplex K] {d : ℕ}
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (hX : ∀ v, IsUnit (X v).det)
    (e : Fin d → Fin d → K) (he : LinearIndependent K e) (v : InfinitePlace K) :
    (gram X v e).det ≠ 0 := by
  intro h
  apply gram_re_ne X hX e he v
  rw [h]; simp

theorem std_li (d : ℕ) : LinearIndependent K (fun i => (Pi.single i 1 : Fin d → K)) := by
  have : (fun i => (Pi.single i 1 : Fin d → K)) = ⇑(Pi.basisFun K (Fin d)) := by
    funext i; simp [Pi.basisFun_apply]
  rw [this]
  exact (Pi.basisFun K (Fin d)).linearIndependent

theorem image_li {d : ℕ} (φ : Matrix (Fin d) (Fin d) K) (hφ : IsUnit φ.det)
    (e : Fin d → Fin d → K) (he : LinearIndependent K e) :
    LinearIndependent K (fun i => φ *ᵥ e i) := by
  have hu : IsUnit φ := (Matrix.isUnit_iff_isUnit_det φ).mpr hφ
  have hinj : Function.Injective φ.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr hu
  exact he.map' (Matrix.mulVecLin φ) (LinearMap.ker_eq_bot.mpr hinj)

theorem vec_expand {d : ℕ} (x : Fin d → K) : x = ∑ k, x k • (Pi.single k 1 : Fin d → K) := by
  funext i
  simp [Finset.sum_apply, Pi.single_apply]

theorem gram_image [IsTotallyComplex K] {d : ℕ}
    (XS XT : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (hXS : ∀ v, IsUnit (XS v).det)
    (φ : Matrix (Fin d) (Fin d) K) (e : Fin d → Fin d → K) (v : InfinitePlace K) :
    (gram XT v (fun i => φ *ᵥ e i)).det = (detRatio XS XT φ v : ℂ) * (gram XS v e).det := by
  let γ : Matrix (Fin d) (Fin d) K := Matrix.of fun k i => e i k
  have he : e = fun i => ∑ k, γ k i • (Pi.single k 1 : Fin d → K) := by
    funext i; exact vec_expand (e i)
  have hφe : (fun i => φ *ᵥ e i) = fun i => ∑ k, γ k i • (φ *ᵥ (Pi.single k 1 : Fin d → K)) := by
    funext i
    conv_lhs => rw [vec_expand (e i)]
    rw [Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, γ, Matrix.of_apply]
  have hS := gram_re_ne XS hXS _ (std_li d) v
  rw [hφe, gram_change, he, gram_change, detRatio]
  rw [gram_det_real XT v (fun i => φ *ᵥ (Pi.single i 1 : Fin d → K)),
    gram_det_real XS v (fun i => (Pi.single i 1 : Fin d → K))]
  have hS' : (((gram XS v fun i => (Pi.single i 1 : Fin d → K)).det.re : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hS
  simp only [Complex.ofReal_re]
  rw [Complex.ofReal_div, div_mul_eq_mul_div, eq_div_iff hS']
  ring

theorem gram_ratHerm {d : ℕ} (K0 : Subfield K) (H : Matrix (Fin d) (Fin d) K)
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (hH : IsRatHerm K0 H X)
    (v0 : InfinitePlace K) (hv0 : IsConjAt v0) (f : Fin d → Fin d → K) :
    (gram X v0 f).det = v0.embedding (gramR H f) := by
  have hm : met X v0 = H.map v0.embedding := (hH.2 v0).2
  rw [gramR, RingHom.map_det]
  congr 1
  ext a b
  simp only [gram, Formalism.HN.gramPl, Matrix.of_apply, majAt_eq, hm, RingHom.mapMatrix_apply,
    Matrix.map_apply, dotProduct, Matrix.mulVec, cvec, Pi.star_apply, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hv0, Complex.star_def]

end Gram

section Lat

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def matEquiv {d : ℕ} (φ : Matrix (Fin d) (Fin d) K) (hφ : IsUnit φ.det) :
    (Fin d → K) ≃ₗ[𝓞 K] (Fin d → K) :=
  LinearEquiv.ofBijective ((Matrix.mulVecLin φ).restrictScalars (𝓞 K))
    ⟨Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det φ).mpr hφ),
     Matrix.mulVec_surjective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det φ).mpr hφ)⟩

theorem matLat_eq_map {d : ℕ} (φ : Matrix (Fin d) (Fin d) K) (hφ : IsUnit φ.det)
    (A : Submodule (𝓞 K) (Fin d → K)) :
    matLat φ A = A.map (matEquiv φ hφ : (Fin d → K) →ₗ[𝓞 K] (Fin d → K)) := by
  ext x
  rw [matLat, Submodule.mem_map, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem matLat_lattice {d : ℕ} (φ : Matrix (Fin d) (Fin d) K) (hφ : IsUnit φ.det)
    (L : Submodule (𝓞 K) (Fin d → K)) (hL : Submodule.IsLattice K L) :
    Submodule.IsLattice K (matLat φ L) := by
  have hsurj : Function.Surjective φ.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det φ).mpr hφ)
  refine ⟨(Submodule.IsLattice.fg (self := hL)).map _, ?_⟩
  have : ((matLat φ L : Submodule (𝓞 K) (Fin d → K)) : Set (Fin d → K)) =
      (Matrix.mulVecLin φ) '' (L : Set (Fin d → K)) := by
    rw [matLat, Submodule.map_coe]
    rfl
  rw [this, Submodule.span_image, Submodule.IsLattice.span_eq_top (self := hL), Submodule.map_top,
    LinearMap.range_eq_top]
  exact hsurj

theorem locS_map {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] (S : Submonoid R)
    (f : W ≃ₗ[R] W) (A : Submodule R W) :
    Formalism.HermitianLatticesTheory.locS S (A.map (f : W →ₗ[R] W)) = (Formalism.HermitianLatticesTheory.locS S A).map (f : W →ₗ[R] W) := by
  ext x
  rw [Submodule.mem_map_equiv, Formalism.HermitianLatticesTheory.locBasic_mem_locS, Formalism.HermitianLatticesTheory.locBasic_mem_locS]
  constructor
  · rintro ⟨s, hs, hx⟩
    refine ⟨s, hs, ?_⟩
    rw [Submodule.mem_map_equiv] at hx
    simpa [map_smul] using hx
  · rintro ⟨s, hs, hx⟩
    refine ⟨s, hs, ?_⟩
    rw [Submodule.mem_map_equiv]
    simpa [map_smul] using hx

theorem locS_locS_of_le {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    {S T : Submonoid R} (hST : S ≤ T) (A : Submodule R W) :
    Formalism.HermitianLatticesTheory.locS T (Formalism.HermitianLatticesTheory.locS S A) = Formalism.HermitianLatticesTheory.locS T A := by
  apply le_antisymm
  · intro x hx
    obtain ⟨t, ht, hx⟩ := Formalism.HermitianLatticesTheory.locBasic_mem_locS.mp hx
    obtain ⟨s, hs, hx⟩ := Formalism.HermitianLatticesTheory.locBasic_mem_locS.mp hx
    exact Formalism.HermitianLatticesTheory.locBasic_mem_locS.mpr ⟨s * t, T.mul_mem (hST hs) ht, by rwa [mul_smul]⟩
  · exact Formalism.HermitianLatticesTheory.locBasic_locS_mono T (Formalism.HermitianLatticesTheory.locBasic_le_locS S A)

theorem span_image {d : ℕ} (φ : Matrix (Fin d) (Fin d) K) (e : Fin d → Fin d → K) :
    Submodule.span (𝓞 K) (Set.range fun i => φ *ᵥ e i) =
      matLat φ (Submodule.span (𝓞 K) (Set.range e)) := by
  rw [matLat, Submodule.map_span, ← Set.range_comp]
  rfl

theorem isLocBasis_image {d : ℕ} (φ : Matrix (Fin d) (Fin d) K) (hφ : IsUnit φ.det)
    (L : Submodule (𝓞 K) (Fin d → K)) (w : HeightOneSpectrum (𝓞 K)) (e : Fin d → Fin d → K)
    (he : IsLocBasis L w e) : IsLocBasis (matLat φ L) w (fun i => φ *ᵥ e i) := by
  refine ⟨image_li φ hφ e he.1, ?_⟩
  have h2 := he.2
  unfold Formalism.HermitianLatticesTheory.loc at h2 ⊢
  rw [span_image, matLat_eq_map φ hφ, matLat_eq_map φ hφ, locS_map, locS_map, h2]

theorem hcompl_le_conj (w : HeightOneSpectrum (𝓞 K)) :
    Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal ≤ (conjPl w).asIdeal.primeCompl := by
  unfold Formalism.HermitianLatticesTheory.hcompl
  rw [Submonoid.closure_le]
  intro s hs
  show s ∉ (conjPl w).asIdeal
  intro hsc
  obtain ⟨u, hu, hus⟩ := (Ideal.mem_map_of_equiv (cO K) s).mp hsc
  apply hs.2 u _ hu
  rw [← hus]
  show (u : K) = star (star (u : K))
  rw [star_star]

theorem localization_eq_and_conj_eq_of_semilocalization_eq (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (A B : Submodule (𝓞 K) (Fin d → K))
    (h : Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal A = Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal B) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B ∧
      Formalism.HermitianLatticesTheory.localization₂ (conjPl w).asIdeal A = Formalism.HermitianLatticesTheory.localization₂ (conjPl w).asIdeal B := by
  have key : ∀ T : Submonoid (𝓞 K), Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal ≤ T →
      Formalism.HermitianLatticesTheory.locS T A = Formalism.HermitianLatticesTheory.locS T B := by
    intro T hT
    rw [← locS_locS_of_le hT A, ← locS_locS_of_le hT B]
    unfold Formalism.HermitianLatticesTheory.loc at h
    rw [h]
  exact ⟨key _ (Formalism.HermitianLatticesTheory.locBasic_hcompl_le (K := K) w.asIdeal), key _ (hcompl_le_conj w)⟩

theorem lidx_congr {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R)
    [p.IsPrime] (A A' B B' : Submodule R W) (hA : Formalism.HermitianLatticesTheory.localization₂ p A = Formalism.HermitianLatticesTheory.localization₂ p A')
    (hB : Formalism.HermitianLatticesTheory.localization₂ p B = Formalism.HermitianLatticesTheory.localization₂ p B') :
    Formalism.HermitianLatticesTheory.lidx p A B = Formalism.HermitianLatticesTheory.lidx p A' B' := by
  have hAB : Formalism.HermitianLatticesTheory.localization₂ p (A ⊓ B) = Formalism.HermitianLatticesTheory.localization₂ p (A' ⊓ B') := by
    unfold Formalism.HermitianLatticesTheory.localization₂ at hA hB ⊢
    rw [Formalism.HermitianLatticesTheory.locBasic_locS_inf, Formalism.HermitianLatticesTheory.locBasic_locS_inf, hA, hB]
  unfold Formalism.HermitianLatticesTheory.lidx Formalism.HermitianLatticesTheory.locLen
  rw [hA, hB, hAB]

theorem exists_coords {d : ℕ} (b : Fin d → Fin d → K) (hb : LinearIndependent K b)
    (f : Fin d → Fin d → K) : ∃ γ : Matrix (Fin d) (Fin d) K, f = fun i => ∑ k, γ k i • b k := by
  have hsp : Submodule.span K (Set.range b) = ⊤ :=
    hb.span_eq_top_of_card_eq_finrank' (by simp)
  let B := Basis.mk hb (by rw [hsp])
  refine ⟨Matrix.of fun k i => B.repr (f i) k, funext fun i => ?_⟩
  have h := (B.sum_repr (f i)).symm
  simpa [B, Basis.mk_apply] using h

end Lat

section Val

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem vw_prod (hV : ValBasic) (w : HeightOneSpectrum (𝓞 K)) {J : Type} (s : Finset J)
    (a : J → K) (ha : ∀ j, a j ≠ 0) : vw w (∏ j ∈ s, a j) = ∑ j ∈ s, vw w (a j) := by
  classical
  obtain ⟨hmul, -, -, -, h1, -, -⟩ := hV K w
  induction s using Finset.induction_on with
  | empty => simp [h1]
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj,
      hmul _ _ (ha j) (Finset.prod_ne_zero_iff.mpr fun i _ => ha i), ih]

theorem vw_pow (hV : ValBasic) (w : HeightOneSpectrum (𝓞 K)) (a : K) (ha : a ≠ 0) (n : ℕ) :
    vw w (a ^ n) = n * vw w a := by
  obtain ⟨hmul, -, -, -, h1, -, -⟩ := hV K w
  induction n with
  | zero => simp [h1]
  | succ n ih =>
    rw [pow_succ, hmul _ _ (pow_ne_zero n ha) ha, ih]
    push_cast; ring

theorem detRatio_ne [IsTotallyComplex K] {d : ℕ}
    (XS XT : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (hXS : ∀ v, IsUnit (XS v).det) (hXT : ∀ v, IsUnit (XT v).det)
    (φ : Matrix (Fin d) (Fin d) K) (hφ : IsUnit φ.det) (v : InfinitePlace K) :
    detRatio XS XT φ v ≠ 0 :=
  div_ne_zero (gram_re_ne XT hXT _ (image_li φ hφ _ (std_li d)) v)
    (gram_re_ne XS hXS _ (std_li d) v)

end Val

section Add

variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem lidx_add (p : Ideal R) [p.IsPrime] (A B C : Submodule R V)
    (hA : Submodule.IsLattice K A) (hB : Submodule.IsLattice K B) (hC : Submodule.IsLattice K C) :
    Formalism.HermitianLatticesTheory.lidx p A C = Formalism.HermitianLatticesTheory.lidx p A B + Formalism.HermitianLatticesTheory.lidx p B C := by
  have hfin : ∀ X Y : Submodule R V, X.FG → Formalism.HermitianLatticesTheory.locS (nonZeroDivisors R) Y = ⊤ →
      Module.length R (↥(Formalism.HermitianLatticesTheory.localization₂ p X) ⧸
        (Formalism.HermitianLatticesTheory.localization₂ p Y).comap (Formalism.HermitianLatticesTheory.localization₂ p X).subtype) ≠ ⊤ := by
    intro X Y hX hY
    obtain ⟨d, hd, hdY⟩ :=
      Formalism.HermitianLatticesTheory.indexBasic_denom (nonZeroDivisors R) X Y hX (by rw [hY]; exact le_top)
    exact Module.length_ne_top_iff.mpr (Formalism.HermitianLatticesTheory.indexBasic_finLen p X Y hX hd hdY)
  have hAt := Formalism.HermitianLatticesTheory.indexBasic_locS_top (K := K) A
    (Submodule.IsLattice.span_eq_top (self := hA))
  have hBt := Formalism.HermitianLatticesTheory.indexBasic_locS_top (K := K) B
    (Submodule.IsLattice.span_eq_top (self := hB))
  have hCt := Formalism.HermitianLatticesTheory.indexBasic_locS_top (K := K) C
    (Submodule.IsLattice.span_eq_top (self := hC))
  have hAfg : A.FG := Submodule.IsLattice.fg (self := hA)
  have hBfg : B.FG := Submodule.IsLattice.fg (self := hB)
  have hCfg : C.FG := Submodule.IsLattice.fg (self := hC)
  have hDt : Formalism.HermitianLatticesTheory.locS (nonZeroDivisors R) (A ⊓ B ⊓ C) = ⊤ := by
    rw [Formalism.HermitianLatticesTheory.locBasic_locS_inf, Formalism.HermitianLatticesTheory.locBasic_locS_inf, hAt, hBt, hCt]
    simp
  have hAD := hfin A _ hAfg hDt
  have hBD := hfin B _ hBfg hDt
  have hCD := hfin C _ hCfg hDt
  rw [Formalism.HermitianLatticesTheory.indexBasic_lidx_via p A C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left)
      inf_le_right hAD hCD,
    Formalism.HermitianLatticesTheory.indexBasic_lidx_via p A B (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left)
      (le_trans inf_le_left inf_le_right) hAD hBD,
    Formalism.HermitianLatticesTheory.indexBasic_lidx_via p B C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_right)
      inf_le_right hBD hCD]
  ring

end Add

theorem key_alg {J : Type} [Fintype J] (D : ℕ) (gE0 gE1 dR0 dR1 G0 G1 Ny κ ρ : ℂ)
    (gW0 gW1 dθ0 dθ1 gT0 gT1 Nz : J → ℂ)
    (h1 : gE1 = Ny * gE0) (h21 : gE1 = dR1 * G1) (h20 : gE0 = dR0 * G0)
    (h31 : dR1 = (κ * ρ) ^ D * ∏ j, dθ1 j) (h30 : dR0 = κ ^ D * ∏ j, dθ0 j)
    (h4 : ∀ j, gW1 j = Nz j * gW0 j) (h51 : ∀ j, gW1 j = dθ1 j * gT1 j)
    (h50 : ∀ j, gW0 j = dθ0 j * gT0 j) (hκ : κ ≠ 0) (hθ : ∀ j, dθ0 j ≠ 0) :
    ρ ^ D * G1 * ∏ j, (Nz j * gT0 j) = Ny * G0 * ∏ j, gT1 j := by
  have hP : (∏ j, dθ1 j) * ∏ j, gT1 j = (∏ j, dθ0 j) * ∏ j, (Nz j * gT0 j) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => by rw [← h51, h4, h50]; ring
  have hne : κ ^ D * ∏ j, dθ0 j ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hκ) (Finset.prod_ne_zero_iff.mpr fun j _ => hθ j)
  apply mul_right_cancel₀ hne
  calc (ρ ^ D * G1 * ∏ j, (Nz j * gT0 j)) * (κ ^ D * ∏ j, dθ0 j)
      = (κ * ρ) ^ D * G1 * ((∏ j, dθ0 j) * ∏ j, (Nz j * gT0 j)) := by rw [mul_pow]; ring
    _ = (κ * ρ) ^ D * G1 * ((∏ j, dθ1 j) * ∏ j, gT1 j) := by rw [hP]
    _ = gE1 * ∏ j, gT1 j := by rw [h21, h31]; ring
    _ = Ny * (dR0 * G0) * ∏ j, gT1 j := by rw [h1, h20]
    _ = (Ny * G0 * ∏ j, gT1 j) * (κ ^ D * ∏ j, dθ0 j) := by rw [h30]; ring

section Local

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem idx_change_img (hIC : IdxChange) {d : ℕ} (ι0 ι1 : Matrix (Fin d) (Fin d) K)
    (hι0 : IsUnit ι0.det) (hι1 : IsUnit ι1.det) (L0 L1 : Submodule (𝓞 K) (Fin d → K))
    (hL1 : Submodule.IsLattice K L1) (w : HeightOneSpectrum (𝓞 K))
    (e0 e1 : Fin d → Fin d → K) (he0 : IsLocBasis L0 w e0) (he1 : IsLocBasis L1 w e1) :
    ∃ γ : Matrix (Fin d) (Fin d) K,
      (fun i => ι1 *ᵥ e1 i) = (fun i => ∑ k, γ k i • (ι0 *ᵥ e0 k)) ∧
      idx w (matLat ι0 L0) (matLat ι1 L1) = vw w γ.det ∧
      idx (conjPl w) (matLat ι0 L0) (matLat ι1 L1) = vw (conjPl w) γ.det := by
  have li0 := image_li ι0 hι0 e0 he0.1
  obtain ⟨γ, hγ⟩ := exists_coords _ li0 (fun i => ι1 *ᵥ e1 i)
  have hlb0 := isLocBasis_image ι0 hι0 L0 w e0 he0
  have hlb1 := isLocBasis_image ι1 hι1 L1 w e1 he1
  rw [hγ] at hlb1
  obtain ⟨h1, h2⟩ := hIC K d (matLat ι1 L1) (matLat_lattice ι1 hι1 L1 hL1) _ li0 w γ hlb1
  obtain ⟨p1, p2⟩ := localization_eq_and_conj_eq_of_semilocalization_eq w _ _ hlb0.2
  refine ⟨γ, hγ, ?_, ?_⟩
  · rw [← h1]
    exact lidx_congr _ _ _ _ _ p1.symm rfl
  · rw [← h2]
    exact lidx_congr _ _ _ _ _ p2.symm rfl

theorem local_id (hV : ValBasic) (hIC : IdxChange) (hJw : JwGram) [IsTotallyComplex K]
    (K0 : Subfield K) (hK0 : IsCMSub K0) (v0 : InfinitePlace K) (hv0 : IsConjAt v0)
    (D : ℕ) (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (hXE : ∀ v, IsUnit (XE v).det)
    (XQ0 XQ1 : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (hXQ0 : ∀ v, IsUnit (XQ0 v).det)
    (hXQ1 : ∀ v, IsUnit (XQ1 v).det)
    (Lam0 Lam1 : Submodule (𝓞 K) (Fin D → K)) (hL1 : Submodule.IsLattice K Lam1)
    (ι0 ι1 : Matrix (Fin D) (Fin D) K) (hι0 : IsUnit ι0.det) (hι1 : IsUnit ι1.det)
    (J : Type) [Fintype J] (d : J → ℕ)
    (XW : ∀ j, InfinitePlace K → Matrix (Fin (d j)) (Fin (d j)) ℂ)
    (hXW : ∀ j v, IsUnit (XW j v).det)
    (M : ∀ j, Submodule (𝓞 K) (Fin (d j) → K)) (hM : ∀ j, Submodule.IsLattice K (M j))
    (HT0 HT1 : ∀ j, Matrix (Fin (d j)) (Fin (d j)) K)
    (XT0 XT1 : ∀ j, InfinitePlace K → Matrix (Fin (d j)) (Fin (d j)) ℂ)
    (hHT0 : ∀ j, IsRatHerm K0 (HT0 j) (XT0 j)) (hHT1 : ∀ j, IsRatHerm K0 (HT1 j) (XT1 j))
    (T0 T1 : ∀ j, Submodule (𝓞 K) (Fin (d j) → K))
    (hT0 : ∀ j, Submodule.IsLattice K (T0 j)) (hT1 : ∀ j, Submodule.IsLattice K (T1 j))
    (θ0 θ1 : ∀ j, Matrix (Fin (d j)) (Fin (d j)) K) (hθ0 : ∀ j, IsUnit (θ0 j).det)
    (hθ1 : ∀ j, IsUnit (θ1 j).det)
    (κ0 ρr : ℝ) (hκ : 0 < κ0) (ρ : K) (hρ : v0.embedding ρ = (ρr : ℂ)) (hρpos : 0 < ρr)
    (w : HeightOneSpectrum (𝓞 K)) (hρv : vw w ρ = 0)
    (hdet0 : detRatio XQ0 XE ι0 v0 = κ0 ^ D * ∏ j, detRatio (XT0 j) (XW j) (θ0 j) v0)
    (hdet1 : detRatio XQ1 XE ι1 v0 = (κ0 * ρr) ^ D * ∏ j, detRatio (XT1 j) (XW j) (θ1 j) v0)
    (G0 G1 : K) (e0 e1 : Fin D → Fin D → K) (he0 : IsLocBasis Lam0 w e0)
    (he1 : IsLocBasis Lam1 w e1)
    (hG0 : v0.embedding G0 = (gram XQ0 v0 e0).det) (hG1 : v0.embedding G1 = (gram XQ1 v0 e1).det)
    (f0 f1 : ∀ j, Fin (d j) → Fin (d j) → K) (hf0 : ∀ j, IsLocBasis (T0 j) w (f0 j))
    (hf1 : ∀ j, IsLocBasis (T1 j) w (f1 j)) :
    idx w (matLat ι0 Lam0) (matLat ι1 Lam1) + idx (conjPl w) (matLat ι0 Lam0) (matLat ι1 Lam1) =
      vw w G1 - vw w G0 + ∑ j, ((idx w (M j) (matLat (θ1 j) (T1 j)) -
          idx w (M j) (matLat (θ0 j) (T0 j))) +
        (idx (conjPl w) (M j) (matLat (θ1 j) (T1 j)) -
          idx (conjPl w) (M j) (matLat (θ0 j) (T0 j))) +
        (jw (HT1 j) w (T1 j) - jw (HT0 j) w (T0 j))) := by
  classical
  obtain ⟨hmul, hstar, -, -, -, -, -⟩ := hV K w
  obtain ⟨γ, hγ, hy1, hy2⟩ := idx_change_img hIC ι0 ι1 hι0 hι1 Lam0 Lam1 hL1 w e0 e1 he0 he1
  choose δ hδ hz1 hz2 using fun j => idx_change_img hIC (θ0 j) (θ1 j) (hθ0 j) (hθ1 j) (T0 j)
    (T1 j) (hT1 j) w (f0 j) (f1 j) (hf0 j) (hf1 j)
  have hc : ∀ j (u : HeightOneSpectrum (𝓞 K)), idx u (M j) (matLat (θ1 j) (T1 j)) =
      idx u (M j) (matLat (θ0 j) (T0 j)) + idx u (matLat (θ0 j) (T0 j)) (matLat (θ1 j) (T1 j)) :=
    fun j u => lidx_add (K := K) u.asIdeal _ _ _ (hM j) (matLat_lattice _ (hθ0 j) _ (hT0 j))
      (matLat_lattice _ (hθ1 j) _ (hT1 j))
  have hj0 : ∀ j, jw (HT0 j) w (T0 j) = - vw w (gramR (HT0 j) (f0 j)) := fun j =>
    hJw K K0 hK0 (d j) (HT0 j) (XT0 j) (hHT0 j) (T0 j) (hT0 j) w (f0 j) (hf0 j)
  have hj1 : ∀ j, jw (HT1 j) w (T1 j) = - vw w (gramR (HT1 j) (f1 j)) := fun j =>
    hJw K K0 hK0 (d j) (HT1 j) (XT1 j) (hHT1 j) (T1 j) (hT1 j) w (f1 j) (hf1 j)
  have hXT0 : ∀ j v, IsUnit (XT0 j v).det := fun j v => ((hHT0 j).2 v).1
  have hXT1 : ∀ j v, IsUnit (XT1 j v).det := fun j v => ((hHT1 j).2 v).1
  have h1 : (gram XE v0 (fun i => ι1 *ᵥ e1 i)).det = star (v0.embedding γ.det) *
      v0.embedding γ.det * (gram XE v0 (fun i => ι0 *ᵥ e0 i)).det := by
    rw [hγ]; exact gram_change _ _ _ _
  have h21 : (gram XE v0 (fun i => ι1 *ᵥ e1 i)).det =
      (detRatio XQ1 XE ι1 v0 : ℂ) * v0.embedding G1 := by
    rw [hG1]; exact gram_image XQ1 XE hXQ1 ι1 e1 v0
  have h20 : (gram XE v0 (fun i => ι0 *ᵥ e0 i)).det =
      (detRatio XQ0 XE ι0 v0 : ℂ) * v0.embedding G0 := by
    rw [hG0]; exact gram_image XQ0 XE hXQ0 ι0 e0 v0
  have h4 : ∀ j, (gram (XW j) v0 (fun i => θ1 j *ᵥ f1 j i)).det =
      star (v0.embedding (δ j).det) * v0.embedding (δ j).det *
        (gram (XW j) v0 (fun i => θ0 j *ᵥ f0 j i)).det := fun j => by
    rw [hδ j]; exact gram_change _ _ _ _
  have h51 : ∀ j, (gram (XW j) v0 (fun i => θ1 j *ᵥ f1 j i)).det =
      (detRatio (XT1 j) (XW j) (θ1 j) v0 : ℂ) * v0.embedding (gramR (HT1 j) (f1 j)) := fun j => by
    rw [← gram_ratHerm K0 (HT1 j) (XT1 j) (hHT1 j) v0 hv0]
    exact gram_image (XT1 j) (XW j) (hXT1 j) (θ1 j) (f1 j) v0
  have h50 : ∀ j, (gram (XW j) v0 (fun i => θ0 j *ᵥ f0 j i)).det =
      (detRatio (XT0 j) (XW j) (θ0 j) v0 : ℂ) * v0.embedding (gramR (HT0 j) (f0 j)) := fun j => by
    rw [← gram_ratHerm K0 (HT0 j) (XT0 j) (hHT0 j) v0 hv0]
    exact gram_image (XT0 j) (XW j) (hXT0 j) (θ0 j) (f0 j) v0
  have hθne : ∀ j, (detRatio (XT0 j) (XW j) (θ0 j) v0 : ℂ) ≠ 0 := fun j => by
    exact_mod_cast detRatio_ne (XT0 j) (XW j) (hXT0 j) (hXW j) (θ0 j) (hθ0 j) v0
  have hC := key_alg (J := J) D
    (gE0 := (gram XE v0 (fun i => ι0 *ᵥ e0 i)).det) (gE1 := (gram XE v0 (fun i => ι1 *ᵥ e1 i)).det)
    (dR0 := (detRatio XQ0 XE ι0 v0 : ℂ)) (dR1 := (detRatio XQ1 XE ι1 v0 : ℂ))
    (G0 := v0.embedding G0) (G1 := v0.embedding G1)
    (Ny := star (v0.embedding γ.det) * v0.embedding γ.det) (κ := (κ0 : ℂ)) (ρ := (ρr : ℂ))
    (gW0 := fun j => (gram (XW j) v0 (fun i => θ0 j *ᵥ f0 j i)).det)
    (gW1 := fun j => (gram (XW j) v0 (fun i => θ1 j *ᵥ f1 j i)).det)
    (dθ0 := fun j => (detRatio (XT0 j) (XW j) (θ0 j) v0 : ℂ))
    (dθ1 := fun j => (detRatio (XT1 j) (XW j) (θ1 j) v0 : ℂ))
    (gT0 := fun j => v0.embedding (gramR (HT0 j) (f0 j)))
    (gT1 := fun j => v0.embedding (gramR (HT1 j) (f1 j)))
    (Nz := fun j => star (v0.embedding (δ j).det) * v0.embedding (δ j).det)
    h1 h21 h20 (by rw [hdet1]; push_cast; ring) (by rw [hdet0]; push_cast; ring) h4 h51 h50
    (by exact_mod_cast hκ.ne') hθne
  have hK : ρ ^ D * G1 * ∏ j, (star (δ j).det * (δ j).det * gramR (HT0 j) (f0 j)) =
      star γ.det * γ.det * G0 * ∏ j, gramR (HT1 j) (f1 j) := by
    have hv0' : ∀ a : K, v0.embedding (star a) = starRingEnd ℂ (v0.embedding a) := hv0
    apply v0.embedding.injective
    simp only [map_mul, map_pow, map_prod, hv0', hρ]
    simp only [Complex.star_def] at hC
    exact hC
  have hG0ne : G0 ≠ 0 := fun h => gram_ne XQ0 hXQ0 e0 he0.1 v0 (by rw [← hG0, h, map_zero])
  have hG1ne : G1 ≠ 0 := fun h => gram_ne XQ1 hXQ1 e1 he1.1 v0 (by rw [← hG1, h, map_zero])
  have hγne : γ.det ≠ 0 := by
    intro h
    apply gram_ne XE hXE _ (image_li ι1 hι1 e1 he1.1) v0
    rw [h1, h, map_zero]; ring
  have hδne : ∀ j, (δ j).det ≠ 0 := by
    intro j h
    apply gram_ne (XW j) (hXW j) _ (image_li (θ1 j) (hθ1 j) (f1 j) (hf1 j).1) v0
    rw [h4 j, h, map_zero]; ring
  have hgT0ne : ∀ j, gramR (HT0 j) (f0 j) ≠ 0 := fun j h =>
    gram_ne (XT0 j) (hXT0 j) (f0 j) (hf0 j).1 v0
      (by rw [gram_ratHerm K0 (HT0 j) (XT0 j) (hHT0 j) v0 hv0, h, map_zero])
  have hgT1ne : ∀ j, gramR (HT1 j) (f1 j) ≠ 0 := fun j h =>
    gram_ne (XT1 j) (hXT1 j) (f1 j) (hf1 j).1 v0
      (by rw [gram_ratHerm K0 (HT1 j) (XT1 j) (hHT1 j) v0 hv0, h, map_zero])
  have hρne : ρ ≠ 0 := by
    intro h
    rw [h, map_zero] at hρ
    exact hρpos.ne' (by exact_mod_cast hρ.symm)
  have hv := congrArg (vw w) hK
  have hL : vw w (ρ ^ D * G1 * ∏ j, (star (δ j).det * (δ j).det * gramR (HT0 j) (f0 j))) =
      vw w G1 + ∑ j, (vw (conjPl w) (δ j).det + vw w (δ j).det + vw w (gramR (HT0 j) (f0 j))) := by
    have hne : ∀ j, star (δ j).det * (δ j).det * gramR (HT0 j) (f0 j) ≠ 0 := fun j =>
      mul_ne_zero (mul_ne_zero (star_ne_zero.mpr (hδne j)) (hδne j)) (hgT0ne j)
    rw [hmul _ _ (mul_ne_zero (pow_ne_zero _ hρne) hG1ne)
        (Finset.prod_ne_zero_iff.mpr fun j _ => hne j),
      hmul _ _ (pow_ne_zero _ hρne) hG1ne, vw_pow hV w ρ hρne, hρv, vw_prod hV w _ _ hne]
    simp only [mul_zero, zero_add]
    refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
    rw [hmul _ _ (mul_ne_zero (star_ne_zero.mpr (hδne j)) (hδne j)) (hgT0ne j),
      hmul _ _ (star_ne_zero.mpr (hδne j)) (hδne j), hstar]
  have hR : vw w (star γ.det * γ.det * G0 * ∏ j, gramR (HT1 j) (f1 j)) =
      vw (conjPl w) γ.det + vw w γ.det + vw w G0 + ∑ j, vw w (gramR (HT1 j) (f1 j)) := by
    rw [hmul _ _ (mul_ne_zero (mul_ne_zero (star_ne_zero.mpr hγne) hγne) hG0ne)
        (Finset.prod_ne_zero_iff.mpr fun j _ => hgT1ne j),
      hmul _ _ (mul_ne_zero (star_ne_zero.mpr hγne) hγne) hG0ne,
      hmul _ _ (star_ne_zero.mpr hγne) hγne, hstar, vw_prod hV w _ _ hgT1ne]
  have hsum : ∑ j, ((idx w (M j) (matLat (θ1 j) (T1 j)) -
          idx w (M j) (matLat (θ0 j) (T0 j))) +
        (idx (conjPl w) (M j) (matLat (θ1 j) (T1 j)) -
          idx (conjPl w) (M j) (matLat (θ0 j) (T0 j))) +
        (jw (HT1 j) w (T1 j) - jw (HT0 j) w (T0 j))) =
      ∑ j, (vw (conjPl w) (δ j).det + vw w (δ j).det + vw w (gramR (HT0 j) (f0 j))) -
        ∑ j, vw w (gramR (HT1 j) (f1 j)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hc j w, hc j (conjPl w), hz1 j, hz2 j, hj0 j, hj1 j]
    ring
  rw [hsum, hy1, hy2]
  rw [hL, hR] at hv
  linarith

end Local

section Supp

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem supp_add {α : Type*} (f g : α → ℝ) (hf : (Function.support f).Finite)
    (hg : (Function.support g).Finite) : (Function.support fun x => f x + g x).Finite :=
  (hf.union hg).subset (Function.support_add f g)

theorem supp_sum {α J : Type*} [Fintype J] (g : J → α → ℝ)
    (h : ∀ j, (Function.support (g j)).Finite) :
    (Function.support fun x => ∑ j, g j x).Finite := by
  refine (Set.finite_iUnion h).subset ?_
  intro x hx
  by_contra hc
  simp only [Set.mem_iUnion, not_exists, Function.mem_support, not_not] at hc
  exact hx (Finset.sum_eq_zero fun j _ => hc j)

theorem supp_conj (hV : ValBasic) (F : HeightOneSpectrum (𝓞 K) → ℝ)
    (hF : (Function.support F).Finite) : (Function.support fun w => F (conjPl w)).Finite := by
  have hinj : Function.Injective (conjPl : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 K)) :=
    fun a b h => by rw [← (hV K a).2.2.2.1, h, (hV K b).2.2.2.1]
  exact hF.preimage hinj.injOn

theorem G_finite (hV : ValBasic) (hIC : IdxChange) (hLB : LcvBasis) (hPF : ProdFormula)
    [IsTotallyComplex K] (v0 : InfinitePlace K) (hv0 : IsConjAt v0) (D : ℕ)
    (XQ : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (hXQ : ∀ v, IsUnit (XQ v).det)
    (abelian₂ : Submodule (𝓞 K) (Fin D → K)) (hLam : Submodule.IsLattice K abelian₂)
    (G : HeightOneSpectrum (𝓞 K) → K) (e : HeightOneSpectrum (𝓞 K) → Fin D → Fin D → K)
    (he : ∀ w, IsLocBasis abelian₂ w (e w)) (hG : ∀ w, v0.embedding (G w) = (gram XQ v0 (e w)).det) :
    (Function.support fun w => lw w * (vw w (G w) : ℝ)).Finite := by
  classical
  by_cases hne : Nonempty (HeightOneSpectrum (𝓞 K))
  swap
  · rw [not_nonempty_iff] at hne
    exact Set.toFinite _
  obtain ⟨w1⟩ := hne
  have hb := (he w1).1
  choose γ hγ using fun w => exists_coords (e w1) hb (e w)
  have hv0' : ∀ a : K, v0.embedding (star a) = starRingEnd ℂ (v0.embedding a) := hv0
  have hGne : ∀ w, G w ≠ 0 := fun w h => gram_ne XQ hXQ (e w) (he w).1 v0 (by rw [← hG w, h, map_zero])
  have hdet : ∀ w, G w = star (γ w).det * (γ w).det * G w1 := by
    intro w
    apply v0.embedding.injective
    rw [hG w, hγ w, gram_change, ← hG w1, map_mul, map_mul, hv0', Complex.star_def]
  have hγne : ∀ w, (γ w).det ≠ 0 := by
    intro w h
    apply hGne w
    rw [hdet w, h]; simp
  have hval : ∀ w, vw w (G w) = idx w (Submodule.span (𝓞 K) (Set.range (e w1))) abelian₂ +
      idx (conjPl w) (Submodule.span (𝓞 K) (Set.range (e w1))) abelian₂ + vw w (G w1) := by
    intro w
    obtain ⟨hmul, hstar, -, -, -, -, -⟩ := hV K w
    have hloc := he w
    rw [hγ w] at hloc
    obtain ⟨i1, i2⟩ := hIC K D abelian₂ hLam (e w1) hb w (γ w) hloc
    rw [hdet w, hmul _ _ (mul_ne_zero (star_ne_zero.mpr (hγne w)) (hγne w)) (hGne w1),
      hmul _ _ (star_ne_zero.mpr (hγne w)) (hγne w), hstar, i1, i2]
    ring
  have s1 := (hLB K D XQ hXQ abelian₂ hLam (e w1) hb).1
  have s2 := supp_conj hV _ s1
  have s3 := (hPF K (G w1) (hGne w1)).1
  refine (supp_add _ _ (supp_add _ _ s1 s2) s3).subset ?_
  intro w hw
  simp only [Function.mem_support] at hw ⊢
  rw [hval w] at hw
  rw [(hV K w).2.2.1]
  push_cast at hw
  convert hw using 1
  ring

end Supp

end StepBAux

open StepBAux in

theorem stepB_of (hPF : ProdFormula) (hLB : LcvBasis) (hIC : IdxChange) (hV : ValBasic)
    (hIm : ImageLcv) (hIL : IdxLcv) (hRH : RatHermLcv) (hJw : JwGram) (hFC : FinsumConj)
    (hLoc : LocBasisEx) : StepB := by
  intro K _ _ _ _ K0 hK0 v0 hv0 D XE hXE Tup μ0 μ hμc hμfin XQ hXQ abelian₂ hLam ι hι J _ d XW hXW M hM
    HT XT hHT T hT θ hθ κ hκ ρ ρr hρ hρ1 hρpos hρv hdetAll hdetV0 G e he hG hR R hRlat hRloc
  classical
  have hlw : ∀ w : HeightOneSpectrum (𝓞 K), lw (conjPl w) = lw w := fun w => (hV K w).2.2.1
  have hΛ0 : Submodule.IsLattice K (matLat (ι μ0) (abelian₂ μ0)) :=
    matLat_lattice _ (hι μ0) _ (hLam μ0)
  have hA0 : ∀ j, Submodule.IsLattice K (matLat (θ j μ0) (T j μ0)) := fun j =>
    matLat_lattice _ (hθ j μ0) _ (hT j μ0)
  have hXT : ∀ j t v, IsUnit (XT j t v).det := fun j t v => ((hHT j t).2 v).1
  choose f hf using fun j t w => hLoc K (d j) (T j t) (hT j t) w

  have hloc : ∀ w : HeightOneSpectrum (𝓞 K),
      idx w (matLat (ι μ0) (abelian₂ μ0)) R + idx (conjPl w) (matLat (ι μ0) (abelian₂ μ0)) R =
        vw w (G (μ w) w) - vw w (G μ0 w) + ∑ j, ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) -
            idx w (M j) (matLat (θ j μ0) (T j μ0))) +
          (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) -
            idx (conjPl w) (M j) (matLat (θ j μ0) (T j μ0))) +
          (jw (HT j (μ w)) w (T j (μ w)) - jw (HT j μ0) w (T j μ0))) := by
    intro w
    have hRc := hRloc (conjPl w)
    rw [hμc] at hRc
    have hx1 : idx w (matLat (ι μ0) (abelian₂ μ0)) R =
        idx w (matLat (ι μ0) (abelian₂ μ0)) (matLat (ι (μ w)) (abelian₂ (μ w))) :=
      lidx_congr _ _ _ _ _ rfl (hRloc w)
    have hx2 : idx (conjPl w) (matLat (ι μ0) (abelian₂ μ0)) R =
        idx (conjPl w) (matLat (ι μ0) (abelian₂ μ0)) (matLat (ι (μ w)) (abelian₂ (μ w))) :=
      lidx_congr _ _ _ _ _ rfl hRc
    rw [hx1, hx2]
    exact local_id hV hIC hJw K0 hK0 v0 hv0 D XE hXE (XQ μ0) (XQ (μ w)) (hXQ μ0) (hXQ (μ w))
      (abelian₂ μ0) (abelian₂ (μ w)) (hLam (μ w)) (ι μ0) (ι (μ w)) (hι μ0) (hι (μ w)) J d XW hXW M hM
      (fun j => HT j μ0) (fun j => HT j (μ w)) (fun j => XT j μ0) (fun j => XT j (μ w))
      (fun j => hHT j μ0) (fun j => hHT j (μ w)) (fun j => T j μ0) (fun j => T j (μ w))
      (fun j => hT j μ0) (fun j => hT j (μ w)) (fun j => θ j μ0) (fun j => θ j (μ w))
      (fun j => hθ j μ0) (fun j => hθ j (μ w)) (κ v0) (ρr (μ w)) (hκ v0) (ρ (μ w)) (hρ (μ w))
      (hρpos (μ w)) w (hρv w) (hdetAll v0) (hdetV0 (μ w)) (G μ0 w) (G (μ w) w) (e μ0 w)
      (e (μ w) w) (he μ0 w) (he (μ w) w) (hG μ0 w) (hG (μ w) w) (fun j => f j μ0 w)
      (fun j => f j (μ w) w) (fun j => hf j μ0 w) (fun j => hf j (μ w) w)

  have hFeq : ∀ w : HeightOneSpectrum (𝓞 K),
      lw w * ((vw w (G (μ w) w) : ℝ) + ∑ j,
        ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
         (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
         (jw (HT j (μ w)) w (T j (μ w)) : ℝ))) =
      lw w * (idx w (matLat (ι μ0) (abelian₂ μ0)) R : ℝ) +
        lw (conjPl w) * (idx (conjPl w) (matLat (ι μ0) (abelian₂ μ0)) R : ℝ) +
        lw w * (vw w (G μ0 w) : ℝ) +
        ∑ j, (lw w * (idx w (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) +
          lw (conjPl w) * (idx (conjPl w) (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) +
          lw w * (jw (HT j μ0) w (T j μ0) : ℝ)) := by
    intro w
    have hZ : vw w (G (μ w) w) + ∑ j, (idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) +
          idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) + jw (HT j (μ w)) w (T j (μ w))) =
        idx w (matLat (ι μ0) (abelian₂ μ0)) R + idx (conjPl w) (matLat (ι μ0) (abelian₂ μ0)) R +
          vw w (G μ0 w) + ∑ j, (idx w (M j) (matLat (θ j μ0) (T j μ0)) +
            idx (conjPl w) (M j) (matLat (θ j μ0) (T j μ0)) + jw (HT j μ0) w (T j μ0)) := by
      have h := hloc w
      have hs : ∑ j, (idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) +
            idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) +
            jw (HT j (μ w)) w (T j (μ w))) =
          ∑ j, ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) -
              idx w (M j) (matLat (θ j μ0) (T j μ0))) +
            (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) -
              idx (conjPl w) (M j) (matLat (θ j μ0) (T j μ0))) +
            (jw (HT j (μ w)) w (T j (μ w)) - jw (HT j μ0) w (T j μ0))) +
          ∑ j, (idx w (M j) (matLat (θ j μ0) (T j μ0)) +
            idx (conjPl w) (M j) (matLat (θ j μ0) (T j μ0)) + jw (HT j μ0) w (T j μ0)) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      linarith
    have hZR : ((vw w (G (μ w) w) : ℤ) : ℝ) + ∑ j,
        ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
         (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
         (jw (HT j (μ w)) w (T j (μ w)) : ℝ)) =
        (idx w (matLat (ι μ0) (abelian₂ μ0)) R : ℝ) + (idx (conjPl w) (matLat (ι μ0) (abelian₂ μ0)) R : ℝ) +
          (vw w (G μ0 w) : ℝ) + ∑ j, ((idx w (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) +
            (idx (conjPl w) (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) +
            (jw (HT j μ0) w (T j μ0) : ℝ)) := by
      exact_mod_cast hZ
    rw [hlw w, hZR]
    simp only [mul_add, Finset.mul_sum]

  have sx := (hIL K D XE hXE _ R hΛ0 hRlat).1
  have sx' := supp_conj hV _ sx
  have sa := G_finite hV hIC hLB hPF v0 hv0 D (XQ μ0) (hXQ μ0) (abelian₂ μ0) (hLam μ0) (G μ0) (e μ0)
    (he μ0) (hG μ0)
  have sb : ∀ j, (Function.support fun w : HeightOneSpectrum (𝓞 K) =>
      lw w * (idx w (M j) (matLat (θ j μ0) (T j μ0)) : ℝ)).Finite := fun j =>
    (hIL K (d j) (XW j) (hXW j) (M j) _ (hM j) (hA0 j)).1
  have sb' : ∀ j, (Function.support fun w : HeightOneSpectrum (𝓞 K) =>
      lw (conjPl w) * (idx (conjPl w) (M j) (matLat (θ j μ0) (T j μ0)) : ℝ)).Finite := fun j =>
    supp_conj hV _ (sb j)
  have sc : ∀ j, (Function.support fun w : HeightOneSpectrum (𝓞 K) =>
      lw w * (jw (HT j μ0) w (T j μ0) : ℝ)).Finite := fun j =>
    (hRH K K0 hK0 (d j) (HT j μ0) (XT j μ0) (hHT j μ0) (T j μ0) (hT j μ0)).1
  have sin : ∀ j, (Function.support fun w : HeightOneSpectrum (𝓞 K) =>
      lw w * (idx w (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) +
        lw (conjPl w) * (idx (conjPl w) (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) +
        lw w * (jw (HT j μ0) w (T j μ0) : ℝ)).Finite := fun j =>
    supp_add _ _ (supp_add _ _ (sb j) (sb' j)) (sc j)
  have sJ := supp_sum (fun j (w : HeightOneSpectrum (𝓞 K)) =>
      lw w * (idx w (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) +
        lw (conjPl w) * (idx (conjPl w) (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) +
        lw w * (jw (HT j μ0) w (T j μ0) : ℝ)) sin
  have s12 := supp_add _ _ sx sx'
  have s123 := supp_add _ _ s12 sa
  have sAll := supp_add _ _ s123 sJ
  refine ⟨sAll.subset ?_, ?_⟩
  · intro w hw
    simp only [Function.mem_support] at hw ⊢
    rwa [hFeq w] at hw

  have hsumF := finsum_congr hFeq
  rw [finsum_add_distrib s123 sJ, finsum_add_distrib s12 sa, finsum_add_distrib sx sx',
    finsum_sum_comm _ _ (fun j _ => sin j)] at hsumF
  have hcx : (∑ᶠ w, lw (conjPl w) * (idx (conjPl w) (matLat (ι μ0) (abelian₂ μ0)) R : ℝ)) =
      ∑ᶠ w, lw w * (idx w (matLat (ι μ0) (abelian₂ μ0)) R : ℝ) :=
    hFC K (fun w => lw w * (idx w (matLat (ι μ0) (abelian₂ μ0)) R : ℝ))
  have hcb : ∑ j, (∑ᶠ w, (lw w * (idx w (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) +
        lw (conjPl w) * (idx (conjPl w) (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) +
        lw w * (jw (HT j μ0) w (T j μ0) : ℝ))) =
      ∑ j, (2 * ∑ᶠ w, lw w * (idx w (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) +
        ∑ᶠ w, lw w * (jw (HT j μ0) w (T j μ0) : ℝ)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [finsum_add_distrib (supp_add _ _ (sb j) (sb' j)) (sc j),
      finsum_add_distrib (sb j) (sb' j),
      hFC K (fun w => lw w * (idx w (M j) (matLat (θ j μ0) (T j μ0)) : ℝ))]
    ring

  have hI1 := (hIL K D XE hXE _ R hΛ0 hRlat).2
  have hI2 := hIm K D (XQ μ0) XE (hXQ μ0) hXE (ι μ0) (hι μ0) (abelian₂ μ0) (hLam μ0)
  have hθne : ∀ j v, detRatio (XT j μ0) (XW j) (θ j μ0) v ≠ 0 := fun j v =>
    detRatio_ne (XT j μ0) (XW j) (hXT j μ0) (hXW j) (θ j μ0) (hθ j μ0) v
  have hlogv : ∀ v, Real.log (detRatio (XQ μ0) XE (ι μ0) v) =
      (D : ℝ) * Real.log (κ v) + ∑ j, Real.log (detRatio (XT j μ0) (XW j) (θ j μ0) v) := by
    intro v
    rw [hdetAll v, Real.log_mul (pow_ne_zero _ (hκ v).ne')
      (Finset.prod_ne_zero_iff.mpr fun j _ => hθne j v), Real.log_pow,
      Real.log_prod (fun j _ => hθne j v)]
  have hlogsum : ∑ v, Real.log (detRatio (XQ μ0) XE (ι μ0) v) =
      (D : ℝ) * ∑ v, Real.log (κ v) +
        ∑ j, ∑ v, Real.log (detRatio (XT j μ0) (XW j) (θ j μ0) v) := by
    rw [Finset.sum_congr rfl (fun v _ => hlogv v), Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_comm]
  have hN : (finrank ℚ K : ℝ) = 2 * (Formalism.HN.nPl K : ℝ) := by
    rw [IsTotallyComplex.finrank, Formalism.HN.nPl,
      NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
    push_cast; ring
  have hmean : (2 / (finrank ℚ K : ℝ)) * ((D : ℝ) * ∑ v, Real.log (κ v)) = (D : ℝ) * meanLog κ := by
    rw [meanLog, hN]
    rcases eq_or_ne (Formalism.HN.nPl K : ℝ) 0 with h0 | h0
    · rw [h0]; simp
    · field_simp
  have hθj : ∀ j, (2 / (finrank ℚ K : ℝ)) *
      ∑ v, Real.log (detRatio (XT j μ0) (XW j) (θ j μ0) v) =
      lcv (XW j) (M j) + (2 * ∑ᶠ w, lw w * (idx w (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) +
        ∑ᶠ w, lw w * (jw (HT j μ0) w (T j μ0) : ℝ)) := by
    intro j
    have e1 := hIm K (d j) (XT j μ0) (XW j) (hXT j μ0) (hXW j) (θ j μ0) (hθ j μ0) (T j μ0)
      (hT j μ0)
    have e2 := (hIL K (d j) (XW j) (hXW j) (M j) _ (hM j) (hA0 j)).2
    have e3 := (hRH K K0 hK0 (d j) (HT j μ0) (XT j μ0) (hHT j μ0) (T j μ0) (hT j μ0)).2
    linarith
  have hθsum : (2 / (finrank ℚ K : ℝ)) *
      ∑ j, ∑ v, Real.log (detRatio (XT j μ0) (XW j) (θ j μ0) v) =
      ∑ j, lcv (XW j) (M j) + ∑ j, (2 * ∑ᶠ w, lw w * (idx w (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) +
        ∑ᶠ w, lw w * (jw (HT j μ0) w (T j μ0) : ℝ)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => hθj j
  rw [hlogsum, mul_add] at hI2
  rw [hsumF, hcx, hcb]
  linarith

theorem reduction_second_step : StepB :=
  stepB_of prod_formula' covolume_via_basis index_change_formula valuation_basic_properties
    (imageLcv_of covolume_via_basis) (idxLcv_of covolume_via_basis)
    (ratHermLcv_of covolume_via_basis index_change_formula semilocal_basis_exists) (jwGram_of index_change_formula)
    finite_sum_conjugation semilocal_basis_exists

end Formalism.DivisionValues
