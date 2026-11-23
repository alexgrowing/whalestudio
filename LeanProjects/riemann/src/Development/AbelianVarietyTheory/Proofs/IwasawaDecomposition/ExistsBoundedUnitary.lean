import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteClassSetHermitianUnitaryOpenLevel

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.AnisoQuotient

theorem exists_short_notMem {X ι : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [Finite ι]
    (b : Module.Basis ι ℝ X) {c : ℝ} (hc : 0 < c) :
    ∃ R : ℝ, ∀ T : X →ₗ[ℝ] X, |LinearMap.det T| = 1 →
      (∀ x ∈ Submodule.span ℤ (Set.range b), x ≠ 0 → c ≤ ‖T x‖) →
      ∀ W : Submodule ℝ X, W ≠ ⊤ → ∃ x ∈ Submodule.span ℤ (Set.range b), x ∉ W ∧ ‖T x‖ ≤ R := by
  classical
  haveI := Fintype.ofFinite ι
  borelize X
  let μ : Measure X := Measure.addHaar
  have hF := ZSpan.isAddFundamentalDomain' b μ
  have hFl : μ (ZSpan.fundamentalDomain b) * 2 ^ Module.finrank ℝ X ≠ ⊤ :=
    ENNReal.mul_ne_top (ZSpan.fundamentalDomain_isBounded b).measure_lt_top.ne (by simp)
  have hB : μ (Metric.ball 0 c) ≠ 0 := (Metric.measure_ball_pos μ 0 hc).ne'
  obtain ⟨s, hs⟩ := ENNReal.exists_nat_mul_gt hB hFl
  refine ⟨c + s * (2 * c), fun T hT hmin W hW => ?_⟩
  have hT0 : LinearMap.det T ≠ 0 := fun h => by simp [h] at hT
  let e := T.equivOfDetNeZero hT0
  have he : ∀ x, e x = T x := fun x => rfl
  have hW' : W.map T < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => hW (eq_top_iff.2 fun x _ => ?_)
    obtain ⟨y, hy, hyx⟩ : T x ∈ W.map T := h ▸ Submodule.mem_top
    exact (e.injective hyx : y = x) ▸ hy
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ hW'
  let φ : X →L[ℝ] ℝ := LinearMap.toContinuousLinearMap f
  have hφ : 0 < ‖φ‖ := norm_pos_iff.2 fun h => hf0 (by ext x; exact congrArg (fun g : X →L[ℝ] ℝ => g x) h)
  obtain ⟨u, hu1, hu2⟩ := φ.exists_lt_apply_of_lt_opNorm (r := ‖φ‖ / 2) (by linarith)
  have hu0 : f u ≠ 0 := fun h => by
    have : ‖φ u‖ = 0 := norm_eq_zero.2 h
    linarith
  let A : X →ₗ[ℝ] X := LinearMap.transvection f (((s : ℝ) / f u) • u)
  have hA : ∀ y, A y = y + f y • ((s : ℝ) / f u) • u := fun y => LinearMap.transvection.apply _ _ _
  have hfv : f (((s : ℝ) / f u) • u) = s := by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hu0]
  have hdA : LinearMap.det A = 1 + s := by rw [LinearMap.transvection.det, hfv]
  haveI : Countable (Submodule.span ℤ (Set.range b)).toAddSubgroup :=
    inferInstanceAs (Countable (Submodule.span ℤ (Set.range b)))
  obtain ⟨x, hx0, y, hy, hxy⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    (s := T ⁻¹' (A '' Metric.ball 0 c)) hF
    (by rintro x ⟨y, hy, e⟩; exact ⟨-y, by simpa using hy, by rw [map_neg, map_neg, e]⟩)
    (((convex_ball 0 c).linear_image A).linear_preimage T)
    (by
      rw [Measure.addHaar_preimage_linearMap μ hT0, Measure.addHaar_image_linearMap, abs_inv, hT, hdA, inv_one,
        ENNReal.ofReal_one, one_mul]
      refine hs.trans_le (mul_le_mul_left ?_ _)
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal ((le_add_of_nonneg_left zero_le_one).trans (le_abs_self _)))
  have hyc : ‖y‖ < c := mem_ball_zero_iff.1 hy
  refine ⟨x, x.2, fun hxW => ?_, ?_⟩
  · have h1 : f (T x) = 0 := hf ⟨x, hxW, rfl⟩
    rw [← hxy, hA, map_add, map_smul, hfv, smul_eq_mul] at h1
    have h2 : f y = 0 := by
      have : f y * (1 + s) = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_right (by positivity)
    have h3 := hmin x x.2 (fun h => hx0 (Subtype.ext h))
    rw [← hxy, hA, h2, zero_smul, add_zero] at h3
    linarith
  · rw [← hxy, hA]
    refine (norm_add_le _ _).trans (add_le_add hyc.le ?_)
    have h1 : ‖f y‖ ≤ ‖φ‖ * c := (φ.le_opNorm y).trans (mul_le_mul_of_nonneg_left hyc.le hφ.le)
    have h2 : ‖φ‖ / 2 < ‖f u‖ := hu2
    have h3 : 0 < ‖f u‖ := norm_pos_iff.2 hu0
    rw [norm_smul, norm_smul, norm_div, Real.norm_natCast]
    calc ‖f y‖ * (s / ‖f u‖ * ‖u‖) ≤ (2 * ‖f u‖ * c) * (s / ‖f u‖ * 1) := by
          gcongr
          exact h1.trans (by gcongr; linarith)
      _ = s * (2 * c) := by field_simp

section Arch

variable {E I : Type} [Field E] [NumberField E] [Fintype I] {τ : I → (E →+* ℂ)}

omit [NumberField E] [Fintype I] in
theorem ringHom_app (x : E) (i : I) : Pi.ringHom τ x i = τ i x := rfl

omit [NumberField E] [Fintype I] in
theorem exists_norm_eq (hτ : Function.Surjective fun i => InfinitePlace.mk (τ i)) (φ : E →+* ℂ) :
    ∃ i, ∀ x, ‖φ x‖ = ‖τ i x‖ := by
  obtain ⟨i, hi⟩ := hτ (InfinitePlace.mk φ)
  exact ⟨i, fun x => (congrArg (fun w : InfinitePlace E => w x) hi).symm⟩

theorem exists_basis [IsTotallyComplex E] (hτ : Function.Bijective fun i => InfinitePlace.mk (τ i)) :
    ∃ b : Module.Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) ℝ (I → ℂ),
      ∀ k, b k = Pi.ringHom τ (integralBasis E k) := by
  have hli : LinearIndependent ℝ fun k => Pi.ringHom τ (integralBasis E k) := by
    refine Fintype.linearIndependent_iff.2 fun r hr k => ?_
    have h1 : ∀ i, ∑ k, (r k : ℂ) * τ i (integralBasis E k) = 0 := fun i => by
      simpa [Finset.sum_apply, ringHom_app] using congrFun hr i
    have h2 := Fintype.linearIndependent_iff.1 (canonicalEmbedding.latticeBasis E).linearIndependent
      (fun k => (r k : ℂ)) (funext fun φ => by
        simp only [canonicalEmbedding.latticeBasis_apply, Finset.sum_apply, Pi.smul_apply,
          canonicalEmbedding.apply_at, smul_eq_mul, Pi.zero_apply]
        obtain ⟨i, hi⟩ := hτ.2 (InfinitePlace.mk φ)
        rcases InfinitePlace.mk_eq_iff.1 hi with h | h
        · rw [← h]; exact h1 i
        · rw [← h]
          simpa using congrArg (starRingEnd ℂ) (h1 i)) k
    exact_mod_cast h2
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) = Module.finrank ℝ (I → ℂ) := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, IsTotallyComplex.finrank,
      Module.finrank_pi_fintype, Finset.sum_const, Complex.finrank_real_complex, Finset.card_univ,
      Fintype.card_of_bijective hτ, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, zero_add, smul_eq_mul, mul_comm]
  exact ⟨basisOfLinearIndependentOfCardEqFinrank hli hcard, fun k => by simp⟩

omit [NumberField E] in

theorem abs_det_eq_one {n : ℕ} {J G : Matrix (Fin n) (Fin n) (I → ℂ)} (hJ : IsUnit J.det)
    (hG : Formalism.UG.cT (starRingEnd (I → ℂ)) G * J * G = J) :
    |LinearMap.det ((Matrix.toLin' G).restrictScalars ℝ)| = 1 := by
  rw [LinearMap.det_restrictScalars, LinearMap.det_toLin']
  have h1 := congrArg Matrix.det hG
  rw [det_mul, det_mul, Formalism.UG.cT, det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h1
  have h2 : starRingEnd (I → ℂ) G.det * G.det = 1 := hJ.mul_left_cancel (by linear_combination h1)
  have h3 : Algebra.norm ℝ (starRingEnd (I → ℂ) G.det) = Algebra.norm ℝ G.det :=
    Algebra.norm_eq_of_algEquiv (AlgEquiv.piCongrRight fun _ : I => Complex.conjAe) G.det
  have h4 := congrArg (Algebra.norm ℝ) h2
  rw [map_mul, h3, map_one] at h4
  rcases mul_self_eq_one_iff.1 h4 with h | h <;> simp [h]

omit [NumberField E] in
theorem norm_hform_le {n : ℕ} (J : Matrix (Fin n) (Fin n) (I → ℂ)) {x y : Fin n → I → ℂ} {R : ℝ}
    (hx : ∀ a, ‖x a‖ ≤ R) (hy : ∀ a, ‖y a‖ ≤ R) (hR : 0 ≤ R) :
    ‖Formalism.UG.hform (starRingEnd (I → ℂ)) J x y‖ ≤ (∑ a, ∑ b, ‖J a b‖) * R ^ 2 := by
  rw [Formalism.UG.hform, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  refine (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)).trans ?_)
  rw [starRingEnd_apply, norm_star]
  calc ‖x a‖ * ‖J a b‖ * ‖y b‖ ≤ R * ‖J a b‖ * R := by gcongr; exacts [hx a, hy b]
    _ = _ := by ring

variable {σ : E →+* E}

omit [NumberField E] [Fintype I] in
theorem map_hform (hσ : ∀ i x, τ i (σ x) = star (τ i x)) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    Pi.ringHom τ (Formalism.UG.hform σ J x y) = Formalism.UG.hform (starRingEnd (I → ℂ)) (J.map (Pi.ringHom τ))
      (fun a => Pi.ringHom τ (x a)) (fun a => Pi.ringHom τ (y a)) := by
  funext i
  simp [Formalism.UG.hform, Finset.sum_apply, hσ, ringHom_app]

omit [NumberField E] in
theorem isIntegral_hform {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {N : ℤ} (hN : ∀ a b, IsIntegral ℤ ((N : E) * J a b))
    {x y : Fin n → E} (hx : ∀ a, IsIntegral ℤ (x a)) (hy : ∀ a, IsIntegral ℤ (y a)) :
    IsIntegral ℤ ((N : E) * Formalism.UG.hform σ J x y) := by
  simp only [Formalism.UG.hform, Finset.mul_sum]
  refine IsIntegral.sum _ fun a _ => IsIntegral.sum _ fun b _ => ?_
  have := ((IsIntegral.map σ.toIntAlgHom (hx a)).mul (hN a b)).mul (hy b)
  convert this using 1
  simp only [RingHom.toIntAlgHom_apply]
  ring

theorem exists_bounded_basis [IsTotallyComplex E] (hτ : Function.Bijective fun i => InfinitePlace.mk (τ i))
    (hσ : ∀ i x, τ i (σ x) = star (τ i x)) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : J.det ≠ 0)
    (han : ∀ x, x ≠ 0 → Formalism.UG.hform σ J x x ≠ 0) :
    ∃ R : ℝ, ∀ G : Matrix (Fin n) (Fin n) (I → ℂ),
      Formalism.UG.cT (starRingEnd (I → ℂ)) G * J.map (Pi.ringHom τ) * G = J.map (Pi.ringHom τ) →
      ∃ B : Matrix (Fin n) (Fin n) E, B.det ≠ 0 ∧ (∀ a b, IsIntegral ℤ (B a b)) ∧
        ∀ a b, ‖(G * B.map (Pi.ringHom τ)) a b‖ ≤ R := by
  classical
  obtain ⟨b, hb⟩ := exists_basis hτ
  obtain ⟨N, hN0, hN⟩ := HermClass.exists_int_mul_isIntegral E (Set.finite_range fun p : Fin n × Fin n => J p.1 p.2)
  let S : ℝ := ‖((N : ℤ) : I → ℂ)‖ * ∑ a, ∑ b, ‖J.map (Pi.ringHom τ) a b‖
  have hS : 0 ≤ S := by positivity
  obtain ⟨R, hR⟩ := exists_short_notMem (Pi.basis fun _ : Fin n => b) (c := (S + 1)⁻¹) (by positivity)
  have hL : ∀ v ∈ Submodule.span ℤ (Set.range (Pi.basis fun _ : Fin n => b)),
      ∃ x : Fin n → E, (∀ a, IsIntegral ℤ (x a)) ∧ v = fun a => Pi.ringHom τ (x a) := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨⟨a, k⟩, rfl⟩ := hv
      refine ⟨Pi.single a (integralBasis E k), fun a' => ?_, funext fun a' => ?_⟩
      · rw [Pi.single_apply]
        split_ifs
        · rw [integralBasis_apply]; exact (RingOfIntegers.basis E k).2
        · exact isIntegral_zero
      · rw [Pi.basis_apply, hb, Pi.single_apply, Pi.single_apply, apply_ite (Pi.ringHom τ), map_zero]
    | zero => exact ⟨0, fun _ => isIntegral_zero, funext fun a => by simp⟩
    | add v w _ _ hv hw =>
      obtain ⟨x, hx, rfl⟩ := hv
      obtain ⟨y, hy, rfl⟩ := hw
      exact ⟨x + y, fun a => (hx a).add (hy a), funext fun a => by simp⟩
    | smul m v _ hv =>
      obtain ⟨x, hx, rfl⟩ := hv
      exact ⟨m • x, fun a => (hx a).zsmul m, funext fun a => by simp⟩
  refine ⟨R, fun G hG => ?_⟩
  have hJu : IsUnit (J.map (Pi.ringHom τ)).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact hJ.isUnit.map _
  have hR' := hR _ (abs_det_eq_one hJu hG) (fun v hv hv0 => by
    obtain ⟨x, hx, rfl⟩ := hL v hv
    have hx0 : x ≠ 0 := fun h => hv0 (funext fun a => by simp [h])
    have hi := isIntegral_hform (σ := σ) (fun a b => hN _ ⟨(a, b), rfl⟩) hx hx
    obtain ⟨φ, hφ⟩ := NumberField.exists_conjugate_one_le_norm (K := E) (α := ⟨_, hi⟩) (fun h =>
      mul_ne_zero (Int.cast_ne_zero.2 hN0) (han x hx0) (congrArg (fun z : 𝓞 E => (z : E)) h))
    obtain ⟨i, hi'⟩ := exists_norm_eq hτ.2 φ
    rw [hi'] at hφ
    have h1 : 1 ≤ ‖Pi.ringHom τ ((N : E) * Formalism.UG.hform σ J x x)‖ :=
      hφ.trans (norm_le_pi_norm (Pi.ringHom τ ((N : E) * Formalism.UG.hform σ J x x)) i)
    rw [map_mul, map_intCast, map_hform hσ, ← hG, ← GlobalTheory.Mem.ClassFinite.hform_mulVec] at h1
    change _ ≤ ‖G *ᵥ fun a => Pi.ringHom τ (x a)‖
    generalize (G *ᵥ fun a => Pi.ringHom τ (x a)) = y at h1
    have h2 : 1 ≤ S * ‖y‖ ^ 2 := by
      refine h1.trans ((norm_mul_le _ _).trans ?_)
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (norm_hform_le _ (norm_le_pi_norm y) (norm_le_pi_norm y) (norm_nonneg _))
        (norm_nonneg _)
    by_contra h3
    have h4 : ‖y‖ * (S + 1) < 1 := by
      rwa [not_le, ← one_div, lt_div_iff₀ (by positivity)] at h3
    have h5 := norm_nonneg y
    have h6 : 0 ≤ ‖y‖ * S := by positivity
    nlinarith)
  let Sx : Set (Fin n → E) := {x | (∀ a, IsIntegral ℤ (x a)) ∧ ‖G *ᵥ fun a => Pi.ringHom τ (x a)‖ ≤ R}
  have hsp : Submodule.span E Sx = ⊤ := by
    by_contra h
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 h)
    let g : (Fin n → I → ℂ) →ₗ[I → ℂ] (I → ℂ) :=
      ∑ a, Pi.ringHom τ (f (Pi.single a 1)) • LinearMap.proj a
    have hg : ∀ x : Fin n → E, g (fun a => Pi.ringHom τ (x a)) = Pi.ringHom τ (f x) := fun x => by
      rw [LinearMap.pi_apply_eq_sum_univ f x, map_sum]
      simp only [g, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul, map_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [mul_comm]
      congr 3
      funext j
      simp [Pi.single_apply, eq_comm]
    haveI : Nonempty I := hτ.2.nonempty
    obtain ⟨v, hv, hvW, hvR⟩ := hR' (LinearMap.ker (g.restrictScalars ℝ)) (fun h' => hf0 (LinearMap.ext fun x => by
      have : g.restrictScalars ℝ (fun a => Pi.ringHom τ (x a)) = 0 := LinearMap.mem_ker.1 (h' ▸ Submodule.mem_top)
      exact (Pi.ringHom τ).injective (by rw [← hg, LinearMap.zero_apply, map_zero]; exact this)))
    obtain ⟨x, hx, rfl⟩ := hL v hv
    refine hvW ?_
    have : f x = 0 := hf (Submodule.subset_span ⟨hx, hvR⟩)
    change g _ = 0
    rw [hg, this, map_zero]
  obtain ⟨v, hv, -, hli⟩ := Submodule.exists_fun_fin_finrank_span_eq E Sx
  have hr : n = Module.finrank E (Submodule.span E Sx) := by rw [hsp, finrank_top]; simp
  refine ⟨(Matrix.of fun k => v (Fin.cast hr k))ᵀ, ?_, fun a k => (hv _).1 a, fun a k => ?_⟩
  · rw [det_transpose]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1
      (hli.comp _ (Fin.cast_injective hr)))).ne_zero
  · exact (norm_le_pi_norm (G *ᵥ fun a => Pi.ringHom τ (v (Fin.cast hr k) a)) a).trans (hv _).2

omit [NumberField E] in
theorem cT_mul {A : Type} [CommRing A] (s : A →+* A) {n : ℕ} (P Q : Matrix (Fin n) (Fin n) A) :
    Formalism.UG.cT s (P * Q) = Formalism.UG.cT s Q * Formalism.UG.cT s P := by
  rw [Formalism.UG.cT, Matrix.map_mul, transpose_mul]; rfl

omit [NumberField E] in
theorem gram_apply {n : ℕ} (J B : Matrix (Fin n) (Fin n) E) (a b : Fin n) :
    (Formalism.UG.cT σ B * J * B) a b = Formalism.UG.hform σ J (fun k => B k a) (fun k => B k b) := by
  simp only [Formalism.UG.hform, Formalism.UG.cT, mul_apply, Finset.sum_mul, transpose_apply, map_apply]
  exact Finset.sum_comm

theorem exists_bounded_unitary [IsTotallyComplex E] (hτ : Function.Bijective fun i => InfinitePlace.mk (τ i))
    (hσ : ∀ i x, τ i (σ x) = star (τ i x)) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : J.det ≠ 0)
    (han : ∀ x, x ≠ 0 → Formalism.UG.hform σ J x x ≠ 0) :
    ∃ (R : ℝ) (𝓒 : Set (Matrix (Fin n) (Fin n) E)), 𝓒.Finite ∧ ∀ G : Matrix (Fin n) (Fin n) (I → ℂ),
      Formalism.UG.cT (starRingEnd (I → ℂ)) G * J.map (Pi.ringHom τ) * G = J.map (Pi.ringHom τ) →
      ∃ u ∈ Formalism.UG.UJ σ J, ∃ B : Matrix (Fin n) (Fin n) E, ∃ C ∈ 𝓒, u.1 = B * C ∧ (∀ a b, IsIntegral ℤ (B a b)) ∧
        ∀ a b, ‖(G * B.map (Pi.ringHom τ)) a b‖ ≤ R := by
  classical
  obtain ⟨R, hR⟩ := exists_bounded_basis hτ hσ hJ han
  obtain ⟨N, hN0, hN⟩ := HermClass.exists_int_mul_isIntegral E (Set.finite_range fun p : Fin n × Fin n => J p.1 p.2)
  let R' : ℝ := ‖((N : ℤ) : I → ℂ)‖ * ((∑ a, ∑ b, ‖J.map (Pi.ringHom τ) a b‖) * |R| ^ 2)
  have hfin : ((fun x : E => (N : E) * x) ⁻¹' {x | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ R'}).Finite :=
    (Embeddings.finite_of_norm_le E ℂ R').preimage (mul_right_injective₀ (Int.cast_ne_zero.2 hN0)).injOn
  have hfin' := Set.Finite.pi' fun _ : Fin n => Set.Finite.pi' fun _ : Fin n => hfin
  let rep : Matrix (Fin n) (Fin n) E → Matrix (Fin n) (Fin n) E := fun T =>
    Classical.epsilon fun P => P.det ≠ 0 ∧ Formalism.UG.cT σ P * J * P = T
  refine ⟨R, _, hfin'.image fun T => (rep T)⁻¹, fun G hG => ?_⟩
  obtain ⟨B, hB0, hBi, hBR⟩ := hR G hG
  obtain ⟨hP0, hP⟩ : (rep (Formalism.UG.cT σ B * J * B)).det ≠ 0 ∧ Formalism.UG.cT σ (rep (Formalism.UG.cT σ B * J * B)) * J *
      rep (Formalism.UG.cT σ B * J * B) = Formalism.UG.cT σ B * J * B :=
    Classical.epsilon_spec (p := fun P => P.det ≠ 0 ∧ Formalism.UG.cT σ P * J * P = Formalism.UG.cT σ B * J * B) ⟨B, hB0, rfl⟩
  refine ⟨GeneralLinearGroup.mkOfDetNeZero (B * (rep (Formalism.UG.cT σ B * J * B))⁻¹) ?_, ?_, B, _,
    ⟨Formalism.UG.cT σ B * J * B, fun a b => ?_, rfl⟩, rfl, hBi, hBR⟩
  · rw [det_mul]
    exact mul_ne_zero hB0 (isUnit_nonsing_inv_det _ hP0.isUnit).ne_zero
  · change Formalism.UG.cT σ (B * (rep (Formalism.UG.cT σ B * J * B))⁻¹) * J * (B * (rep (Formalism.UG.cT σ B * J * B))⁻¹) = J
    generalize rep (Formalism.UG.cT σ B * J * B) = P at hP0 hP
    have h1 : Formalism.UG.cT σ (B * P⁻¹) * J * (B * P⁻¹) = Formalism.UG.cT σ P⁻¹ * (Formalism.UG.cT σ B * J * B) * P⁻¹ := by
      simp only [cT_mul, Matrix.mul_assoc]
    have h2 : Formalism.UG.cT σ (P * P⁻¹) * J * (P * P⁻¹) = Formalism.UG.cT σ P⁻¹ * (Formalism.UG.cT σ P * J * P) * P⁻¹ := by
      simp only [cT_mul, Matrix.mul_assoc]
    rw [h1, ← hP, ← h2, mul_nonsing_inv _ hP0.isUnit]
    simp [Formalism.UG.cT]
  · rw [gram_apply]
    refine ⟨isIntegral_hform (fun a b => hN _ ⟨(a, b), rfl⟩) (fun k => hBi k a) (fun k => hBi k b), fun φ => ?_⟩
    obtain ⟨i, hi⟩ := exists_norm_eq hτ.2 φ
    rw [hi]
    refine (norm_le_pi_norm (Pi.ringHom τ ((N : E) * Formalism.UG.hform σ J (fun k => B k a) fun k => B k b)) i).trans ?_
    rw [map_mul, map_intCast, map_hform hσ, ← hG, ← GlobalTheory.Mem.ClassFinite.hform_mulVec]
    refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    exact norm_hform_le _ (fun k => (hBR k a).trans (le_abs_self R)) (fun k => (hBR k b).trans (le_abs_self R))
      (abs_nonneg R)

end Arch

theorem exists_compact_mul {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] {n : ℕ}
    {C : Set A} (hC : IsCompact C) {𝓒 : Set (Matrix (Fin n) (Fin n) A)} (h𝓒 : 𝓒.Finite) :
    ∃ C' : Set A, IsCompact C' ∧ ∀ M ∈ 𝓒, ∀ P Q : Matrix (Fin n) (Fin n) A, (∀ a b, P a b ∈ C) → (∀ a b, Q a b ∈ C) →
      ∀ a b, (P * M * Q) a b ∈ C' := by
  let S : Set (Matrix (Fin n) (Fin n) A) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => C
  have hS : IsCompact S := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hC
  refine ⟨⋃ M ∈ 𝓒, ⋃ a, ⋃ b, (fun p : Matrix (Fin n) (Fin n) A × Matrix (Fin n) (Fin n) A => (p.1 * M * p.2) a b) ''
    (S ×ˢ S), h𝓒.isCompact_biUnion fun M _ => isCompact_iUnion fun a => isCompact_iUnion fun b => (hS.prod hS).image
      (((continuous_fst.matrix_mul continuous_const).matrix_mul continuous_snd).matrix_elem a b),
    fun M hM P Q hP hQ a b => ?_⟩
  exact Set.mem_iUnion₂.2 ⟨M, hM, Set.mem_iUnion₂.2 ⟨a, b, (P, Q), ⟨fun a _ b _ => hP a b, fun a _ b _ => hQ a b⟩, rfl⟩⟩

theorem hform_ne_zero {D : D7} {V : HSp D} (h : IsAniso V) (x : Fin V.rank → D.host.E) (hx : x ≠ 0) :
    Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram x x ≠ 0 := fun h0 => by
  refine h 1 (Matrix.of fun a _ => x a) ⟨one_pos, linearIndependent_unique_iff.2 hx, ?_⟩
  ext a b
  rw [Matrix.zero_apply, ← h0]
  simp only [Formalism.UG.hform, Formalism.UG.cT, mul_apply, Finset.sum_mul, transpose_apply, map_apply, of_apply]
  rw [Finset.sum_comm]

theorem mt_mul {D : D7} (V : HSp D) (x y : GA D V) : mt V (x * y) = mt V x * mt V y := by
  unfold Formalism.L2.Theta.mt
  rw [map_mul, Units.val_mul]

theorem mt_mul_rat {D : D7} (V : HSp D) (x u : GA D V) {B M : Matrix (Fin V.rank) (Fin V.rank) D.host.E}
    (h : mt V u = (B * M).map (incA D)) : mt V (x * u) = mt V x * B.map (incA D) * M.map (incA D) * 1 := by
  rw [mt_mul, h, Matrix.map_mul, Matrix.mul_one, Matrix.mul_assoc]

theorem exists_finite_part (D : D7) (V : HSp D) : ∃ C : Set (Af D.host.F ⊗[D.host.F] D.host.E), IsCompact C ∧
    ∀ g : GA D V, ∃ γ ∈ GQ V, ∀ B : Matrix (Fin V.rank) (Fin V.rank) D.host.E, (∀ a b, IsIntegral ℤ (B a b)) →
      ∀ a b, finPart D ((mt V (g * γ) * B.map (incA D)) a b) ∈ C := by
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
  obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram
  obtain ⟨S, hS⟩ := GlobalTheory.Mem.ClassFinite.exists_finset_classes _ _ _ (GlobalTheory.DefiniteQuotient.cmExt D) _ _
    (GlobalTheory.DefiniteQuotient.gram_hermND V) _ (GlobalTheory.Mass.isOpen_stdLevel D.sp.cm.sig V.gram)
  obtain ⟨C, hC, hCe⟩ := (GlobalTheory.Mass.intTens_open_compact D.host.F D.host.E).2
  obtain ⟨C₁, hC₁, hCe₁⟩ := exists_compact_mul hC
    (S.finite_toSet.image fun s => (HA.mat (Af D.host.F) D.sp.cm.sig V.gram s⁻¹).1)
  refine ⟨C₁, hC₁, fun g => ?_⟩
  obtain ⟨γ₀, s, hs, k, hk, e⟩ := hS (π g⁻¹)
  obtain ⟨γ, hγ, hγe⟩ : (γ₀.1 : HA (Af D.host.F) D.sp.cm.sig V.gram) ∈
      (GlobalTheory.Mass.ratIn (AF D.host.F) D.sp.cm.sig V.gram).map π := by
    rw [hπ.map_ratIn]; exact γ₀.2
  refine ⟨γ, hγ, fun B hBi a b => ?_⟩
  have e' : π (g * γ) = k⁻¹ * s⁻¹ := by
    have e1 : π g⁻¹ = π γ * (s * k) := by rw [hγe]; exact e
    rw [map_mul, ← inv_inv g, map_inv, e1]; group
  generalize g * γ = x at e'
  have e3 : (mt V x).map (finPart D) = (HA.mat (Af D.host.F) D.sp.cm.sig V.gram k⁻¹).1 *
      (HA.mat (Af D.host.F) D.sp.cm.sig V.gram s⁻¹).1 := by
    have := congrArg Units.val (hπ x)
    rw [e'] at this
    exact this.symm
  have e4 : finPart D ((mt V x * B.map (incA D)) a b) =
      ((mt V x).map (finPart D) * (B.map (incA D)).map (finPart D)) a b :=
    congrFun (congrFun (Matrix.map_mul (L := mt V x) (M := B.map (incA D)) (f := finPart D)) a) b
  rw [e4, e3]
  refine hCe₁ _ ⟨s, hs, rfl⟩ _ _ (fun a b => hCe _ ((GlobalTheory.Mass.mem_stdLevel _ _ _).1 (inv_mem hk) a b).1)
    (fun a b => hCe _ ?_) a b
  exact Subring.subset_closure (Or.inl ⟨⟨B a b, ⟨_, hBi a b⟩, rfl⟩, rfl⟩)

theorem exists_real_part (D : D7) (V : HSp D) (hV : IsAniso V) {θ : InfF D} (hθ : IsInfFam θ) :
    ∃ (R : ℝ) (𝓒 : Set (Matrix (Fin V.rank) (Fin V.rank) D.host.E)), 𝓒.Finite ∧ ∀ x : GA D V,
      ∃ u ∈ GQ V, ∃ B : Matrix (Fin V.rank) (Fin V.rank) D.host.E, ∃ M ∈ 𝓒, mt V u = (B * M).map (incA D) ∧
        (∀ a b, IsIntegral ℤ (B a b)) ∧ ∀ a b τ, ‖θ τ (infPart D ((mt V x * B.map (incA D)) a b))‖ ≤ R := by
  have hcm := GlobalTheory.DefiniteQuotient.cmExt D
  haveI := hcm.2.1
  obtain ⟨R, 𝓒, h𝓒, H⟩ := exists_bounded_unitary (σ := (D.sp.cm.sig : D.host.E →+* D.host.E))
    (GlobalTheory.CMTypePlaces.mk_tauE_bijective D) (fun τ x => hcm.2.2.2 _ x) (GlobalTheory.DefiniteQuotient.gram_hermND V).2
    (hform_ne_zero hV)
  refine ⟨R, 𝓒, h𝓒, fun x => ?_⟩
  let p : AE D →+* (D.what₂.Tau → ℂ) := Pi.ringHom fun τ => (θ τ).comp (infPart D)
  have hp : ∀ M : Matrix (Fin V.rank) (Fin V.rank) D.host.E,
      (M.map (incA D)).map p = M.map (Pi.ringHom (tauE D)) := fun M => by
    ext i j τ; exact GlobalTheory.FockCompare.comp_incA hθ τ _
  obtain ⟨u, hu, B, M, hM, hum, hBi, hBR⟩ := H ((mt V x).map p) (by
    have hu : Formalism.UG.cT (cA D) (mt V x) * V.gram.map (incA D) * mt V x = V.gram.map (incA D) := x.2
    have e : (Formalism.UG.cT (cA D) (mt V x)).map p = Formalism.UG.cT (starRingEnd _) ((mt V x).map p) := by
      ext i j τ; exact GlobalTheory.FockCompare.comp_cA hθ τ _
    have := congrArg (fun M => M.map p) hu
    simpa only [Matrix.map_mul, e, hp] using this)
  refine ⟨⟨_, GlobalTheory.Mem.ClassFinite.baseChange_mem (AF D.host.F) _ V.gram u hu⟩, ⟨u, hu, rfl⟩, B, M, hM,
    congrArg (fun X => X.map (incA D)) hum, hBi, fun a b τ => ?_⟩
  have := hBR a b
  rw [← hp, ← Matrix.map_mul] at this
  exact (norm_le_pi_norm (p ((mt V x * B.map (incA D)) a b)) τ).trans this

theorem exists_compact : ∀ (D : D7) (V : HSp D), IsAniso V → ∃ K : Set (GA D V), IsCompact K ∧ ∀ g, ∃ γ ∈ GQ V, ∃ k ∈ K, g = γ * k := by
  intro D V hV
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  obtain ⟨C₁, hC₁, H₁⟩ := exists_finite_part D V
  obtain ⟨R, 𝓒, h𝓒, H₂⟩ := exists_real_part D V hV hθ
  obtain ⟨C₂, hC₂, hCe₂⟩ := GlobalTheory.StabCompact.exists_compact_adele D θ hθ R C₁ hC₁
  obtain ⟨C₃, hC₃, hCe₃⟩ := exists_compact_mul ((hC₂.insert 0).insert 1) (h𝓒.image fun M => M.map (incA D))
  obtain ⟨K, hK, hKe⟩ := GlobalTheory.StabCompact.exists_compact_of_entries (AF D.host.F) D.sp.cm.sig V.gram
    (GlobalTheory.DefiniteQuotient.gram_hermND V).2 C₃ hC₃
  refine ⟨K⁻¹, hK.inv, fun g => ?_⟩
  obtain ⟨γ, hγ, h₁⟩ := H₁ g⁻¹
  obtain ⟨u, hu, B, M, hM, hum, hBi, hBR⟩ := H₂ (g⁻¹ * γ)
  refine ⟨γ * u, mul_mem hγ hu, (g⁻¹ * γ * u)⁻¹, Set.inv_mem_inv.2 (hKe _ fun a b => ?_), by group⟩
  change mt V (g⁻¹ * γ * u) a b ∈ C₃
  rw [mt_mul_rat V _ _ hum]
  refine hCe₃ _ ⟨M, hM, rfl⟩ _ _ (fun a b => Or.inr (Or.inr (hCe₂ _ (h₁ B hBi a b) (hBR a b)))) (fun a b => ?_) a b
  rw [Matrix.one_apply]
  split_ifs
  exacts [Or.inl rfl, Or.inr (Or.inl rfl)]

end GlobalTheory.Mem.AnisoQuotient
