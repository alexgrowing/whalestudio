import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsEigenProjectorRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsColsDetNeZeroOfMul
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.PolyChartSmoothFractionLift

open NumberField

namespace GlobalTheory.Reg.CellChart

section Lin
open Matrix

theorem det_of_inCell {R : Type} [CommRing R] {n r : ℕ} (ix : Fin r ↪ Fin n) (u : Matrix (Fin n) (Fin r) R)
    (h : InCell ix u) : (u.submatrix ix id).det = 1 := by
  rw [Matrix.det_of_lowerTriangular (u.submatrix ix id) (fun i j hij => h.1 i j hij)]
  simp [h.2]

theorem rank_of_quasi_idem {L : Type} [Field L] {n : ℕ} (P : Matrix (Fin n) (Fin n) L) (N : L) (hN : N ≠ 0)
    (hP : P * P = N • P) (S : Submodule L (Fin n → L)) (hS : ∀ x, x ∈ S ↔ P.mulVec x = N • x) :
    P.rank = Module.finrank L S := by
  have : LinearMap.range P.mulVecLin = S := by
    ext x
    rw [hS, LinearMap.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hP, Matrix.smul_mulVec]
    · intro h
      refine ⟨N⁻¹ • x, ?_⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_smul, h, smul_smul, inv_mul_cancel₀ hN, one_smul]
  rw [Matrix.rank, this]

theorem exists_minor {L : Type} [Field L] {n r : ℕ} (P : Matrix (Fin n) (Fin n) L) (N : L) (hN : N ≠ 0)
    (ix : Fin r ↪ Fin n) (u : Matrix (Fin n) (Fin r) L) (hu : P * u = N • u) (hc : InCell ix u) :
    ∃ κ : Fin r → Fin n, (P.submatrix ix κ).det ≠ 0 := by
  have h : P.submatrix ix id * u = N • u.submatrix ix id := by
    ext i j
    have := congrFun (congrFun hu (ix i)) j
    simpa [Matrix.mul_apply] using this
  obtain ⟨κ, hκ⟩ := GlobalTheory.exists_cols_det_ne_zero_of_mul (P.submatrix ix id) u (by
    rw [h, Matrix.det_smul, det_of_inCell ix u hc]; simp [hN])
  exact ⟨κ, hκ⟩

theorem eq_of_rows {L : Type} [Field L] {n r m : ℕ} (P : Matrix (Fin n) (Fin n) L) (hr : P.rank = r) (N : L)
    (hN : N ≠ 0) (ix κ : Fin r → Fin n) (hd : (P.submatrix ix κ).det ≠ 0) (u : Matrix (Fin n) (Fin m) L)
    (hu : P * u = N • u) : u = P.submatrix id κ * (P.submatrix ix κ)⁻¹ * u.submatrix ix id := by
  have h : P.submatrix ix id * u = N • u.submatrix ix id := by
    ext i j
    have := congrFun (congrFun hu (ix i)) j
    simpa [Matrix.mul_apply] using this
  have h1 := ((GlobalTheory.rank_minor_factorisation L n r P hr ix).1 κ hd)
  have h2 : N • u = N • (P.submatrix id κ * (P.submatrix ix κ)⁻¹ * u.submatrix ix id) := by
    rw [← hu, ← Matrix.mul_smul, ← h, ← Matrix.mul_assoc, ← h1]
  exact smul_right_injective _ hN h2

end Lin

theorem exists_projector (E K : Type) [Field E] [NumberField E] [Field K] (emb : (E →+* ℂ) → (E →+* K))
    (hemb : Function.Injective emb) (O : Type) [CommRing O] [IsDomain O] [Algebra O K] [IsFractionRing O K]
    (A : Type) [CommRing A] (α : O →+* A) (n : ℕ) (ρ : 𝓞 E →+* Matrix (Fin n) (Fin n) A) (τ : E →+* ℂ) :
    ∃ (N : O) (p : Matrix (Fin n) (Fin n) A), N ≠ 0 ∧ ∀ (R : Type) [CommRing R] [Algebra K R] (f : A →+* R),
      f.comp α = (algebraMap K R).comp (algebraMap O K) →
      (p.map f * p.map f = f (α N) • p.map f) ∧ ∀ x : Fin n → R,
        (∀ b : 𝓞 E, ((ρ b).map f).mulVec x = algebraMap K R (emb τ (b : E)) • x) ↔
          (p.map f).mulVec x = f (α N) • x := by
  obtain ⟨m, a, κ, h⟩ := GlobalTheory.exists_eigen_projector_ringOfIntegers E K emb hemb τ
  obtain ⟨N, hN⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) κ
  choose t ht using hN
  refine ⟨N, ∑ k, α (t k) • ρ (a k), nonZeroDivisors.ne_zero N.2, fun R _ _ f hf => ?_⟩
  have hf' : ∀ o, f (α o) = algebraMap K R (algebraMap O K o) := fun o => RingHom.congr_fun hf o
  obtain ⟨h1, h2⟩ := h R n (f.mapMatrix.comp ρ)
  set π := ∑ k, algebraMap K R (κ k) • (f.mapMatrix.comp ρ) (a k) with hπ
  have hp : (∑ k, α (t k) • ρ (a k)).map f = f (α N) • π := by
    ext i j
    have ht' : ∀ i, algebraMap O K (t i) = algebraMap O K N * κ i := fun i => (ht i).trans (Algebra.smul_def _ _)
    simp only [hπ, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, hf', ht',
      Finset.mul_sum, RingHom.comp_apply, RingHom.mapMatrix_apply, mul_assoc]
  have hu : IsUnit (f (α N)) := by
    rw [hf']
    exact (IsLocalization.map_units K N).map _
  have hππ : π * π = π := by
    ext i j
    have := h2 (fun k => π k j) (fun b => by
      funext k
      have := congrFun (congrFun (h1 b) k) j
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this)
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun this i
  rw [hp]
  refine ⟨by rw [Matrix.smul_mul, Matrix.mul_smul, hππ], fun x => ⟨fun hx => ?_, fun hx b => ?_⟩⟩
  · rw [Matrix.smul_mulVec, h2 x hx]
  · rw [Matrix.smul_mulVec] at hx
    have hx' : π.mulVec x = x := hu.smul_left_cancel.mp hx
    have := congrArg (fun M => Matrix.mulVec M x) (h1 b)
    simp only [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, hx'] at this
    exact this

theorem loc_descr {K O A F : Type} [Field K] [CommRing O] [IsDomain O] [Algebra O K] [IsFractionRing O K]
    [CommRing A] [Field F] [Algebra K F] (α : O →+* A) (i : A →+* F)
    (hi : i.comp α = (algebraMap K F).comp (algebraMap O K)) (g : A) (hg : i g ≠ 0) (x : F)
    (hx : x ∈ Algebra.adjoin K (insert (i g)⁻¹ (Set.range i))) :
    ∃ (a : A) (b : O) (m : ℕ), b ≠ 0 ∧ x * i (α b * g ^ m) = i a := by
  have hi' : ∀ o, i (α o) = algebraMap K F (algebraMap O K o) := fun o => RingHom.congr_fun hi o
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with rfl | ⟨a, rfl⟩
    · exact ⟨1, 1, 1, one_ne_zero, by simp [hg]⟩
    · exact ⟨a, 1, 0, one_ne_zero, by simp⟩
  | algebraMap k =>
    obtain ⟨⟨a, b⟩, h⟩ := IsLocalization.surj (nonZeroDivisors O) k
    refine ⟨α a, b, 0, nonZeroDivisors.ne_zero b.2, ?_⟩
    rw [pow_zero, mul_one, hi', hi', ← map_mul, h]
  | add x y _ _ hx hy =>
    obtain ⟨a, b, m, hb, h⟩ := hx
    obtain ⟨a', b', m', hb', h'⟩ := hy
    refine ⟨a * (α b' * g ^ m') + a' * (α b * g ^ m), b * b', m + m', mul_ne_zero hb hb', ?_⟩
    simp only [map_add, map_mul, map_pow] at h h' ⊢
    rw [← h, ← h']; ring
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, m, hb, h⟩ := hx
    obtain ⟨a', b', m', hb', h'⟩ := hy
    refine ⟨a * a', b * b', m + m', mul_ne_zero hb hb', ?_⟩
    simp only [map_add, map_mul, map_pow] at h h' ⊢
    rw [← h, ← h']; ring

theorem loc_lift {K O A F L : Type} [Field K] [CommRing O] [IsDomain O] [Algebra O K] [IsFractionRing O K]
    [CommRing A] [Field F] [Algebra K F] [Field L] [Algebra K L] (α : O →+* A) (i : A →+* F)
    (hinj : Function.Injective i)
    (hi : i.comp α = (algebraMap K F).comp (algebraMap O K)) (g : A) (hg : i g ≠ 0) (f : A →+* L)
    (hf : f.comp α = (algebraMap K L).comp (algebraMap O K)) (hfg : f g ≠ 0) :
    ∃ ψ : Algebra.adjoin K (insert (i g)⁻¹ (Set.range i)) →ₐ[K] L,
      ∀ a (h : i a ∈ Algebra.adjoin K (insert (i g)⁻¹ (Set.range i))), ψ ⟨i a, h⟩ = f a := by
  have hi' : ∀ o, i (α o) = algebraMap K F (algebraMap O K o) := fun o => RingHom.congr_fun hi o
  have hf' : ∀ o, f (α o) = algebraMap K L (algebraMap O K o) := fun o => RingHom.congr_fun hf o
  set R₀ := Algebra.adjoin K (insert (i g)⁻¹ (Set.range i)) with hR₀
  have hm : ∀ a, i a ∈ R₀ := fun a => Algebra.subset_adjoin (Or.inr ⟨a, rfl⟩)
  let i₀ : A →+* R₀ := i.codRestrict R₀.toSubring hm
  letI : Algebra A R₀ := i₀.toAlgebra
  let S : Submonoid A := (IsUnit.submonoid R₀).comap i₀ ⊓ (IsUnit.submonoid L).comap f
  have hO : ∀ b : O, i₀ (α b) = algebraMap K R₀ (algebraMap O K b) := fun b => Subtype.ext (hi' b)
  have hK : ∀ b : O, b ≠ 0 → IsUnit (algebraMap O K b) := fun b hb =>
    IsLocalization.map_units K (⟨b, mem_nonZeroDivisors_of_ne_zero hb⟩ : nonZeroDivisors O)
  have hgS : g ∈ S := ⟨IsUnit.of_mul_eq_one (⟨(i g)⁻¹, Algebra.subset_adjoin (Or.inl rfl)⟩ : R₀)
    (Subtype.ext (mul_inv_cancel₀ hg)), isUnit_iff_ne_zero.mpr hfg⟩
  have hbS : ∀ b : O, b ≠ 0 → α b ∈ S := fun b hb =>
    ⟨show IsUnit (i₀ (α b)) from hO b ▸ (hK b hb).map _, show IsUnit (f (α b)) from hf' b ▸ (hK b hb).map _⟩
  haveI : IsLocalization S R₀ := by
    refine (isLocalization_iff S R₀).mpr ⟨fun y => y.2.1, fun z => ?_, fun {x y} h => ⟨1, ?_⟩⟩
    · obtain ⟨a, b, m, hb, h⟩ := loc_descr α i hi g hg z z.2
      exact ⟨⟨a, ⟨α b * g ^ m, S.mul_mem (hbS b hb) (S.pow_mem hgS m)⟩⟩, Subtype.ext h⟩
    · rw [hinj (congrArg Subtype.val h)]
  let φ : R₀ →+* L := IsLocalization.lift (M := S) (g := f) (fun y => y.2.2)
  have hφ : ∀ a, φ (i₀ a) = f a := fun a => IsLocalization.lift_eq (M := S) (g := f) (fun y => y.2.2) a
  have hc : φ.comp (algebraMap K R₀) = algebraMap K L := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors O) (RingHom.ext fun o => ?_)
    simp only [RingHom.comp_apply]
    rw [← hO, hφ, hf']
  exact ⟨⟨φ, fun k => RingHom.congr_fun hc k⟩, fun a h => hφ a⟩

end GlobalTheory.Reg.CellChart
