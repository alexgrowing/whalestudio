import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigRank
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.BalProjOpen

open GlobalTheory.BalProj

theorem eigSp_eq_range {O k : Type} [Field k] {n : ℕ} (B : O → Matrix (Fin n) (Fin n) k) (χ : O → k)
    (P : Matrix (Fin n) (Fin n) k) (hP : ∀ a, P * B a = χ a • P) (hfix : ∀ c ∈ eigSp B χ, c ᵥ* P = c) :
    eigSp B χ = LinearMap.range (Matrix.vecMulLinear P) := by
  ext c
  constructor
  · intro hc
    exact ⟨c, hfix c hc⟩
  · rintro ⟨d, rfl⟩ a
    show (d ᵥ* P) ᵥ* B a = χ a • (d ᵥ* P)
    rw [Matrix.vecMul_vecMul, hP a, Matrix.vecMul_smul]

theorem finrank_range_eq_trace {k : Type} [Field k] {n : ℕ} (P : Matrix (Fin n) (Fin n) k) (hP : P * P = P) :
    (Module.finrank k (LinearMap.range (Matrix.vecMulLinear P)) : k) = P.trace := by
  have h1 : Matrix.vecMulLinear P = Matrix.toLin' Pᵀ := by
    ext c i
    simp [Matrix.mulVec_transpose]
  have hi : IsIdempotentElem (Matrix.toLin' Pᵀ) := by
    show Matrix.toLin' Pᵀ * Matrix.toLin' Pᵀ = Matrix.toLin' Pᵀ
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.transpose_mul, hP]
  rw [h1, ← (LinearMap.IsIdempotentElem.isProj_range _ hi).trace, Matrix.trace_toLin'_eq, Matrix.trace_transpose]

theorem eigRank_cast_eq_trace {O R k : Type} [CommRing O] [CommRing R] [Field k] (φ : R →+* k) {n : ℕ}
    (A : O → Matrix (Fin n) (Fin n) R) (hmul : ∀ a b, A (a * b) = A a * A b) (χ : O → R)
    {J : Type} [Fintype J] (f : J → R) (b : J → O) (h1 : ∑ i, f i * χ (b i) = 1)
    (h2 : ∀ a, ∑ i, f i • A (a * b i) = χ a • ∑ i, f i • A (b i)) :
    (eigRank φ A χ : k) = φ (∑ i, f i • A (b i)).trace := by
  set P := ∑ i, f i • A (b i) with hPdef
  have hPA : ∀ a, P * A a = χ a • P := by
    intro a
    rw [← h2 a, hPdef, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, ← hmul, mul_comm]
  have hPP : P * P = P := by
    conv_lhs => arg 2; rw [hPdef]
    rw [Finset.mul_sum]
    simp_rw [mul_smul_comm, hPA, smul_smul, ← Finset.sum_smul, h1, one_smul]
  set Pb := P.map φ
  have hPbA : ∀ a, Pb * (A a).map φ = φ (χ a) • Pb := by
    intro a
    rw [← Matrix.map_mul, hPA a]
    ext i j
    simp [Pb]
  have hfix : ∀ c ∈ eigSp (fun a => (A a).map φ) (fun a => φ (χ a)), c ᵥ* Pb = c := by
    intro c hc
    have : Pb = ∑ i, φ (f i) • (A (b i)).map φ := by
      ext i j
      simp [Pb, hPdef, Matrix.sum_apply, map_sum]
    rw [this, Matrix.vecMul_sum]
    simp_rw [Matrix.vecMul_smul, hc _, smul_smul, ← Finset.sum_smul, ← map_mul, ← map_sum, h1, map_one, one_smul]
  have hPbPb : Pb * Pb = Pb := by rw [← Matrix.map_mul, hPP]
  unfold eigRank
  rw [eigSp_eq_range _ _ Pb hPbA hfix, finrank_range_eq_trace Pb hPbPb]
  simp [Pb, Matrix.trace, map_sum]

theorem isOpen_eigRank_eq_of_datum {O R K : Type} [CommRing O] [CommRing R] [Field K] [CharZero K] (j : K →+* R)
    {n : ℕ} (A : O → Matrix (Fin n) (Fin n) R) (hmul : ∀ a b, A (a * b) = A a * A b) (χ : O → R)
    {J : Type} [Fintype J] (f : J → R) (b : J → O) (h1 : ∑ i, f i * χ (b i) = 1)
    (h2 : ∀ a, ∑ i, f i • A (a * b i) = χ a • ∑ i, f i • A (b i)) (N : ℕ) :
    IsOpen {𝔭 : PrimeSpectrum R | eigRank (algebraMap R 𝔭.asIdeal.ResidueField) A χ = N} := by
  set t := (∑ i, f i • A (b i)).trace with ht
  have key : ∀ (𝔭 : PrimeSpectrum R) (M : ℕ),
      eigRank (algebraMap R 𝔭.asIdeal.ResidueField) A χ = M ↔ t - M ∈ 𝔭.asIdeal := by
    intro 𝔭 M
    haveI : CharZero 𝔭.asIdeal.ResidueField :=
      (RingHom.charZero_iff ((algebraMap R 𝔭.asIdeal.ResidueField).comp j).injective).1 inferInstance
    rw [← Nat.cast_inj (R := 𝔭.asIdeal.ResidueField), eigRank_cast_eq_trace _ A hmul χ f b h1 h2,
      ← Ideal.algebraMap_residueField_eq_zero, map_sub, map_natCast, sub_eq_zero]
  have hle : ∀ 𝔭 : PrimeSpectrum R, eigRank (algebraMap R 𝔭.asIdeal.ResidueField) A χ ≤ n := by
    intro 𝔭
    unfold eigRank
    exact (Submodule.finrank_le _).trans (by simp)
  have hset : {𝔭 : PrimeSpectrum R | eigRank (algebraMap R 𝔭.asIdeal.ResidueField) A χ = N} =
      (⋃ M ∈ (Finset.range (n + 1)).filter (· ≠ N), PrimeSpectrum.zeroLocus {t - (M : R)})ᶜ := by
    ext 𝔭
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iUnion, Finset.mem_filter, Finset.mem_range,
      PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe, exists_prop, not_exists, not_and]
    constructor
    · intro h M hM hM'
      exact hM.2 (((key 𝔭 M).2 hM').symm.trans h)
    · intro h
      by_contra hne
      exact h _ ⟨Nat.lt_succ_of_le (hle 𝔭), hne⟩ ((key 𝔭 _).1 rfl)
  rw [hset]
  exact (isClosed_biUnion_finset fun M _ => PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl

theorem exists_datum {E : Type} [Field E] [NumberField E] (F : IntermediateField ℚ ℂ)
    (hF : ∀ (τ : E →+* ℂ) (a : E), τ a ∈ F) (R : Type) [CommRing R] (iF : F →+* R) (n : ℕ)
    (A : 𝓞 E → Matrix (Fin n) (Fin n) R) (hadd : ∀ a b, A (a + b) = A a + A b) (τ : E →+* ℂ) :
    ∃ (J : Type) (_ : Fintype J) (f : J → R) (b : J → 𝓞 E),
      ∑ i, f i * embR F hF iF τ (b i) = 1 ∧
      ∀ a, ∑ i, f i • A (a * b i) = embR F hF iF τ a • ∑ i, f i • A (b i) := by
  classical
  set bO := RingOfIntegers.basis E
  set bE := integralBasis E
  have hnd := _root_.traceForm_nondegenerate ℚ E
  obtain ⟨d, hd⟩ : ∃ d, d = (Algebra.traceForm ℚ E).dualBasis hnd bE := ⟨_, rfl⟩
  have hdr : ∀ i j, Algebra.trace ℚ E (bE i * d j) = if i = j then 1 else 0 := by
    intro i j
    rw [← Algebra.traceForm_apply, hd]
    exact LinearMap.BilinForm.apply_dualBasis_right hnd (Algebra.traceForm_isSymm ℚ) bE i j
  have hdrep0 : ∀ (y : E) i, d.repr y i = Algebra.trace ℚ E (y * bE i) := by
    intro y i
    rw [hd, LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
  set g : E →+* R := iF.comp (τ.codRestrict F.toSubfield (hF τ))
  have hg : ∀ a : 𝓞 E, embR F hF iF τ a = g (a : E) := fun a => rfl
  have hbE : ∀ i, bE i = (bO i : E) := fun i => integralBasis_apply E i
  have hrep : ∀ (y : E) i, bE.repr y i = Algebra.trace ℚ E (y * d i) := by
    intro y i
    conv_rhs => rw [← bE.sum_repr y]
    rw [Finset.sum_mul, map_sum]
    simp_rw [smul_mul_assoc, map_smul, hdr, smul_eq_mul, mul_ite, _root_.mul_one]
    simp
  have hdrep : ∀ y : E, y = ∑ i, Algebra.trace ℚ E (y * bE i) • d i := by
    intro y
    conv_lhs => rw [← d.sum_repr y]
    simp_rw [hdrep0]
  have hA : ∑ i, d i * bE i = 1 := by
    rw [← sub_eq_zero]
    refine hnd.1 _ fun y => ?_
    rw [Algebra.traceForm_apply, sub_mul, map_sub, _root_.one_mul, Finset.sum_mul, map_sum, sub_eq_zero,
      Algebra.trace_eq_matrix_trace bE y, Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, hrep]
    congr 1
    ring
  have hB : ∀ (a : 𝓞 E) j, ∑ i, ((bO.repr (a * bO i) j : ℤ) : E) * d i = (a : E) * d j := by
    intro a j
    conv_rhs => rw [hdrep ((a : E) * d j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : Algebra.trace ℚ E ((a : E) * d j * bE i) = bE.repr ((a : E) * bE i) j := by
      rw [hrep]; congr 1; ring
    have h2 : bE.repr ((a : E) * bE i) j = ((bO.repr (a * bO i) j : ℤ) : ℚ) := by
      rw [hbE]
      exact integralBasis_repr_apply E (a * bO i) j
    rw [h1, h2, Algebra.smul_def, eq_ratCast, Rat.cast_intCast]
  have hexp : ∀ x : 𝓞 E, A x = ∑ j, bO.repr x j • A (bO j) := by
    intro x
    let Aa : 𝓞 E →+ Matrix (Fin n) (Fin n) R := AddMonoidHom.mk' A hadd
    conv_lhs => rw [← bO.sum_repr x]
    exact (map_sum Aa _ _).trans (Finset.sum_congr rfl fun j _ => map_zsmul Aa _ _)
  refine ⟨_, inferInstance, fun i => g (d i), bO, ?_, ?_⟩
  · simp_rw [hg, ← map_mul, ← map_sum, ← hbE, hA, map_one]
  · intro a
    calc ∑ i, g (d i) • A (a * bO i)
        = ∑ i, ∑ j, (g (d i) * ((bO.repr (a * bO i) j : ℤ) : R)) • A (bO j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hexp (a * bO i), Finset.smul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← smul_smul, Int.cast_smul_eq_zsmul]
      _ = ∑ j, (∑ i, g (d i) * ((bO.repr (a * bO i) j : ℤ) : R)) • A (bO j) := by
          rw [Finset.sum_comm]
          simp_rw [Finset.sum_smul]
      _ = ∑ j, (embR F hF iF τ a * g (d j)) • A (bO j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          congr 1
          rw [hg, ← map_mul, ← hB a j, map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_mul g, map_intCast g, _root_.mul_comm]
      _ = _ := by
          rw [Finset.smul_sum]
          simp_rw [smul_smul]

theorem isOpen_eigRank_eq : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (F : IntermediateField ℚ ℂ) (hF : ∀ (τ : E →+* ℂ) (a : E), τ a ∈ F) (R : Type) [CommRing R] (iF : F →+* R) (n : ℕ) (A : 𝓞 E → Matrix (Fin n) (Fin n) R), A 1 = 1 → (∀ a b, A (a + b) = A a + A b) → (∀ a b, A (a * b) = A a * A b) → ∀ (τ : E →+* ℂ) (N : ℕ), IsOpen {𝔭 : PrimeSpectrum R | GlobalTheory.BalProj.eigRank (algebraMap R 𝔭.asIdeal.ResidueField) A (GlobalTheory.BalProj.embR F hF iF τ) = N} := by
  intro E _ _ _ F hF R _ iF n A h1 hadd hmul τ N
  obtain ⟨J, _, f, b, hf1, hf2⟩ := exists_datum F hF R iF n A hadd τ
  exact isOpen_eigRank_eq_of_datum iF A hmul _ f b hf1 hf2 N

end GlobalTheory.BalProjOpen
