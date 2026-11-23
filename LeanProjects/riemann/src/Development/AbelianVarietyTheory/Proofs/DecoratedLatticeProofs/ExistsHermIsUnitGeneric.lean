import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.GramMatrixAdjoint
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthogonalIdempotentsOfSumMulEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHermitianDetNeZeroTwoStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixFieldStableRangeOneDetNeZeroStatement
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ExistsBaseRingOfConjugationFixedTensor
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf

noncomputable section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HermTransversal

theorem isUnit_glue {R ι : Type} [CommRing R] [Fintype ι] {n : ℕ} (e t : ι → R)
    (A : ι → Matrix (Fin n) (Fin n) R) (h1 : ∑ i, e i = 1) (ho : ∀ i j, i ≠ j → e i * e j = 0)
    (ht : ∀ i, t i * (A i).det = e i) : IsUnit (∑ i, e i • A i) := by
  classical
  have hee : ∀ i, e i * e i = e i := fun i => by
    have : e i * ∑ j, e j = e i * e i := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_single i (fun j _ hj => ho i j (Ne.symm hj)) (by simp)
    rw [← this, h1, mul_one]
  have hs : ∀ i, e i • (∑ j, e j • A j) = e i • A i := fun i => by
    rw [Finset.smul_sum, Finset.sum_eq_single i]
    · rw [smul_smul, hee]
    · intro j _ hj
      rw [smul_smul, ho i j (Ne.symm hj), zero_smul]
    · simp
  have hB : (∑ i, e i • A i) * (∑ j, (t j * e j) • (A j).adjugate) = 1 := by
    rw [Finset.mul_sum]
    have : ∀ j, (∑ i, e i • A i) * ((t j * e j) • (A j).adjugate) = e j • (1 : Matrix (Fin n) (Fin n) R) := fun j => by
      rw [Matrix.mul_smul, mul_smul, ← Matrix.smul_mul (e j), hs, Matrix.smul_mul, Matrix.mul_adjugate, smul_smul,
        smul_smul]
      congr 1
      rw [mul_right_comm, ht, hee]
    simp only [this]
    rw [← Finset.sum_smul, h1, one_smul]
  exact (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse hB)

section Generic

variable {E R : Type} [Field E] [CharZero E] [CommRing R] {n : ℕ}

theorem exists_herm_notMem (σ : E →+* E) (δ : E) (hδ : δ ≠ 0) (hσδ : σ δ = -δ) (ι : E →+* R) (τ : R →+* R)
    (hτι : ∀ z, τ (ι z) = ι (σ z)) (c d p q : Matrix (Fin n) (Fin n) R) (h : c * p + d * q = 1) (M : Ideal R)
    (hM : M.IsMaximal) :
    ∃ x : Matrix (Fin n) (Fin n) E, (∀ i j, σ (x i j) = x j i) ∧
      (c * x.map ι + d).det * τ (c * x.map ι + d).det ∉ M := by
  letI := Ideal.Quotient.field M
  let π₀ : R →+* R ⧸ M := Ideal.Quotient.mk M
  let φ : E →+* R ⧸ M := π₀.comp ι
  let π := π₀.mapMatrix (m := Fin n)
  let ψ := (π₀.comp τ).mapMatrix (m := Fin n)
  have h1 : π c * π p + π d * π q = 1 := by rw [← map_mul, ← map_mul, ← map_add, h, map_one]
  have h2 : ψ c * ψ p + ψ d * ψ q = 1 := by rw [← map_mul, ← map_mul, ← map_add, h, map_one]
  obtain ⟨y, hy⟩ := GlobalTheory.T.matrix_field_stableRange_one_det_ne_zero _ n _ _ _ _ h1
  obtain ⟨y', hy'⟩ := GlobalTheory.T.matrix_field_stableRange_one_det_ne_zero _ n _ _ _ _ h2
  obtain ⟨x, hxs, hx1, hx2⟩ := GlobalTheory.T.exists_hermitian_two_det_ne_zero E (R ⧸ M) σ φ δ hδ hσδ n _ _ _ _ _ _ hy hy'
  have hx : ∀ i j, σ (x i j) = x j i := fun i j => congrFun (congrFun hxs i) j
  refine ⟨x, hx, fun hmem => ?_⟩
  rcases hM.isPrime.mem_or_mem hmem with h' | h'
  · apply hx1
    have e : π₀ (c * x.map ι + d).det = 0 := Ideal.Quotient.eq_zero_iff_mem.2 h'
    rw [RingHom.map_det] at e
    change (π (c * x.map ι + d)).det = 0 at e
    rw [map_add, map_mul] at e
    exact e
  · apply hx2
    have e : (π₀.comp τ) (c * x.map ι + d).det = 0 := Ideal.Quotient.eq_zero_iff_mem.2 h'
    rw [RingHom.map_det] at e
    change (ψ (c * x.map ι + d)).det = 0 at e
    rw [map_add, map_mul] at e
    have e2 : ψ (x.map ι) = x.transpose.map φ := by
      funext i j
      change π₀ (τ (ι (x i j))) = π₀ (ι (x j i))
      rw [hτι, hx]
    rw [e2] at e
    exact e

theorem exists_herm_isUnit_generic {A : Type} [CommRing A] (σ : E →+* E) (δ : E) (hδ : δ ≠ 0) (hσδ : σ δ = -δ)
    (ι : E →+* R) (τ : R →+* R) (hτι : ∀ z, τ (ι z) = ι (σ z)) (hττ : ∀ z, τ (τ z) = z)
    (a : A →+* R) (ha : Function.Injective a) (hτa : ∀ z, τ (a z) = a z) (hfix : ∀ y, τ y = y → ∃ z, a z = y)
    (k : A) (hk : k * 2 = 1)
    (hid : ∀ (κ : Type) [Fintype κ] (f s : κ → A), ∑ i, s i * f i = 1 → ∃ e t : κ → A,
      ∑ i, e i = 1 ∧ (∀ i j, i ≠ j → e i * e j = 0) ∧ ∀ i, t i * f i = e i)
    (c d p q : Matrix (Fin n) (Fin n) R) (h : c * p + d * q = 1) :
    ∃ x : Matrix (Fin n) (Fin n) R, (x.map τ)ᵀ = x ∧ IsUnit (c * x + d) := by
  classical
  let H := {x : Matrix (Fin n) (Fin n) E // ∀ i j, σ (x i j) = x j i}
  let u : H → R := fun x => (c * x.1.map ι + d).det
  let f : H → R := fun x => u x * τ (u x)
  have htop : Ideal.span (Set.range f) = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨x, hx, hn⟩ := exists_herm_notMem σ δ hδ hσδ ι τ hτι c d p q h M hM
    exact hn (hle (Ideal.subset_span ⟨⟨x, hx⟩, rfl⟩))
  have h1 : (1 : R) ∈ Submodule.span R (Set.range f) := (Ideal.eq_top_iff_one _).1 htop
  obtain ⟨C, hC⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 h1
  have hC' : ∑ i : C.support, C i * f i = 1 := by
    rw [Finset.sum_coe_sort C.support (fun i => C i * f i)]
    exact hC
  have hf : ∀ x, τ (f x) = f x := fun x => by
    simp only [f]
    rw [map_mul, hττ, mul_comm]
  choose g hg using fun x => hfix (f x) (hf x)
  have hs : ∀ x, τ (C x + τ (C x)) = C x + τ (C x) := fun x => by
    rw [map_add, hττ, add_comm]
  choose s hs' using fun x => hfix _ (hs x)
  have h2 : ∑ i : C.support, s i * g i = 2 := by
    apply ha
    have hc := congrArg τ hC'
    rw [map_sum, map_one] at hc
    simp only [map_mul τ, hf] at hc
    rw [map_sum, map_ofNat]
    simp only [map_mul, hg, hs', add_mul]
    rw [Finset.sum_add_distrib, hC', hc, one_add_one_eq_two]
  have h3 : ∑ i : C.support, (k * s i) * g i = 1 := by
    simp only [mul_assoc]
    rw [← Finset.mul_sum, h2, hk]
  obtain ⟨e, t, he1, heo, het⟩ := hid C.support (fun i => g i) _ h3
  have ha1 : ∑ i, a (e i) = 1 := by rw [← map_sum, he1, map_one]
  refine ⟨∑ i : C.support, a (e i) • i.1.1.map ι, ?_, ?_⟩
  · ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum,
      map_mul, hτa, hτι]
    exact Finset.sum_congr rfl fun x _ => by rw [x.1.2]
  · have : c * (∑ i : C.support, a (e i) • i.1.1.map ι) + d =
        ∑ i : C.support, a (e i) • (c * i.1.1.map ι + d) := by
      simp only [smul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_smul, ha1, one_smul, Finset.mul_sum]
      simp only [Matrix.mul_smul]
    rw [this]
    refine isUnit_glue _ (fun i => a (t i) * τ (u i)) _ ha1 (fun i j hij => ?_) (fun i => ?_)
    · rw [← map_mul, heo i j hij, map_zero]
    · rw [← het i, map_mul, hg, mul_assoc, mul_comm (τ (u i))]

end Generic

theorem cA_algebraMap {D : D7} (a : AF D.host.F) :
    cA D (algebraMap (AF D.host.F) (AE D) a) = algebraMap (AF D.host.F) (AE D) a := by
  rw [Algebra.algebraMap_eq_smul_one, GlobalTheory.FinTranslate.cA_smul, map_one]

theorem algebraMap_inj {D : D7} : Function.Injective (algebraMap (AF D.host.F) (AE D)) :=
  Algebra.TensorProduct.includeLeft_injective (S := AF D.host.F) (algebraMap D.host.F D.host.E).injective

theorem half_mul_two {F A : Type} [Field F] [CharZero F] [CommRing A] [Algebra F A] :
    algebraMap F A (1 / 2) * 2 = 1 := by
  rw [← map_ofNat (algebraMap F A) 2, ← map_mul]
  simp

theorem exists_herm_isUnit (D : D7) (n : ℕ) (c d p q : Mx D n n) (h : c * p + d * q = 1) :
    ∃ x : Mx D n n, GlobalTheory.MixModel.adj x = x ∧ IsUnit (c * x + d) :=
  exists_herm_isUnit_generic (D.sp.cm.sig : D.host.E →+* D.host.E) D.host.xi0 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
    (GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D) (incA D) (cA D) GlobalTheory.DualPairCheck.cA_incA GlobalTheory.DualPairCheck.cA_cA
    (algebraMap (AF D.host.F) (AE D)) algebraMap_inj cA_algebraMap GlobalTheory.DetRootRows.fixed_mem_range
    (algebraMap D.host.F (AF D.host.F) (1 / 2)) half_mul_two (GlobalTheory.T.exists_orthogonal_idempotents_of_sum_mul_eq_one' D.host.F) c d p q h

end GlobalTheory.HermTransversal

end
