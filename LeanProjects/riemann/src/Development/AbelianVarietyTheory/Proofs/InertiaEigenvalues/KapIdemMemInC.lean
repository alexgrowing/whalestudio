import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

noncomputable section

namespace GlobalTheory.Cyc.Decomp

variable {l : ℕ} [Fact l.Prime]

theorem coe_emb_algebraMap (LL : FinExt l) (τ : ↥LL.1 →ₐ[ℚ_[l]] Om l) (x : ℤ_[l]) :
    algebraMap (Om l) (PadicComplex l) (τ ((algebraMap ℤ_[l] ↥(OL LL) x : ↥(OL LL)) : ↥LL.1)) = zC x := by
  have h : ((algebraMap ℤ_[l] ↥(OL LL) x : ↥(OL LL)) : ↥LL.1) = algebraMap ℚ_[l] ↥LL.1 (x : ℚ_[l]) := by
    rw [Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1]; rfl
  rw [h, AlgHom.commutes]; rfl

theorem exists_evEmb (LL : FinExt l) (τ : ↥LL.1 →ₐ[ℚ_[l]] Om l) :
    ∃ ev : OCO LL →+* PadicComplex l, ∀ (c : OC l) (a : ↥(OL LL)),
      ev (c ⊗ₜ[ℤ_[l]] a) = (c : PadicComplex l) * algebraMap (Om l) (PadicComplex l) (τ (a : ↥LL.1)) := by
  letI : Algebra ℤ_[l] (PadicComplex l) :=
    ((algebraMap ℚ_[l] (PadicComplex l)).comp PadicInt.Coe.ringHom).toAlgebra
  let u : OC l →ₐ[ℤ_[l]] PadicComplex l :=
    { (PadicComplexInt l).subtype with commutes' := fun x => rfl }
  let v : ↥(OL LL) →ₐ[ℤ_[l]] PadicComplex l :=
    { (algebraMap (Om l) (PadicComplex l)).comp (τ.toRingHom.comp (OL LL).val.toRingHom) with
      commutes' := fun x => coe_emb_algebraMap LL τ x }
  exact ⟨(Algebra.TensorProduct.productMap u v).toRingHom, fun c a => rfl⟩

theorem evEmb_eq_sum {LL : FinExt l} {f : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL))
    (τ : ↥LL.1 →ₐ[ℚ_[l]] Om l) (ev : OCO LL →+* PadicComplex l)
    (hev : ∀ (c : OC l) (a : ↥(OL LL)),
      ev (c ⊗ₜ[ℤ_[l]] a) = (c : PadicComplex l) * algebraMap (Om l) (PadicComplex l) (τ (a : ↥LL.1)))
    (x : OCO LL) :
    ev x = ∑ k, kap o x k * algebraMap (Om l) (PadicComplex l) (τ (o k : ↥LL.1)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, kap_zero, zero_mul, Finset.sum_const_zero]
  | add x y hx hy => simp only [map_add, kap_add, hx, hy, add_mul, Finset.sum_add_distrib]
  | tmul c a =>
    rw [hev]
    simp only [kap_tmul, mul_assoc, ← Finset.mul_sum]
    congr 1
    conv_lhs => rw [← o.sum_repr a]
    simp only [Algebra.smul_def, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, map_sum,
      map_mul, coe_emb_algebraMap]

theorem exists_emb_det_ne_zero {LL : FinExt l} {f : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) :
    ∃ τ : Fin f → (↥LL.1 →ₐ[ℚ_[l]] Om l),
      (Matrix.of fun i j => τ j (o i : ↥LL.1) : Matrix (Fin f) (Fin f) (Om l)).det ≠ 0 := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI : IsIntegralClosure ↥(OL LL) ℤ_[l] ↥LL.1 := integralClosure.isIntegralClosure ℤ_[l] ↥LL.1
  haveI := IsIntegralClosure.isLocalization ℤ_[l] ℚ_[l] ↥LL.1 ↥(OL LL)
  let b := o.localizationLocalization ℚ_[l] (nonZeroDivisors ℤ_[l]) ↥LL.1
  have hb : ∀ i, b i = (o i : ↥LL.1) := fun i =>
    Module.Basis.localizationLocalization_apply _ _ _ _ i
  have hc : Fintype.card (Fin f) = Fintype.card (↥LL.1 →ₐ[ℚ_[l]] Om l) := by
    rw [AlgHom.card, Module.finrank_eq_card_basis b]
  let e := Fintype.equivOfCardEq hc
  refine ⟨e, fun h0 => ?_⟩
  have h1 := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ_[l] (Om l) b e
  have h2 : Algebra.embeddingsMatrixReindex ℚ_[l] (Om l) b e =
      Matrix.of fun i j => e j (o i : ↥LL.1) := by
    ext i j
    simp [Algebra.embeddingsMatrixReindex, hb]
  rw [h2, h0, zero_pow two_ne_zero, map_eq_zero] at h1
  exact Algebra.discr_not_zero_of_basis ℚ_[l] b h1

theorem kap_idem_algebraic {LL : FinExt l} {f : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL))
    (e : OCO LL) (he : IsIdempotentElem e) (k : Fin f) :
    ∃ x : Om l, algebraMap (Om l) (PadicComplex l) x = kap o e k := by
  obtain ⟨τ, hτ⟩ := exists_emb_det_ne_zero o
  set M : Matrix (Fin f) (Fin f) (Om l) := Matrix.of fun i j => τ j (o i : ↥LL.1) with hM
  have hy : ∀ j, ∃ y : Om l, algebraMap (Om l) (PadicComplex l) y =
      ∑ k, kap o e k * algebraMap (Om l) (PadicComplex l) (M k j) := by
    intro j
    obtain ⟨ev, hev⟩ := exists_evEmb LL (τ j)
    have h1 := evEmb_eq_sum o (τ j) ev hev e
    rcases IsIdempotentElem.iff_eq_zero_or_one.1 (he.map ev) with h | h
    · exact ⟨0, by rw [map_zero, ← h, h1]; rfl⟩
    · exact ⟨1, by rw [map_one, ← h, h1]; rfl⟩
  choose y hy using hy
  refine ⟨∑ j, y j * M⁻¹ j k, ?_⟩
  have hinv : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M (Ne.isUnit hτ)
  simp only [map_sum, map_mul, hy, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, ← map_mul, ← map_sum, ← Matrix.mul_apply, hinv, Matrix.one_apply]
  simp [apply_ite (algebraMap (Om l) (PadicComplex l))]

theorem kap_idem_mem_inC (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l))
    (K LL : FinExt l) (f : ℕ) (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (e : OCO LL)
    (hact : IsActC act) (he : IsIdempotentElem e)
    (hfix : ∀ g ∈ GK K, ∀ k, act g (kap o e k) = kap o e k) (k : Fin f) : kap o e k ∈ inC K.1 := by
  obtain ⟨x, hx⟩ := kap_idem_algebraic o e he k
  refine ⟨x, ?_, hx⟩
  rw [← InfiniteGalois.fixedField_fixingSubgroup K.1]
  rintro ⟨g, hg⟩
  have h1 := hfix g hg k
  rw [← hx] at h1
  apply (algebraMap (Om l) (PadicComplex l)).injective
  exact (hact.1 g x).symm.trans h1

end GlobalTheory.Cyc.Decomp
