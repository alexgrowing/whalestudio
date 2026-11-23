import Mathlib
import Formalism.PeriodIntegrals.ProdFormulaE

noncomputable section

open IsDedekindDomain NumberField Formalism.MainNotions.S.Loc

namespace PI.ProdFormulaE.Base

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}

theorem finrank_pos (L : LocAt F E sig p) : 0 < Module.finrank L.Fp L.Ep := by
  rw [L.rank]; norm_num

theorem nontrivial (L : LocAt F E sig p) : Nontrivial L.Ep :=
  Module.nontrivial_of_finrank_pos (finrank_pos L)

theorem finite (L : LocAt F E sig p) : Module.Finite L.Fp L.Ep :=
  Module.finite_of_finrank_pos (finrank_pos L)

theorem ιE_injective (L : LocAt F E sig p) : Function.Injective L.ιE := by
  have := nontrivial L
  exact L.ιE.injective

theorem isUnit_ιE (L : LocAt F E sig p) {x : E} (hx : x ≠ 0) : IsUnit (L.ιE x) :=
  (isUnit_iff_ne_zero.mpr hx).map L.ιE

theorem ιE_smul (L : LocAt F E sig p) (a : F) (y : E) : L.ιE (a • y) = L.ιF a • L.ιE y := by
  rw [Algebra.smul_def, map_mul, L.compat, Algebra.smul_def]

theorem ιE_eq_sum (L : LocAt F E sig p) {ι : Type*} [Fintype ι] (b : Module.Basis ι F E) (y : E) :
    L.ιE y = ∑ i, L.ιF (b.repr y i) • L.ιE (b i) := by
  conv_lhs => rw [← b.sum_repr y]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => ιE_smul L _ _

theorem span_basis (L : LocAt F E sig p) {ι : Type*} [Fintype ι] (b : Module.Basis ι F E) :
    Submodule.span L.Fp (Set.range (L.ιE ∘ b)) = ⊤ := by
  rw [eq_top_iff, ← L.span, Submodule.span_le]
  rintro _ ⟨y, rfl⟩
  rw [ιE_eq_sum L b y]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

def basisE (L : LocAt F E sig p) {ι : Type*} [Fintype ι] (b : Module.Basis ι F E)
    (h : Module.finrank F E = 2) : Module.Basis ι L.Fp L.Ep :=
  haveI := finite L
  basisOfTopLeSpanOfCardEqFinrank (L.ιE ∘ b) (span_basis L b).ge
    (by rw [L.rank, ← h, Module.finrank_eq_card_basis b])

theorem basisE_apply (L : LocAt F E sig p) {ι : Type*} [Fintype ι] (b : Module.Basis ι F E)
    (h : Module.finrank F E = 2) (i : ι) : basisE L b h i = L.ιE (b i) := by
  simp [basisE]

theorem basisE_repr (L : LocAt F E sig p) {ι : Type*} [Fintype ι] (b : Module.Basis ι F E)
    (h : Module.finrank F E = 2) (y : E) (i : ι) :
    (basisE L b h).repr (L.ιE y) i = L.ιF (b.repr y i) := by
  have hy : L.ιE y = ∑ j, L.ιF (b.repr y j) • basisE L b h j := by
    simp only [basisE_apply]; exact ιE_eq_sum L b y
  rw [hy, Module.Basis.repr_sum_self]

theorem leftMulMatrix_ιE (L : LocAt F E sig p) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι F E) (h : Module.finrank F E = 2) (x : E) :
    Algebra.leftMulMatrix (basisE L b h) (L.ιE x) = (Algebra.leftMulMatrix b x).map L.ιF := by
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    basisE_apply, ← map_mul, basisE_repr]

theorem trace_ιE (L : LocAt F E sig p) (h : Module.finrank F E = 2) (x : E) :
    Algebra.trace L.Fp L.Ep (L.ιE x) = L.ιF (Algebra.trace F E x) := by
  classical
  let b := Module.finBasisOfFinrankEq F E h
  rw [Algebra.trace_eq_matrix_trace (basisE L b h), Algebra.trace_eq_matrix_trace b,
    leftMulMatrix_ιE, Matrix.trace, Matrix.trace, map_sum]
  rfl

theorem norm_ιE (L : LocAt F E sig p) (h : Module.finrank F E = 2) (x : E) :
    Algebra.norm L.Fp (L.ιE x) = L.ιF (Algebra.norm F x) := by
  classical
  let b := Module.finBasisOfFinrankEq F E h
  rw [Algebra.norm_eq_matrix_det (basisE L b h), Algebra.norm_eq_matrix_det b,
    leftMulMatrix_ιE, RingHom.map_det]
  rfl

theorem trace_tower (L : LocAt F E sig p) (y : L.Ep) :
    (haveI := L.ellPrime
     letI := ((algebraMap L.Fp L.Ep).comp (algebraMap ℚ_[resChar p] L.Fp)).toAlgebra
     Algebra.trace ℚ_[resChar p] L.Ep y) =
    (haveI := L.ellPrime
     Algebra.trace ℚ_[resChar p] L.Fp (Algebra.trace L.Fp L.Ep y)) := by
  have := L.ellPrime
  let _ : Algebra ℚ_[resChar p] L.Ep :=
    ((algebraMap L.Fp L.Ep).comp (algebraMap ℚ_[resChar p] L.Fp)).toAlgebra
  have : IsScalarTower ℚ_[resChar p] L.Fp L.Ep := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := L.free
  have := finite L
  have := L.qlFin
  exact (Algebra.trace_trace (R := ℚ_[resChar p]) (S := L.Fp) (T := L.Ep) y).symm

theorem trace_ιE_ql (L : LocAt F E sig p) (h : Module.finrank F E = 2) (x : E) :
    (haveI := L.ellPrime
     letI := ((algebraMap L.Fp L.Ep).comp (algebraMap ℚ_[resChar p] L.Fp)).toAlgebra
     Algebra.trace ℚ_[resChar p] L.Ep (L.ιE x)) =
    (haveI := L.ellPrime
     Algebra.trace ℚ_[resChar p] L.Fp (L.ιF (Algebra.trace F E x))) := by
  rw [trace_tower, trace_ιE L h]

theorem psiE_ιE (L : LocAt F E sig p) (h : Module.finrank F E = 2) (x : E) :
    haveI := L.ellPrime
    ∃ a : ℚ, (∃ n : ℕ, a.den = (resChar p) ^ n) ∧
      ‖Algebra.trace ℚ_[resChar p] L.Fp (L.ιF (Algebra.trace F E x)) - (a : ℚ_[resChar p])‖ ≤ 1 ∧
      L.psiE (L.ιE x) = Complex.exp (2 * Real.pi * Complex.I * (a : ℂ)) := by
  obtain ⟨a, ha, hn, he⟩ := L.psiE_def (L.ιE x)
  exact ⟨a, ha, by rwa [trace_ιE_ql L h] at hn, he⟩

end PI.ProdFormulaE.Base

end
