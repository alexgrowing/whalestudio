import Mathlib

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.QuadSymbol

section Local

variable (K L : Type) [Field K] [Field L] [Algebra K L]

def globalNorms : Subgroup Kˣ := (Units.map (Algebra.norm K : L →* K)).range

def normGroup (A : Type) [CommRing A] [Algebra K A] : Subgroup Aˣ :=
  (Units.map (Algebra.norm A : A ⊗[K] L →* A)).range

open Classical in

def eta (A : Type) [CommRing A] [Algebra K A] (x : Aˣ) : ℤˣ :=
  if x ∈ normGroup K L A then 1 else -1

def toUnits (A : Type) [CommRing A] [Algebra K A] : Kˣ →* Aˣ :=
  Units.map (algebraMap K A : K →* A)

variable {K L}

open NumberField IsDedekindDomain in
open scoped TensorProduct in
variable (K L : Type) [Field K] [Field L] [Algebra K L] in
variable {K L} in
theorem _root_.GlobalTheory.QuadSymbol.eta_eq_one_iff {A : Type} [CommRing A] [Algebra K A] {x : Aˣ} :
    _root_.GlobalTheory.QuadSymbol.eta K L A x = 1 ↔ x ∈ _root_.GlobalTheory.QuadSymbol.normGroup K L A := by
  unfold _root_.GlobalTheory.QuadSymbol.eta
  split_ifs with h
  · simp [h]
  · simp only [h, iff_false]
    decide

open NumberField IsDedekindDomain in
open scoped TensorProduct in
variable (K L : Type) [Field K] [Field L] [Algebra K L] in
variable {K L} in
theorem _root_.GlobalTheory.QuadSymbol.eta_eq_neg_one_iff {A : Type} [CommRing A] [Algebra K A] {x : Aˣ} :
    _root_.GlobalTheory.QuadSymbol.eta K L A x = -1 ↔ x ∉ _root_.GlobalTheory.QuadSymbol.normGroup K L A := by
  unfold _root_.GlobalTheory.QuadSymbol.eta
  split_ifs with h
  · simp only [h, not_true_eq_false, iff_false]
    decide
  · simp [h]

open NumberField IsDedekindDomain in
open scoped TensorProduct in
variable (K L : Type) [Field K] [Field L] [Algebra K L] in
variable {K L} in
private theorem isUnit_of_isUnit_norm' {A S : Type} [CommRing A] [CommRing S] [Algebra A S]
    [Module.Free A S] [Module.Finite A S] {z : S} (h : IsUnit (Algebra.norm A z)) : IsUnit z := by
  rw [Algebra.norm_apply, ← LinearMap.isUnit_iff_isUnit_det] at h
  obtain ⟨u, hu⟩ := h
  have h2 : ((u * u⁻¹ : (Module.End A S)ˣ) : Module.End A S) 1 = 1 := by simp
  rw [Units.val_mul, Module.End.mul_apply, hu] at h2
  exact IsUnit.of_mul_eq_one _ (by simpa using h2)

open NumberField IsDedekindDomain in
open scoped TensorProduct in
variable (K L : Type) [Field K] [Field L] [Algebra K L] in
variable {K L} in

theorem _root_.GlobalTheory.QuadSymbol.mem_normGroup_iff [FiniteDimensional K L] {A : Type} [CommRing A]
    [Algebra K A] {x : Aˣ} :
    x ∈ _root_.GlobalTheory.QuadSymbol.normGroup K L A ↔ ∃ z : A ⊗[K] L, Algebra.norm A z = x := by
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, congrArg Units.val hu⟩
  · rintro ⟨z, hz⟩
    have hu : IsUnit z := isUnit_of_isUnit_norm' (A := A) (by rw [hz]; exact x.isUnit)
    exact ⟨hu.unit, Units.ext (by simp [hz])⟩

open NumberField IsDedekindDomain in
open scoped TensorProduct in
variable (K L : Type) [Field K] [Field L] [Algebra K L] in
variable {K L} in

theorem _root_.GlobalTheory.QuadSymbol.mem_globalNorms_iff [FiniteDimensional K L] {x : Kˣ} :
    x ∈ _root_.GlobalTheory.QuadSymbol.globalNorms K L ↔ ∃ z : L, Algebra.norm K z = x := by
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, congrArg Units.val hu⟩
  · rintro ⟨z, hz⟩
    have hu : IsUnit z := isUnit_of_isUnit_norm' (A := K) (by rw [hz]; exact x.isUnit)
    exact ⟨hu.unit, Units.ext (by simp [hz])⟩

open NumberField IsDedekindDomain in
open scoped TensorProduct in
variable (K L : Type) [Field K] [Field L] [Algebra K L] in
variable {K L} in
private theorem norm_one_tmul_eq_algebraMap_norm [FiniteDimensional K L] {A : Type} [CommRing A] [Algebra K A]
    (z : L) : Algebra.norm A ((1 : A) ⊗ₜ[K] z) = algebraMap K A (Algebra.norm K z) := by
  rw [Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_baseChange]
  congr 1
  ext w
  simp

open NumberField IsDedekindDomain in
open scoped TensorProduct in
variable (K L : Type) [Field K] [Field L] [Algebra K L] in
variable {K L} in

theorem _root_.GlobalTheory.QuadSymbol.toUnits_mem_normGroup [FiniteDimensional K L] (A : Type) [CommRing A]
    [Algebra K A] {x : Kˣ} (hx : x ∈ _root_.GlobalTheory.QuadSymbol.globalNorms K L) :
    _root_.GlobalTheory.QuadSymbol.toUnits K A x ∈ _root_.GlobalTheory.QuadSymbol.normGroup K L A := by
  obtain ⟨z, hz⟩ := _root_.GlobalTheory.QuadSymbol.mem_globalNorms_iff.mp hx
  refine _root_.GlobalTheory.QuadSymbol.mem_normGroup_iff.mpr ⟨(1 : A) ⊗ₜ[K] z, ?_⟩
  rw [norm_one_tmul_eq_algebraMap_norm, hz]
  rfl

open NumberField IsDedekindDomain in
open scoped TensorProduct in
variable (K L : Type) [Field K] [Field L] [Algebra K L] in
variable {K L} in
private theorem norm_smul_add_smul_basis_eq_sq_sub_mul_sq {A S : Type} [CommRing A] [CommRing S]
    [Algebra A S] (f : Module.Basis (Fin 2) A S) (h0 : f 0 = 1) {c : A}
    (h1 : f 1 * f 1 = algebraMap A S c) (a b : A) :
    Algebra.norm A (a • f 0 + b • f 1) = a ^ 2 - c * b ^ 2 := by
  have hm0 : (a • f 0 + b • f 1) * f 0 = a • f 0 + b • f 1 := by rw [h0, mul_one]
  have hm1 : (a • f 0 + b • f 1) * f 1 = (b * c) • f 0 + a • f 1 := by
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, h1, h0, one_mul, Algebra.algebraMap_eq_smul_one,
      smul_smul, add_comm]
  rw [Algebra.norm_eq_matrix_det f, Matrix.det_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, hm0, hm1, map_add, map_smul,
    Module.Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply]
  simp
  ring

open NumberField IsDedekindDomain in
open scoped TensorProduct in
variable (K L : Type) [Field K] [Field L] [Algebra K L] in
variable {K L} in

theorem _root_.GlobalTheory.QuadSymbol.mem_normGroup_iff_form (e : Module.Basis (Fin 2) K L)
    (h0 : e 0 = 1) {δ : K} (h1 : e 1 * e 1 = algebraMap K L δ) {A : Type} [CommRing A]
    [Algebra K A] {x : Aˣ} :
    x ∈ _root_.GlobalTheory.QuadSymbol.normGroup K L A ↔
      ∃ a b : A, (x : A) = a ^ 2 - algebraMap K A δ * b ^ 2 := by
  haveI : FiniteDimensional K L := Module.Finite.of_basis e
  set f := Algebra.TensorProduct.basis A e
  have hf0 : f 0 = 1 := by
    rw [Algebra.TensorProduct.basis_apply, h0]
    rfl
  have hf1 : f 1 * f 1 = algebraMap A (A ⊗[K] L) (algebraMap K A δ) := by
    simp only [f, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      h1, Algebra.TensorProduct.algebraMap_apply]
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']
    congr 1
    simp [Algebra.smul_def]
  rw [_root_.GlobalTheory.QuadSymbol.mem_normGroup_iff]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨f.repr z 0, f.repr z 1, ?_⟩
    have hz' : z = f.repr z 0 • f 0 + f.repr z 1 • f 1 := by
      conv_lhs => rw [← f.sum_repr z]
      rw [Fin.sum_univ_two]
    have hn := norm_smul_add_smul_basis_eq_sq_sub_mul_sq f hf0 hf1 (f.repr z 0) (f.repr z 1)
    rw [← hz', hz] at hn
    exact hn
  · rintro ⟨a, b, h⟩
    exact ⟨a • f 0 + b • f 1, by rw [norm_smul_add_smul_basis_eq_sq_sub_mul_sq f hf0 hf1, h]⟩

end Local

section Global

variable (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]

abbrev FinFam : Type := ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ

abbrev InfFam : Type := ∀ w : InfinitePlace K, (w.Completion)ˣ

def finDiag (t : Kˣ) : FinFam K := fun v => toUnits K (v.adicCompletion K) t

def infDiag (t : Kˣ) : InfFam K := fun w => toUnits K w.Completion t

def AlmostNorm (x : FinFam K) : Prop :=
  {v | x v ∉ normGroup K L (v.adicCompletion K)}.Finite

def EverywhereNorm (x : FinFam K) (y : InfFam K) : Prop :=
  (∀ v, x v ∈ normGroup K L (v.adicCompletion K)) ∧ ∀ w, y w ∈ normGroup K L w.Completion

def etaProd (x : FinFam K) (y : InfFam K) : ℤˣ :=
  (∏ᶠ v : HeightOneSpectrum (𝓞 K), eta K L (v.adicCompletion K) (x v)) *
    ∏ w : InfinitePlace K, eta K L w.Completion (y w)

open NumberField IsDedekindDomain in
open scoped TensorProduct in
variable (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L] in

theorem _root_.GlobalTheory.QuadSymbol.AlmostNorm.finite_mulSupport
    {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L]
    {x : _root_.GlobalTheory.QuadSymbol.FinFam K} (h : _root_.GlobalTheory.QuadSymbol.AlmostNorm K L x) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) =>
      _root_.GlobalTheory.QuadSymbol.eta K L (v.adicCompletion K) (x v)).Finite := by
  refine h.subset fun v hv => ?_
  simp only [Function.mem_mulSupport] at hv
  exact fun hmem => hv (_root_.GlobalTheory.QuadSymbol.eta_eq_one_iff.mpr hmem)

def LocalCharacters : Prop :=
  (∀ (v : HeightOneSpectrum (𝓞 K)) (a b : (v.adicCompletion K)ˣ),
    eta K L (v.adicCompletion K) (a * b) = eta K L (v.adicCompletion K) a * eta K L (v.adicCompletion K) b) ∧
  ∀ (w : InfinitePlace K) (a b : (w.Completion)ˣ),
    eta K L w.Completion (a * b) = eta K L w.Completion a * eta K L w.Completion b

def NormTheorem : Prop :=
  ∀ t : Kˣ, t ∈ globalNorms K L ↔ EverywhereNorm K L (finDiag K t) (infDiag K t)

def ExactSequence : Prop :=
  (∀ t : Kˣ, AlmostNorm K L (finDiag K t)) ∧
  (∀ t : Kˣ, EverywhereNorm K L (finDiag K t) (infDiag K t) ↔ t ∈ globalNorms K L) ∧
  (∀ (x : FinFam K) (y : InfFam K), AlmostNorm K L x →
    ((∃ t : Kˣ, EverywhereNorm K L (x / finDiag K t) (y / infDiag K t)) ↔ etaProd K L x y = 1)) ∧
  ∃ (x : FinFam K) (y : InfFam K), AlmostNorm K L x ∧ etaProd K L x y = -1

def ProductFormula : Prop :=
  ∀ t : Kˣ, AlmostNorm K L (finDiag K t) ∧ etaProd K L (finDiag K t) (infDiag K t) = 1

end Global

def BaseChangeAt (F E K L A : Type) [Field F] [Field E] [Field K] [Field L] [Field A]
    [Algebra F E] [Algebra F K] [Algebra K L] [Algebra F A] : Prop :=
  ∀ (B : Type) [Field B] [Algebra A B] [FiniteDimensional A B] [Algebra K B] [Algebra F B]
    [IsScalarTower F A B] [IsScalarTower F K B] (x : Bˣ),
    eta K L B x = eta F E A (Units.map (Algebra.norm A : B →* A) x)

end GlobalTheory.QuadSymbol

namespace GlobalTheory.Published

open GlobalTheory.QuadSymbol

def QuadraticClassFieldTheory : Prop :=
  (∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [Algebra.IsQuadraticExtension K L],
    LocalCharacters K L ∧ NormTheorem K L ∧ ExactSequence K L ∧ ProductFormula K L) ∧
  (∀ (F E K L : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra F E] [Algebra F K] [Algebra K L] [Algebra E L] [Algebra F L]
    [IsScalarTower F K L] [IsScalarTower F E L]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsQuadraticExtension K L],
    Algebra.adjoin K (Set.range (algebraMap E L)) = ⊤ →
    (∀ v : HeightOneSpectrum (𝓞 F), BaseChangeAt F E K L (v.adicCompletion F)) ∧
    ∀ v : InfinitePlace F, BaseChangeAt F E K L v.Completion)

end GlobalTheory.Published

end
