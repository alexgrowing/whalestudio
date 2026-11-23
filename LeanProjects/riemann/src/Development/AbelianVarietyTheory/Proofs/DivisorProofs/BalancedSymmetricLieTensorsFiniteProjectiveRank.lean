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

namespace GlobalTheory.BalProj.Alg

open Module

theorem trace_matrix_end {R : Type} [CommRing R] {n : ℕ}
    (f : Matrix (Fin n) (Fin n) R →ₗ[R] Matrix (Fin n) (Fin n) R) :
    LinearMap.trace R _ f = ∑ i, ∑ j, f (Matrix.single i j 1) i j := by
  rw [LinearMap.trace_eq_matrix_trace R (Matrix.stdBasis R (Fin n) (Fin n)), Matrix.trace, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Matrix.stdBasis_eq_single]
  simp [Matrix.stdBasis]

def sand {R : Type} [CommRing R] {n : ℕ} (P Q : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) R →ₗ[R] Matrix (Fin n) (Fin n) R where
  toFun Θ := Pᵀ * Θ * Q
  map_add' := fun x y => by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' := fun r x => by simp

theorem trace_sand {R : Type} [CommRing R] {n : ℕ} (P Q : Matrix (Fin n) (Fin n) R) :
    LinearMap.trace R _ (sand P Q) = P.trace * Q.trace := by
  rw [trace_matrix_end, Matrix.trace, Matrix.trace, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [sand, Matrix.mul_apply, Matrix.single_apply, ite_and]

theorem trace_sand_transpose {R : Type} [CommRing R] {n : ℕ} (P Q : Matrix (Fin n) (Fin n) R) :
    LinearMap.trace R _ (sand P Q ∘ₗ (Matrix.transposeLinearEquiv (Fin n) (Fin n) R R).toLinearMap) =
      (Q * P).trace := by
  rw [trace_matrix_end, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [sand, Matrix.mul_apply, Matrix.single_apply, ite_and, mul_comm]

theorem finrank_retract {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M]
    [Module.Finite R M] (N : Submodule R M) (r : M →ₗ[R] N) (hr : r ∘ₗ N.subtype = LinearMap.id)
    (k : Type) [Field k] [Algebra R k] :
    (finrank k (k ⊗[R] N) : k) = algebraMap R k (LinearMap.trace R M (N.subtype ∘ₗ r)) := by
  have : Module.Finite R N := Module.Finite.of_surjective r
    (fun x => ⟨x, LinearMap.congr_fun hr x⟩)
  rw [← LinearMap.trace_baseChange, LinearMap.baseChange_comp, LinearMap.trace_comp_comm',
    ← LinearMap.baseChange_comp, hr, LinearMap.baseChange_id, LinearMap.trace_id]

section abstract

variable {O R J : Type} [CommRing R] [Fintype J] {n : ℕ} {A : O → Matrix (Fin n) (Fin n) R} {χ : J → O → R}
  {P : J → Matrix (Fin n) (Fin n) R}

theorem eq_zero_of_unit {M : Type} [AddCommGroup M] [Module R M] {x y : R} (h : IsUnit (x - y)) {v : M}
    (hv : x • v = y • v) : v = 0 := by
  rw [← sub_eq_zero, ← sub_smul] at hv
  exact (h.smul_eq_zero).1 hv

theorem orth (hl : ∀ τ a, A a * P τ = χ τ a • P τ) (hr : ∀ τ a, P τ * A a = χ τ a • P τ)
    (hs : ∀ σ τ, σ ≠ τ → ∃ a, IsUnit (χ σ a - χ τ a)) {σ τ : J} (h : σ ≠ τ) : P σ * P τ = 0 := by
  obtain ⟨a, ha⟩ := hs σ τ h
  refine eq_zero_of_unit ha ?_
  rw [← Matrix.smul_mul, ← hr, ← Matrix.mul_smul, ← hl, Matrix.mul_assoc]

theorem eigRank_eq (h1 : ∑ τ, P τ = 1) (hl : ∀ τ a, A a * P τ = χ τ a • P τ)
    (hr : ∀ τ a, P τ * A a = χ τ a • P τ) (hs : ∀ σ τ, σ ≠ τ → ∃ a, IsUnit (χ σ a - χ τ a))
    {k : Type} [Field k] (φ : R →+* k) (σ : J) : (eigRank φ A (χ σ) : k) = φ (P σ).trace := by
  have hm : ∀ (x : R) (X : Matrix (Fin n) (Fin n) R), (x • X).map φ = φ x • X.map φ := fun x X => by
    ext i j; simp
  have hp : LinearMap.IsProj (eigSp (fun a => (A a).map φ) (fun a => φ (χ σ a)))
      (Matrix.toLin' ((P σ).map φ)ᵀ) := by
    constructor
    · intro c a
      rw [Matrix.toLin'_apply, Matrix.mulVec_transpose, Matrix.vecMul_vecMul, ← Matrix.map_mul, hr, hm,
        Matrix.vecMul_smul]
    · intro c hc
      have h0 : ∀ τ, τ ≠ σ → c ᵥ* (P τ).map φ = 0 := fun τ h => by
        obtain ⟨a, ha⟩ := hs τ σ h
        have ha' := ha.map φ
        rw [map_sub] at ha'
        refine eq_zero_of_unit ha' ?_
        rw [← Matrix.vecMul_smul, ← hm, ← hl, Matrix.map_mul, ← Matrix.vecMul_vecMul, hc a, Matrix.smul_vecMul]
      have h2 : ∑ τ, (P τ).map φ = 1 := by
        have := congrArg φ.mapMatrix h1
        rw [map_sum, map_one] at this
        exact this
      rw [Matrix.toLin'_apply, Matrix.mulVec_transpose]
      conv_rhs => rw [← Matrix.vecMul_one c, ← h2, Matrix.vecMul_sum]
      rw [Finset.sum_eq_single σ (fun τ _ h => h0 τ h) (by simp)]
  rw [eigRank, ← hp.trace, Matrix.trace_toLin'_eq, Matrix.trace_transpose]
  simp [Matrix.trace]

theorem exists_retract (h1 : ∑ τ, P τ = 1) (hl : ∀ τ a, A a * P τ = χ τ a • P τ)
    (hr : ∀ τ a, P τ * A a = χ τ a • P τ) (hs : ∀ σ τ, σ ≠ τ → ∃ a, IsUnit (χ σ a - χ τ a))
    (bar : O → O) (c : J → J) (hcc : ∀ τ, c (c τ) = τ) (hc : ∀ τ, c τ ≠ τ)
    (hb : ∀ τ a, χ τ (bar a) = χ (c τ) a) (u : R) (hu : 2 * u = 1) :
    ∃ r : Matrix (Fin n) (Fin n) R →ₗ[R] balanced bar A, r ∘ₗ (balanced bar A).subtype = LinearMap.id ∧
      2 * LinearMap.trace R _ ((balanced bar A).subtype ∘ₗ r) = ∑ τ, (P τ).trace * (P (c τ)).trace := by
  let T := (Matrix.transposeLinearEquiv (Fin n) (Fin n) R R).toLinearMap
  let S : Matrix (Fin n) (Fin n) R →ₗ[R] Matrix (Fin n) (Fin n) R := ∑ τ, sand (P τ) (P (c τ))
  have hS : ∀ Θ, S Θ = ∑ τ, (P τ)ᵀ * Θ * P (c τ) := fun Θ => by
    simp only [S, LinearMap.sum_apply]; rfl
  let q : Matrix (Fin n) (Fin n) R →ₗ[R] Matrix (Fin n) (Fin n) R := u • (S + S ∘ₗ T)
  have hq : ∀ Θ, q Θ = u • S (Θ + Θᵀ) := fun Θ => by
    rw [map_add]; rfl
  have hmem : ∀ Θ, q Θ ∈ balanced bar A := fun Θ => by
    rw [hq]
    refine Submodule.smul_mem _ _ ?_
    rw [hS]
    refine ⟨?_, fun a => ?_⟩
    · rw [Matrix.transpose_sum]
      refine Fintype.sum_bijective c (Function.Involutive.bijective hcc) _ _ fun τ => ?_
      rw [hcc, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_add,
        Matrix.transpose_transpose, add_comm, Matrix.mul_assoc]
    · rw [Matrix.mul_sum, Matrix.sum_mul]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.transpose_mul, hr, Matrix.mul_assoc _ (P (c τ)), hr,
        hb, hcc, Matrix.transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul]
  have hfix : ∀ Θ ∈ balanced bar A, q Θ = Θ := fun Θ hΘ => by
    have h0 : ∀ σ τ, τ ≠ c σ → (P σ)ᵀ * Θ * P τ = 0 := fun σ τ h => by
      obtain ⟨a, ha⟩ := hs σ (c τ) (fun e => h (by rw [e, hcc]))
      refine eq_zero_of_unit ha ?_
      rw [← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.transpose_smul, ← hl, Matrix.transpose_mul,
        Matrix.mul_assoc _ _ Θ, hΘ.2 a, ← hb, ← Matrix.mul_smul, ← hl]
      simp only [Matrix.mul_assoc]
    have h2 : S Θ = Θ := by
      rw [hS]
      conv_rhs => rw [← Matrix.one_mul Θ, ← Matrix.transpose_one, ← h1, Matrix.transpose_sum, Matrix.sum_mul]
      refine Finset.sum_congr rfl fun σ _ => ?_
      conv_rhs => rw [← Matrix.mul_one ((P σ)ᵀ * Θ), ← h1, Matrix.mul_sum]
      rw [Finset.sum_eq_single (c σ) (fun τ _ h => h0 σ τ h) (by simp)]
    rw [hq, hΘ.1, map_add, h2, ← two_smul R, smul_smul, mul_comm, hu, one_smul]
  refine ⟨q.codRestrict _ hmem, ?_, ?_⟩
  · ext1 x
    exact Subtype.ext (hfix x.1 x.2)
  · have hT : LinearMap.trace R _ (S ∘ₗ T) = 0 := by
      have e : S ∘ₗ T = ∑ τ, sand (P τ) (P (c τ)) ∘ₗ T := by
        ext1 x
        simp only [S, LinearMap.sum_apply, LinearMap.comp_apply]
      rw [e, map_sum]
      refine Finset.sum_eq_zero fun τ _ => ?_
      rw [trace_sand_transpose, orth hl hr hs (hc τ), Matrix.trace_zero]
    rw [LinearMap.subtype_comp_codRestrict]
    simp only [q]
    rw [map_smul, map_add, hT, add_zero, smul_eq_mul, ← _root_.mul_assoc, hu, _root_.one_mul]
    simp only [S]
    rw [map_sum]
    exact Finset.sum_congr rfl fun τ _ => trace_sand _ _

end abstract

theorem exists_projectors {E : Type} [Field E] [NumberField E] (F : IntermediateField ℚ ℂ)
    (hF : ∀ (τ : E →+* ℂ) (a : E), τ a ∈ F) {R : Type} [CommRing R] (iF : F →+* R) {n : ℕ}
    (A : 𝓞 E → Matrix (Fin n) (Fin n) R) (h1 : A 1 = 1) (ha : ∀ a b, A (a + b) = A a + A b)
    (hm : ∀ a b, A (a * b) = A a * A b) :
    ∃ P : (E →+* ℂ) → Matrix (Fin n) (Fin n) R, ∑ τ, P τ = 1 ∧
      (∀ τ a, A a * P τ = embR F hF iF τ a • P τ) ∧ (∀ τ a, P τ * A a = embR F hF iF τ a • P τ) := by
  classical
  let b := (RingOfIntegers.basis E).reindex (equivReindex E).symm
  let M : Matrix (E →+* ℂ) (E →+* ℂ) F := Matrix.of fun i τ => ⟨τ (b i : E), hF τ _⟩
  have hM : IsUnit M.det := by
    have e : (algebraMap F ℂ).mapMatrix M = basisMatrix E := by
      ext i τ
      simp [M, b, canonicalEmbedding.latticeBasis_apply, integralBasis_apply]
    rw [isUnit_iff_ne_zero]
    intro h
    apply det_of_basisMatrix_non_zero E
    rw [← e, ← RingHom.map_det, h, map_zero]
  let χ : (E →+* ℂ) → 𝓞 E → R := embR F hF iF
  have hχa : ∀ τ a a', χ τ (a + a') = χ τ a + χ τ a' := fun τ a a' => by
    simp only [χ, embR]; rw [← map_add]; congr 1; ext; simp
  have hχm : ∀ τ a a', χ τ (a * a') = χ τ a * χ τ a' := fun τ a a' => by
    simp only [χ, embR]; rw [← map_mul]; congr 1; ext; simp
  have hχ1 : ∀ τ, χ τ 1 = 1 := fun τ => by
    simp only [χ, embR]; rw [← map_one iF]; congr 1; ext; simp
  let M' := iF.mapMatrix M
  let N := iF.mapMatrix M⁻¹
  have hMN : M' * N = 1 := by rw [← map_mul, Matrix.mul_nonsing_inv _ hM, map_one]
  have hNM : N * M' = 1 := by rw [← map_mul, Matrix.nonsing_inv_mul _ hM, map_one]
  have hM' : ∀ i τ, M' i τ = χ τ (b i) := fun i τ => rfl
  have ind : ∀ X : (E →+* ℂ) → Matrix (Fin n) (Fin n) R, (∀ a, ∑ τ, χ τ a • X τ = 0) → ∀ σ, X σ = 0 := by
    intro X hX σ
    have : ∑ i, N σ i • ∑ τ, χ τ (b i) • X τ = X σ := by
      simp only [Finset.smul_sum, smul_smul, ← hM']
      rw [Finset.sum_comm]
      simp only [← Finset.sum_smul, ← Matrix.mul_apply, hNM]
      simp [Matrix.one_apply]
    rw [← this]
    simp [hX]
  let P : (E →+* ℂ) → Matrix (Fin n) (Fin n) R := fun τ => ∑ i, N τ i • A (b i)
  have hA : ∀ a, A a = ∑ τ, χ τ a • P τ := by
    let f : 𝓞 E →+ Matrix (Fin n) (Fin n) R := AddMonoidHom.mk' A ha
    let g : 𝓞 E →+ Matrix (Fin n) (Fin n) R := AddMonoidHom.mk' (fun a => ∑ τ, χ τ a • P τ) fun a a' => by
      simp only [hχa, add_smul, Finset.sum_add_distrib]
    have : f.toIntLinearMap = g.toIntLinearMap := b.ext fun j => by
      show A (b j) = ∑ τ, χ τ (b j) • ∑ i, N τ i • A (b i)
      simp only [Finset.smul_sum, smul_smul, ← hM']
      rw [Finset.sum_comm]
      simp only [← Finset.sum_smul, ← Matrix.mul_apply, hMN]
      simp [Matrix.one_apply]
    exact fun a => LinearMap.congr_fun this a
  refine ⟨P, ?_, fun τ a => ?_, fun τ a => ?_⟩
  · rw [← h1, hA 1]
    simp [hχ1]
  · refine sub_eq_zero.1 (ind (fun τ => A a * P τ - χ τ a • P τ) (fun a' => ?_) τ)
    simp only [smul_sub, Finset.sum_sub_distrib, smul_smul, ← hχm, ← Matrix.mul_smul, ← Matrix.mul_sum, ← hA]
    rw [mul_comm a', hm, sub_self]
  · refine sub_eq_zero.1 (ind (fun τ => P τ * A a - χ τ a • P τ) (fun a' => ?_) τ)
    simp only [smul_sub, Finset.sum_sub_distrib, smul_smul, ← hχm, ← Matrix.smul_mul, ← Matrix.sum_mul, ← hA]
    rw [hm, sub_self]

theorem embR_sep {E : Type} [Field E] [NumberField E] (F : IntermediateField ℚ ℂ)
    (hF : ∀ (τ : E →+* ℂ) (a : E), τ a ∈ F) {R : Type} [CommRing R] (iF : F →+* R) (σ τ : E →+* ℂ) (h : σ ≠ τ) :
    ∃ a, IsUnit (embR F hF iF σ a - embR F hF iF τ a) := by
  have : ∃ a : 𝓞 E, σ (a : E) ≠ τ (a : E) := by
    by_contra hh
    push Not at hh
    exact h (IsFractionRing.ringHom_ext (A := 𝓞 E) hh)
  obtain ⟨a, ha⟩ := this
  refine ⟨a, ?_⟩
  rw [embR, embR, ← map_sub]
  refine IsUnit.map iF (isUnit_iff_ne_zero.2 (sub_ne_zero.2 fun e => ha ?_))
  exact congrArg Subtype.val e

theorem balanced_finite_projective_rank : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (F : IntermediateField ℚ ℂ) (hF : ∀ (τ : E →+* ℂ) (a : E), τ a ∈ F) (R : Type) [CommRing R] (iF : F →+* R) (n : ℕ) (A : 𝓞 E → Matrix (Fin n) (Fin n) R), A 1 = 1 → (∀ a b, A (a + b) = A a + A b) → (∀ a b, A (a * b) = A a * A b) → Module.Finite R (balanced H.bar A) ∧ Module.Projective R (balanced H.bar A) ∧ ∀ (m : Ideal R) [m.IsMaximal], 2 * Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] balanced H.bar A) = ∑ τ : E →+* ℂ, GlobalTheory.BalProj.eigRank (algebraMap R m.ResidueField) A (GlobalTheory.BalProj.embR F hF iF τ) * GlobalTheory.BalProj.eigRank (algebraMap R m.ResidueField) A (GlobalTheory.BalProj.embR F hF iF (NumberField.ComplexEmbedding.conjugate τ)) := by
  intro E _ _ _ H F hF R _ iF n A h1 ha hm
  obtain ⟨P, hP, hl, hr⟩ := exists_projectors F hF iF A h1 ha hm
  have hs := embR_sep F hF iF
  obtain ⟨r, hr1, hr2⟩ := exists_retract hP hl hr hs H.bar NumberField.ComplexEmbedding.conjugate
    (fun τ => star_star τ)
    (fun τ h => IsTotallyComplex.complexEmbedding_not_isReal τ (ComplexEmbedding.isReal_iff.2 h))
    (fun τ a => by
      simp only [embR]
      congr 2
      rw [H.bar_eq, ComplexEmbedding.conjugate_coe_eq, IsCMField.complexEmbedding_complexConj])
    (iF 2⁻¹) (by rw [← map_ofNat iF 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one])
  refine ⟨Module.Finite.of_surjective r (fun x => ⟨x, LinearMap.congr_fun hr1 x⟩),
    Module.Projective.of_split _ r hr1, fun m _ => ?_⟩
  letI := Ideal.Quotient.field m
  haveI : CharZero m.ResidueField :=
    charZero_of_injective_ringHom (f := (algebraMap R m.ResidueField).comp iF) (RingHom.injective _)
  apply Nat.cast_injective (R := m.ResidueField)
  have h2 := congrArg (algebraMap (R ⧸ m) m.ResidueField) (finrank_retract _ r hr1 (R ⧸ m))
  rw [map_natCast, ← IsScalarTower.algebraMap_apply] at h2
  push_cast
  simp only [eigRank_eq hP hl hr hs, ← map_mul, ← map_sum, ← hr2]
  rw [map_mul, map_ofNat]
  exact congrArg _ h2

end GlobalTheory.BalProj.Alg
