import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConjInvIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogHeightBoundFromInequalityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiFibrationLieLatticeFullStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetSlopeDegreeInequalityStatement
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.PosSemidefOfForallCombination
import ReciprocityTheory.GeometryOfNumbers.MatrixArithmetic.WeakMatSt
open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder

namespace GlobalTheory.BCIso

section
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] (h : HermFam K V)

theorem form_zero_right (σ : K →+* ℂ) (x : V) : h.form σ x 0 = 0 := by
  have := h.smul_right σ 0 x 0
  simpa using this

theorem form_sum_right (σ : K →+* ℂ) (x : V) {ι : Type*} (s : Finset ι) (f : ι → V) :
    h.form σ x (∑ i ∈ s, f i) = ∑ i ∈ s, h.form σ x (f i) :=
  map_sum (AddMonoidHom.mk' (h.form σ x) (h.add_right σ x)) f s

theorem form_sum_left (σ : K →+* ℂ) (y : V) {ι : Type*} (s : Finset ι) (f : ι → V) :
    h.form σ (∑ i ∈ s, f i) y = ∑ i ∈ s, h.form σ (f i) y := by
  rw [← h.conj_symm, form_sum_right, map_sum]
  exact Finset.sum_congr rfl fun i _ => h.conj_symm σ y (f i)

theorem form_smul_left (σ : K →+* ℂ) (a : K) (x y : V) :
    h.form σ (a • x) y = starRingEnd ℂ (σ a) * h.form σ x y := by
  rw [← h.conj_symm, h.smul_right, map_mul, h.conj_symm]

theorem form_expand (σ : K →+* ℂ) {ι κ : Type*} (s : Finset ι) (t : Finset κ) (c : ι → K) (u : ι → V)
    (d : κ → K) (w : κ → V) :
    h.form σ (∑ i ∈ s, c i • u i) (∑ j ∈ t, d j • w j) =
      ∑ i ∈ s, ∑ j ∈ t, starRingEnd ℂ (σ (c i)) * σ (d j) * h.form σ (u i) (w j) := by
  rw [form_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [form_smul_left, form_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h.smul_right]; ring

end

theorem vec_eq_sum {R : Type*} [Semiring R] {n : ℕ} (y : Fin n → R) :
    y = ∑ i, y i • (Pi.single i 1 : Fin n → R) := by
  ext j; simp [Finset.sum_apply, Pi.single_apply]

theorem form_eq_sum {K : Type*} [Field K] {m : ℕ} (h : HermFam K (Fin m → K)) (σ : K →+* ℂ)
    (x y : Fin m → K) : h.form σ x y = ∑ k, ∑ l, starRingEnd ℂ (σ (x k)) * σ (y l) *
      h.form σ (Pi.single k 1) (Pi.single l 1) := by
  conv_lhs => rw [vec_eq_sum x, vec_eq_sum y]
  exact form_expand h σ _ _ _ _ _ _

theorem bc_form {K K' : Type} [Field K] [Field K'] [NumberField K] [NumberField K'] [Algebra K K'] {m : ℕ}
    (h : HermFam K (Fin m → K)) (h' : HermFam K' (Fin m → K')) (hb : IsBC h h') (σ : K' →+* ℂ)
    (u v : Fin m → K) :
    h'.form σ (fun i => algebraMap K K' (u i)) (fun i => algebraMap K K' (v i)) =
      h.form (σ.comp (algebraMap K K')) u v := by
  rw [form_eq_sum h', form_eq_sum h]
  have hbσ := hb σ
  simp only [hbσ, RingHom.comp_apply]

end GlobalTheory.BCIso

open GlobalTheory.BCIso in
theorem GlobalTheory.baseChange_isometry_injective : ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K'] (n m : ℕ) (α : (Fin n → K) →ₗ[K] (Fin m → K)) (h : HermFam K (Fin m → K)) (hW : HermFam K (Fin n → K)) (h' : HermFam K' (Fin m → K')) (hW' : HermFam K' (Fin n → K')), (∀ σ y z, hW.form σ y z = h.form σ (α y) (α z)) → IsBC h h' → IsBC hW hW' → ∃ β : (Fin n → K') →ₗ[K'] (Fin m → K'), Function.Injective β ∧ (∀ σ y z, h'.form σ (β y) (β z) = hW'.form σ y z) ∧ ∀ y : Fin n → K, β (fun i => algebraMap K K' (y i)) = fun j => algebraMap K K' (α y j) := by
  intro K K' _ _ _ _ _ n m α h hW h' hW' hα hb hbW
  let β : (Fin n → K') →ₗ[K'] (Fin m → K') :=
    Matrix.mulVecLin ((LinearMap.toMatrix' α).map (algebraMap K K'))
  have h3 : ∀ y : Fin n → K, β (fun i => algebraMap K K' (y i)) = fun j => algebraMap K K' (α y j) := by
    intro y
    ext j
    have := RingHom.map_mulVec (algebraMap K K') (LinearMap.toMatrix' α) y j
    rw [LinearMap.toMatrix'_mulVec] at this
    rw [this]
    rfl
  have hiso : ∀ σ y z, h'.form σ (β y) (β z) = hW'.form σ y z := by
    intro σ y z
    conv_lhs => rw [vec_eq_sum y, vec_eq_sum z]
    conv_rhs => rw [vec_eq_sum y, vec_eq_sum z]
    simp only [map_sum, map_smul]
    rw [form_expand, form_expand]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    congr 1
    have e : ∀ k, (Pi.single k 1 : Fin n → K') = fun i => algebraMap K K' ((Pi.single k 1 : Fin n → K) i) := by
      intro k; ext i; by_cases hik : i = k <;> simp [Pi.single_apply, hik]
    rw [e i, e j, h3, h3, bc_form h h' hb, ← hα, ← bc_form hW hW' hbW]
  refine ⟨β, ?_, hiso, h3⟩
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  by_contra hne
  let σ : K' →+* ℂ := (IsAlgClosed.lift : K' →ₐ[ℚ] ℂ).toRingHom
  have hli : LinearIndependent K' ![y] := by
    rw [linearIndependent_unique_iff]; simpa using hne
  have hp := (hW'.posDef σ 1 ![y] hli).diag_pos (i := 0)
  have h0 : hW'.form σ y y = 0 := by
    rw [← hiso, hy, form_zero_right]
  simp [h0] at hp
