import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HermDiagCM

open ComplexConjugate

theorem matrix_eq_zero_of_im_form {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (Λ : Submodule ℤ (Fin n → ℂ)) (hs : Submodule.span ℝ (Λ : Set (Fin n → ℂ)) = ⊤)
    (h0 : ∀ v ∈ Λ, ∀ v' ∈ Λ, (v ⬝ᵥ M.mulVec (star v')).im = 0) : M = 0 := by
  let B : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun v v' => (v ⬝ᵥ M.mulVec (star v')).im)
      (fun a b c => by simp [add_dotProduct])
      (fun r a b => by simp [smul_dotProduct])
      (fun a b c => by simp [star_add, Matrix.mulVec_add, dotProduct_add])
      (fun r a b => by simp [star_smul, Matrix.mulVec_smul, dotProduct_smul])
  have h1 : ∀ v ∈ Λ, B v = 0 := fun v hv =>
    LinearMap.ext_on hs (fun v' hv' => by simpa [B] using h0 v hv v' hv')
  have hB : B = 0 := LinearMap.ext_on hs (fun v hv => by simpa using h1 v hv)
  have him : ∀ z w : Fin n → ℂ, (z ⬝ᵥ M.mulVec (star w)).im = 0 := fun z w => by
    have := congrArg (fun f => f z w) hB
    simpa [B] using this
  have hall : ∀ z w : Fin n → ℂ, z ⬝ᵥ M.mulVec (star w) = 0 := fun z w => by
    apply Complex.ext
    · have := him (Complex.I • z) w
      simpa [smul_dotProduct] using this
    · simpa using him z w
  ext i j
  have := hall (Pi.single i 1) (Pi.single j 1)
  simpa [Matrix.mulVec_single, single_dotProduct] using this

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem sum_embeddings_eq {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hφ : GlobalTheory.CMVal.IsCMType φ)
    (w : E) : ∑ σ : E →+* ℂ, σ w = ∑ i, (φ i w + conj (φ i w)) := by
  let f : I × Bool → (E →+* ℂ) := fun p => cond p.2 (ComplexEmbedding.conjugate (φ p.1)) (φ p.1)
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨i, a⟩ ⟨j, b⟩ hij
      have uniq : ∀ k l, φ k = φ l ∨ φ k = ComplexEmbedding.conjugate (φ l) → k = l := by
        intro k l hkl
        obtain ⟨m, -, hm⟩ := hφ (φ k)
        exact (hm k (Or.inl rfl)).trans (hm l hkl).symm
      cases a <;> cases b <;> simp only [f, cond_true, cond_false] at hij
      · simp [uniq i j (Or.inl hij)]
      · have hij' := uniq i j (Or.inr hij)
        subst hij'
        exact absurd (ComplexEmbedding.isReal_iff.mpr hij.symm)
          (IsTotallyComplex.complexEmbedding_not_isReal (φ i))
      · have hij' := uniq j i (Or.inr hij.symm)
        subst hij'
        exact absurd (ComplexEmbedding.isReal_iff.mpr hij)
          (IsTotallyComplex.complexEmbedding_not_isReal (φ j))
      · have : φ i = φ j := by
          have := congrArg ComplexEmbedding.conjugate hij
          simpa using this
        simp [uniq i j (Or.inl this)]
    · intro σ
      obtain ⟨i, hi, -⟩ := hφ σ
      rcases hi with h | h
      · exact ⟨(i, false), h.symm⟩
      · exact ⟨(i, true), h.symm⟩
  rw [← Fintype.sum_bijective f hf (fun p => f p w) (fun σ => σ w) (fun _ => rfl),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Fintype.sum_bool]
  simp [f, ComplexEmbedding.conjugate_coe_eq, add_comm]

theorem sum_embeddings_map (g : ℂ ≃+* ℂ) (w : E) :
    ∑ σ : E →+* ℂ, g (σ w) = ∑ σ : E →+* ℂ, σ w := by
  let eq : (E →+* ℂ) ≃ (E →+* ℂ) :=
    { toFun := fun σ => (g : ℂ →+* ℂ).comp σ
      invFun := fun σ => (g.symm : ℂ →+* ℂ).comp σ
      left_inv := fun σ => by ext x; simp
      right_inv := fun σ => by ext x; simp }
  exact Fintype.sum_equiv eq _ _ (fun σ => by simp [eq])

theorem term_eq (σ : E →+* ℂ) (β x x' : E) (hβ : conj (σ β) = -σ β) :
    (2 * Complex.I * σ β) * (((σ x * conj (σ x')).im : ℝ) : ℂ) =
      σ (β * x * IsCMField.complexConj E x') + conj (σ (β * x * IsCMField.complexConj E x')) := by
  have e1 : σ (β * x * IsCMField.complexConj E x') = σ β * (σ x * conj (σ x')) := by
    rw [map_mul, map_mul, IsCMField.complexEmbedding_complexConj]; ring
  rw [e1, map_mul, hβ]
  have hs := Complex.sub_conj (σ x * conj (σ x'))
  push_cast at hs
  linear_combination (-σ β) * hs

end CM

end GlobalTheory.HermDiagCM

open ComplexConjugate in

theorem GlobalTheory.HermDiagCM.diagonal_of_conj_form : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), 0 < d → δ ^ 2 = -(d : K) →
    ∀ g : ℂ ≃+* ℂ, (∀ x, g (io x) = io x) →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) →
      ∀ (n : ℕ) (e : Fin n ≃ I) (Λ : Submodule ℤ (Fin n → ℂ)) (L : Set E),
        Submodule.span ℝ (Λ : Set (Fin n → ℂ)) = ⊤ → (∀ w, w ∈ Λ ↔ ∃ x ∈ L, w = fun j ↦ g (φ (e j) x)) →
      ∀ (h : I → ℝ) (β : E), (∀ i, (h i : ℂ) = 2 * Complex.I * φ i β) → ∀ N : ℝ, 0 < N →
      ∀ Hm : Matrix (Fin n) (Fin n) ℂ, Hm.IsHermitian →
        (∀ x ∈ L, ∀ x' ∈ L, ((fun j ↦ g (φ (e j) x)) ⬝ᵥ Hm.mulVec (star fun j ↦ g (φ (e j) x'))).im =
          N⁻¹ * ∑ i, h i * (φ i x * starRingEnd ℂ (φ i x')).im) →
        ∃ h' : I → ℝ, Hm = Matrix.diagonal (fun j ↦ (h' (e j) : ℂ)) ∧
          ∀ i, g ((h i : ℂ) * (Real.sqrt d : ℝ)) = (N : ℂ) * ((h' i : ℂ) * (Real.sqrt d : ℝ)) := by
  intro K _ _ d δ io hd hδ g hg E _ _ _ _ I _ φ hφ hio n e Λ L hs hΛ h β hh N hN Hm hHm hform
  have hconj : ∀ (σ : E →+* ℂ) (y : E), conj (σ y) = σ (IsCMField.complexConj E y) :=
    fun σ y => (IsCMField.complexEmbedding_complexConj E σ y).symm
  have hgcomp : ∀ i y, ((g : ℂ →+* ℂ).comp (φ i)) y = g (φ i y) := fun i y => rfl
  have hβi : ∀ i, conj (φ i β) = -(φ i β) := by
    intro i
    have h2 : conj ((h i : ℂ)) = (h i : ℂ) := Complex.conj_ofReal _
    rw [hh i, map_mul, map_mul, Complex.conj_I, map_ofNat] at h2
    have h3 : (2 * Complex.I : ℂ) ≠ 0 := by simp
    have h4 : (2 * Complex.I) * conj (φ i β) = (2 * Complex.I) * (-(φ i β)) := by
      linear_combination -h2
    exact mul_left_cancel₀ h3 h4
  have hcβ : ∀ i, IsCMField.complexConj E β = -β := fun i =>
    (φ i).injective (by rw [← hconj, hβi, map_neg])
  have hgc : ∀ i y, conj (g (φ i y)) = g (conj (φ i y)) := by
    intro i y
    rw [← hgcomp, hconj, hconj, hgcomp]
  have hgβ : ∀ i, conj (g (φ i β)) = -(g (φ i β)) := by
    intro i
    rw [hgc, hβi, map_neg]
  set h' : I → ℝ := fun i => ((2 * Complex.I * g (φ i β)) / N).re with hh'def
  have hh' : ∀ i, (h' i : ℂ) = 2 * Complex.I * g (φ i β) / N := by
    intro i
    exact Complex.conj_eq_iff_re.mp (by
      rw [map_div₀, map_mul, map_mul, Complex.conj_I, hgβ i, map_ofNat, Complex.conj_ofReal]; ring)
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨h', ?_, ?_⟩
  · set D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun j ↦ (h' (e j) : ℂ)) with hD
    suffices Hm - D = 0 from sub_eq_zero.mp this
    apply matrix_eq_zero_of_im_form (Hm - D) Λ hs
    intro v hv v' hv'
    obtain ⟨x, hx, rfl⟩ := (hΛ v).mp hv
    obtain ⟨x', hx', rfl⟩ := (hΛ v').mp hv'
    rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_im, hform x hx x' hx', sub_eq_zero]
    have hDv : ((fun j ↦ g (φ (e j) x)) ⬝ᵥ D.mulVec (star fun j ↦ g (φ (e j) x'))).im =
        ∑ i, h' i * (g (φ i x) * conj (g (φ i x'))).im := by
      rw [dotProduct, Complex.im_sum]
      rw [← Equiv.sum_comp e (fun i => h' i * (g (φ i x) * conj (g (φ i x'))).im)]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [hD, Matrix.mulVec_diagonal, Pi.star_apply, Complex.star_def]
      rw [mul_left_comm, Complex.im_ofReal_mul]
    rw [hDv]
    apply Complex.ofReal_injective
    push_cast
    simp only [hh, hh']
    set w := β * x * IsCMField.complexConj E x' with hw
    have A : ∀ i, 2 * Complex.I * g (φ i β) / N * (((g (φ i x) * conj (g (φ i x'))).im : ℝ) : ℂ) =
        (N : ℂ)⁻¹ * (g (φ i w) + conj (g (φ i w))) := by
      intro i
      have := term_eq ((g : ℂ →+* ℂ).comp (φ i)) β x x' (by rw [hgcomp]; exact hgβ i)
      simp only [hgcomp] at this
      rw [div_eq_mul_inv, mul_comm _ (N : ℂ)⁻¹, _root_.mul_assoc, this]
    have B : ∀ i, 2 * Complex.I * φ i β * (((φ i x * conj (φ i x')).im : ℝ) : ℂ) =
        φ i w + conj (φ i w) := fun i => term_eq (φ i) β x x' (hβi i)
    rw [Finset.sum_congr rfl (fun i _ => A i), Finset.sum_congr rfl (fun i _ => B i),
      ← Finset.mul_sum]
    congr 1
    rw [← sum_embeddings_eq φ hφ w, ← sum_embeddings_map g w, ← map_sum, sum_embeddings_eq φ hφ w,
      map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_add, hgc]
  · intro i
    have key : g (Complex.I * (Real.sqrt d : ℂ)) = Complex.I * (Real.sqrt d : ℂ) := by
      have hsq : (Complex.I * (Real.sqrt d : ℂ)) ^ 2 = -(d : ℂ) := by
        rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
        push_cast; ring
      have hio2 : (io δ) ^ 2 = -(d : ℂ) := by rw [← map_pow, hδ, map_neg, map_natCast]
      have hprod : (io δ - Complex.I * (Real.sqrt d : ℂ)) * (io δ + Complex.I * (Real.sqrt d : ℂ)) = 0 := by
        linear_combination hio2 - hsq
      rcases mul_eq_zero.mp hprod with h1 | h1
      · have h5 : Complex.I * (Real.sqrt d : ℂ) = io δ := by linear_combination -h1
        rw [h5, hg]
      · have h5 : Complex.I * (Real.sqrt d : ℂ) = -io δ := by linear_combination h1
        rw [h5, map_neg, hg]
    rw [hh i, hh' i]
    have e2 : 2 * Complex.I * φ i β * (Real.sqrt d : ℂ) = 2 * φ i β * (Complex.I * (Real.sqrt d : ℂ)) := by
      ring
    rw [e2, map_mul, map_mul, key, map_ofNat]
    field_simp
