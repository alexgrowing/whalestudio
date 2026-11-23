import Mathlib
import Formalism.HermitianLattices.StatementMass
import Formalism.HermitianLattices.HermitianLatticesProofs.MassBasic

open NumberField

noncomputable section

namespace Formalism.HermitianLatticesTheory

section MassTelescopeAux

variable (K : Type) [Field K] [NumberField K] [StarRing K]

def massTelescope_form (n : ℕ) : (Fin n → K) →ₗ⋆[K] (Fin n → K) →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun x y => ∑ i, star (x i) * y i)
    (by intro m₁ m₂ y; simp [star_add, add_mul, Finset.sum_add_distrib])
    (by
      intro c m y
      simp only [Pi.smul_apply, smul_eq_mul, star_mul, Finset.mul_sum, starRingEnd_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring)
    (by intro m y₁ y₂; simp [mul_add, Finset.sum_add_distrib])
    (by
      intro c m y
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring)

def massTelescope_lat (n : ℕ) : Submodule (RingOfIntegers K) (Fin n → K) :=
  Submodule.span (RingOfIntegers K) (Set.range (Pi.basisFun K (Fin n)))

lemma massTelescope_form_apply (n : ℕ) (x y : Fin n → K) :
    massTelescope_form K n x y = ∑ i, star (x i) * y i := rfl

lemma massTelescope_symm (n : ℕ) : (massTelescope_form K n).IsSymm := by
  have key : ∀ x y : Fin n → K,
      starRingEnd K (massTelescope_form K n x y) = massTelescope_form K n y x := by
    intro x y
    simp only [massTelescope_form_apply, map_sum, starRingEnd_apply, star_mul, star_star]
  first
  | exact key
  | exact ⟨key⟩

lemma massTelescope_ortho (n : ℕ) :
    IsOrthoLattice (massTelescope_form K n) (massTelescope_lat K n) n := by
  unfold IsOrthoLattice
  refine ⟨⇑(Pi.basisFun K (Fin n)), (Pi.basisFun K (Fin n)).linearIndependent,
    (Pi.basisFun K (Fin n)).span_eq, rfl, ?_⟩
  intro i j
  rw [massTelescope_form_apply]
  simp only [Pi.basisFun_apply]
  rw [Finset.sum_eq_single i]
  · by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Pi.single_eq_of_ne hij]
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

lemma massTelescope_isLattice (n : ℕ) : Submodule.IsLattice K (massTelescope_lat K n) where
  fg := Submodule.fg_span (Set.finite_range _)
  span_eq_top := by
    rw [massTelescope_lat, Submodule.span_span_of_tower]
    exact (Pi.basisFun K (Fin n)).span_eq

lemma massTelescope_trace_pos (hCM : IsCMUnram K) (a : K) (ha : a ≠ 0) :
    0 < Algebra.trace ℚ K (star a * a) := by
  haveI : Nonempty (K →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
  have key : ∀ σ : K →ₐ[ℚ] ℂ, σ (star a * a) = ((Complex.normSq (σ a) : ℝ) : ℂ) := by
    intro σ
    have h1 : σ (star a) = starRingEnd ℂ (σ a) := hCM.2.1 (σ : K →+* ℂ) a
    rw [map_mul, h1]
    exact Complex.normSq_eq_conj_mul_self.symm
  have hE : algebraMap ℚ ℂ (Algebra.trace ℚ K (star a * a)) =
      ∑ σ : K →ₐ[ℚ] ℂ, σ (star a * a) := by
    first
    | exact trace_eq_sum_embeddings ℂ
    | exact trace_eq_sum_embeddings (E := ℂ)
    | exact Algebra.trace_eq_sum_embeddings ℂ
  simp only [key] at hE
  rw [eq_ratCast (algebraMap ℚ ℂ)] at hE
  have hR := congrArg Complex.re hE
  simp only [Complex.ratCast_re, Complex.re_sum, Complex.ofReal_re] at hR
  have hpos : (0 : ℝ) < ((Algebra.trace ℚ K (star a * a) : ℚ) : ℝ) := by
    rw [hR]
    exact Finset.sum_pos (fun σ _ => Complex.normSq_pos.mpr ((map_ne_zero σ).mpr ha))
      Finset.univ_nonempty
  exact_mod_cast hpos

lemma massTelescope_trace_nonneg (hCM : IsCMUnram K) (a : K) :
    0 ≤ Algebra.trace ℚ K (star a * a) := by
  by_cases ha : a = 0
  · subst ha
    simp
  · exact le_of_lt (massTelescope_trace_pos K hCM a ha)

lemma massTelescope_def (hCM : IsCMUnram K) (n : ℕ) (x : Fin n → K) (hx : x ≠ 0) :
    0 < Algebra.trace ℚ K (massTelescope_form K n x x) := by
  rw [massTelescope_form_apply, map_sum]
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hx (funext hc)
  exact Finset.sum_pos' (fun j _ => massTelescope_trace_nonneg K hCM (x j))
    ⟨i, Finset.mem_univ _, massTelescope_trace_pos K hCM (x i) hi⟩

lemma massTelescope_std_pos (hCM : IsCMUnram K) (n : ℕ) :
    0 < mass (massTelescope_form K n) (massTelescope_lat K n) := by
  exact (massBasic K (Fin n → K) (massTelescope_form K n) (massTelescope_symm K n)
    (fun x hx => massTelescope_def K hCM n x hx) (massTelescope_lat K n)
    (massTelescope_isLattice K n)).2.2

lemma massTelescope_step (hS : SiegelMassRatio) (hCM : IsCMUnram K) (r : ℕ) (hr : 2 ≤ r) :
    mass (massTelescope_form K (r + 1)) (massTelescope_lat K (r + 1)) =
      mass (massTelescope_form K r) (massTelescope_lat K r) * massRatioRightSide K (r + 1) := by
  have h := hS K hCM (r + 1) (by omega) (Fin (r + 1) → K) (Fin r → K)
    (massTelescope_form K (r + 1)) (massTelescope_form K r) (massTelescope_lat K (r + 1))
    (massTelescope_lat K r) (massTelescope_symm K (r + 1)) (massTelescope_symm K r)
    (massTelescope_ortho K (r + 1)) (by simpa using massTelescope_ortho K r)
  have hp := massTelescope_std_pos K hCM r
  rw [← h]
  field_simp

end MassTelescopeAux

end Formalism.HermitianLatticesTheory
