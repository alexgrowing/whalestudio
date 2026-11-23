import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexPoints
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory MvPolynomial GroundTheory.Arith.SchemeCoh
open scoped LinearAlgebra.Projectivization NumberField

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ProjScheme

variable (A : Type u) [CommRing A] (N : ℕ)

def baseEval : MvPolynomial (Fin (N + 1)) A →+* Γ(Spec (.of A), ⊤) :=
  (Scheme.ΓSpecIso (.of A)).inv.hom.comp (MvPolynomial.eval (Pi.single 0 1))

lemma X_zero_mem_irrelevant :
    (MvPolynomial.X 0 : MvPolynomial (Fin (N + 1)) A) ∈ HomogeneousIdeal.irrelevant (ProjSpace.grading A N) := by
  rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
    DirectSum.decompose_of_mem_ne _ (ProjSpace.X_mem 0) one_ne_zero]

lemma baseEval_irrelevant :
    (HomogeneousIdeal.irrelevant (ProjSpace.grading A N)).toIdeal.map (baseEval A N) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have : baseEval A N (MvPolynomial.X 0) = 1 := by simp [baseEval]
  rw [← this]
  exact Ideal.mem_map_of_mem _ (X_zero_mem_irrelevant A N)

def baseSection : Spec (.of A) ⟶ projectiveSpace A N :=
  Proj.fromOfGlobalSections (ProjSpace.grading A N) (baseEval A N) (baseEval_irrelevant A N)

lemma baseSection_toSpecBase : baseSection A N ≫ ProjSpace.toSpecBase A N = 𝟙 _ := by
  rw [ProjSpace.toSpecBase, ← Category.assoc, baseSection, Proj.fromOfGlobalSections_toSpecZero,
    Category.assoc, ← Spec.map_comp]
  have : CommRingCat.ofHom (algebraMap A (ProjSpace.grading A N 0)) ≫
      CommRingCat.ofHom ((baseEval A N).comp (algebraMap _ _)) = (Scheme.ΓSpecIso (.of A)).inv := by
    ext a
    change (Scheme.ΓSpecIso (.of A)).inv.hom (MvPolynomial.eval (Pi.single 0 1)
      (MvPolynomial.C a)) = (Scheme.ΓSpecIso (.of A)).inv.hom a
    rw [MvPolynomial.eval_C]
  rw [this, toSpecΓ_SpecMap_ΓSpecIso_inv]

instance : IsClosedImmersion (baseSection A N) := by
  have : IsClosedImmersion (baseSection A N ≫ ProjSpace.toSpecBase A N) := by
    rw [baseSection_toSpecBase]; infer_instance
  exact IsClosedImmersion.of_comp _ (ProjSpace.toSpecBase A N)

def base : ProjScheme A N where
  X := Spec (.of A)
  ι := baseSection A N
  isClosedImmersion := inferInstance

variable {A N}

lemma mem_baseSection_of_pos (p : Spec (.of A)) {f : MvPolynomial (Fin (N + 1)) A} {n : ℕ}
    (hn : 0 < n) (hf : f ∈ ProjSpace.grading A N n) :
    f ∈ ((baseSection A N).base p).asHomogeneousIdeal ↔
      MvPolynomial.eval (Pi.single 0 1) f ∈ p.asIdeal := by
  have h := Proj.fromOfGlobalSections_preimage_basicOpen (ProjSpace.grading A N) (baseEval A N)
    (baseEval_irrelevant A N) hn hf
  have h' : p ∈ (baseSection A N) ⁻¹ᵁ Proj.basicOpen (ProjSpace.grading A N) f ↔
      p ∈ (Spec (.of A)).basicOpen (baseEval A N f) := by
    rw [baseSection, h]
  rw [baseEval, RingHom.comp_apply, basicOpen_eq_of_affine] at h'
  rw [← not_iff_not]
  exact h'

lemma mem_baseSection (p : Spec (.of A)) {f : MvPolynomial (Fin (N + 1)) A} {n : ℕ}
    (hf : f ∈ ProjSpace.grading A N n) :
    f ∈ ((baseSection A N).base p).asHomogeneousIdeal ↔
      MvPolynomial.eval (Pi.single 0 1) f ∈ p.asIdeal := by
  have h0 : (MvPolynomial.X 0 : MvPolynomial (Fin (N + 1)) A) ∉ ((baseSection A N).base p).asHomogeneousIdeal := by
    rw [mem_baseSection_of_pos p Nat.one_pos (ProjSpace.X_mem 0), eval_X, Pi.single_eq_same]
    exact (Ideal.ne_top_iff_one _).1 p.isPrime.ne_top
  have hX := mem_baseSection_of_pos p (by omega : 0 < 1 + n)
    (SetLike.mul_mem_graded (ProjSpace.X_mem 0) hf)
  rw [map_mul, eval_X, Pi.single_eq_same, one_mul] at hX
  have hp := ((baseSection A N).base p).isPrime
  constructor
  · intro h
    exact hX.1 (((baseSection A N).base p).asHomogeneousIdeal.toIdeal.mul_mem_left _ h)
  · intro h
    exact (hp.mem_or_mem (hX.2 h)).resolve_left h0

theorem complexPoints_base (ρ : A →+* ℂ) :
    (base A N).complexPoints ρ =
      {Projectivization.mk ℂ (Pi.single 0 1) (by simp [funext_iff, Pi.single_apply])} := by
  have hval : ∀ f : MvPolynomial (Fin (N + 1)) A,
      evalAt ρ (Pi.single 0 1) f = ρ (MvPolynomial.eval (Pi.single 0 1) f) := by
    intro f
    rw [evalAt, MvPolynomial.eval, coe_eval₂Hom, eval₂_comp_left]
    congr 1
    funext j
    by_cases hj : j = 0
    · subst hj; simp
    · simp [hj]
  ext v
  induction v using Projectivization.ind with
  | h w hw =>
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro ⟨p, hp⟩
      have hzero : ∀ j, j ≠ 0 → w j = 0 := by
        intro j hj
        have h1 : (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ∈ ((baseSection A N).base p).asHomogeneousIdeal := by
          rw [mem_baseSection p (ProjSpace.X_mem j), eval_X, Pi.single_eq_of_ne hj]
          exact zero_mem _
        change (baseSection A N).base p = _ at hp
        rw [hp, mem_projPoint ρ w hw (ProjSpace.X_mem j)] at h1
        simpa using h1
      have h0 : w 0 ≠ 0 := by
        intro h
        exact hw (funext fun j => by by_cases hj : j = 0 <;> simp_all)
      rw [Projectivization.mk_eq_mk_iff]
      refine ⟨Units.mk0 (w 0) h0, ?_⟩
      funext j
      by_cases hj : j = 0
      · subst hj; simp
      · simp [hzero j hj, hj]
    · intro hv
      rw [hv]
      let p : Spec (.of A) := (⟨RingHom.ker ρ, RingHom.ker_isPrime ρ⟩ : PrimeSpectrum A)
      refine ⟨p, ?_⟩
      refine projPoint_ext fun d f hf => ?_
      change f ∈ ((baseSection A N).base p).asHomogeneousIdeal ↔ _
      rw [mem_baseSection _ hf, mem_projPoint ρ _ _ hf, hval]
      exact RingHom.mem_ker

end ProjScheme

variable {N : ℕ} (K : Type) [Field K]

def complexPointsAt (X : ProjScheme (𝓞 K) N) (σ : K →+* ℂ) : Set (CP N) :=
  X.complexPoints (σ.comp (algebraMap (𝓞 K) K))

variable {K}

end

end GroundTheory.Heights₂.Heights
