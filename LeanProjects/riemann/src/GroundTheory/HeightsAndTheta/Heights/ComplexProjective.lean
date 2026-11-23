import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjSpace
import GroundTheory.HeightsAndTheta.Heights.ProjTopology
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial GroundTheory.Arith.SchemeCoh
open scoped LinearAlgebra.Projectivization

noncomputable section

abbrev CP (N : ℕ) := ℙ ℂ (Fin (N + 1) → ℂ)

variable {N : ℕ}

namespace CP

def conjVec : (Fin (N + 1) → ℂ) →ₛₗ[starRingEnd ℂ] (Fin (N + 1) → ℂ) where
  toFun w k := starRingEnd ℂ (w k)
  map_add' w w' := by ext k; simp
  map_smul' c w := by ext k; simp

lemma conjVec_apply (w : Fin (N + 1) → ℂ) (k : Fin (N + 1)) :
    conjVec w k = starRingEnd ℂ (w k) := rfl

lemma conjVec_injective : Function.Injective (conjVec (N := N)) := by
  intro w w' h
  ext k
  exact (starRingEnd ℂ).injective (congrFun h k)

lemma conjVec_ne_zero {w : Fin (N + 1) → ℂ} (hw : w ≠ 0) : conjVec w ≠ 0 :=
  fun h => hw (conjVec_injective (h.trans (map_zero _).symm))

def conj : CP N → CP N := Projectivization.map (conjVec (N := N)) conjVec_injective

lemma conj_mk (w : Fin (N + 1) → ℂ) (hw : w ≠ 0) :
    conj (Projectivization.mk ℂ w hw) = Projectivization.mk ℂ (conjVec w) (conjVec_ne_zero hw) :=
  Projectivization.map_mk _ _ _ _

lemma conj_conj (v : CP N) : conj (conj v) = v := by
  induction v using Projectivization.ind with
  | h w hw =>
    rw [conj_mk, conj_mk]
    congr 1
    ext k
    simp [conjVec_apply]

lemma continuous_conj : Continuous (conj : CP N → CP N) := by
  apply ProjTopology.continuous_iff.mpr
  have : (conj ∘ Projectivization.mk' ℂ : {w : Fin (N + 1) → ℂ // w ≠ 0} → CP N) =
      Projectivization.mk' ℂ ∘ fun w => ⟨conjVec w.1, conjVec_ne_zero w.2⟩ := by
    funext w
    exact conj_mk w.1 w.2
  rw [this]
  refine ProjTopology.continuous_mk'.comp (Continuous.subtype_mk ?_ _)
  exact continuous_pi fun k => Complex.continuous_conj.comp
    ((continuous_apply k).comp continuous_subtype_val)

end CP

variable {A : Type*} [CommRing A]

abbrev evalAt (ρ : A →+* ℂ) (w : Fin (N + 1) → ℂ) (f : MvPolynomial (Fin (N + 1)) A) : ℂ :=
  eval₂ ρ w f

lemma evalAt_smul (ρ : A →+* ℂ) {f : MvPolynomial (Fin (N + 1)) A} {d : ℕ}
    (hf : f.IsHomogeneous d) (c : ℂ) (w : Fin (N + 1) → ℂ) :
    evalAt ρ (c • w) f = c ^ d * evalAt ρ w f := by
  rw [evalAt, evalAt, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ k, m k = d := by
    have := hf (mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hd]
  ring

lemma evalAt_conj (ρ : A →+* ℂ) (w : Fin (N + 1) → ℂ) (f : MvPolynomial (Fin (N + 1)) A) :
    evalAt ((starRingEnd ℂ).comp ρ) (CP.conjVec w) f = starRingEnd ℂ (evalAt ρ w f) := by
  rw [evalAt, evalAt, eval₂_comp_left]
  rfl

lemma continuous_evalAt (ρ : A →+* ℂ) (f : MvPolynomial (Fin (N + 1)) A) :
    Continuous fun w : Fin (N + 1) → ℂ => evalAt ρ w f := by
  have : (fun w : Fin (N + 1) → ℂ => evalAt ρ w f) = fun w => eval w (map ρ f) := by
    funext w; rw [eval_map]
  rw [this]
  exact MvPolynomial.continuous_eval _

attribute [local instance] MvPolynomial.gradedAlgebra

def vanishingAt (ρ : A →+* ℂ) (w : Fin (N + 1) → ℂ) : Ideal (MvPolynomial (Fin (N + 1)) A) :=
  RingHom.ker (eval₂Hom ρ w)

lemma mem_vanishingAt (ρ : A →+* ℂ) (w : Fin (N + 1) → ℂ) (f : MvPolynomial (Fin (N + 1)) A) :
    f ∈ vanishingAt ρ w ↔ evalAt ρ w f = 0 := RingHom.mem_ker

def projPointOf (ρ : A →+* ℂ) (w : Fin (N + 1) → ℂ) (hw : w ≠ 0) : projectiveSpace A N where
  asHomogeneousIdeal := (vanishingAt ρ w).homogeneousCore (ProjSpace.grading A N)
  isPrime := (RingHom.ker_isPrime _).homogeneousCore
  not_irrelevant_le := by
    intro h
    obtain ⟨k, hk⟩ : ∃ k, w k ≠ 0 := by
      by_contra! h'
      exact hw (funext h')
    have hX : (X k : MvPolynomial (Fin (N + 1)) A) ∈ HomogeneousIdeal.irrelevant
        (ProjSpace.grading A N) := by
      rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
        DirectSum.decompose_of_mem_ne _ (ProjSpace.X_mem k) one_ne_zero]
    have := Ideal.toIdeal_homogeneousCore_le _ _ (h hX)
    rw [mem_vanishingAt] at this
    simp [evalAt] at this
    exact hk this

lemma mem_projPointOf (ρ : A →+* ℂ) {w : Fin (N + 1) → ℂ} (hw : w ≠ 0)
    {f : MvPolynomial (Fin (N + 1)) A} {d : ℕ} (hf : f ∈ ProjSpace.grading A N d) :
    f ∈ (projPointOf ρ w hw).asHomogeneousIdeal ↔ evalAt ρ w f = 0 := by
  rw [← mem_vanishingAt]
  constructor
  · exact fun h => Ideal.toIdeal_homogeneousCore_le _ _ h
  · exact fun h => Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨d, hf⟩ h

lemma projPoint_ext {x y : projectiveSpace A N}
    (h : ∀ d, ∀ f ∈ ProjSpace.grading A N d,
      f ∈ x.asHomogeneousIdeal ↔ f ∈ y.asHomogeneousIdeal) : x = y := by
  have : x.asHomogeneousIdeal = y.asHomogeneousIdeal := HomogeneousIdeal.ext' h
  cases x; cases y
  cases this
  rfl

lemma projPointOf_smul (ρ : A →+* ℂ) {w : Fin (N + 1) → ℂ} (hw : w ≠ 0) {c : ℂ} (hc : c ≠ 0) :
    projPointOf ρ (c • w) (smul_ne_zero hc hw) = projPointOf ρ w hw := by
  refine projPoint_ext fun d f hf => ?_
  rw [mem_projPointOf ρ _ hf, mem_projPointOf ρ _ hf, evalAt_smul ρ hf, mul_eq_zero,
    or_iff_right (pow_ne_zero _ hc)]

def projPoint (ρ : A →+* ℂ) (v : CP N) : projectiveSpace A N :=
  projPointOf ρ v.rep v.rep_nonzero

lemma projPoint_mk (ρ : A →+* ℂ) (w : Fin (N + 1) → ℂ) (hw : w ≠ 0) :
    projPoint ρ (Projectivization.mk ℂ w hw) = projPointOf ρ w hw := by
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ (Projectivization.rep_nonzero _) hw).1
    (Projectivization.mk_rep (Projectivization.mk ℂ w hw))
  rw [projPoint]
  have e : (Projectivization.mk ℂ w hw).rep = (c : ℂ) • w := hc.symm
  simp_rw [e]
  exact projPointOf_smul ρ hw (Units.ne_zero _)

lemma mem_projPoint (ρ : A →+* ℂ) (w : Fin (N + 1) → ℂ) (hw : w ≠ 0)
    {f : MvPolynomial (Fin (N + 1)) A} {d : ℕ} (hf : f ∈ ProjSpace.grading A N d) :
    f ∈ (projPoint ρ (Projectivization.mk ℂ w hw)).asHomogeneousIdeal ↔ evalAt ρ w f = 0 := by
  rw [projPoint_mk, mem_projPointOf ρ hw hf]

lemma isClosed_setOf_mem_projPoint (ρ : A →+* ℂ) {f : MvPolynomial (Fin (N + 1)) A} {d : ℕ}
    (hf : f ∈ ProjSpace.grading A N d) :
    IsClosed {v : CP N | f ∈ (projPoint ρ v).asHomogeneousIdeal} := by
  rw [ProjTopology.isClosed_iff]
  have : (Projectivization.mk' ℂ) ⁻¹' {v : CP N | f ∈ (projPoint ρ v).asHomogeneousIdeal} =
      {w : {w : Fin (N + 1) → ℂ // w ≠ 0} | evalAt ρ w.1 f = 0} := by
    ext w
    exact mem_projPoint ρ w.1 w.2 hf
  rw [this]
  exact isClosed_eq ((continuous_evalAt ρ f).comp continuous_subtype_val) continuous_const

lemma projPoint_conj (ρ : A →+* ℂ) (v : CP N) :
    projPoint ((starRingEnd ℂ).comp ρ) (CP.conj v) = projPoint ρ v := by
  induction v using Projectivization.ind with
  | h w hw =>
    rw [CP.conj_mk]
    refine projPoint_ext fun d f hf => ?_
    rw [mem_projPoint _ _ _ hf, mem_projPoint _ _ _ hf, evalAt_conj, map_eq_zero]

end

end GroundTheory.Heights₂.Heights
