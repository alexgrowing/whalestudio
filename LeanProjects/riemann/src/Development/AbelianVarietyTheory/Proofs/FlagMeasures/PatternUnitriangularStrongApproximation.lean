import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationAdditiveQuadraticExtensionStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.PatternApprox

theorem exists_clear {Fp Ep : Type} [Field Fp] [ValuativeRel Fp] [TopologicalSpace Fp]
    [IsNonarchimedeanLocalField Fp] [CommRing Ep] [Algebra Fp Ep] [Module.Finite Fp Ep]
    (O : Subring Ep) (hO : ∀ x, x ∈ O ↔ IsIntegral 𝒪[Fp] x) {ι : Type} [Fintype ι] (x : ι → Ep) :
    ∃ a : Fp, a ≠ 0 ∧ ∀ i, algebraMap Fp Ep a * x i ∈ O := by
  have hfr : IsFractionRing 𝒪[Fp] Fp := (Valuation.integer.integers (valuation Fp)).isFractionRing
  have halg : ∀ i, IsAlgebraic 𝒪[Fp] (x i) := fun i =>
    (IsFractionRing.isAlgebraic_iff 𝒪[Fp] Fp Ep).mpr (Algebra.IsIntegral.isIntegral (R := Fp) (x i)).isAlgebraic
  choose y hy0 hyi using fun i => (halg i).exists_integral_multiple
  have hym : ∀ k, algebraMap Fp Ep (y k : Fp) ∈ O := fun k => by
    rw [hO, show algebraMap Fp Ep (y k : Fp) = algebraMap 𝒪[Fp] Ep (y k) from
      (IsScalarTower.algebraMap_apply 𝒪[Fp] Fp Ep (y k)).symm]
    exact isIntegral_algebraMap
  refine ⟨∏ k, (y k : Fp), ?_, fun i => ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro k _ h
    exact hy0 k (Subtype.ext (by simpa using h))
  · have h1 : algebraMap Fp Ep (y i : Fp) * x i ∈ O := by
      rw [hO, show algebraMap Fp Ep (y i : Fp) = algebraMap 𝒪[Fp] Ep (y i) from
        (IsScalarTower.algebraMap_apply 𝒪[Fp] Fp Ep (y i)).symm, ← Algebra.smul_def]
      exact hyi i
    rw [map_prod, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_assoc]
    exact O.mul_mem (O.prod_mem fun k _ => hym k) h1

variable {R : Type} [CommRing R]

theorem det_eq_one {m : ℕ} (I : Fin m → Fin m → Prop) (hI : ∀ i j, I i j → i < j)
    (s : Matrix (Fin m) (Fin m) R) (hs : ∀ i j, ¬ I i j → s i j = if i = j then 1 else 0) : s.det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    rw [hs i i (fun h => lt_irrefl i (hI i i h))]
    simp
  · intro i j hji
    rw [hs i j (fun h => lt_asymm (hI i j h) hji)]
    have hne : i ≠ j := fun h => by subst h; exact lt_irrefl _ hji
    simp [hne]

theorem adjugate_mem {m : ℕ} (O : Subring R) (s : Matrix (Fin m) (Fin m) R) (h : ∀ i j, s i j ∈ O) :
    ∀ i j, s.adjugate i j ∈ O := by
  let S : Matrix (Fin m) (Fin m) O := fun i j => ⟨s i j, h i j⟩
  have hS : O.subtype.mapMatrix S = s := by ext i j; rfl
  intro i j
  rw [← hS, ← RingHom.map_adjugate]
  exact (S.adjugate i j).2

end GlobalTheory.HL.PatternApprox

open GlobalTheory.HL.PatternApprox in

theorem GlobalTheory.HL.pattern_strong_approx : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (m : ℕ) (I : Fin m → Fin m → Prop), (∀ i j, I i j → i < j) → (∀ i j l, I i j → I j l → I i l) → ∀ c : ∀ p, ((A.loc p).Fp)ˣ, {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite → ∀ s : ∀ p, Matrix (Fin m) (Fin m) (A.loc p).Ep, (∀ p i j, ¬ I i j → s p i j = if i = j then 1 else 0) → {p | ¬ IsIntM (A.L p) (s p)}.Finite → ∃ t : Matrix (Fin m) (Fin m) E, (∀ i j, ¬ I i j → t i j = if i = j then 1 else 0) ∧ ∀ p i j, ∃ o ∈ (A.L p).O, ((s p)⁻¹ * t.map (A.loc p).ιE - 1) i j = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) * o := by
  intro F E _ _ _ _ _ sig A m I hlt _htr c hc s hs hsint
  have hinv : ∀ p, (s p)⁻¹ = (s p).adjugate := fun p => by
    rw [Matrix.inv_def, det_eq_one I hlt (s p) (hs p), Ring.inverse_one, one_smul]
  have hcl : ∀ p, ∃ a : ((A.loc p).Fp)ˣ, (IsIntM (A.L p) (s p) → a = 1) ∧
      ∀ i j, algebraMap (A.loc p).Fp (A.loc p).Ep (a : (A.loc p).Fp) * (s p)⁻¹ i j ∈ (A.L p).O := by
    intro p
    haveI := (A.loc p).lf
    haveI : Module.Free (A.loc p).Fp (A.loc p).Ep := (A.loc p).free
    haveI : Module.Finite (A.loc p).Fp (A.loc p).Ep := Module.finite_of_finrank_eq_succ (A.loc p).rank
    by_cases h : IsIntM (A.L p) (s p)
    · refine ⟨1, fun _ => rfl, fun i j => ?_⟩
      rw [Units.val_one, map_one, one_mul, hinv p]
      exact adjugate_mem (A.L p).O (s p) h i j
    · obtain ⟨a, ha0, ha⟩ := exists_clear (A.L p).O (A.L p).O_def
        (fun ij : Fin m × Fin m => (s p)⁻¹ ij.1 ij.2)
      exact ⟨Units.mk0 a ha0, fun h' => absurd h' h, fun i j => ha (i, j)⟩
  choose c' hc'1 hc'2 using hcl
  let d : ∀ p, ((A.loc p).Fp)ˣ := fun p => c p * c' p
  have hd : {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = d p}.Finite := by
    apply (hc.union hsint).subset
    intro p hp
    by_contra hno
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hno
    obtain ⟨⟨u, hu⟩, hint⟩ := hno
    exact hp ⟨u, by simp [d, hc'1 p hint, hu]⟩
  have hap := (GlobalTheory.T.strong_approximation_additive_quadratic_extension A d hd).2.1
  have hx : ∀ i j, ∃ x : E, ∀ p, ∃ o ∈ (A.L p).O,
      (A.loc p).ιE x - s p i j = algebraMap (A.loc p).Fp (A.loc p).Ep (d p : (A.loc p).Fp) * o :=
    fun i j => hap (fun p => s p i j) (hsint.subset fun p hp hi => hp (hi i j))
  choose x hx using hx
  refine ⟨fun i j => if I i j then x i j else if i = j then 1 else 0, fun i j h => by simp [h], fun p i j => ?_⟩
  set t : Matrix (Fin m) (Fin m) E := fun i j => if I i j then x i j else if i = j then 1 else 0 with ht
  have hD : ∀ k l, ∃ o ∈ (A.L p).O, (t.map (A.loc p).ιE - s p) k l =
      algebraMap (A.loc p).Fp (A.loc p).Ep (d p : (A.loc p).Fp) * o := by
    intro k l
    by_cases hkl : I k l
    · obtain ⟨o, ho, he⟩ := hx k l p
      refine ⟨o, ho, ?_⟩
      rw [← he]
      show (A.loc p).ιE (t k l) - s p k l = (A.loc p).ιE (x k l) - s p k l
      rw [ht]
      simp only [hkl, if_true]
    · refine ⟨0, (A.L p).O.zero_mem, ?_⟩
      rw [Matrix.sub_apply, Matrix.map_apply, hs p k l hkl, mul_zero]
      simp only [ht, hkl, if_false]
      split_ifs <;> simp
  choose o ho hoeq using hD
  have hunit : (s p)⁻¹ * s p = 1 :=
    Matrix.nonsing_inv_mul _ (by rw [det_eq_one I hlt (s p) (hs p)]; exact isUnit_one)
  have heq : (s p)⁻¹ * t.map (A.loc p).ιE - 1 = (s p)⁻¹ * (t.map (A.loc p).ιE - s p) := by
    rw [Matrix.mul_sub, hunit]
  refine ⟨∑ k, (algebraMap (A.loc p).Fp (A.loc p).Ep (c' p : (A.loc p).Fp) * (s p)⁻¹ i k) * o k j,
    (A.L p).O.sum_mem fun k _ => (A.L p).O.mul_mem (hc'2 p i k) (ho k j), ?_⟩
  rw [heq, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hoeq k j]
  simp only [d, Units.val_mul, map_mul]
  ring
