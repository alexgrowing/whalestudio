import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIntegralClosureOfEssFiniteTypeIntDomain

open scoped nonZeroDivisors

namespace GlobalTheory.ReducedNormalisation

theorem exists_mem_others_not_mem {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : ι → Ideal R) (hp : ∀ i, (p i).IsPrime) (hmin : ∀ i j, p i ≤ p j → i = j) (i : ι) :
    ∃ a : R, a ∉ p i ∧ ∀ j, j ≠ i → a ∈ p j := by
  by_contra h
  push_neg at h
  have hle : (Finset.univ.erase i).inf p ≤ p i := by
    intro a ha
    by_contra hai
    obtain ⟨j, hj, hja⟩ := h a hai
    exact hja ((Finset.inf_le (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩) : _ ≤ p j) ha)
  obtain ⟨j, hj, hji⟩ := ((hp i).inf_le').1 hle
  exact (Finset.mem_erase.1 hj).1 (hmin j i hji)

theorem exists_conductor_elem {R : Type} [CommRing R] (p : Ideal R) [hp : p.IsPrime] (J : Ideal R)
    (e : R) (he : e ∈ J) (hep : e ∉ p)
    [Module.Finite (R ⧸ p) (integralClosure (R ⧸ p) (FractionRing (R ⧸ p)))] :
    ∃ c : R, c ∉ p ∧ c ∈ J ∧ ∀ d : integralClosure (R ⧸ p) (FractionRing (R ⧸ p)),
      ∃ y ∈ J, algebraMap R (FractionRing (R ⧸ p)) y =
        algebraMap R (FractionRing (R ⧸ p)) c * (d : FractionRing (R ⧸ p)) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R ⧸ p)
    (M := integralClosure (R ⧸ p) (FractionRing (R ⧸ p)))
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (R ⧸ p)⁰
    (S := FractionRing (R ⧸ p)) (s.image Subtype.val)
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (b : R ⧸ p)
  have htp : t ∉ p := by
    intro h
    have h0 : (b : R ⧸ p) = 0 := by rw [← ht]; exact Ideal.Quotient.eq_zero_iff_mem.2 h
    exact nonZeroDivisors.coe_ne_zero b h0
  refine ⟨e * t, fun h => (hp.mem_or_mem h).elim hep htp, J.mul_mem_right t he, fun d => ?_⟩
  have key : ∀ d ∈ Submodule.span (R ⧸ p)
      (s : Set (integralClosure (R ⧸ p) (FractionRing (R ⧸ p)))),
      ∃ y ∈ J, algebraMap R (FractionRing (R ⧸ p)) y =
        algebraMap R (FractionRing (R ⧸ p)) (e * t) * (d : FractionRing (R ⧸ p)) := by
    intro d hd
    induction hd using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨x, hx⟩ := hb (g : FractionRing (R ⧸ p)) (Finset.mem_image_of_mem Subtype.val hg)
      obtain ⟨x', rfl⟩ := Ideal.Quotient.mk_surjective x
      refine ⟨e * x', J.mul_mem_right x' he, ?_⟩
      have h1 : algebraMap R (FractionRing (R ⧸ p)) x' =
          algebraMap R (FractionRing (R ⧸ p)) t * (g : FractionRing (R ⧸ p)) := by
        rw [IsScalarTower.algebraMap_apply R (R ⧸ p) (FractionRing (R ⧸ p)) x',
          IsScalarTower.algebraMap_apply R (R ⧸ p) (FractionRing (R ⧸ p)) t,
          Ideal.Quotient.algebraMap_eq, hx, ht]
        exact Algebra.smul_def _ _
      rw [map_mul, map_mul, h1, mul_assoc]
    | zero => exact ⟨0, J.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨y1, hy1, e1⟩ := hx
      obtain ⟨y2, hy2, e2⟩ := hy
      exact ⟨y1 + y2, J.add_mem hy1 hy2, by
        rw [map_add, e1, e2, ← mul_add]; rfl⟩
    | smul q x _ hx =>
      obtain ⟨y1, hy1, e1⟩ := hx
      obtain ⟨q', rfl⟩ := Ideal.Quotient.mk_surjective q
      refine ⟨q' * y1, J.mul_mem_left q' hy1, ?_⟩
      rw [map_mul, e1]
      show _ = _ * ((Ideal.Quotient.mk p q') • (x : FractionRing (R ⧸ p)))
      rw [Algebra.smul_def, ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      ring
  exact key d (by rw [hs]; trivial)

theorem algebraMap_eq_zero_of_mem {R : Type} [CommRing R] (p : Ideal R) [p.IsPrime] {z : R}
    (hz : z ∈ p) : algebraMap R (FractionRing (R ⧸ p)) z = 0 := by
  rw [IsScalarTower.algebraMap_apply R (R ⧸ p) (FractionRing (R ⧸ p)),
    Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 hz, map_zero]

theorem exists_conductor {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : ι → Ideal R) [hp : ∀ i, (p i).IsPrime] (hmin : ∀ i j, p i ≤ p j → i = j)
    [∀ i, Module.Finite (R ⧸ p i) (integralClosure (R ⧸ p i) (FractionRing (R ⧸ p i)))] :
    ∃ a : R, (∀ i, a ∉ p i) ∧
      ∀ r : (∀ i, integralClosure (R ⧸ p i) (FractionRing (R ⧸ p i))),
        ∃ y : R, algebraMap R _ y = algebraMap R _ a * r := by
  classical
  have hc : ∀ i, ∃ c : R, c ∉ p i ∧ c ∈ (⨅ (j : ι) (_ : j ≠ i), p j) ∧
      ∀ d : integralClosure (R ⧸ p i) (FractionRing (R ⧸ p i)),
        ∃ y ∈ (⨅ (j : ι) (_ : j ≠ i), p j), algebraMap R (FractionRing (R ⧸ p i)) y =
          algebraMap R (FractionRing (R ⧸ p i)) c * (d : FractionRing (R ⧸ p i)) := by
    intro i
    obtain ⟨e, hei, hej⟩ := exists_mem_others_not_mem p hp hmin i
    exact exists_conductor_elem (p i) _ e
      ((Submodule.mem_iInf _).2 fun j => (Submodule.mem_iInf _).2 fun hj => hej j hj) hei
  choose c hcp hcJ hcd using hc
  have hmemJ : ∀ {i k : ι} {z : R}, z ∈ (⨅ (j : ι) (_ : j ≠ i), p j) → i ≠ k → z ∈ p k :=
    fun hz hik => (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hz _) (Ne.symm hik)
  refine ⟨∑ i, c i, fun i h => hcp i ?_, fun r => ?_⟩
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at h
    refine (Submodule.add_mem_iff_left _ (Submodule.sum_mem _ fun j hj => ?_)).1 h
    exact hmemJ (hcJ j) (Finset.mem_erase.1 hj).1
  choose y hyJ hy using fun i => hcd i (r i)
  refine ⟨∑ i, y i, funext fun k => Subtype.ext ?_⟩
  change algebraMap R (FractionRing (R ⧸ p k)) (∑ i, y i) =
    algebraMap R (FractionRing (R ⧸ p k)) (∑ i, c i) * (r k : FractionRing (R ⧸ p k))
  rw [map_sum, map_sum, Finset.sum_mul, Finset.sum_eq_single k, Finset.sum_eq_single k, hy k]
  · intro i _ hik
    rw [algebraMap_eq_zero_of_mem (p k) (hmemJ (hcJ i) hik), zero_mul]
  · intro h; exact absurd (Finset.mem_univ k) h
  · intro i _ hik
    exact algebraMap_eq_zero_of_mem (p k) (hmemJ (hyJ i) hik)
  · intro h; exact absurd (Finset.mem_univ k) h

end GlobalTheory.ReducedNormalisation

namespace GlobalTheory.ReducedNormalisation

theorem exists_finiteIndex_prod_normalDomains :
    ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] [IsReduced R] [Nontrivial R],
      ∃ (n : ℕ) (D : Fin n → Type) (_ : ∀ i, CommRing (D i)) (_ : ∀ i, Algebra R (D i)),
        (∀ i, IsDomain (D i) ∧ IsIntegrallyClosed (D i) ∧ Module.Finite R (D i)) ∧
        Function.Injective (algebraMap R (∀ i, D i)) ∧
        ∃ a : R, a ≠ 0 ∧ ∀ r : (∀ i, D i), ∃ y : R,
          algebraMap R (∀ i, D i) y = algebraMap R (∀ i, D i) a * r := by
  intro R _ _ _ _
  classical
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  letI : Fintype (minimalPrimes R) := (minimalPrimes.finite_of_isNoetherianRing R).fintype
  let e := Fintype.equivFin (minimalPrimes R)
  let p : Fin (Fintype.card (minimalPrimes R)) → Ideal R := fun k => (e.symm k).1
  haveI hp : ∀ k, (p k).IsPrime := fun k => Ideal.minimalPrimes_isPrime (e.symm k).2
  have hmin : ∀ k l, p k ≤ p l → k = l := by
    intro k l h
    have h2 : p l ≤ p k := (e.symm l).2.2 ⟨hp k, bot_le⟩ h
    exact e.symm.injective (Subtype.ext (le_antisymm h h2))
  haveI : ∀ k, Module.Finite (R ⧸ p k) (integralClosure (R ⧸ p k) (FractionRing (R ⧸ p k))) :=
    fun k => by
      have h : Algebra.EssFiniteType ℤ (R ⧸ p k) := Algebra.instEssFiniteTypeQuotientIdeal ℤ R (p k)
      refine @GlobalTheory.finite_integralClosure_of_essFiniteType_int (R ⧸ p k) _ _ ?_
      convert h
      first | exact Subsingleton.elim _ _ | exact Algebra.algebra_ext _ _ fun r => (eq_intCast _ r).trans (eq_intCast _ r).symm
  obtain ⟨a, ha, hr⟩ := exists_conductor p hmin
  have hzero : ∀ {x : R} (k), algebraMap R (integralClosure (R ⧸ p k) (FractionRing (R ⧸ p k))) x = 0 →
      x ∈ p k := by
    intro x k hx
    have h1 : algebraMap R (FractionRing (R ⧸ p k)) x = 0 := congrArg Subtype.val hx
    rw [IsScalarTower.algebraMap_apply R (R ⧸ p k) (FractionRing (R ⧸ p k)),
      Ideal.Quotient.algebraMap_eq] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.1
      ((map_eq_zero_iff _ (IsFractionRing.injective (R ⧸ p k) (FractionRing (R ⧸ p k)))).1 h1)
  refine ⟨Fintype.card (minimalPrimes R),
    fun k => integralClosure (R ⧸ p k) (FractionRing (R ⧸ p k)), fun k => inferInstance,
    fun k => inferInstance, fun k => ⟨inferInstance,
      integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing (R ⧸ p k)),
      Module.Finite.trans (R ⧸ p k) _⟩, ?_, a, ?_, hr⟩
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    have hmem : x ∈ sInf (minimalPrimes R) := Submodule.mem_sInf.2 fun q hq => by
      have := hzero (e ⟨q, hq⟩) (congrFun hx (e ⟨q, hq⟩))
      simpa [p] using this
    rw [minimalPrimes, Ideal.sInf_minimalPrimes] at hmem
    exact IsReduced.eq_zero x (mem_nilradical.mp hmem)
  · intro h0
    obtain ⟨q⟩ := Ideal.nonempty_minimalPrimes (I := (⊥ : Ideal R)) bot_ne_top
    apply ha (e q)
    rw [h0]
    exact zero_mem _

end GlobalTheory.ReducedNormalisation

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

example : ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] [IsReduced R] [Nontrivial R], ∃ (n : ℕ) (D : Fin n → Type) (_ : ∀ i, CommRing (D i)) (_ : ∀ i, Algebra R (D i)), (∀ i, IsDomain (D i) ∧ IsIntegrallyClosed (D i) ∧ Module.Finite R (D i)) ∧ Function.Injective (algebraMap R (∀ i, D i)) ∧ ∃ a : R, a ≠ 0 ∧ ∀ r : (∀ i, D i), ∃ y : R, algebraMap R (∀ i, D i) y = algebraMap R (∀ i, D i) a * r :=
  GlobalTheory.ReducedNormalisation.exists_finiteIndex_prod_normalDomains
