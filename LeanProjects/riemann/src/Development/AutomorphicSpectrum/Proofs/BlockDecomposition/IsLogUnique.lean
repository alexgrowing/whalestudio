import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.CrisLog

variable {l : ℕ} [Fact l.Prime]

theorem dpw_mul' {R : Type} [CommRing R] (k : ℕ) (c x : WittVector l R) :
    dpw k (c * x) = algebraMap _ (WL l R) c ^ k * dpw k x := by
  simp only [dpw, map_mul, mul_pow]; ring

theorem dpw_idem {R : Type} [CommRing R] (k : ℕ) {e x x' : WittVector l R} (he : IsIdempotentElem e)
    (h : e * x = e * x') :
    algebraMap _ (WL l R) e * dpw (k + 1) x = algebraMap _ (WL l R) e * dpw (k + 1) x' := by
  have key : e * x ^ (k + 1) = e * x' ^ (k + 1) := by
    have hp : e ^ (k + 1) = e := he.pow_succ_eq k
    calc e * x ^ (k + 1) = (e * x) ^ (k + 1) := by rw [mul_pow, hp]
      _ = (e * x') ^ (k + 1) := by rw [h]
      _ = e * x' ^ (k + 1) := by rw [mul_pow, hp]
  have key' := congrArg (algebraMap _ (WL l R)) key
  rw [map_mul, map_mul, map_pow, map_pow] at key'
  simp only [dpw]
  rw [mul_left_comm, key', mul_left_comm]

theorem dpw_mem (A : PAlg l) {x : A.W} (hx : A.th x = 0) (k : ℕ) : dpw k x ∈ A.Acr0 := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hx)
  rw [dpw_mul']
  exact mul_mem (pow_mem (Subalgebra.algebraMap_mem _ c) k) (A.dpw_xi_mem k)

theorem isLog_exists (A : PAlg l) (n : ℕ) (w : A.W) (hw : A.th w = 1) : ∃ y, IsLog A n w y := by
  have h0 : A.th (w - 1) = 0 := by rw [map_sub, hw, map_one, sub_self]
  exact ⟨_, fun k => ⟨dpw k (w - 1), dpw_mem A h0 k⟩, fun _ => rfl, rfl⟩

theorem isLog_unique (A : PAlg l) (n : ℕ) (w : A.W) (y y' : A.Acr n) (h : IsLog A n w y)
    (h' : IsLog A n w y') : y = y' := by
  obtain ⟨g, hg, rfl⟩ := h
  obtain ⟨g', hg', rfl⟩ := h'
  have e : g = g' := funext fun k => Subtype.ext ((hg k).trans (hg' k).symm)
  rw [e]

theorem isLog_local (A : PAlg l) (n : ℕ) (e w w' : A.W) (y y' : A.Acr n) (he : IsIdempotentElem e)
    (h : e * w = e * w') (hy : IsLog A n w y) (hy' : IsLog A n w' y') :
    A.toAcr n e * y = A.toAcr n e * y' := by
  obtain ⟨g, hg, rfl⟩ := hy
  obtain ⟨g', hg', rfl⟩ := hy'
  have h1 : e * (w - 1) = e * (w' - 1) := by rw [mul_sub, mul_sub, h]
  have h2 : ∀ k, algebraMap A.W A.Acr0 e * g (k + 1) = algebraMap A.W A.Acr0 e * g' (k + 1) := fun k =>
    Subtype.ext (by
      change algebraMap A.W (WL l A.A) e * (g (k + 1)).1 = algebraMap A.W (WL l A.A) e * (g' (k + 1)).1
      rw [hg, hg']
      exact dpw_idem k he h1)
  have h3 : ∀ k, A.toAcr n e * A.mkAcr n (g (k + 1)) = A.toAcr n e * A.mkAcr n (g' (k + 1)) := fun k => by
    have := congrArg (A.mkAcr n) (h2 k)
    rwa [map_mul, map_mul] at this
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, h3 k, mul_left_comm]

theorem logEx : CrystallineSemistableComparison.E.LogEx := fun l _ A n =>
  ⟨isLog_exists A n, fun w y y' => isLog_unique A n w y y', fun e w w' y y' => isLog_local A n e w w' y y'⟩

end GlobalTheory.CompanionTheory.CrisLog
