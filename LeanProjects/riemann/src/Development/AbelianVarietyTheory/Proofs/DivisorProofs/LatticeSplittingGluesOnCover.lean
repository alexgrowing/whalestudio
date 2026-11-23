import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRingOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitsTop

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.PerfdLat GlobalTheory.Published GlobalTheory.GroupBplus GlobalTheory.BplusDescent

namespace GlobalTheory.BplusDescent.Glue

variable {R R' K : Type} [CommRing R] [CommRing R'] [CommRing K]

theorem eventually_clear (ι : R →+* K) (a : R) (y : K) (hy : ∃ (N : ℕ) (r : R), ι r = ι a ^ N * y) :
    ∀ᶠ N in Filter.atTop, ∃ r : R, ι r = ι a ^ N * y := by
  obtain ⟨N, r, hr⟩ := hy
  filter_upwards [Filter.eventually_ge_atTop N] with M hM
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hM
  exact ⟨a ^ d * r, by rw [map_mul, map_pow, hr]; ring⟩

theorem eventually_mem {h : ℕ} (ι : R →+* K) (ι' : R' →+* K) (ρ : R →+* R') (hρ : ∀ x, ι' (ρ x) = ι x) (a : R)
    (hloc : ∀ x : R', ∃ (N : ℕ) (r : R), ι r = ι a ^ N * ι' x) (L : Submodule R (Fin h → R)) (v : Fin h → R')
    (hv : v ∈ Submodule.span R' ((fun (w : Fin h → R) i => ρ (w i)) '' (L : Set (Fin h → R)))) :
    ∀ᶠ N in Filter.atTop, ∃ w ∈ L, ∀ i, ι (w i) = ι a ^ N * ι' (v i) := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    exact Filter.Eventually.of_forall fun N => ⟨a ^ N • w, L.smul_mem _ hw, fun i => by simp [hρ]⟩
  | zero => exact Filter.Eventually.of_forall fun N => ⟨0, L.zero_mem, fun i => by simp⟩
  | add x y _ _ hx hy =>
    filter_upwards [hx, hy] with N ⟨w, hw, e⟩ ⟨w', hw', e'⟩
    exact ⟨w + w', L.add_mem hw hw', fun i => by simp [e, e', mul_add]⟩
  | smul c x _ hx =>
    obtain ⟨N, r, hr⟩ := hloc c
    obtain ⟨M, w, hw, e⟩ := hx.exists
    filter_upwards [Filter.eventually_ge_atTop (N + M)] with P hP
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hP
    refine ⟨(a ^ d * r) • w, L.smul_mem _ hw, fun i => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_pow, hr, e]
    ring

theorem eventually_row {h : ℕ} (ι : R →+* K) (a : R) (L : Submodule R (Fin h → R)) (hL : L.FG) (s : Fin h → K)
    (hs : ∀ v ∈ L, ∃ (N : ℕ) (r : R), ι r = ι a ^ N * ∑ i, s i * ι (v i)) :
    ∀ᶠ N in Filter.atTop, ∀ v ∈ L, ∃ r : R, ι r = ι a ^ N * ∑ i, s i * ι (v i) := by
  obtain ⟨F, rfl⟩ := hL
  have h1 : ∀ᶠ N in Filter.atTop, ∀ v ∈ F, ∃ r : R, ι r = ι a ^ N * ∑ i, s i * ι (v i) :=
    (Filter.eventually_all_finset F).2 fun v hv => eventually_clear ι a _ (hs v (Submodule.subset_span hv))
  filter_upwards [h1] with N hN v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact hN x hx
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨r, e⟩ := hx
    obtain ⟨r', e'⟩ := hy
    exact ⟨r + r', by simp [e, e', mul_add, Finset.sum_add_distrib]⟩
  | smul c x _ hx =>
    obtain ⟨r, e⟩ := hx
    refine ⟨c * r, ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, e, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

theorem splits_glue : ∀ (X : Scheme.{0}) [IsIntegral X] (K' : IntermediateField X.functionField (Kbar X)) (U : AffOp X) (h m : ℕ) (a : Fin m → Γ(X, U.1)) (V : Fin m → AffOp X) (hle : ∀ k, (V k).1 ≤ U.1) (L : Submodule U.Bp (Fin h → U.Bp)) (L' : ∀ k, Submodule (V k).Bp (Fin h → (V k).Bp)) (n : Fin m → ℕ) (g : ∀ k, Fin (n k) → Fin h → (V k).Bp) (S : ∀ k, Fin (n k) → Fin h → Kbar X), Ideal.span (Set.range a) = ⊤ → L.FG → (∀ k (x : (V k).Bp), ∃ (N : ℕ) (r : U.Bp), (r : Kbar X) = algebraMap Γ(X, U.1) (Kbar X) (a k) ^ N * x) → (∀ k, L' k = Submodule.span (V k).Bp (piMap (AffOp.res (hle k)) (Fin h) '' (L : Set (Fin h → U.Bp)))) → (∀ k, Splits (V k) (L' k) (g k) (S k)) → (∀ k l i, ((g k l i : (V k).Bp) : Kbar X) ∈ K') → (∀ k l i, S k l i ∈ K') → ∃ (n' : ℕ) (g' : Fin n' → Fin h → U.Bp) (S' : Fin n' → Fin h → Kbar X), Splits U L g' S' ∧ (∀ l i, (g' l i : Kbar X) ∈ K') ∧ ∀ l i, S' l i ∈ K' := by
  intro X _ K' U h m a V hle L L' n g S ha hL hloc hL' hS hg hSK
  let ι : U.Bp →+* Kbar X := algebraMap U.Bp (Kbar X)
  let α : Fin m → U.Bp := fun k => algebraMap Γ(X, U.1) U.Bp (a k)
  have hK : ∀ x : Γ(X, U.1), algebraMap Γ(X, U.1) (Kbar X) x ∈ K' := fun x => by
    rw [IsScalarTower.algebraMap_apply Γ(X, U.1) X.functionField (Kbar X)]
    exact K'.algebraMap_mem _
  have h1 : ∀ᶠ N in Filter.atTop, ∀ k l, ∃ w ∈ L, ∀ i, ι (w i) = ι (α k) ^ N * (g k l i : Kbar X) := by
    refine Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun l => ?_
    have hm := (hS k).1 l
    rw [hL' k] at hm
    exact eventually_mem ι (algebraMap (V k).Bp (Kbar X)) (AffOp.res (hle k)) (fun _ => rfl) (α k) (hloc k) L _ hm
  have h2 : ∀ᶠ N in Filter.atTop, ∀ k l, ∀ v ∈ L, ∃ r : U.Bp, ι r = ι (α k) ^ N * ∑ i, S k l i * ι (v i) := by
    refine Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun l => ?_
    refine eventually_row ι (α k) L hL (S k l) fun v hv => ?_
    have hm : piMap (AffOp.res (hle k)) (Fin h) v ∈ L' k := by
      rw [hL' k]
      exact Submodule.subset_span ⟨v, hv, rfl⟩
    obtain ⟨x, hx⟩ := (hS k).2.2 _ hm l
    obtain ⟨N, r, hr⟩ := hloc k x
    exact ⟨N, r, hr.trans (by rw [hx]; rfl)⟩
  obtain ⟨N, hN1, hN2⟩ := (h1.and h2).exists
  choose w hw hwe using hN1
  have hpow := Ideal.span_pow_eq_top _ ha (2 * N)
  rw [← Set.range_comp, Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun] at hpow
  obtain ⟨c, hc⟩ := hpow
  have hc' : ∑ k, algebraMap Γ(X, U.1) (Kbar X) (c k) * ι (α k) ^ (2 * N) = 1 := by
    have := congrArg (algebraMap Γ(X, U.1) (Kbar X)) hc
    simp only [map_sum, map_mul, map_one, Function.comp_apply, map_pow] at this
    exact this
  let e := (Fintype.equivFin (Σ k, Fin (n k))).symm
  refine ⟨_, fun j => w (e j).1 (e j).2,
    fun j i => algebraMap Γ(X, U.1) (Kbar X) (c (e j).1) * ι (α (e j).1) ^ N * S (e j).1 (e j).2 i,
    ⟨fun j => hw _ _, fun i i' => ?_, fun v hv j => ?_⟩, fun j i => ?_, fun j i => ?_⟩
  · rw [e.sum_comp fun p : (Σ k, Fin (n k)) => (w p.1 p.2 i : Kbar X) *
      (algebraMap Γ(X, U.1) (Kbar X) (c p.1) * ι (α p.1) ^ N * S p.1 p.2 i'), Fintype.sum_sigma]
    calc _ = ∑ k, algebraMap Γ(X, U.1) (Kbar X) (c k) * ι (α k) ^ (2 * N) *
            ∑ l, (g k l i : Kbar X) * S k l i' := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          have := hwe k l i
          change ι (w k l i) * _ = _
          rw [this]; ring
      _ = _ := by
          simp only [fun k => (hS k).2.1 i i']
          rw [← Finset.sum_mul, hc', one_mul]
  · obtain ⟨r, hr⟩ := hN2 (e j).1 (e j).2 v hv
    refine ⟨algebraMap Γ(X, U.1) U.Bp (c (e j).1) * r, ?_⟩
    change algebraMap Γ(X, U.1) (Kbar X) (c (e j).1) * ι r = _
    rw [hr, ← mul_assoc, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (mul_assoc _ _ _).symm
  · change ι _ ∈ K'
    rw [hwe]
    exact mul_mem (pow_mem (hK _) _) (hg _ _ _)
  · exact mul_mem (mul_mem (hK _) (pow_mem (hK _) _)) (hSK _ _ _)

end GlobalTheory.BplusDescent.Glue
