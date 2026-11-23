import Mathlib

set_option autoImplicit false
noncomputable section

open NumberField IsDedekindDomain Matrix Module
open scoped BigOperators nonZeroDivisors

namespace GlobalTheory.LatticeLocBasis

theorem exists_basis_up_to_fintype {O A E : Type} [CommRing O] [CommRing A] [IsDomain A] [Field E] [Algebra O A]
    [Algebra A E] [Algebra O E] [IsScalarTower O A E] (S : Submonoid O) [IsLocalization S A] [IsFractionRing A E]
    [IsPrincipalIdealRing A] {n : Type} [Fintype n] (L : Submodule O (n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (n → E)) = ⊤) :
    ∃ (s : S) (b : n → n → E), LinearIndependent E b ∧ (∀ i, b i ∈ L) ∧
      ∀ w ∈ L, (s : O) • w ∈ Submodule.span O (Set.range b) := by
  classical
  set M : Submodule A (n → E) := Submodule.span A (L : Set (n → E)) with hM
  have : Submodule.IsLattice E M :=
    { fg := by
        obtain ⟨s, hs⟩ := hfg
        refine ⟨s, ?_⟩
        rw [hM, ← hs, Submodule.span_span_of_tower]
      span_eq_top := by rw [hM, Submodule.span_span_of_tower, hsp] }
  have hrk : Module.finrank A M = Fintype.card n := by
    simpa using Submodule.IsLattice.finrank_of_pi E M
  let c : Basis n A M := (Module.finBasisOfFinrankEq A M hrk).reindex (Fintype.equivFin n).symm
  have hc : ∀ i, ∃ t : S, (t : O) • (c i : n → E) ∈ L := fun i => by
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span S A (L : Set (n → E)) _ (c i).2
    rw [Submodule.span_eq] at ht
    exact ⟨t, ht⟩
  choose t ht using hc
  let u : n → Aˣ := fun i => (IsLocalization.map_units A (t i)).unit
  let c' : Basis n A M := c.unitsSMul u
  have hc' : ∀ i, (c' i : n → E) = (t i : O) • (c i : n → E) := fun i => by
    simp only [c', Basis.unitsSMul_apply, u, Units.smul_def, IsUnit.unit_spec, algebraMap_smul,
      Submodule.coe_smul_of_tower]
  let b : n → n → E := fun i => (c' i : n → E)
  have hli : LinearIndependent E b := by
    have h : b = c'.extendOfIsLattice E := funext fun i => by simp [b]
    rw [h]
    exact (c'.extendOfIsLattice E).linearIndependent
  have hspanA : Submodule.span A (Set.range b) = M := by
    have : Set.range b = M.subtype '' Set.range c' := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, c'.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hw : ∀ w ∈ L, ∃ r : S, (r : O) • w ∈ Submodule.span O (Set.range b) := fun w hw => by
    obtain ⟨r, hr⟩ := multiple_mem_span_of_mem_localization_span S A (Set.range b) w
      (hspanA ▸ Submodule.subset_span hw)
    exact ⟨r, hr⟩
  obtain ⟨G, hG⟩ := hfg
  choose! r hr using hw
  refine ⟨∏ x ∈ G, r x, b, hli, fun i => by simpa only [b, hc'] using ht i, fun w hw => ?_⟩
  rw [← hG] at hw
  induction hw using Submodule.span_induction with
  | mem y hy =>
    have hy' : y ∈ G := hy
    rw [← Finset.prod_erase_mul G r hy', Submonoid.coe_mul, mul_smul]
    exact Submodule.smul_mem _ _ (hr y (hG ▸ Submodule.subset_span hy))
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ _ hy

theorem exists_matrix_up_to_notMem : ∀ (K : Type) [Field K] [NumberField K] (n : Type) [Fintype n] [DecidableEq n] (L : Submodule (𝓞 K) (n → K)) (𝔭 : HeightOneSpectrum (𝓞 K)), L.FG → Submodule.span K (L : Set (n → K)) = ⊤ → ∃ g : Matrix n n K, IsUnit g.det ∧ ∃ t : 𝓞 K, t ∉ 𝔭.asIdeal ∧ (∀ x ∈ L, ∀ i, (t : K) * (g⁻¹ *ᵥ x) i ∈ (algebraMap (𝓞 K) K).range) ∧ ∀ j, (t : K) • (fun i => g i j) ∈ L := by
  intro K _ _ n _ _ L 𝔭 hfg hsp
  have hp := 𝔭.isPrime
  have hS : 𝔭.asIdeal.primeCompl ≤ (𝓞 K)⁰ := Ideal.primeCompl_le_nonZeroDivisors _
  let A := Localization.subalgebra K 𝔭.asIdeal.primeCompl hS
  have : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) 𝔭.ne_bot A
  obtain ⟨⟨s, hs⟩, b, hli, hb, hw⟩ := exists_basis_up_to_fintype (A := A) 𝔭.asIdeal.primeCompl L hfg hsp
  let g : Matrix n n K := Matrix.of fun i j => b j i
  have hcol : g.col = b := by funext j i; rfl
  have hunit : IsUnit g := Matrix.linearIndependent_cols_iff_isUnit.1 (hcol ▸ hli)
  have hdet : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det _).1 hunit
  refine ⟨g, hdet, s, hs, ?_, ?_⟩
  · intro x hx i
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hw x hx)
    have hg : g *ᵥ (fun i => algebraMap (𝓞 K) K (a i)) = (s : K) • x := by
      have : (s : K) • x = s • x := algebraMap_smul K s x
      rw [this]
      change _ = ((⟨s, hs⟩ : 𝔭.asIdeal.primeCompl) : 𝓞 K) • x
      rw [← ha]
      funext i
      simp only [Matrix.mulVec, dotProduct, g, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, mul_comm]
    have h2 : (s : K) • (g⁻¹ *ᵥ x) = fun i => algebraMap (𝓞 K) K (a i) := by
      rw [← Matrix.mulVec_smul, ← hg, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
    exact ⟨a i, (congrFun h2 i).symm⟩
  · intro j
    have : (s : K) • (fun i => g i j) = s • b j := algebraMap_smul K s (b j)
    rw [this]
    exact L.smul_mem _ (hb j)

end GlobalTheory.LatticeLocBasis
