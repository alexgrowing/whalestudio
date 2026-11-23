import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import Development.WeilBound.CoreStatements.SesquilinearFractions.GramDetNeZeroLocalBasisCofinite

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.gram_det_ne_zero_local_basis_cofinite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (I : Type) [Fintype I] [DecidableEq I] (e : I → D.La), Fintype.card I = D.p + D.q → LinearIndependent (𝓞 E) e → (gramE D e).det ≠ 0 ∧ {ℓ : Nat.Primes | ¬ IsLocBasis (𝓞 E) ℓ e}.Finite := by
  classical
  intro E _ _ _ H D I _ _ e hcard hli
  haveI := D.fin
  have T : ∀ (c : 𝓞 E) (x y : D.La), Algebra.trace ℚ E (algebraMap (𝓞 E) E c * sesq D x y) = ((D.EF (c • x) y : ℤ) : ℚ) := by
    intro c x y
    have key : ∀ j, Algebra.trace ℚ E (algebraMap (𝓞 E) E (RingOfIntegers.basis E j) * sesq D x y) = ((D.EF (RingOfIntegers.basis E j • x) y : ℤ) : ℚ) := by
      intro j
      have hterm : ∀ k, Algebra.trace ℚ E (algebraMap (𝓞 E) E (RingOfIntegers.basis E j) * (((D.EF (RingOfIntegers.basis E k • x) y : ℤ) : E) * HT.dualInt E k)) = ((D.EF (RingOfIntegers.basis E k • x) y : ℤ) : ℚ) * (if j = k then 1 else 0) := by
        intro k
        rw [← HT.LatBasic.trace_dualInt k j, ← map_intCast (algebraMap ℚ E), mul_left_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm (algebraMap (𝓞 E) E _), ← NumberField.integralBasis_apply]
      simp only [sesq, Finset.mul_sum, map_sum, hterm, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      exact mul_one _
    conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr c]
    conv_rhs => rw [← (RingOfIntegers.basis E).sum_repr c]
    simp only [map_sum, Finset.sum_mul, Finset.sum_smul, LinearMap.sum_apply, Int.cast_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_zsmul, smul_mul_assoc, map_zsmul, key j, smul_assoc, map_zsmul, LinearMap.smul_apply, zsmul_eq_mul, zsmul_eq_mul, Int.cast_mul]
    norm_cast
  have hy : ∀ y : D.La, ∃ c : 𝓞 E, c ≠ 0 ∧ c • y ∈ Submodule.span (𝓞 E) (Set.range e) := by
    intro y
    by_contra hne
    push_neg at hne
    have hli' : LinearIndependent (𝓞 E) (fun o : Option I => Option.elim o y e) := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      rw [Fintype.sum_option] at hg
      simp only [Option.elim] at hg
      have hnone : g none = 0 := by
        by_contra h0
        apply hne (g none) h0
        have : g none • y = -∑ i, g (some i) • e i := eq_neg_of_add_eq_zero_left hg
        rw [this]
        exact Submodule.neg_mem _ (Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)))
      rw [hnone, zero_smul, zero_add] at hg
      intro o
      cases o with
      | none => exact hnone
      | some i => exact (Fintype.linearIndependent_iff.mp hli) _ hg i
    have := hli'.fintype_card_le_finrank
    rw [Fintype.card_option, hcard, D.rank] at this
    omega
  have hfin : ∃ c : 𝓞 E, c ≠ 0 ∧ ∀ y : D.La, c • y ∈ Submodule.span (𝓞 E) (Set.range e) := by
    obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule (𝓞 E) D.La).FG)
    choose f hf0 hfm using hy
    refine ⟨∏ y ∈ s, f y, Finset.prod_ne_zero_iff.mpr (fun y _ => hf0 y), ?_⟩
    intro y
    have hy' : y ∈ Submodule.span (𝓞 E) (s : Set D.La) := hs ▸ Submodule.mem_top
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy'
    · intro z hz
      rw [← Finset.mul_prod_erase s f hz, mul_comm (f z), mul_smul]
      exact Submodule.smul_mem _ _ (hfm z)
    · simp
    · intro a b _ _ ha hb
      rw [smul_add]
      exact Submodule.add_mem _ ha hb
    · intro r a _ ha
      rw [smul_comm]
      exact Submodule.smul_mem _ _ ha
  obtain ⟨c, hc0, hc⟩ := hfin
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {c}))
  have hN0 : Ideal.absNorm (Ideal.span {c}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hc0
  have hNy : ∀ y : D.La, Ideal.absNorm (Ideal.span {c}) • y ∈ Submodule.span (𝓞 E) (Set.range e) := by
    intro y
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E), ← ht, mul_smul]
    exact Submodule.smul_mem _ _ (hc y)
  constructor
  · intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 E)) Finset.univ v
    choose a ha using fun i => RingHom.mem_rangeS.mp (hb i (Finset.mem_univ i))
    obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hv0
    have hai0 : a i0 ≠ 0 := by
      intro h0
      have := ha i0
      rw [h0, map_zero, Algebra.smul_def, eq_comm, mul_eq_zero] at this
      rcases this with h | h
      · exact nonZeroDivisors.coe_ne_zero b ((map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mp h)
      · exact hi0 h
    have hx0 : (∑ i, a i • e i) ≠ 0 := fun h => hai0 ((Fintype.linearIndependent_iff.mp hli) a h i0)
    have hEFc : ∀ (c : 𝓞 E) (n : I), D.EF (c • ∑ i, a i • e i) (e n) = 0 := by
      intro c n
      have h1 : c • ∑ i, a i • e i = ∑ m, (c * a m) • e m := by simp only [Finset.smul_sum, mul_smul]
      apply Int.cast_injective (α := ℚ)
      rw [h1, map_sum, LinearMap.sum_apply, Int.cast_sum, Int.cast_zero]
      simp only [← T]
      rw [← map_sum]
      have h2 : ∑ m, algebraMap (𝓞 E) E (c * a m) * sesq D (e m) (e n) = algebraMap (𝓞 E) E c * (algebraMap (𝓞 E) E b * (v ᵥ* gramE D e) n) := by
        simp only [Matrix.vecMul, dotProduct, gramE, Matrix.of_apply, map_mul, ha, Algebra.smul_def, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun m _ => by ring)
      rw [h2, hv, Pi.zero_apply, mul_zero, mul_zero, map_zero]
    have hEF : ∀ y, D.EF (∑ i, a i • e i) y = 0 := by
      intro y
      obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).mp (hNy y)
      have h2 : D.EF (∑ i, a i • e i) (Ideal.absNorm (Ideal.span {c}) • y) = 0 := by
        rw [← hg, map_sum]
        refine Finset.sum_eq_zero (fun n _ => ?_)
        have := D.adj (H.bar.symm (g n)) (∑ i, a i • e i) (e n)
        rw [RingEquiv.apply_symm_apply] at this
        rw [← this]
        exact hEFc _ n
      rw [map_nsmul] at h2
      exact (smul_eq_zero.mp h2).resolve_left hN0
    apply hx0
    apply D.unimod.1
    rw [map_zero]
    exact LinearMap.ext hEF
  · apply Set.Finite.subset ((Nat.divisors (Ideal.absNorm (Ideal.span {c}))).finite_toSet.preimage (f := ((↑) : Nat.Primes → ℕ)) (Set.injOn_of_injective Subtype.val_injective))
    intro ℓ hℓ
    simp only [Set.mem_preimage, Finset.mem_coe, Nat.mem_divisors]
    refine ⟨?_, hN0⟩
    by_contra hd
    exact hℓ (by unfold IsLocBasis; exact ⟨hli, _, hd, hNy⟩)
