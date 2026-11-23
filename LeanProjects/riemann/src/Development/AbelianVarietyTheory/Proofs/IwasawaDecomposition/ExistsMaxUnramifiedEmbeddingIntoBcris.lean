import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootOfUnityPrimeToTeichmullerLiftStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem exists_factor_of_range {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* D) (ι : B →+* D)
    (hι : Function.Injective ι) (h : ∀ x, f x ∈ ι.range) : ∃ u : A →+* B, ∀ x, ι (u x) = f x := by
  let e : B ≃+* ι.range := RingEquiv.ofBijective ι.rangeRestrict
    ⟨fun a b hab => hι (congrArg Subtype.val hab), ι.rangeRestrict_surjective⟩
  refine ⟨e.symm.toRingHom.comp (f.codRestrict ι.range h), fun x => ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply (f.codRestrict ι.range h x))

theorem padic_mem_range {l : ℕ} [Fact l.Prime] {B D : Type} [CommRing B] [CommRing D] (g : ℚ_[l] →+* D)
    (ι : B →+* D) (hz : ∀ z : ℤ_[l], g z ∈ ι.range) (hl : IsUnit (l : B)) (q : ℚ_[l]) : g q ∈ ι.range := by
  obtain ⟨w, hw⟩ := hl.exists_right_inv
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have h1 : g (l : ℚ_[l])⁻¹ = ι w := by
    have a : (l : D) * ι w = 1 := by simpa using congrArg ι hw
    have b : g (l : ℚ_[l])⁻¹ * (l : D) = 1 := by
      rw [← map_natCast g, ← map_mul, inv_mul_cancel₀ hl0, map_one]
    calc g (l : ℚ_[l])⁻¹ = g (l : ℚ_[l])⁻¹ * ((l : D) * ι w) := by rw [a, mul_one]
      _ = ι w := by rw [← mul_assoc, b, one_mul]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖(l : ℚ_[l]) ^ n * q‖ ≤ 1 := by
    have hp : ‖(l : ℚ_[l])‖ < 1 := Padic.norm_p_lt_one
    have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hp).mul_const ‖q‖
    rw [zero_mul] at ht
    obtain ⟨n, hn⟩ := (ht.eventually (ge_mem_nhds one_pos)).exists
    exact ⟨n, by rwa [norm_mul, norm_pow]⟩
  have e : q = ((l : ℚ_[l])⁻¹) ^ n * ((⟨_, hn⟩ : ℤ_[l]) : ℚ_[l]) := by
    change q = _ * ((l : ℚ_[l]) ^ n * q)
    rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hl0, one_pow, one_mul]
  rw [e, map_mul, map_pow, h1]
  exact mul_mem (pow_mem (ι.mem_range_self w) n) (hz _)

theorem exists_unram_to_cris : ∀ (l : ℕ) [Fact l.Prime], ∀ (o : Om l →+* Per.BdRp l) (ι : Per.Bcris l →+* Per.BdR l), IsSec o → Function.Injective ι → (∀ a : Per.Ainf l, ι (Per.aB l a) = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l a)) → IsUnit (l : Per.Bcris l) → ∃ u : ↥(MaximalUnramifiedExtension l) →+* Per.Bcris l, ∀ c : ↥(MaximalUnramifiedExtension l), ι (u c) = algebraMap (Per.BdRp l) (Per.BdR l) (o (c : Om l)) := by
  intro l _ o ι ho hι ha hl
  let f : Om l →+* Per.BdR l := (algebraMap (Per.BdRp l) (Per.BdR l)).comp o
  have hq : ∀ q : ℚ_[l], f (algebraMap ℚ_[l] (Om l) q) ∈ ι.range :=
    padic_mem_range (f.comp (algebraMap ℚ_[l] (Om l))) ι
      (fun z => ⟨Per.aB l (Per.zA l z), (ha _).trans (by
        rw [← ho.z]; rfl)⟩) hl
  let S : Subalgebra ℚ_[l] (Om l) :=
    { (ι.range.comap f).toSubsemiring with algebraMap_mem' := hq }
  have key : ∀ x ∈ MaximalUnramifiedExtension l, f x ∈ ι.range := by
    intro x hx
    unfold MaximalUnramifiedExtension at hx
    rw [← IntermediateField.mem_toSubalgebra, IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
      (fun y _ => Algebra.IsAlgebraic.isAlgebraic y)] at hx
    refine (Algebra.adjoin_le (S := S) ?_) hx
    rintro c ⟨m, h0, h1, h2⟩
    obtain ⟨⟨xb, hxb⟩, h⟩ := GlobalTheory.T.rootOfUnity_prime_to_teichmuller_lift l o ho c m h0 h1 h2
    refine ⟨Per.aB l (Per.tm xb), ?_⟩
    exact (ha _).trans (by rw [(h xb hxb).2.2]; rfl)
  exact exists_factor_of_range (f.comp (MaximalUnramifiedExtension l).val.toRingHom) ι hι (fun x => key x x.2)

end GlobalTheory.MemLoc
