import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroTypeInertia
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalCharExistsOfGreen
open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT

noncomputable section

namespace GlobalTheory.RegLabelChar

open Polynomial GlobalTheory.GLq

variable {g : ℕ} [Fact g.Prime]

theorem pow_congr (L : LabelDatum g) {n : ℕ} (hn : 0 < n) {t : ℂ} (ht : t ^ (g ^ n - 1) = 1) {a b : ℕ}
    (h : L.gen n ^ a = L.gen n ^ b) : t ^ a = t ^ b := by
  have hN := L.gen_order n hn
  have hq1 : 0 < g ^ n - 1 := by
    have := Nat.one_lt_pow hn.ne' (Fact.out : g.Prime).one_lt
    omega
  have hpos : 0 < orderOf (L.gen n) := hN ▸ hq1
  have h2 : L.gen n ^ (a % orderOf (L.gen n)) = L.gen n ^ (b % orderOf (L.gen n)) := by
    rw [pow_mod_orderOf, pow_mod_orderOf, h]
  have h3 := pow_injOn_Iio_orderOf (Set.mem_Iio.2 (Nat.mod_lt a hpos)) (Set.mem_Iio.2 (Nat.mod_lt b hpos)) h2
  rw [hN] at h3
  rw [← Nat.mod_add_div a (g ^ n - 1), ← Nat.mod_add_div b (g ^ n - 1), pow_add, pow_add, pow_mul, pow_mul, ht,
    one_pow, one_pow, h3]

theorem thetaOf_eq (L : LabelDatum g) {n : ℕ} (hn : 0 < n) {x : Formalism.CyclotomicNorms.Fbar g}
    (hx : L.teich x ^ (g ^ n - 1) = 1) {z : Formalism.CyclotomicNorms.Fbar g} {k : ℕ} (hz : z = L.gen n ^ k) :
    thetaOf L n x z = L.teich x ^ k := by
  have he : ∃ m : ℕ, z = L.gen n ^ m := ⟨k, hz⟩
  unfold thetaOf
  rw [dif_pos he]
  exact pow_congr L hn hx ((Exists.choose_spec he).symm.trans hz)

theorem exists_regularChar :
    ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (n : ℕ) (hn : 0 < n) (P : (ZMod g)[X])
    (hP : IsPrimeLab n P) (K : Type) [Field K] [Finite K] (hK : Nat.card K = g ^ n) (ι : K →+* Formalism.CyclotomicNorms.Fbar g),
    ∃ θ : Kˣ →* ℂˣ, GlobalTheory.Published.IsRegularChar g n θ ∧
      (∃ x ∈ Formalism.CyclotomicNorms.rootsBar P, ∀ u : Kˣ, ((θ u : ℂˣ) : ℂ) = thetaOf L n x (ι u)) ∧
      ∀ u : Kˣ, ι u = L.gen n →
        ∏ j ∈ Finset.range n, (X - C ((θ (u ^ g ^ j) : ℂˣ) : ℂ)) = GlobalTheory.SerSys.TameGen.liftPoly L.teich P := by
  intro g _ L n hn P hP K _ _ hK ι
  classical
  haveI := Fintype.ofFinite K
  have hg1 : 1 < g := (Fact.out : g.Prime).one_lt
  have hq : 1 < g ^ n := Nat.one_lt_pow hn.ne' hg1
  have hq1 : 0 < g ^ n - 1 := by omega
  haveI : NeZero (g ^ n - 1) := ⟨hq1.ne'⟩
  have hdegP : P.natDegree = n := hP.2.2.2
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero (Formalism.CyclotomicNorms.Fbar g) P (degree_pos_of_irreducible hP.2.1).ne'
  have hxmem : x ∈ Formalism.CyclotomicNorms.rootsBar P := by
    simpa [Formalism.CyclotomicNorms.rootsBar, hP.2.1.ne_zero, aeval_def, eval_map] using hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [← coeff_zero_eq_aeval_zero'] at hx
    exact hP.2.2.1 ((map_eq_zero_iff _ (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective).1 hx)
  have hxq : x ^ (g ^ n - 1) = 1 := by
    have h1 : x ^ g ^ n = x := (GlobalTheory.GreenExists.pow_eq_self_iff hP.2.1 hx n).2 (hdegP ▸ dvd_refl _)
    have h2 : x ^ (g ^ n - 1) * x = 1 * x := by
      rw [← pow_succ, Nat.sub_add_cancel hq.le, h1, one_mul]
    exact mul_right_cancel₀ hx0 h2
  have ht1 : L.teich x ^ (g ^ n - 1) = 1 := by rw [← map_pow, hxq, map_one]
  have hgo : orderOf (L.gen n) = g ^ n - 1 := L.gen_order n hn
  have hprim : IsPrimitiveRoot (L.gen n) (g ^ n - 1) := hgo ▸ IsPrimitiveRoot.orderOf _
  have hcardK : Fintype.card K = g ^ n := by rw [← Nat.card_eq_fintype_card, hK]
  have hpow : ∀ u : Kˣ, ∃ k : ℕ, ι u = L.gen n ^ k := fun u => by
    have h1 : (ι u) ^ (g ^ n - 1) = 1 := by
      rw [← map_pow, ← hcardK, FiniteField.pow_card_sub_one_eq_one (u : K) u.ne_zero, map_one]
    obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one h1
    exact ⟨i, hi.symm⟩
  let f : Kˣ →* ℂ :=
    { toFun := fun u => thetaOf L n x (ι u)
      map_one' := by
        rw [thetaOf_eq L hn ht1 (k := 0) (by rw [Units.val_one, map_one, pow_zero]), pow_zero]
      map_mul' := fun u v => by
        obtain ⟨a, ha⟩ := hpow u
        obtain ⟨b, hb⟩ := hpow v
        rw [thetaOf_eq L hn ht1 ha, thetaOf_eq L hn ht1 hb,
          thetaOf_eq L hn ht1 (k := a + b) (by rw [Units.val_mul, map_mul, ha, hb, pow_add]), pow_add] }
  have hf : ∀ u : Kˣ, ((f.toHomUnits u : ℂˣ) : ℂ) = thetaOf L n x (ι u) := fun u => rfl
  have hfpow : ∀ (u : Kˣ) (m : ℕ), ι u = L.gen n → ((f.toHomUnits (u ^ m) : ℂˣ) : ℂ) = L.teich x ^ m :=
    fun u m hu => by
      rw [hf]
      exact thetaOf_eq L hn ht1 (by rw [Units.val_pow_eq_pow_val, map_pow, hu])

  have hroots := GlobalTheory.GreenExists.rootsBar_eq hP.2.1 hx
  rw [hdegP] at hroots
  have hnd : (Formalism.CyclotomicNorms.rootsBar P).Nodup := by
    unfold Formalism.CyclotomicNorms.rootsBar
    exact nodup_roots ((PerfectField.separable_of_irreducible hP.2.1).map)
  rw [hroots] at hnd
  refine ⟨f.toHomUnits, ?_, ⟨x, hxmem, hf⟩, ?_⟩
  ·
    intro i j hi hj h
    obtain ⟨w, hw⟩ := IsCyclic.exists_generator (α := Kˣ)
    have hwo : orderOf w = g ^ n - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hw, Nat.card_eq_fintype_card, Fintype.card_units, hcardK]
    have hιw : orderOf (ι (w : K)) = g ^ n - 1 := by
      have h := orderOf_injective ι.toMonoidHom ι.injective (w : K)
      rw [orderOf_units, hwo] at h
      exact h
    have hwp : IsPrimitiveRoot (ι (w : K)) (g ^ n - 1) := hιw ▸ IsPrimitiveRoot.orderOf _
    obtain ⟨k, -, hk⟩ := hwp.eq_pow_of_pow_eq_one (hgo ▸ pow_orderOf_eq_one (L.gen n))
    have hu0 : ι ((w ^ k : Kˣ) : K) = L.gen n := by rw [Units.val_pow_eq_pow_val, map_pow, hk]
    have h1 := congrArg (fun φ : Kˣ →* ℂˣ => ((φ (w ^ k) : ℂˣ) : ℂ)) h
    simp only [MonoidHom.pow_apply, Units.val_pow_eq_pow_val] at h1
    have hθ0 : ((f.toHomUnits (w ^ k) : ℂˣ) : ℂ) = L.teich x := by
      rw [hf]
      exact (thetaOf_eq L hn ht1 (k := 1) (by rw [hu0, pow_one])).trans (pow_one _)
    rw [hθ0, ← map_pow, ← map_pow] at h1
    have h2 := L.teich_inj _ _ (pow_ne_zero _ hx0) (pow_ne_zero _ hx0) h1
    exact Multiset.inj_on_of_nodup_map hnd i (Finset.mem_range.2 hi) j
      (Finset.mem_range.2 hj) h2
  · intro u hu
    rw [GlobalTheory.SerSys.TameGen.liftPoly, hroots, Multiset.map_map, Finset.prod_eq_multiset_prod]
    congr 1
    refine Multiset.map_congr rfl fun j _ => ?_
    rw [Function.comp_apply, hfpow u _ hu, map_pow L.teich]

end GlobalTheory.RegLabelChar

end
