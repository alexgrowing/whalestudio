import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

namespace ResultantNorm

open Polynomial Filter Topology

theorem exists_prod_aeval {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (a : Multiset Ω)
    (P : K[X]) (hP : P.map (algebraMap K Ω) = (a.map fun x => X - C x).prod) (F : K[X]) :
    ∃ u : K, algebraMap K Ω u = (a.map fun x => aeval x F).prod := by
  have hs : (P.map (algebraMap K Ω)).Splits := by
    rw [hP]; exact Splits.multisetProd (by
      intro f hf; obtain ⟨x, -, rfl⟩ := Multiset.mem_map.1 hf; exact Splits.X_sub_C x)
  have hm : (P.map (algebraMap K Ω)).Monic := by
    rw [hP]; exact monic_multisetProd_X_sub_C a
  have hr : (P.map (algebraMap K Ω)).roots = a := by
    rw [hP]; exact roots_multiset_prod_X_sub_C a
  refine ⟨resultant P F (P.map (algebraMap K Ω)).natDegree F.natDegree, ?_⟩
  rw [← resultant_map_map, resultant_eq_prod_eval _ _ _ natDegree_map_le hs, hm.leadingCoeff,
    one_pow, _root_.one_mul, hr]
  congr 1
  refine Multiset.map_congr rfl fun x _ => ?_
  rw [eval_map_algebraMap]

theorem eq_of_countP {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    [DecidableEq Ω] (n : ℕ) : ∀ (a b : Multiset Ω) (P Q : K[X]), a.card = n →
      P.map (algebraMap K Ω) = (a.map fun x => X - C x).prod →
      Q.map (algebraMap K Ω) = (b.map fun x => X - C x).prod →
      (∀ G : K[X], a.countP (fun x => aeval x G = 0) = b.countP (fun x => aeval x G = 0)) →
      P = Q := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b P Q hn hP hQ h
  have hinj := map_injective (algebraMap K Ω) (algebraMap K Ω).injective
  by_cases ha : a = 0
  · have h0 := h 0
    subst ha
    simp at h0
    have hb : b = 0 := by
      rw [← Multiset.card_eq_zero]
      simpa using h0.symm
    subst hb
    exact hinj (hP.trans hQ.symm)
  obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero ha
  have hxi : IsIntegral K x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  set G := minpoly K x with hG
  have hpos : 0 < b.countP (fun y => aeval y G = 0) := by
    rw [← h G]; exact Multiset.countP_pos.2 ⟨x, hx, minpoly.aeval K x⟩
  obtain ⟨y, hy, hyG⟩ := Multiset.countP_pos.1 hpos
  have hGy : G = minpoly K y :=
    minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hxi) hyG (minpoly.monic hxi)
  have hGm : (G.map (algebraMap K Ω)).Monic := (minpoly.monic hxi).map _
  have key : ∀ (c : Multiset Ω) (R : K[X]) (z : Ω), z ∈ c → G = minpoly K z →
      R.map (algebraMap K Ω) = (c.map fun x => X - C x).prod →
      ∃ (c' : Multiset Ω) (R' : K[X]), R = G * R' ∧ c = (G.map (algebraMap K Ω)).roots + c' ∧
        R'.map (algebraMap K Ω) = (c'.map fun x => X - C x).prod := by
    intro c R z hz hGz hR
    have hs : (R.map (algebraMap K Ω)).Splits := by
      rw [hR]; exact Splits.multisetProd (by
        intro f hf; obtain ⟨x, -, rfl⟩ := Multiset.mem_map.1 hf; exact Splits.X_sub_C x)
    have hm : (R.map (algebraMap K Ω)).Monic := by
      rw [hR]; exact monic_multisetProd_X_sub_C c
    have hr : (R.map (algebraMap K Ω)).roots = c := by
      rw [hR]; exact roots_multiset_prod_X_sub_C c
    have hz0 : aeval z R = 0 := by
      rw [← hr] at hz
      have := (mem_roots hm.ne_zero).1 hz
      rwa [IsRoot.def, eval_map_algebraMap] at this
    obtain ⟨R', hR'⟩ : G ∣ R := hGz ▸ minpoly.dvd K z hz0
    have hmul : R.map (algebraMap K Ω) = G.map (algebraMap K Ω) * R'.map (algebraMap K Ω) := by
      rw [hR', Polynomial.map_mul]
    refine ⟨(R'.map (algebraMap K Ω)).roots, R', hR', ?_, ?_⟩
    · rw [← hr, ← roots_mul (hmul ▸ hm.ne_zero), ← hmul]
    · exact (hs.of_dvd hm.ne_zero ⟨_, by rw [hmul, mul_comm]⟩).eq_prod_roots_of_monic
        (hGm.of_mul_monic_left (hmul ▸ hm))
  obtain ⟨a', P', hP1, hP2, hP3⟩ := key a P x hx hG hP
  obtain ⟨b', Q', hQ1, hQ2, hQ3⟩ := key b Q y hy hGy hQ
  have hxr : x ∈ (G.map (algebraMap K Ω)).roots := by
    rw [mem_roots hGm.ne_zero, IsRoot.def, eval_map_algebraMap]; exact minpoly.aeval K x
  have hlt : a'.card < n := by
    have := Multiset.card_pos_iff_exists_mem.2 ⟨x, hxr⟩
    rw [← hn, hP2, Multiset.card_add]; omega
  rw [hP1, hQ1, ih _ hlt a' b' P' Q' rfl hP3 hQ3 fun H => ?_]
  have := h H
  rw [hP2, hQ2, Multiset.countP_add, Multiset.countP_add] at this
  omega

section Normed

variable {K Ω : Type} [NontriviallyNormedField K] [NormedField Ω] [NormedAlgebra K Ω]

theorem norm_prod_add [DecidableEq Ω] (a : Multiset Ω) (g : Ω → Ω) (t : K) :
    ‖(a.map fun x => g x + algebraMap K Ω t).prod‖ =
      ‖t‖ ^ a.countP (fun x => g x = 0) *
        ‖((a.filter fun x => ¬ g x = 0).map fun x => g x + algebraMap K Ω t).prod‖ := by
  induction a using Multiset.induction_on with
  | empty => simp
  | cons x a ih =>
    by_cases hx : g x = 0
    · rw [Multiset.map_cons, Multiset.prod_cons, norm_mul, ih,
        Multiset.countP_cons_of_pos _ (by exact hx), Multiset.filter_cons_of_neg _ (by simpa using hx), hx,
        zero_add, norm_algebraMap']
      ring
    · rw [Multiset.map_cons, Multiset.prod_cons, norm_mul, ih,
        Multiset.countP_cons_of_neg _ (by exact hx), Multiset.filter_cons_of_pos _ (by exact hx),
        Multiset.map_cons, Multiset.prod_cons, norm_mul]
      ring

theorem countP_le [DecidableEq Ω] (a b : Multiset Ω) (g : Ω → Ω)
    (h : ∀ t : K, ‖(a.map fun x => g x + algebraMap K Ω t).prod‖ =
      ‖(b.map fun x => g x + algebraMap K Ω t).prod‖) :
    b.countP (fun x => g x = 0) ≤ a.countP (fun x => g x = 0) := by
  by_contra hlt
  push Not at hlt
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hlt
  set A : K → ℝ := fun t =>
    ‖((a.filter fun x => ¬ g x = 0).map fun x => g x + algebraMap K Ω t).prod‖ with hA
  set B : K → ℝ := fun t =>
    ‖((b.filter fun x => ¬ g x = 0).map fun x => g x + algebraMap K Ω t).prod‖ with hB
  have hc : ∀ c : Multiset Ω, Continuous fun t : K =>
      ‖(c.map fun x => g x + algebraMap K Ω t).prod‖ := fun c =>
    (continuous_multiset_prod c fun x _ => continuous_const.add (continuous_algebraMap K Ω)).norm
  have hAc : Continuous A := hc _
  have hBc : Continuous fun t : K => ‖t‖ ^ (k + 1) * B t := (continuous_norm.pow _).mul (hc _)
  have heq : Set.EqOn A (fun t : K => ‖t‖ ^ (k + 1) * B t) {0}ᶜ := by
    intro t ht
    have ht0 : ‖t‖ ≠ 0 := norm_ne_zero_iff.2 ht
    have := h t
    rw [norm_prod_add a, norm_prod_add b, hk, add_assoc, pow_add, _root_.mul_assoc] at this
    exact mul_left_cancel₀ (pow_ne_zero _ ht0) this
  have h0 := congrFun (Continuous.ext_on (dense_compl_singleton (0 : K)) hAc hBc heq) 0
  simp only [hA, norm_zero, pow_succ, mul_zero, zero_mul, map_zero, add_zero, norm_eq_zero,
    Multiset.prod_eq_zero_iff, Multiset.mem_map, Multiset.mem_filter] at h0
  obtain ⟨x, ⟨-, hx⟩, hx'⟩ := h0
  exact hx hx'

end Normed

section Padic

variable {l : ℕ} [Fact l.Prime] {Ω : Type} [NormedField Ω] [NormedAlgebra ℚ_[l] Ω]

theorem card_eq (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] Ω] (a b : Multiset Ω)
    (h : ∀ F : ℤ[X], ‖(a.map fun x => aeval x F).prod‖ = ‖(b.map fun x => aeval x F).prod‖) :
    a.card = b.card := by
  have h1 := h (C (l : ℤ))
  have hl : ‖(l : Ω)‖ = ‖(l : ℚ_[l])‖ := by
    rw [← norm_algebraMap' Ω (l : ℚ_[l]), map_natCast]
  simp only [aeval_C, map_natCast, Multiset.map_const', Multiset.prod_replicate, norm_pow,
    hl] at h1
  refine pow_right_injective₀ ?_ ?_ h1
  · exact norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  · exact Padic.norm_p_lt_one.ne

theorem rat_case (a b : Multiset Ω)
    (h : ∀ F : ℤ[X], ‖(a.map fun x => aeval x F).prod‖ = ‖(b.map fun x => aeval x F).prod‖)
    (F : ℚ[X]) :
    ‖(a.map fun x => aeval x (F.map (algebraMap ℚ ℚ_[l]))).prod‖ =
      ‖(b.map fun x => aeval x (F.map (algebraMap ℚ ℚ_[l]))).prod‖ := by
  obtain ⟨d, hd, hF⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) F
  set F₀ := IsLocalization.integerNormalization (nonZeroDivisors ℤ) F
  have hd0 : ((d : ℚ_[l])) ≠ 0 := Int.cast_ne_zero.2 (nonZeroDivisors.ne_zero hd)
  have hx : ∀ x : Ω, aeval x F₀ =
      algebraMap ℚ_[l] Ω (d : ℚ_[l]) * aeval x (F.map (algebraMap ℚ ℚ_[l])) := by
    intro x
    have h1 : F₀.map (algebraMap ℤ ℚ_[l]) = C (d : ℚ_[l]) * F.map (algebraMap ℚ ℚ_[l]) := by
      have := congrArg (Polynomial.map (algebraMap ℚ ℚ_[l])) hF
      rw [Polynomial.map_map, zsmul_eq_mul, Polynomial.map_mul, Polynomial.map_intCast] at this
      rw [← C_eq_intCast] at this
      rw [← this]
      congr 1
    rw [← aeval_map_algebraMap ℚ_[l], h1, map_mul, aeval_C]
  have h1 := h F₀
  simp only [hx, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, norm_mul,
    norm_pow, norm_algebraMap', card_eq l a b h] at h1
  exact mul_left_cancel₀ (pow_ne_zero _ (norm_ne_zero_iff.2 hd0)) h1

theorem padic_case (a b : Multiset Ω)
    (h : ∀ F : ℤ[X], ‖(a.map fun x => aeval x F).prod‖ = ‖(b.map fun x => aeval x F).prod‖)
    (F : ℚ_[l][X]) :
    ‖(a.map fun x => aeval x F).prod‖ = ‖(b.map fun x => aeval x F).prod‖ := by
  set n := F.natDegree + 1
  let φ : Multiset Ω → (Fin n → ℚ_[l]) → ℝ := fun c v =>
    ‖(c.map fun x => ∑ i : Fin n, algebraMap ℚ_[l] Ω (v i) * x ^ (i : ℕ)).prod‖
  have hc : ∀ c, Continuous (φ c) := fun c =>
    (continuous_multiset_prod c fun x _ => continuous_finsetSum _ fun i _ =>
      ((continuous_algebraMap ℚ_[l] Ω).comp (continuous_apply i)).mul continuous_const).norm
  have hd : DenseRange (Pi.map (fun (_ : Fin n) => ((↑) : ℚ → ℚ_[l]))) :=
    DenseRange.piMap fun _ => Padic.denseRange_ratCast l
  have heq : φ a = φ b := by
    refine Continuous.ext_on hd (hc a) (hc b) ?_
    rintro _ ⟨v, rfl⟩
    have := rat_case (l := l) a b h (∑ i : Fin n, monomial (i : ℕ) (v i))
    simpa [φ, Polynomial.map_sum, aeval_monomial] using this
  have := congrFun heq fun i => F.coeff i
  have hx : ∀ x : Ω, aeval x F = ∑ i : Fin n, algebraMap ℚ_[l] Ω (F.coeff i) * x ^ (i : ℕ) := by
    intro x
    rw [aeval_eq_sum_range, Finset.sum_range]
    simp only [Algebra.smul_def]
    rfl
  simpa only [hx] using this

end Padic

end ResultantNorm

theorem eq_of_norm_resultant_eq : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ_[l] Ω] [Algebra.IsAlgebraic ℚ_[l] Ω] (a b : Multiset Ω) (P Q : Polynomial ℚ_[l]), P.map (algebraMap ℚ_[l] Ω) = (a.map fun x => Polynomial.X - Polynomial.C x).prod → Q.map (algebraMap ℚ_[l] Ω) = (b.map fun x => Polynomial.X - Polynomial.C x).prod → (∀ (F : Polynomial ℤ) (u v : ℚ_[l]), algebraMap ℚ_[l] Ω u = (a.map fun x => Polynomial.aeval x F).prod → algebraMap ℚ_[l] Ω v = (b.map fun x => Polynomial.aeval x F).prod → ‖u‖ = ‖v‖) → P = Q := by
  intro l _ Ω _ _ _ a b P Q hP hQ h
  classical
  letI : NormedField Ω := spectralNorm.normedField ℚ_[l] Ω
  letI : NormedAlgebra ℚ_[l] Ω := spectralNorm.normedAlgebra ℚ_[l] Ω
  have h1 : ∀ F : Polynomial ℤ, ‖(a.map fun x => Polynomial.aeval x F).prod‖ =
      ‖(b.map fun x => Polynomial.aeval x F).prod‖ := by
    intro F
    obtain ⟨u, hu⟩ := ResultantNorm.exists_prod_aeval a P hP (F.map (algebraMap ℤ ℚ_[l]))
    obtain ⟨v, hv⟩ := ResultantNorm.exists_prod_aeval b Q hQ (F.map (algebraMap ℤ ℚ_[l]))
    simp only [Polynomial.aeval_map_algebraMap] at hu hv
    rw [← hu, ← hv, norm_algebraMap', norm_algebraMap']
    exact h F u v hu hv
  refine ResultantNorm.eq_of_countP _ a b P Q rfl hP hQ fun G => ?_
  have h2 : ∀ t : ℚ_[l],
      ‖(a.map fun x => Polynomial.aeval x G + algebraMap ℚ_[l] Ω t).prod‖ =
      ‖(b.map fun x => Polynomial.aeval x G + algebraMap ℚ_[l] Ω t).prod‖ := by
    intro t
    simpa only [map_add, Polynomial.aeval_C] using
      ResultantNorm.padic_case (l := l) a b h1 (G + Polynomial.C t)
  exact le_antisymm (ResultantNorm.countP_le b a _ fun t => (h2 t).symm)
    (ResultantNorm.countP_le a b _ h2)

end GlobalTheory
