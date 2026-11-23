import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar.IntClGens

variable {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} (x : κ → Ω)

theorem twist_mem {c j : κ} (hc : x c ≠ 0) {b : Ω} (hb : b ∈ chRing o x c) :
    ∃ e : ℕ, ∀ m, e ≤ m → (x c / x j) ^ m * b ∈ chRing o x j := by
  have ht : x c / x j ∈ chRing o x j := Algebra.subset_adjoin ⟨c, rfl⟩
  induction hb using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨l, rfl⟩ := hy
    refine ⟨1, fun m hm => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    have key : x c / x j * (x l / x c) = x l / x j := by
      rw [div_mul_div_comm, mul_comm (x j), mul_div_mul_left _ _ hc]
    have : (x c / x j) ^ (1 + k) * (x l / x c) = (x c / x j) ^ k * (x l / x j) := by
      rw [← key]; ring
    rw [this]
    exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ ht _) (Algebra.subset_adjoin ⟨l, rfl⟩)
  | algebraMap r =>
    exact ⟨0, fun m _ => Subalgebra.mul_mem _ (Subalgebra.pow_mem _ ht _) (Subalgebra.algebraMap_mem _ r)⟩
  | add y z _ _ hy hz =>
    obtain ⟨e1, h1⟩ := hy
    obtain ⟨e2, h2⟩ := hz
    exact ⟨max e1 e2, fun m hm => by
      rw [mul_add]
      exact Subalgebra.add_mem _ (h1 m (le_of_max_le_left hm)) (h2 m (le_of_max_le_right hm))⟩
  | mul y z _ _ hy hz =>
    obtain ⟨e1, h1⟩ := hy
    obtain ⟨e2, h2⟩ := hz
    refine ⟨e1 + e2, fun m hm => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    have : (x c / x j) ^ (e1 + e2 + k) * (y * z) =
        ((x c / x j) ^ (e1 + k) * y) * ((x c / x j) ^ e2 * z) := by ring
    rw [this]
    exact Subalgebra.mul_mem _ (h1 _ (by omega)) (h2 _ le_rfl)

theorem twist_integral {c j : κ} (hc : x c ≠ 0) {a : Ω} (ha : IsIntegral (chRing o x c) a) :
    ∃ e : ℕ, ∀ m, e ≤ m → IsIntegral (chRing o x j) ((x c / x j) ^ m * a) := by
  have ht : x c / x j ∈ chRing o x j := Algebra.subset_adjoin ⟨c, rfl⟩
  obtain ⟨p, hmon, hp⟩ := ha
  have hE : ∀ i, ∃ e : ℕ, ∀ m, e ≤ m → (x c / x j) ^ m * (p.coeff i : Ω) ∈ chRing o x j :=
    fun i => twist_mem x hc (p.coeff i).2
  choose E hE using hE
  obtain ⟨E0, hE0⟩ : ∃ E0, ∀ i ≤ p.natDegree, E i ≤ E0 :=
    ⟨(Finset.range (p.natDegree + 1)).sup E, fun i hi => Finset.le_sup (Finset.mem_range.2 (by omega))⟩
  have hn' : (p.map (algebraMap (chRing o x c) Ω)).natDegree = p.natDegree := hmon.natDegree_map _
  have hqm : ((p.map (algebraMap (chRing o x c) Ω)).scaleRoots ((x c / x j) ^ E0)).Monic :=
    (Polynomial.monic_scaleRoots_iff _).2 (hmon.map _)
  have hq0 : ((p.map (algebraMap (chRing o x c) Ω)).scaleRoots ((x c / x j) ^ E0)).eval
      ((x c / x j) ^ E0 * a) = 0 := by
    have h1 : (p.map (algebraMap (chRing o x c) Ω)).eval₂ (RingHom.id Ω) a = 0 := by
      rw [Polynomial.eval₂_map, RingHom.id_comp]; exact hp
    have := Polynomial.scaleRoots_eval₂_eq_zero (RingHom.id Ω) (s := (x c / x j) ^ E0) h1
    simpa [Polynomial.eval₂_id] using this
  have hlift : (p.map (algebraMap (chRing o x c) Ω)).scaleRoots ((x c / x j) ^ E0) ∈
      Polynomial.lifts (algebraMap (chRing o x j) Ω) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    have hmem : ((p.map (algebraMap (chRing o x c) Ω)).scaleRoots ((x c / x j) ^ E0)).coeff i ∈
        chRing o x j := by
      rw [Polynomial.coeff_scaleRoots, hn', Polynomial.coeff_map]
      rcases lt_trichotomy i p.natDegree with hi | hi | hi
      · have h1 : E i ≤ E0 := hE0 i hi.le
        have h2 : 1 ≤ p.natDegree - i := by omega
        have hle : E i ≤ E0 * (p.natDegree - i) :=
          calc E i ≤ E0 := h1
            _ = E0 * 1 := (mul_one _).symm
            _ ≤ E0 * (p.natDegree - i) := Nat.mul_le_mul_left _ h2
        rw [← pow_mul, mul_comm]
        exact hE i _ hle
      · rw [hi, Nat.sub_self, pow_zero, mul_one, hmon.coeff_natDegree, map_one]
        exact Subalgebra.one_mem _
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi, map_zero, zero_mul]
        exact Subalgebra.zero_mem _
    exact ⟨⟨_, hmem⟩, rfl⟩
  obtain ⟨q0, hq0map, -, hq0m⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hqm
  have hint : IsIntegral (chRing o x j) ((x c / x j) ^ E0 * a) :=
    ⟨q0, hq0m, by rw [← Polynomial.eval_map, hq0map]; exact hq0⟩
  refine ⟨E0, fun m hm => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have : (x c / x j) ^ (E0 + k) * a = (x c / x j) ^ k * ((x c / x j) ^ E0 * a) := by ring
  rw [this]
  have htk : IsIntegral (chRing o x j) ((x c / x j) ^ k) :=
    isIntegral_algebraMap (x := (⟨_, Subalgebra.pow_mem _ ht k⟩ : chRing o x j))
  exact htk.mul hint

theorem exists_twisted_gens : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ]
    (x : κ → Ω), (∀ c, x c ≠ 0 → Module.Finite (chRing o x c) (integralClosure (chRing o x c) Ω)) →
    ∃ (d n : ℕ) (z : κ ⊕ Fin n → Ω), (∀ c, z (Sum.inl c) = x c ^ d) ∧ ∀ c, x c ≠ 0 → ∀ a : Ω,
      IsIntegral (chRing o x c) a ↔ a ∈ Submodule.span (chRing o x c) (Set.range fun k => z k / x c ^ d) := by
  intro o _ Ω _ _ κ _ x hfin
  have hgen : ∀ c, ∃ (N : ℕ) (g : Fin N → Ω), (∀ k, x c ≠ 0 ∧ IsIntegral (chRing o x c) (g k)) ∧
      (x c ≠ 0 → ∀ a, IsIntegral (chRing o x c) a → a ∈ Submodule.span (chRing o x c) (Set.range g)) := by
    intro c
    by_cases hc : x c = 0
    · exact ⟨0, Fin.elim0, fun k => k.elim0, fun h => absurd hc h⟩
    · haveI := hfin c hc
      obtain ⟨N, s, hs⟩ := Module.Finite.exists_fin (R := chRing o x c) (M := integralClosure (chRing o x c) Ω)
      refine ⟨N, fun k => ((s k : integralClosure (chRing o x c) Ω) : Ω),
        fun k => ⟨hc, (s k).2⟩, fun _ a ha => ?_⟩
      have hle : Submodule.map (integralClosure (chRing o x c) Ω).val.toLinearMap
          (Submodule.span (chRing o x c) (Set.range s)) ≤
          Submodule.span (chRing o x c) (Set.range fun k => ((s k : integralClosure (chRing o x c) Ω) : Ω)) := by
        rw [Submodule.map_span_le]
        rintro _ ⟨k, rfl⟩
        exact Submodule.subset_span ⟨k, rfl⟩
      rw [hs] at hle
      exact hle (Submodule.mem_map_of_mem (p := ⊤) (f := (integralClosure (chRing o x c) Ω).val.toLinearMap)
        (r := ⟨a, ha⟩) Submodule.mem_top)
  choose N g hg using hgen
  obtain ⟨M, ⟨eI⟩⟩ := Finite.exists_equiv_fin (Σ c, Fin (N c))
  have hD : ∀ (i : Σ c, Fin (N c)) (j : κ), ∃ e : ℕ, ∀ m, e ≤ m →
      IsIntegral (chRing o x j) ((x i.1 / x j) ^ m * g i.1 i.2) :=
    fun i j => twist_integral x ((hg i.1).1 i.2).1 ((hg i.1).1 i.2).2
  choose D hD using hD
  obtain ⟨d, hd⟩ := Finite.exists_le (fun q : (Σ c, Fin (N c)) × κ => D q.1 q.2)
  refine ⟨d, M, Sum.elim (fun c => x c ^ d) (fun k => x (eI.symm k).1 ^ d * g (eI.symm k).1 (eI.symm k).2),
    fun c => rfl, fun c hc a => ⟨fun ha => ?_, fun ha => ?_⟩⟩
  · refine Submodule.span_mono ?_ ((hg c).2 hc a ha)
    rintro _ ⟨k, rfl⟩
    refine ⟨Sum.inr (eI ⟨c, k⟩), ?_⟩
    have he : eI.symm (eI ⟨c, k⟩) = ⟨c, k⟩ := eI.symm_apply_apply _
    simp only [Sum.elim_inr]
    rw [he]
    exact mul_div_cancel_left₀ _ (pow_ne_zero _ hc)
  · have hsub : (Set.range fun k => (Sum.elim (fun c => x c ^ d)
        (fun k => x (eI.symm k).1 ^ d * g (eI.symm k).1 (eI.symm k).2) k : Ω) / x c ^ d) ⊆
        ((integralClosure (chRing o x c) Ω).toSubmodule : Set Ω) := by
      rintro _ ⟨k, rfl⟩
      rw [SetLike.mem_coe, Subalgebra.mem_toSubmodule, mem_integralClosure_iff]
      rcases k with j | k
      · simp only [Sum.elim_inl]
        rw [← div_pow]
        exact isIntegral_algebraMap (x := (⟨_, Subalgebra.pow_mem _
          (Algebra.subset_adjoin ⟨j, rfl⟩ : x j / x c ∈ chRing o x c) d⟩ : chRing o x c))
      · simp only [Sum.elim_inr]
        rw [mul_div_right_comm, ← div_pow]
        exact hD (eI.symm k) c d (hd (eI.symm k, c))
    have := Submodule.span_le.2 hsub ha
    rwa [Subalgebra.mem_toSubmodule, mem_integralClosure_iff] at this

end GlobalTheory.CompanionTheory.Ar.IntClGens
