import Mathlib
import Formalism.HermitianLattices.StatementLat
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.LocBasic

noncomputable section

namespace Formalism.HermitianLatticesTheory

section SlopeTestRemainingChoices

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem locDual_mem_dualAt (h : V →ₗ⋆[K] V →ₗ[K] K) (p : Ideal R) (L : Submodule R V) (x : V) :
    x ∈ dualAt h p L ↔ ∀ y ∈ L, h y x ∈ locR (K := K) p := by
  simp only [dualAt, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]

theorem locDual_mem_locR (p : Ideal R) (k : K) :
    k ∈ locR (K := K) p ↔
      ∃ s ∈ hcompl (K := K) p, algebraMap R K s * k ∈ (1 : Submodule R K) := by
  show (∃ s ∈ hcompl (K := K) p, s • k ∈ (1 : Submodule R K)) ↔ _
  simp only [Algebra.smul_def]

theorem locDual_h_smul_right (h : V →ₗ⋆[K] V →ₗ[K] K) (r : R) (y x : V) :
    h y (r • x) = algebraMap R K r * h y x := by
  rw [← algebraMap_smul K r x, map_smul, smul_eq_mul]

theorem locDual_h_smul_left (h : V →ₗ⋆[K] V →ₗ[K] K) (r : R) (y x : V) :
    h (r • y) x = star (algebraMap R K r) * h y x := by
  rw [← algebraMap_smul K r y, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply]

theorem locDual_one_mul {a b : K} (ha : a ∈ (1 : Submodule R K)) (hb : b ∈ (1 : Submodule R K)) :
    a * b ∈ (1 : Submodule R K) := by
  simpa using Submodule.mul_mem_mul ha hb

theorem locDual_alg_mem (r : R) : algebraMap R K r ∈ (1 : Submodule R K) :=
  Submodule.algebraMap_mem r

theorem locDual_dualAt_anti (h : V →ₗ⋆[K] V →ₗ[K] K) (p : Ideal R) {L M : Submodule R V}
    (hLM : L ≤ M) : dualAt h p M ≤ dualAt h p L := by
  intro x hx
  rw [locDual_mem_dualAt] at hx ⊢
  exact fun y hy => hx y (hLM hy)

private theorem mem_dual_iff_forall_mem_one (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule R V) (x : V) :
    x ∈ dual h L ↔ ∀ y ∈ L, h y x ∈ (1 : Submodule R K) := by
  simp only [dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply]

theorem locDual_loc_dual_le (h : V →ₗ⋆[K] V →ₗ[K] K) (p : Ideal R) (L : Submodule R V) :
    loc (K := K) p (dual h L) ≤ dualAt h p L := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ : ∃ s ∈ hcompl (K := K) p, s • x ∈ dual h L := hx
  rw [mem_dual_iff_forall_mem_one] at hsx
  rw [locDual_mem_dualAt]
  intro y hy
  rw [locDual_mem_locR]
  refine ⟨s, hs, ?_⟩
  rw [← locDual_h_smul_right]
  exact hsx y hy

theorem locDual_dualAt_le (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (p : Ideal R) (L : Submodule R V) (hL : L.FG) :
    dualAt h p L ≤ loc (K := K) p (dual h L) := by
  classical
  intro x hx
  rw [locDual_mem_dualAt] at hx
  obtain ⟨t, rfl⟩ := hL
  have hloc : ∀ y ∈ t, ∃ s ∈ hcompl (K := K) p,
      algebraMap R K s * h y x ∈ (1 : Submodule R K) :=
    fun y hy => (locDual_mem_locR p _).mp (hx y (Submodule.subset_span hy))
  choose! s hs hsy using hloc
  refine ⟨∏ y ∈ t, s y, Submonoid.prod_mem _ (fun y hy => hs y hy), ?_⟩
  rw [mem_dual_iff_forall_mem_one]
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    rw [locDual_h_smul_right, ← Finset.mul_prod_erase t s hy, map_mul,
      mul_comm (algebraMap R K (s y)), mul_assoc]
    exact locDual_one_mul (locDual_alg_mem _) (hsy y hy)
  | zero => simp
  | add y z _ _ hy hz =>
    rw [map_add, LinearMap.add_apply]
    exact Submodule.add_mem _ hy hz
  | smul r y _ hy =>
    rw [locDual_h_smul_left]
    obtain ⟨u, hu⟩ := hstar r
    rw [← hu]
    exact locDual_one_mul (locDual_alg_mem u) hy

theorem locDual_sigma_mem (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K)) (p : Ideal R)
    (s : R) (hs : s ∈ hcompl (K := K) p) :
    locBasic_sigma hinj hstar s ∈ hcompl (K := K) p := by
  have spec : ∀ r : R, algebraMap R K (locBasic_sigma hinj hstar r) = star (algebraMap R K r) :=
    fun r => (hstar r).choose_spec
  unfold hcompl at hs ⊢
  induction hs using Submonoid.closure_induction with
  | mem s hs =>
    apply Submonoid.subset_closure
    obtain ⟨hs1, hs2⟩ := hs
    refine ⟨hs2 _ (spec s), fun t ht => ?_⟩
    rw [spec, star_star] at ht
    rw [hinj ht]
    exact hs1
  | one => rw [map_one]; exact Submonoid.one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact Submonoid.mul_mem _ ha hb

theorem locDual_dualAt_loc (h : V →ₗ⋆[K] V →ₗ[K] K) (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (p : Ideal R) (L : Submodule R V) :
    dualAt h p (loc (K := K) p L) = dualAt h p L := by
  apply le_antisymm
  · apply locDual_dualAt_anti
    intro y hy
    show ∃ s ∈ hcompl (K := K) p, s • y ∈ L
    exact ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact hy⟩
  · intro x hx
    rw [locDual_mem_dualAt] at hx ⊢
    intro y hy
    obtain ⟨s, hs, hsy⟩ : ∃ s ∈ hcompl (K := K) p, s • y ∈ L := hy
    have h1 := hx _ hsy
    rw [locDual_h_smul_left, locDual_mem_locR] at h1
    obtain ⟨t, ht, hty⟩ := h1
    rw [locDual_mem_locR]
    refine ⟨t * locBasic_sigma hinj hstar s,
      Submonoid.mul_mem _ ht (locDual_sigma_mem hinj hstar p s hs), ?_⟩
    have spec : algebraMap R K (locBasic_sigma hinj hstar s) = star (algebraMap R K s) :=
      (hstar s).choose_spec
    rw [map_mul, spec, mul_assoc]
    exact hty

end SlopeTestRemainingChoices

theorem locDual : LocDual := by
  intro R K V _ _ _ _ _ _ _ _ _ _ h _ hstar L hL
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have key : ∀ p : Ideal R, loc (K := K) p (dual h L) = dualAt h p L := fun p =>
    le_antisymm (locDual_loc_dual_le h p L) (locDual_dualAt_le h hstar p L hL)
  have key2 : ∀ p : Ideal R, dualAt h p (loc (K := K) p L) = dualAt h p L :=
    fun p => locDual_dualAt_loc h hinj hstar p L
  refine ⟨fun p _ => ⟨key p, key2 p⟩, ?_⟩
  unfold IsUnimodular IsUnimodularAt
  constructor
  · intro hu p _
    rw [key2, ← key, hu]
  · intro H
    have H' : ∀ p : Ideal R, p.IsMaximal → loc (K := K) p (dual h L) = loc (K := K) p L := by
      intro p hp
      rw [key, ← key2]
      exact H p hp

    have avoid : ∀ p : Ideal R, p.IsPrime → ∀ s ∈ hcompl (K := K) p, s ∉ p := by
      intro p hp s hs
      unfold hcompl at hs
      induction hs using Submonoid.closure_induction with
      | mem s hs => exact hs.1
      | one => exact (Ideal.ne_top_iff_one p).mp hp.ne_top
      | mul a b _ _ ha hb => exact fun hab => (hp.mem_or_mem hab).elim ha hb

    have incl : ∀ M N : Submodule R V,
        (∀ p : Ideal R, p.IsMaximal → loc (K := K) p M = loc (K := K) p N) → N ≤ M := by
      intro M N hMN x hx
      by_contra hxM
      let I : Ideal R := M.comap (LinearMap.toSpanSingleton R V x)
      have hI : I ≠ ⊤ := by
        intro hI
        apply hxM
        have h1 : (1 : R) ∈ I := hI ▸ Submodule.mem_top
        simpa [I] using h1
      obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
      have hxN : x ∈ loc (K := K) m N := by
        show ∃ s ∈ hcompl (K := K) m, s • x ∈ N
        exact ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact hx⟩
      rw [← hMN m hm] at hxN
      obtain ⟨s, hs, hsx⟩ : ∃ s ∈ hcompl (K := K) m, s • x ∈ M := hxN
      exact avoid m hm.isPrime s hs (hIm (Submodule.mem_comap.mpr (by simpa using hsx)))
    exact le_antisymm (incl _ _ (fun p hp => (H' p hp).symm)) (incl _ _ H')

end Formalism.HermitianLatticesTheory
