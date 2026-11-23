import Mathlib

open scoped nonZeroDivisors

namespace GlobalTheory
namespace LatticeDescent

theorem exists_extend_functional {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] {n : ℕ} (P : Submodule A (Fin n → K))
    (hP : Submodule.span K (P : Set (Fin n → K)) = ⊤) (ψ : P →ₗ[A] A) :
    ∃ φ : (Fin n → K) →ₗ[K] K, ∀ x : P, φ x = algebraMap A K (ψ x) := by
  haveI : IsLocalizedModule A⁰ P.subtype := by
    refine ⟨?_, ?_, ?_⟩
    · intro a
      rw [Module.End.isUnit_iff]
      have ha0 : algebraMap A K (a : A) ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors a.2
      have e : ⇑(algebraMap A (Module.End A (Fin n → K)) a) =
          fun v => algebraMap A K (a : A) • v := by
        funext v
        exact (algebraMap_smul K (a : A) v).symm
      rw [e]
      exact MulAction.bijective (Units.mk0 _ ha0)
    · intro y
      have hy : y ∈ Submodule.span K (P : Set (Fin n → K)) := hP ▸ Submodule.mem_top
      obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span A⁰ K _ y hy
      rw [Submodule.span_eq] at ht
      exact ⟨(⟨_, ht⟩, t), rfl⟩
    · intro x y hxy
      exact ⟨1, by rw [Subtype.ext hxy]⟩
  let g : P →ₗ[A] K := Algebra.linearMap A K ∘ₗ ψ
  have hu : ∀ a : A⁰, IsUnit (algebraMap A (Module.End A K) a) :=
    fun a => IsLocalizedModule.map_units (S := A⁰) (Algebra.linearMap A K) a
  refine ⟨(IsLocalizedModule.lift A⁰ P.subtype g hu).extendScalarsOfIsLocalization A⁰ K,
    fun x => ?_⟩
  exact IsLocalizedModule.lift_apply A⁰ P.subtype g hu x

theorem mem_of_map_mem_span_integralClosure :
    ∀ (A K L : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K] [Algebra A K]
      [IsFractionRing A K] [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] (n : ℕ)
      (P : Submodule A (Fin n → K)), Module.Finite A P → Module.Projective A P →
      Submodule.span K (P : Set (Fin n → K)) = ⊤ → ∀ v : Fin n → K,
      (fun i => algebraMap K L (v i)) ∈ Submodule.span (integralClosure A L)
        ((fun (w : Fin n → K) (i : Fin n) => algebraMap K L (w i)) '' (P : Set (Fin n → K))) →
      v ∈ P := by
  intro A K L _ _ _ _ _ _ _ _ _ _ n P hfin hproj hspan v hv

  obtain ⟨m, π, hπ⟩ := Module.Finite.exists_fin' A P
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  have hs' : ∀ x, π (s x) = x := fun x => LinearMap.congr_fun hs x
  let p : Fin m → P := fun j => π (fun k => if j = k then 1 else 0)
  have hdecomp : ∀ x : P, x = ∑ j, s x j • p j := by
    intro x
    conv_lhs => rw [← hs' x]
    exact LinearMap.pi_apply_eq_sum_univ π (s x)

  have hF : ∀ j : Fin m, ∃ φ : (Fin n → K) →ₗ[K] K, ∀ x : P,
      φ x = algebraMap A K (s x j) :=
    fun j => exists_extend_functional P hspan ((LinearMap.proj j) ∘ₗ s)
  choose F hFx using hF

  have hid : (∑ j, (F j).smulRight ((p j : P) : Fin n → K)) = LinearMap.id := by
    apply LinearMap.ext_on hspan
    intro x hx
    have hx' := hdecomp ⟨x, hx⟩
    simp only [Finset.sum_apply, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.id_apply]
    conv_rhs => rw [show x = ((⟨x, hx⟩ : P) : Fin n → K) from rfl, hx']
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hFx j ⟨x, hx⟩, Submodule.coe_smul, algebraMap_smul]
  have hvsum : v = ∑ j, F j v • ((p j : P) : Fin n → K) := by
    have := LinearMap.congr_fun hid v
    simpa [Finset.sum_apply, LinearMap.sum_apply, LinearMap.smulRight_apply] using this.symm

  set ι : (Fin n → K) → (Fin n → L) := fun w i => algebraMap K L (w i) with hι
  have hint : ∀ j, IsIntegral A (F j v) := by
    intro j
    let g : (Fin n → L) → L := fun w => ∑ i, w i * algebraMap K L (F j (Pi.single i 1))
    have hg : ∀ u : Fin n → K, g (ι u) = algebraMap K L (F j u) := by
      intro u
      have hu := LinearMap.pi_apply_eq_sum_univ (F j) u
      rw [hu, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have e : (fun k => if i = k then (1 : K) else 0) = Pi.single i 1 := by
        ext k; simp [Pi.single_apply, eq_comm]
      rw [smul_eq_mul, map_mul, e]
    have key : ∀ w ∈ Submodule.span (integralClosure A L) (ι '' (P : Set (Fin n → K))),
        IsIntegral A (g w) := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨u, hu, rfl⟩ := hx
        rw [hg u, hFx j ⟨u, hu⟩, ← IsScalarTower.algebraMap_apply]
        exact isIntegral_algebraMap
      | zero => simpa [g] using (isIntegral_zero : IsIntegral A (0 : L))
      | add x y _ _ hx hy =>
        have : g (x + y) = g x + g y := by
          simp only [g, Pi.add_apply, add_mul, Finset.sum_add_distrib]
        rw [this]; exact hx.add hy
      | smul b x _ hx =>
        have : g (b • x) = (b : L) * g x := by
          simp only [g, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Pi.smul_apply, Subalgebra.smul_def, smul_eq_mul, mul_assoc]
        rw [this]; exact b.2.mul hx
    have := key _ hv
    rw [hg v, isIntegral_algebraMap_iff (algebraMap K L).injective] at this
    exact this
  choose y hy using fun j => IsIntegrallyClosed.isIntegral_iff.1 (hint j)
  rw [hvsum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [← hy j, algebraMap_smul]
  exact P.smul_mem _ (p j).2

end LatticeDescent
end GlobalTheory
