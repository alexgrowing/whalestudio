import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftSemiTmul

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB

theorem form_mem_of_mem_smul_top {A N : Type} [CommRing A] [AddCommGroup N] [Module A N]
    (J : Ideal A) (φ : N →ₗ[A] A) {n : N} (h : n ∈ J • (⊤ : Submodule A N)) : φ n ∈ J := by
  refine Submodule.smul_induction_on h ?_ ?_
  · intro r hr n _
    rw [map_smul, smul_eq_mul]
    exact J.mul_mem_right _ hr
  · intro x y hx hy
    rw [map_add]
    exact J.add_mem hx hy

theorem exists_step_of_sup_span {A : Type} [CommRing A] (K I : Ideal A) (S : Finset A)
    (hS : K ⊔ Ideal.span (S : Set A) = I) (hne : K ≠ I) :
    ∃ (J : Ideal A) (t : A), K ≤ J ∧ J ≠ I ∧ J ⊔ Ideal.span {t} = I := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact absurd (by simpa using hS) hne
  | insert a S' _ ih =>
    by_cases h : K ⊔ Ideal.span (S' : Set A) = I
    · exact ih h
    · refine ⟨K ⊔ Ideal.span (S' : Set A), a, le_sup_left, h, ?_⟩
      rw [← hS, Finset.coe_insert, Ideal.span_insert, sup_assoc, sup_comm (Ideal.span {a})]

theorem eq_zero_of_lift_of_mem_maximalIdeal_smul (A Q N : Type) [CommRing A] [IsLocalRing A]
    [AddCommGroup Q] [Module A Q] [Module.Finite A Q] [AddCommGroup N] [Module A N]
    [Module.Finite A N] [Module.Free A N] (b : Q →ₗ[A] N) (hL : Lift b)
    (hb : ∀ q, b q ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A N)) : b = 0 := by
  classical
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule A Q).FG)
  let v := Module.finBasis A N
  let g : Fin (Module.finrank A N) × S → A := fun p ↦ v.coord p.1 (b p.2)
  let I : Ideal A := Ideal.span (Set.range g)
  have hIfg : I.FG := ⟨(Set.finite_range g).toFinset, by simp [I]⟩

  have hcoord : ∀ q i, v.coord i (b q) ∈ I := by
    intro q
    have hq : q ∈ Submodule.span A (S : Set Q) := by rw [hS]; trivial
    induction hq using Submodule.span_induction with
    | mem x hx =>
      intro i
      exact Ideal.subset_span ⟨(i, ⟨x, hx⟩), rfl⟩
    | zero => intro i; simp
    | add x y _ _ hx hy =>
      intro i
      rw [map_add, map_add]
      exact I.add_mem (hx i) (hy i)
    | smul r x _ hx =>
      intro i
      rw [map_smul, map_smul, smul_eq_mul]
      exact I.mul_mem_left _ (hx i)

  have hval : ∀ q, b q ∈ I • (⊤ : Submodule A N) := by
    intro q
    rw [← v.sum_repr (b q)]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem_smul (hcoord q i) trivial
  have hIm : I ≤ IsLocalRing.maximalIdeal A := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨p, rfl⟩
    exact form_mem_of_mem_smul_top _ _ (hb p.2)
  have hI : I = ⊥ := by
    by_contra hI
    set m := IsLocalRing.maximalIdeal A with hm
    have hjac : m ≤ Ideal.jacobson (⊥ : Ideal A) := by
      rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    have hne : m * I ≠ I := by
      intro h
      exact hI (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot m I hIfg
        (by rw [smul_eq_mul, h]) hjac)
    obtain ⟨T, hT⟩ := hIfg
    have hsup : m * I ⊔ Ideal.span (T : Set A) = I := by
      have hT' : Ideal.span (T : Set A) = I := hT
      rw [hT']
      exact sup_eq_right.2 (Ideal.mul_le_right : m * I ≤ I)
    obtain ⟨J, t, hKJ, hJI, hJt⟩ := exists_step_of_sup_span (m * I) I T hsup hne
    have hJle : J ≤ I := hJt ▸ le_sup_left
    have htI : t ∈ I := by
      rw [← hJt]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self t)
    have hJtop : J ≠ ⊤ := fun h ↦ by
      have : (1 : A) ∈ m := hIm (hJle (h ▸ Submodule.mem_top))
      exact (Ideal.ne_top_iff_one m).1 (IsLocalRing.maximalIdeal.isMaximal A).ne_top this
    have hxt : ∀ x ∈ IsLocalRing.maximalIdeal A, x * t ∈ J :=
      fun x hx ↦ hKJ (Ideal.mul_mem_mul hx htI)

    have hstep : ∀ y ∈ I • (⊤ : Submodule A Q), b y ∈ J • (⊤ : Submodule A N) := by
      intro y hy
      refine Submodule.smul_induction_on hy ?_ ?_
      · intro r hr q _
        rw [map_smul]
        have h1 : r • b q ∈ I • m • (⊤ : Submodule A N) :=
          Submodule.smul_mem_smul hr (hb q)
        have h2 : I • m • (⊤ : Submodule A N) ≤ J • (⊤ : Submodule A N) := by
          rw [← Submodule.mul_smul, mul_comm]
          exact Submodule.smul_mono_left hKJ
        exact h2 h1
      · intro x y hx hy
        rw [map_add]
        exact Submodule.add_mem _ hx hy
    have hzJ : ∀ z, b z ∈ J • (⊤ : Submodule A N) := by
      intro z
      obtain ⟨x, hx, hxz⟩ := hL J t hJtop hxt z (by rw [hJt]; exact hval z)
      rw [hJt] at hxz
      have h := Submodule.sub_mem _ hx (hstep _ hxz)
      rwa [← map_sub, sub_sub_cancel] at h
    apply hJI
    refine le_antisymm hJle (Ideal.span_le.2 ?_)
    rintro _ ⟨p, rfl⟩
    exact form_mem_of_mem_smul_top _ _ (hzJ p.2)
  ext q
  apply v.repr.injective
  ext i
  have := hcoord q i
  rw [hI, Ideal.mem_bot] at this
  simpa using this

end GlobalTheory.CompanionTheory.PerfVB
