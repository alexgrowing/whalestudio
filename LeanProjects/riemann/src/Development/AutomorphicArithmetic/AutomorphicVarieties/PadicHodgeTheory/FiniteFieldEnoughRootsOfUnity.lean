import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Mathlib.GroupTheory.FiniteAbelian.Duality

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem UpperTheory.V.Loc.finite_field_enough_roots_of_unity (k : Type) [Field k] [Finite k] :
    HasEnoughRootsOfUnity k (Nat.card kˣ) := by
  haveI : NeZero (Nat.card kˣ) := ⟨Nat.card_pos.ne'⟩
  refine HasEnoughRootsOfUnity.of_card_le ?_
  have htop : rootsOfUnity (Nat.card kˣ) k = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    rw [mem_rootsOfUnity]
    exact pow_card_eq_one'
  rw [htop, Subgroup.card_top]

private theorem UpperTheory.V.Loc.mem_closure_of_kernel_containment {G k J : Type} [Group G] [Field k] [Finite k] [Finite J]
    (χ : J → G →* kˣ) (ω : G →* kˣ) (h : ∀ g, (∀ j, χ j g = 1) → ω g = 1) :
    ω ∈ Subgroup.closure (Set.range χ) := by
  classical
  let Φ : G →* (J → kˣ) := Pi.monoidHom χ
  let A := Φ.range
  have hker : Φ.ker ≤ ω.ker := fun g hg => by
    rw [MonoidHom.mem_ker] at hg ⊢
    exact h g fun j => congrFun hg j
  let ψ : A →* kˣ := (QuotientGroup.lift Φ.ker ω hker).comp
    (QuotientGroup.quotientKerEquivRange Φ).symm.toMonoidHom
  have hψ : ∀ g, ψ (Φ.rangeRestrict g) = ω g := by
    intro g
    have hs : (QuotientGroup.quotientKerEquivRange Φ).symm (Φ.rangeRestrict g)
        = (g : G ⧸ Φ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift Φ.ker ω hker
      ((QuotientGroup.quotientKerEquivRange Φ).symm (Φ.rangeRestrict g)) = ω g
    rw [hs]
    rfl
  let e : J → (A →* kˣ) := fun j => (Pi.evalMonoidHom (fun _ : J => kˣ) j).comp A.subtype
  have he : ∀ j, (e j).comp Φ.rangeRestrict = χ j := fun j => by
    ext g
    rfl
  have hω : ω = ψ.comp Φ.rangeRestrict := by
    ext g
    rw [MonoidHom.comp_apply, hψ]
  haveI : Finite (A →* kˣ) :=
    Finite.of_injective (fun f : A →* kˣ => (f : A → kˣ)) DFunLike.coe_injective
  haveI : NeZero (Nat.card kˣ) := ⟨Nat.card_pos.ne'⟩
  haveI := UpperTheory.V.Loc.finite_field_enough_roots_of_unity k
  haveI : HasEnoughRootsOfUnity k (Monoid.exponent A) := by
    refine HasEnoughRootsOfUnity.of_dvd k (n := Nat.card kˣ) ?_
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_
    refine Subtype.ext (funext fun j => ?_)
    simp [pow_card_eq_one']
  haveI : HasEnoughRootsOfUnity k (Monoid.exponent (A →* kˣ)) := by
    refine HasEnoughRootsOfUnity.of_dvd k (n := Nat.card kˣ) ?_
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun f => ?_
    refine MonoidHom.ext fun a => ?_
    simp [pow_card_eq_one']
  have hS : ψ ∈ Subgroup.closure (Set.range e) := by
    rw [← CommGroup.forall_monoidHom_apply_eq_one_iff k]
    intro η hη
    have ha : CommGroup.monoidHomMonoidHomEquiv A k η = 1 := by
      refine Subtype.ext (funext fun j => ?_)
      have hj := CommGroup.apply_monoidHomMonoidHomEquiv k (e j) η
      rw [hη _ (Subgroup.subset_closure ⟨j, rfl⟩)] at hj
      exact hj
    rw [← CommGroup.apply_monoidHomMonoidHomEquiv k ψ η, ha, map_one]
  have key : ∀ φ ∈ Subgroup.closure (Set.range e),
      φ.comp Φ.rangeRestrict ∈ Subgroup.closure (Set.range χ) := by
    intro φ hφ
    induction hφ using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [he]
      exact Subgroup.subset_closure ⟨j, rfl⟩
    | one =>
      rw [MonoidHom.one_comp]
      exact one_mem _
    | mul x y _ _ hx hy =>
      rw [MonoidHom.mul_comp]
      exact mul_mem hx hy
    | inv x _ hx =>
      rw [MonoidHom.inv_comp]
      exact inv_mem hx
  rw [hω]
  exact key ψ hS

theorem UpperTheory.V.Loc.v0e :
    ∀ {G k ι : Type} [Group G] [Field k] [Finite k] [Finite ι] (κ : ι → G →* kˣ) (ω : G →* kˣ), (∃ g, (∀ i j, κ i g = κ j g) ∧ ω g ≠ 1) ↔ ω ∉ Subgroup.closure (Set.range fun q : ι × ι => κ q.1 / κ q.2) := by
  intro G k ι _ _ _ _ κ ω
  constructor
  · rintro ⟨g, hg, hω⟩ hmem
    apply hω
    refine Subgroup.closure_induction (p := fun x _ => x g = 1) ?_ ?_ ?_ ?_ hmem
    · rintro _ ⟨q, rfl⟩
      simp [hg q.1 q.2]
    · rfl
    · intro x y _ _ hx hy
      simp [hx, hy]
    · intro x _ hx
      simp [hx]
  · intro hn
    by_contra hc
    apply hn
    refine UpperTheory.V.Loc.mem_closure_of_kernel_containment _ ω fun g hg => ?_
    by_contra hne
    refine hc ⟨g, fun i j => ?_, hne⟩
    have := hg (i, j)
    simpa [div_eq_one] using this
