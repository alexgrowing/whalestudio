import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
open GlobalTheory.K5

namespace GlobalTheory.K5

theorem gal_finite_subcover : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ S : Gal p Ω → Finset Ω, ∃ F : Finset (Gal p Ω), ∀ h : Gal p Ω, ∃ g ∈ F, ∀ x ∈ S g, h x = g x := by
  intro p _ Ω _ _ hΩ S
  classical
  letI : TopologicalSpace Ω := ⊥
  haveI : DiscreteTopology Ω := ⟨rfl⟩
  haveI : IsDomain (O0 p) := hΩ.inj.isDomain (algebraMap (O0 p) Ω)
  haveI : Module.IsTorsionFree (O0 p) Ω := Module.isTorsionFree_iff_algebraMap_injective.mpr hΩ.inj
  haveI := hΩ.alg
  choose P hP0 hP using fun x : Ω => (Algebra.IsAlgebraic.isAlgebraic (R := O0 p) x)
  have hmap : ∀ x, (P x).map (algebraMap (O0 p) Ω) ≠ 0 := fun x =>
    (Polynomial.map_ne_zero_iff hΩ.inj).mpr (hP0 x)
  let R : Ω → Set Ω := fun x => (((P x).map (algebraMap (O0 p) Ω)).roots.toFinset : Set Ω)
  have hR : ∀ (φ : Ω →ₐ[O0 p] Ω) x, φ x ∈ R x := by
    intro φ x
    simp only [R, Finset.mem_coe, Multiset.mem_toFinset]
    rw [Polynomial.mem_roots (hmap x), Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def,
      Polynomial.aeval_algHom_apply, hP x, map_zero]
  let K : Set (Ω → Ω) := Set.pi Set.univ R
  have hK : IsCompact K := isCompact_univ_pi (fun x => (Finset.finite_toSet _).isCompact)
  let C : Set (Ω → Ω) := (⋂ a, ⋂ b, {f | f (a + b) = f a + f b}) ∩ (⋂ a, ⋂ b, {f | f (a * b) = f a * f b})
      ∩ {f | f 1 = 1} ∩ ⋂ r : O0 p, {f | f (algebraMap (O0 p) Ω r) = algebraMap (O0 p) Ω r}
  have hC : IsClosed C := by
    have key : ∀ (u : (Ω → Ω) → Ω × Ω × Ω), Continuous u → ∀ T : Set (Ω × Ω × Ω),
        IsClosed (u ⁻¹' T) := fun u hu T => (isClosed_discrete T).preimage hu
    refine IsClosed.inter (IsClosed.inter (IsClosed.inter ?_ ?_) ?_) ?_
    · refine isClosed_iInter fun a => isClosed_iInter fun b => ?_
      exact key (fun f => (f (a + b), f a, f b)) (by fun_prop) {t | t.1 = t.2.1 + t.2.2}
    · refine isClosed_iInter fun a => isClosed_iInter fun b => ?_
      exact key (fun f => (f (a * b), f a, f b)) (by fun_prop) {t | t.1 = t.2.1 * t.2.2}
    · exact key (fun f => (f 1, f 1, f 1)) (by fun_prop) {t | t.1 = 1}
    · refine isClosed_iInter fun r => ?_
      exact key (fun f => (f (algebraMap (O0 p) Ω r), f 1, f 1)) (by fun_prop)
        {t | t.1 = algebraMap (O0 p) Ω r}
  let U : Gal p Ω → Set (Ω → Ω) := fun g => ⋂ x ∈ S g, (fun f => f x) ⁻¹' {g x}
  have hU : ∀ g, IsOpen (U g) := fun g =>
    isOpen_biInter_finset (fun x _ => (isOpen_discrete {g x}).preimage (continuous_apply x))
  have hcov : K ∩ C ⊆ ⋃ g, U g := by
    rintro f ⟨-, ⟨⟨hadd, hmul⟩, h1⟩, halg⟩
    simp only [Set.mem_iInter, Set.mem_setOf_eq] at hadd hmul h1 halg
    have h0 : f 0 = 0 := by
      have := hadd 0 0
      simp only [add_zero] at this
      exact left_eq_add.mp this
    let φ : Ω →ₐ[O0 p] Ω :=
      { toFun := f, map_one' := h1, map_mul' := hmul, map_zero' := h0, map_add' := hadd,
        commutes' := halg }
    let e : Gal p Ω := AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ)
    refine Set.mem_iUnion.mpr ⟨e, ?_⟩
    simp only [U, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
    intro x _
    rfl
  have hmem : ∀ h : Gal p Ω, (⇑h : Ω → Ω) ∈ K ∩ C := by
    intro h
    refine ⟨fun x _ => hR (h : Ω →ₐ[O0 p] Ω) x, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · simp only [Set.mem_iInter, Set.mem_setOf_eq]; intro a b; exact map_add h a b
    · simp only [Set.mem_iInter, Set.mem_setOf_eq]; intro a b; exact map_mul h a b
    · exact map_one h
    · simp only [Set.mem_iInter, Set.mem_setOf_eq]; intro r; exact h.commutes r
  obtain ⟨F, hF⟩ := (hK.inter_right hC).elim_finite_subcover U hU hcov
  refine ⟨F, fun h => ?_⟩
  obtain ⟨g, hg, hgh⟩ := Set.mem_iUnion₂.mp (hF (hmem h))
  refine ⟨g, hg, fun x hx => ?_⟩
  have := Set.mem_iInter₂.mp hgh x hx
  simpa using this

end GlobalTheory.K5
