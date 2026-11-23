import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJFEBlockKernel
import GroundTheory.AutomorphicForms.SmoothRepContragredient
import GroundTheory.AutomorphicForms.CompactModCentre

noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open SchurOrthogonality

variable {𝔊 : Type*} [Group 𝔊] [TopologicalSpace 𝔊] [IsTopologicalGroup 𝔊] [LocallyCompactSpace 𝔊]
  [T2Space 𝔊] [TotallyDisconnectedSpace 𝔊]
  {W : Type*} [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ 𝔊 W}

theorem apply_fixedProj_of_invariant (hρ : IsSmooth ρ) {K : Subgroup 𝔊}
    (hKc : IsCompact (K : Set 𝔊)) (hKo : IsOpen (K : Set 𝔊)) {f : W →ₗ[ℂ] ℂ}
    (hf : ∀ k ∈ K, ∀ w, f (ρ k w) = f w) (w : W) :
    f (fixedProj ρ hρ hKc hKo w) = f w := by
  have hs := sub_fixedProj_mem hρ hKc hKo w
  have := coinvariantsKer_le_ker_of_invariant hf hs
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
  exact this.symm

theorem exists_smul_of_bilinear (hρ : IsAdmissible ρ) [ρ.IsIrreducible] {K : Subgroup 𝔊}
    (hKc : IsCompact (K : Set 𝔊)) (hKo : IsOpen (K : Set 𝔊))
    (b : W →ₗ[ℂ] smoothVectors (Representation.dual ρ) →ₗ[ℂ] ℂ)
    (hinvR : ∀ u ∈ fixedVectors ρ K, ∀ k ∈ K, ∀ l, b u (contragredient ρ k l) = b u l)
    (hinvL : ∀ l ∈ fixedVectors (contragredient ρ) K, ∀ k ∈ K, ∀ w, b (ρ k w) l = b w l)
    (hcomm : ∀ u ∈ fixedVectors ρ K, ∀ l ∈ fixedVectors (contragredient ρ) K, ∀ z,
      b (ρ z u) l = b u (contragredient ρ z⁻¹ l)) :
    ∃ c : ℂ, ∀ u ∈ fixedVectors ρ K, ∀ l : smoothVectors (Representation.dual ρ),
      b u l = c * (l : Module.Dual ℂ W) u := by
  classical
  set U := fixedVectors ρ K
  have : FiniteDimensional ℂ U := hρ.2 K hKc hKo
  set FC := fixedVectors (contragredient ρ) K
  set e := fixedContragredientEquiv hρ.1 hKc hKo with he
  set β : U →ₗ[ℂ] Module.Dual ℂ (Module.Dual ℂ U) :=
    (b ∘ₗ U.subtype).compl₂ (FC.subtype ∘ₗ (e.symm : Module.Dual ℂ U →ₗ[ℂ] FC)) with hβ
  set T : U →ₗ[ℂ] U := (Module.evalEquiv ℂ U).symm.toLinearMap ∘ₗ β with hTdef
  have hT : ∀ (u : U) (φ : Module.Dual ℂ U), φ (T u) = b u (e.symm φ : FC) := by
    intro u φ
    have h := congrArg (fun ψ : Module.Dual ℂ (Module.Dual ℂ U) => ψ φ)
      ((Module.evalEquiv ℂ U).apply_symm_apply (β u))
    simpa [hTdef, Module.evalEquiv_apply, hβ] using h
  have hTl : ∀ (u : U) (l : FC), ((l : smoothVectors (Representation.dual ρ)) :
      Module.Dual ℂ W) (T u) = b u l := by
    intro u l
    have h := hT u (e l)
    rw [e.symm_apply_apply] at h
    have h2 : (e l) (T u) = ((l : smoothVectors (Representation.dual ρ)) : Module.Dual ℂ W)
        (T u) := by
      rw [he, fixedContragredientEquiv_apply, restrictFixed_apply]
    rw [← h2, h]

  have hText : ∀ (u : U) (l : smoothVectors (Representation.dual ρ)),
      b u l = (l : Module.Dual ℂ W) (T u) := by
    intro u
    let g : smoothVectors (Representation.dual ρ) →ₗ[ℂ] ℂ :=
      { toFun := fun l => (l : Module.Dual ℂ W) (T u)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have heq := eq_of_invariant_of_eqOn (isSmooth_contragredient ρ) hKc hKo (f := b u) (g := g)
      (fun k hk l => hinvR u u.2 k hk l)
      (fun k hk l => by
        show ((contragredient ρ k l : smoothVectors (Representation.dual ρ)) :
          Module.Dual ℂ W) (T u) = (l : Module.Dual ℂ W) (T u)
        rw [contragredient_apply_apply, (T u).2 k⁻¹ (inv_mem hk)])
      (fun l hl => (hTl u ⟨l, hl⟩).symm)
    exact fun l => LinearMap.congr_fun heq l

  have hsep : ∀ x : U, (∀ l : FC, ((l : smoothVectors (Representation.dual ρ)) :
      Module.Dual ℂ W) x = 0) → x = 0 := by
    intro x hx
    refine (Module.forall_dual_apply_eq_zero_iff ℂ x).1 fun φ => ?_
    have := hx (e.symm φ)
    rw [← this]
    conv_lhs => rw [← e.apply_symm_apply φ]
    rw [he, fixedContragredientEquiv_apply, restrictFixed_apply]

  set E := fixedProj ρ hρ.1 hKc hKo
  set S : 𝔊 → U →ₗ[ℂ] U := fun z => E ∘ₗ ρ z ∘ₗ U.subtype with hS
  have hEl : ∀ l : FC, ∀ w : W, ((l : smoothVectors (Representation.dual ρ)) :
      Module.Dual ℂ W) (E w) = (l : Module.Dual ℂ W) w := fun l w =>
    apply_fixedProj_of_invariant hρ.1 hKc hKo (f := (l : Module.Dual ℂ W))
      (fun k hk v => (mem_fixedVectors_contragredient.1 l.2) k hk v) w
  have hcommT : ∀ z (u : U), T (S z u) = S z (T u) := by
    intro z u
    rw [← sub_eq_zero]
    refine hsep _ fun l => ?_
    rw [Submodule.coe_sub, map_sub, sub_eq_zero]
    rw [hTl, show S z (T u) = E (ρ z (T u)) from rfl, hEl]
    have h1 : b (S z u) l = b (ρ z u) l := by
      show b (E (ρ z u)) l = b (ρ z u) l
      exact apply_fixedProj_of_invariant hρ.1 hKc hKo (f := b.flip l)
        (fun k hk w => hinvL l l.2 k hk w) _
    rw [h1, hcomm u u.2 l l.2 z, hText u]
    rw [contragredient_apply_apply, inv_inv]

  have hspan : ∀ x : U, x ≠ 0 → ∀ y : U, y ∈ Submodule.span ℂ (Set.range fun z => S z x) := by
    intro x hx y
    have hx' : (x : W) ≠ 0 := fun h => hx (Subtype.ext h)
    have hy : (y : W) ∈ Submodule.span ℂ (Set.range fun z => ρ z (x : W)) := by
      rw [span_orbit_eq_top hx']; trivial
    have hmap := Submodule.mem_map_of_mem (f := E) hy
    rw [Submodule.map_span, ← Set.range_comp] at hmap
    rwa [show E (y : W) = y from Subtype.ext (fixedProj_apply_of_mem hρ.1 hKc hKo y.2)] at hmap

  by_cases htriv : Subsingleton U
  · refine ⟨0, fun u hu l => ?_⟩
    have : (⟨u, hu⟩ : U) = 0 := Subsingleton.elim _ _
    have hu0 : u = 0 := congrArg Subtype.val this
    rw [hu0, map_zero, LinearMap.zero_apply, map_zero, mul_zero]
  · rw [not_subsingleton_iff_nontrivial] at htriv
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
    obtain ⟨x, hx⟩ := hc.exists_hasEigenvector
    have hall : ∀ y : U, T y = c • y := by
      intro y
      have hmem : y ∈ Module.End.eigenspace T c := by
        refine Submodule.span_le.2 ?_ (hspan x hx.2 y)
        rintro _ ⟨z, rfl⟩
        rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
        show T (S z x) = c • S z x
        rw [hcommT,
          (Module.End.mem_eigenspace_iff.1 hx.1), map_smul]
      exact Module.End.mem_eigenspace_iff.1 hmem
    refine ⟨c, fun u hu l => ?_⟩
    rw [show u = ((⟨u, hu⟩ : U) : W) from rfl, hText, hall, Submodule.coe_smul, map_smul,
      smul_eq_mul]

end GodementJacquet

end GroundTheory.Automorphic
