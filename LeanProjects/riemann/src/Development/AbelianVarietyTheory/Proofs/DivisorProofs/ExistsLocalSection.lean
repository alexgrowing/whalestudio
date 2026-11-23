import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB
open GlobalTheory.Twist (resM resM_resM resM_smul app_resM germ_resM)
open GlobalTheory.QCoh (appLinear appLinear_apply)

namespace GlobalTheory.DualExact

variable {X : Scheme.{0}}

theorem exists_local_section {F G : X.Modules} (φ : F ⟶ G) [Epi φ] {s : ℕ} (hG : IsVB G s)
    {V : X.Opens} {x : X} (hx : x ∈ V) :
    ∃ (U : X.Opens), U ≤ V ∧ x ∈ U ∧
      ∃ σ : ∀ W : X.Opens, W ≤ U → (Γ(G, W) →ₗ[Γ(X, W)] Γ(F, W)),
        (∀ (W W' : X.Opens) (h : W ≤ U) (h' : W' ≤ W) (t : Γ(G, W)),
          σ W' (h'.trans h) (resM G h' t) = resM F h' (σ W h t)) ∧
        ∀ (W : X.Opens) (h : W ≤ U) (t : Γ(G, W)), φ.app W (σ W h t) = t := by
  obtain ⟨U, e, -, hxU, hle, he⟩ := hG.exists_affine hx
  choose T hT hxT a ha using fun i => exists_app_eq_of_epi φ (e i) hxU
  let U' : X.Opens := U ⊓ Finset.univ.inf T
  have hx' : x ∈ U' := ⟨hxU, by rw [Opens.coe_finset_inf]; simpa using hxT⟩
  have hU' (i) : U' ≤ T i := inf_le_right.trans (Finset.inf_le (Finset.mem_univ i))
  have hU : U' ≤ U := inf_le_left
  refine ⟨U', hU.trans hle, hx', fun W h =>
    (he.basis (h.trans hU)).constr Γ(X, W) fun i => resM F (h.trans (hU' i)) (a i),
    fun W W' h h' t => ?_, fun W h t => ?_⟩
  · simp only [Module.Basis.constr_apply_fintype, Module.Basis.equivFun_apply, map_sum,
      resM_smul, resM_resM]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← he.repr_resM (h.trans hU) h']
  · rw [← appLinear_apply]
    simp only [Module.Basis.constr_apply_fintype, Module.Basis.equivFun_apply, map_sum,
      map_smul, appLinear_apply, app_resM, ha, resM_resM]
    conv_rhs => rw [← (he.basis (h.trans hU)).sum_repr t]
    simp only [IsFrame.basis_apply]

theorem exact_of_locally (S : ShortComplex X.Modules)
    (H : ∀ (V : X.Opens) (x : X), x ∈ V → ∃ U : X.Opens, U ≤ V ∧ x ∈ U ∧
      ∀ t : Γ(S.X₂, U), S.g.app U t = 0 → ∃ u, S.f.app U u = t) : S.Exact := by
  refine (QCoh.exact_iff_stalkLinear S).2 fun x t => ⟨fun ht => ?_, ?_⟩
  · obtain ⟨V, hV, t, rfl⟩ := S.X₂.presheaf.exists_germ_eq t
    rw [QCoh.stalkLinear_germ, ← map_zero (S.X₃.presheaf.germ V x hV).hom] at ht
    obtain ⟨V', hV', i₁, i₂, e⟩ := S.X₃.presheaf.germ_eq x hV hV _ _ ht
    have e' : resM S.X₃ i₁.le (S.g.app V t) = 0 := e.trans (map_zero _)
    obtain ⟨U, hU, hxU, HU⟩ := H V' x hV'
    obtain ⟨u, hu⟩ := HU (resM S.X₂ (hU.trans i₁.le) t) (by
      rw [app_resM, ← resM_resM i₁.le hU, e', map_zero])
    exact ⟨S.X₁.presheaf.germ U x hxU u, by rw [QCoh.stalkLinear_germ, hu, germ_resM]⟩
  · rintro ⟨u, rfl⟩
    rw [← LinearMap.comp_apply, ← QCoh.stalkLinear_comp, S.zero, QCoh.stalkLinear_zero,
      LinearMap.zero_apply]

theorem shortExact_dual : ∀ (X : Scheme.{0}) (S : ShortComplex X.Modules) (s : ℕ),
    S.ShortExact → IsVB S.X₃ s → (ShortComplex.mk (dualMap S.g) (dualMap S.f)
      (by rw [← dualMap_comp, S.zero, dualMap_zero])).ShortExact := by
  intro X S s hS h₃
  have := hS.mono_f
  have := hS.epi_g
  have hex (W : X.Opens) (t : Γ(S.X₂, W)) (ht : S.g.app W t = 0) : ∃ u, S.f.app W u = t :=
    (QCoh.exact_app_of_exact_of_mono hS.exact W t).1 ht
  have hz (W : X.Opens) (u : Γ(S.X₁, W)) : S.g.app W (S.f.app W u) = 0 :=
    (QCoh.exact_app_of_exact_of_mono hS.exact W _).2 ⟨u, rfl⟩
  have hinj (W : X.Opens) : Function.Injective (appLinear S.f W) :=
    QCoh.injective_app_of_mono S.f W
  refine ShortComplex.ShortExact.mk' (exact_of_locally _ fun V x hx => ?_)
    (mono_dualMap S.g) (QCoh.epi_of_locally_app_surjective _ fun V x hx => ?_)
  · obtain ⟨U, hU, hxU, σ, hσ, hg⟩ := exists_local_section S.g h₃ hx
    refine ⟨U, hU, hxU, fun (l : Γ(dual S.X₂, U)) (hl : (dualMap S.f).app U l = 0) =>
      ⟨dualMk (fun W h => dualApp l h ∘ₗ σ W h) fun W W' h h' t => ?_, ?_⟩⟩
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, hσ W W' h h', dualApp_resM]
    · refine dual_ext fun W h t => ?_
      change dualApp l h (σ W h (S.g.app W t)) = _
      obtain ⟨u, hu⟩ := hex W (t - σ W h (S.g.app W t)) (by rw [map_sub, hg, sub_self])
      have := dualApp_dualMap S.f l h u
      rw [hl, hu, map_sub, dualApp_zero, LinearMap.zero_apply, eq_comm, sub_eq_zero] at this
      exact this.symm
  · obtain ⟨U, hU, hxU, σ, hσ, hg⟩ := exists_local_section S.g h₃ hx
    let ρ (W : X.Opens) (h : W ≤ U) : Γ(S.X₂, W) →ₗ[Γ(X, W)] Γ(S.X₁, W) :=
      LinearMap.codRestrictOfInjective (LinearMap.id - σ W h ∘ₗ appLinear S.g W)
        (appLinear S.f W) (hinj W) fun t => hex W _ (by
          change S.g.app W (t - σ W h (S.g.app W t)) = 0
          rw [map_sub, hg, sub_self])
    have hρ (W : X.Opens) (h : W ≤ U) (t : Γ(S.X₂, W)) :
        S.f.app W (ρ W h t) = t - σ W h (S.g.app W t) :=
      LinearMap.codRestrictOfInjective_comp_apply _ (appLinear S.f W) _ _ t
    refine ⟨U, hxU, hU, fun (l : Γ(dual S.X₁, U)) =>
      ⟨dualMk (fun W h => dualApp l h ∘ₗ ρ W h) fun W W' h h' t => ?_, ?_⟩⟩
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, ← dualApp_resM]
      congr 1
      apply hinj W'
      rw [appLinear_apply, appLinear_apply, app_resM, hρ, hρ, map_sub, app_resM, hσ W W' h h']
    · refine dual_ext fun W h u => ?_
      change dualApp l h (ρ W h (S.f.app W u)) = _
      congr 1
      apply hinj W
      rw [appLinear_apply, appLinear_apply, hρ, hz, map_zero, sub_zero]

end GlobalTheory.DualExact
