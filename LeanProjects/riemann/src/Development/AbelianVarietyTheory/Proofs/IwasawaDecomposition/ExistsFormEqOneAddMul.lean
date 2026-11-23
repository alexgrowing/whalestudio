import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsExtendResidue
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocM

theorem exists_form_eq_one_add_mul {O M : Type} [CommRing O] [IsDomain O] [IsDedekindDomain O] [AddCommGroup M]
    [Module O M] [Module.Projective O M] [Nontrivial M] {q : O} (hq0 : q ≠ 0) :
    ∃ (g : M →ₗ[O] O) (x : M) (t : O), g x = 1 + q * t := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective O M)
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : M)
  have hsx : s x₀ ≠ 0 := fun h => hx₀ (by simpa [h] using (LinearMap.congr_fun hs x₀).symm)
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hsx
  set g₀ : M →ₗ[O] O := Finsupp.lapply i ∘ₗ s with hg₀
  have hg₀x : g₀ x₀ ≠ 0 := by simpa [hg₀] using hi
  by_cases hq : IsUnit q
  · obtain ⟨u, rfl⟩ := hq
    exact ⟨g₀, x₀, ↑u⁻¹ * (g₀ x₀ - 1), by rw [← mul_assoc, Units.mul_inv, one_mul]; ring⟩
  set J : Ideal O := LinearMap.range g₀ with hJ
  have hJ0 : J ≠ ⊥ := fun h => hg₀x (by
    have : g₀ x₀ ∈ J := LinearMap.mem_range_self _ _
    rwa [h, Ideal.mem_bot] at this)
  have h0 : Ideal.span {q} * J ≠ ⊥ := mul_ne_zero (by simpa using hq0) hJ0
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq (I := Ideal.span {q} * J) (J := J) Ideal.mul_le_right h0
  have haJ : a ∈ J := ha ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
  obtain ⟨x, hx⟩ := LinearMap.mem_range.1 haJ
  obtain ⟨J', hJ'⟩ := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 haJ)
  have hcop : Ideal.span {q} ⊔ J' = ⊤ := by
    apply mul_left_cancel₀ hJ0
    rw [Ideal.mul_sup, Ideal.mul_top, mul_comm J, ← hJ', ha]
  obtain ⟨y, hy, c, hc, hyc⟩ := Submodule.mem_sup.1 (hcop ▸ Submodule.mem_top : (1 : O) ∈ Ideal.span {q} ⊔ J')
  obtain ⟨t', rfl⟩ := Ideal.mem_span_singleton'.1 hy
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hq
    have hJ'0 : J' = ⊥ := by
      have h1 : J * J' = ⊥ := by rw [← hJ', Ideal.span_singleton_eq_bot]
      exact (mul_eq_zero.1 h1).resolve_left hJ0
    rw [hJ'0, sup_bot_eq, Ideal.span_singleton_eq_top] at hcop
    exact hcop
  have hmem : ∀ z, (c • g₀) z ∈ LinearMap.range (LinearMap.mulLeft O a) := by
    intro z
    have : g₀ z * c ∈ Ideal.span {a} := hJ' ▸ Ideal.mul_mem_mul (LinearMap.mem_range_self g₀ z) hc
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 this
    exact ⟨w, by rw [LinearMap.mulLeft_apply, mul_comm, hw, LinearMap.smul_apply, smul_eq_mul, mul_comm]⟩
  let e := LinearEquiv.ofInjective (LinearMap.mulLeft O a) (mul_right_injective₀ ha0)
  let g : M →ₗ[O] O := e.symm.toLinearMap ∘ₗ (c • g₀).codRestrict _ hmem
  have hg : ∀ z, a * g z = c * g₀ z := fun z => by
    set w := e.symm ⟨_, hmem z⟩ with hw
    have h1 : ((e w) : O) = (c • g₀) z := by rw [hw, e.apply_symm_apply]
    have h2 : ((e w) : O) = a * w := LinearEquiv.ofInjective_apply _ _
    show a * w = c * g₀ z
    rw [← h2, h1, LinearMap.smul_apply, smul_eq_mul]
  refine ⟨g, x, -t', mul_left_cancel₀ ha0 ?_⟩
  rw [hg, hx]
  linear_combination a * hyc

theorem exists_isCompl_equiv_quot {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (I : Ideal O)
    (ψ : M →ₗ[O] O ⧸ I) (x : M) (hx : ψ x = 1) (hIx : ∀ r ∈ I, r • x = 0) :
    ∃ l : Submodule O M, (∃ l', IsCompl l l') ∧ Nonempty (l ≃ₗ[O] O ⧸ I) := by
  let σ : (O ⧸ I) →ₗ[O] M := Submodule.liftQ I (LinearMap.toSpanSingleton O M x) fun r hr => by
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
    exact hIx r hr
  have hσ : ∀ u, ψ (σ u) = u := by
    intro u
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective u
    show ψ (σ (Submodule.Quotient.mk r)) = _
    rw [Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, map_smul, hx, Algebra.smul_def, mul_one]
    rfl
  have hinj : Function.Injective σ := Function.LeftInverse.injective hσ
  let f : M →ₗ[O] LinearMap.range σ := (σ ∘ₗ ψ).codRestrict _ fun m => LinearMap.mem_range_self σ _
  refine ⟨LinearMap.range σ, ⟨_, LinearMap.isCompl_of_proj (f := f) ?_⟩, ⟨(LinearEquiv.ofInjective σ hinj).symm⟩⟩
  rintro ⟨_, u, rfl⟩
  exact Subtype.ext (congrArg σ (hσ u))

theorem nonempty_sum1 :
    ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (p : ℕ) (ct : At S κ p), Nonempty ct.Sum1 := by
  intro D A N j S κ p ct
  have := S.Dw.proj
  have : Nontrivial S.Dw.La := Module.nontrivial_of_finrank_pos (R := 𝓞 D.host.E)
    (by rw [S.Dw.rank, S.rank_eq]; exact lt_of_lt_of_le two_pos S.two_le)
  have hp0 : (p : 𝓞 D.host.E) ≠ 0 := by exact_mod_cast ct.hp.ne_zero
  obtain ⟨g, x, t, hg⟩ := exists_form_eq_one_add_mul (M := S.Dw.La) hp0
  let P : Submodule (𝓞 D.host.E) S.Dw.La := Ideal.span {(p : 𝓞 D.host.E)} • ⊤
  let ψ : ct.LaP →ₗ[𝓞 D.host.E] 𝓞 D.host.E ⧸ Ideal.span {(p : 𝓞 D.host.E)} :=
    P.liftQ ((Ideal.span {(p : 𝓞 D.host.E)}).mkQ ∘ₗ g) (Submodule.smul_le.2 fun r hr n _ => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, map_smul,
        smul_eq_mul]
      exact Ideal.mul_mem_right _ _ hr)
  have hx : ψ (Submodule.Quotient.mk x) = 1 := by
    show Submodule.Quotient.mk (g x) = (1 : 𝓞 D.host.E ⧸ Ideal.span {(p : 𝓞 D.host.E)})
    exact (Submodule.Quotient.eq _).2 (by
      rw [hg, add_sub_cancel_left]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  have hIx : ∀ r ∈ Ideal.span {(p : 𝓞 D.host.E)}, r • (Submodule.Quotient.mk x : ct.LaP) = 0 := by
    intro r hr
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  obtain ⟨l, hl, he⟩ := exists_isCompl_equiv_quot _ ψ _ hx hIx
  exact ⟨⟨l, hl, he⟩⟩

end GlobalTheory.LocM
