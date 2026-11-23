import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.HasPres
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.AdmissibleLatticesCommensurable

open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations TensorProduct UpperTheory.KN

theorem _root_.UpperTheory.KN.isLocallyConstant_torsion_push_of_continuous :
    ∀ {G O LL Q : Type} [TopologicalSpace G] [CommRing O] [IsDomain O] [IsNoetherianRing O] [Field LL] [TopologicalSpace LL]
      [IsTopologicalRing LL] [Algebra O LL] [IsFractionRing O LL] [AddCommGroup Q] [Module O Q] {a n : ℕ}
      (Y : Submodule O (Fin a → Fin n → LL)) (φ : ↥Y →ₗ[O] Q) (u : G → Fin a → Fin n → LL) (hu : ∀ g, u g ∈ Y) (c : O),
      IsOpen (Set.range (algebraMap O LL)) → Continuous u → c ≠ 0 → (∀ y, c • φ y = 0) →
      IsLocallyConstant fun g => φ ⟨u g, hu g⟩ := by
  classical
  intro G O LL Q _ _ _ _ _ _ _ _ _ _ _ a n Y φ u hu c hopen hcont hc hkill
  let Lmap : (Fin a → Fin n → O) →ₗ[O] (Fin a → Fin n → LL) :=
    ((Algebra.linearMap O LL).compLeft (Fin n)).compLeft (Fin a)
  let Λ := LinearMap.range Lmap
  have hΛ : Λ.FG := by
    show (LinearMap.range Lmap).FG
    rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map _
  obtain ⟨μ, hμ0, hμ⟩ := admissible_lattices_commensurable (LL := LL) Λ Y hΛ c hc
  have hμL : algebraMap O LL μ ≠ 0 := fun h =>
    hμ0 ((IsFractionRing.injective O LL) (h.trans (map_zero _).symm))
  let W : Set LL := (fun x => (algebraMap O LL μ)⁻¹ * x) ⁻¹' Set.range (algebraMap O LL)
  have hW : IsOpen W := hopen.preimage (continuous_const.mul continuous_id)
  let U : Set (Fin a → Fin n → LL) := {v | ∀ j m, v j m ∈ W}
  have hU : IsOpen U := by
    have hUe : U = ⋂ j, ⋂ m, (fun v : Fin a → Fin n → LL => v j m) ⁻¹' W := by
      ext v; simp [U]
    rw [hUe]
    exact isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun m =>
      hW.preimage ((continuous_apply m).comp (continuous_apply j))
  have key : ∀ v ∈ Y, v ∈ U → ∃ y ∈ Y, v = c • y := by
    intro v hvY hvU
    simp only [U, W, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_range] at hvU
    choose x hx using hvU
    have hxΛ : Lmap x ∈ Λ := LinearMap.mem_range_self _ _
    have hmul : μ • Lmap x = v := by
      funext j m
      show μ • algebraMap O LL (x j m) = v j m
      rw [Algebra.smul_def, hx j m, ← mul_assoc, mul_inv_cancel₀ hμL, one_mul]
    obtain ⟨y, hy, hyeq⟩ := hμ _ hxΛ (hmul ▸ hvY)
    exact ⟨y, hy, hmul ▸ hyeq⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g0
  have hnhds : {g | u g - u g0 ∈ U} ∈ nhds g0 := by
    refine (hU.preimage (hcont.sub continuous_const)).mem_nhds ?_
    intro j m
    refine ⟨0, ?_⟩
    simp
  filter_upwards [hnhds] with g hg
  obtain ⟨y, hy, hyeq⟩ := key _ (Y.sub_mem (hu g) (hu g0)) hg
  have hsplit : (⟨u g, hu g⟩ : Y) = ⟨u g0, hu g0⟩ + c • ⟨y, hy⟩ := by
    ext1
    simp only [Submodule.coe_add, Submodule.coe_smul]
    rw [← hyeq]
    abel
  rw [hsplit, map_add, map_smul, hkill, add_zero]
