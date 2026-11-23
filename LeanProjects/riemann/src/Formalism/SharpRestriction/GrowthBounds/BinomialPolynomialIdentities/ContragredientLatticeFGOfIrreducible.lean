import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.NablaDualLatticeOfIrreducibleLowestGenerated

noncomputable section

open Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

theorem fg_of_integral_on_spanning_duals {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]
    [FiniteDimensional (KK O) V] (M : Submodule O V) (S : Set (Module.Dual (KK O) V))
    (hS : Submodule.span (KK O) S = ⊤) (hint : ∀ φ ∈ S, ∀ x ∈ M, Oval O (φ x)) : M.FG := by
  classical
  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent (KK O) S
  have hfin : Finite b := hbli.finite

  let Φ : V →ₗ[KK O] (b → KK O) := LinearMap.pi fun φ => (φ : Module.Dual (KK O) V)
  have hΦ : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    rw [← Module.forall_dual_apply_eq_zero_iff (KK O) x]
    intro φ
    have hφ : φ ∈ Submodule.span (KK O) b := by rw [hbspan, hS]; exact Submodule.mem_top
    induction hφ using Submodule.span_induction with
    | mem ψ hψ => exact congrFun hx ⟨ψ, hψ⟩
    | zero => rfl
    | add a c _ _ ha hc => rw [LinearMap.add_apply, ha, hc, add_zero]
    | smul r a _ ha => rw [LinearMap.smul_apply, ha, smul_zero]
  let ΦO : V →ₗ[O] (b → KK O) := Φ.restrictScalars O
  have hΦO : Function.Injective ΦO := hΦ
  let L : Submodule O (b → KK O) := LinearMap.range ((Algebra.linearMap O (KK O)).compLeft b)
  have hL : L.FG := Submodule.fg_range _
  have hLN : IsNoetherian O L := isNoetherian_of_fg_of_noetherian L hL
  have hle : M.map ΦO ≤ L := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : ∀ φ : b, ∃ c : O, algebraMap O (KK O) c = (φ : Module.Dual (KK O) V) x :=
      fun φ => hint φ (hbS φ.2) x hx
    choose g hg using h1
    exact ⟨g, funext fun φ => hg φ⟩
  exact Submodule.fg_of_fg_map_injective ΦO hΦO (isNoetherian_submodule.1 hLN _ hle)

theorem contragredientLatticeFG_of_irreducible (hIrr : ContragredientIrreducibleGeneratedByHighestWeight) : DeltaFinitelyGenerated := by
  intro p _ O _ _ _ _ S n V _ _ _ _ E mu v v' hI hv' hnorm
  have hcz : CharZero (KK O) := charZero_of_injective_algebraMap (IsFractionRing.injective O (KK O))
  have hfd : FiniteDimensional (KK O) V := irreducible_highest_weight_findim hI
  have hI' := hIrr p O S n V E mu v v' hI hv'
  refine fg_of_integral_on_spanning_duals (Delta (O := O) E v) {φ | ∃ u ∈ Umon (dualOps E), φ = u v'} hI'.2.2.2 ?_
  rintro _ ⟨u, hu, rfl⟩ x hx
  refine integral_dual_preserved_by_integralMonoid E hI.1.2.2 (Delta (O := O) E v) (delta_integral_enveloping_stable E v) (rationalMonoid_le_integralMonoid _ hu) v' ?_ x hx
  intro y hy
  have : v' y ∈ v' '' (Delta (O := O) E v : Set V) := ⟨y, hy, rfl⟩
  rw [hnorm] at this
  exact this

end Formalism.MainNotions.G.ColumnFamilies
