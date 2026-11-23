import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.RingKrullDimMvPowerSeriesFinField
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsFiniteInjectiveMvPowerSeriesCompatibleSect
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegrallyClosedPowerSeries
open IsLocalRing UpperTheory.V.Alg

private theorem normal_mv (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] (n : ℕ) : IsIntegrallyClosed (MvPowerSeries (Fin n) R) := by
  induction n with
  | zero => exact IsIntegrallyClosed.of_equiv (MvPowerSeries.isEmptyEquiv (Fin 0) R).toRingEquiv.symm
  | succ n ih =>
    have : IsDomain (MvPowerSeries (Fin n) R) := NoZeroDivisors.to_isDomain _
    have := GlobalTheory.PowerSeriesNormal.isIntegrallyClosed_powerSeries (MvPowerSeries (Fin n) R)
    exact IsIntegrallyClosed.of_equiv (MvPowerSeries.finSuccEquiv R n).toRingEquiv.symm

private theorem ht_const (O : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] (n : ℕ) :
    (n : ℕ∞) ≤ (RingHom.ker (MvPowerSeries.constantCoeff : MvPowerSeries (Fin n) O →+* O)).height := by
  let x : MvPowerSeries (Fin n) O →ₐ[O] O :=
    { (MvPowerSeries.constantCoeff : MvPowerSeries (Fin n) O →+* O) with
      commutes' := fun a => by simp [MvPowerSeries.algebraMap_apply] }
  let φ : MvPowerSeries (Fin n) O →ₐ[O] MvPowerSeries (Fin n) (FractionRing O) :=
    { (MvPowerSeries.map (algebraMap O (FractionRing O))) with
      commutes' := fun a => by simp [MvPowerSeries.algebraMap_apply] }
  have hφ : ∀ a, φ a = MvPowerSeries.map (algebraMap O (FractionRing O)) a := fun _ => rfl
  refine UpperTheory.ringKrullDim_mvPowerSeries_fin_field O (FractionRing O) (MvPowerSeries (Fin n) O) x n φ MvPowerSeries.X 1
    one_ne_zero (fun a => ?_) (fun i => ?_)
  · rw [hφ, MvPowerSeries.constantCoeff_map]; rfl
  · rw [hφ]; simp

theorem UpperTheory.ringKrullDim_eq_height_ker_section_add_one :
    ∀ (O S : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CommRing S] [IsDomain S] [Algebra O S] [IsCO O S] (x : S →ₐ[O] O), ringKrullDim S = ((RingHom.ker x).height : WithBot ℕ∞) + 1 := by
  intro O S _ _ _ _ _ _ _ hS x
  have hn : IsNoetherianRing S := hS.toIsNoetherian
  have hl : IsLocalHom (algebraMap O S) := IsCO.isLocalHom
  obtain ⟨d, F, hinj, hfin, hd, hF⟩ := UpperTheory.exists_finite_injective_mvPowerSeries_compatible_section O S x
  haveI : (RingHom.ker x).IsPrime := RingHom.ker_isPrime _
  refine le_antisymm ?_ ?_
  · let A := MvPowerSeries (Fin d) O
    letI : Algebra A S := F.toRingHom.toAlgebra
    haveI : Module.Finite A S := hfin
    haveI : FaithfulSMul A S := (faithfulSMul_iff_algebraMap_injective A S).2 hinj
    haveI : IsIntegrallyClosed A := normal_mv O d
    let p : Ideal A := RingHom.ker (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) O →+* O)
    haveI : p.IsPrime := RingHom.ker_isPrime _
    haveI : (RingHom.ker x).LiesOver p := ⟨by
      ext a
      rw [Ideal.under_def, Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker, ← hF]
      rfl⟩
    have h1 := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p (RingHom.ker x)
    have h2 : (d : ℕ∞) ≤ (RingHom.ker x).height := by
      rw [h1]; exact (ht_const O d).trans le_self_add
    rw [hd]
    have h3 : ((d + 1 : ℕ) : ℕ∞) ≤ (RingHom.ker x).height + 1 := by
      push_cast; gcongr
    exact_mod_cast h3
  · obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
    have hlt : RingHom.ker x < maximalIdeal S := by
      refine lt_of_le_of_ne (le_maximalIdeal Ideal.IsPrime.ne_top') fun h => ?_
      have h1 : algebraMap O S π ∈ maximalIdeal S := fun h => hπ.not_isUnit (IsLocalHom.map_nonunit π h)
      rw [← h, RingHom.mem_ker, AlgHom.commutes] at h1
      exact hπ.ne_zero h1
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    exact_mod_cast Ideal.height_add_one_le_of_lt_of_isPrime hlt
