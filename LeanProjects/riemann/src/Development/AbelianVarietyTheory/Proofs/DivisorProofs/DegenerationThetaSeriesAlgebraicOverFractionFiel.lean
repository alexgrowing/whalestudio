import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNumDHomDegenerationValuesFieldExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralDegenerationValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasSumOfAdicSumUnitBallExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesTermsTorsionPointFiniteAdicCombinatioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdicSumFieldOfCoeffTendstoZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesTermsRescaleByGeneratorMultipleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.ThetaSer

theorem hasSum_map_of_sumF {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] {I : Ideal R} {F C : Type} [Field F]
    [Algebra (FractionRing R) F] [NormedField C] [IsUltrametricDist C] [Algebra (FractionRing R) C]
    (hC : GlobalTheory.Ex.CExt R I C) (em : F →ₐ[FractionRing R] C) {Ix : Type} {x : Ix → F} {s : F}
    (h : GlobalTheory.UT.SumF I F x s) : HasSum (fun i => em (x i)) (em s) := by
  letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))
  letI : Module R C := Module.compHom C (algebraMap R (FractionRing R))
  let f : F →ₗ[R] C :=
    { toFun := em
      map_add' := em.map_add
      map_smul' := fun r y => by
        change em ((algebraMap R (FractionRing R) r) • y) = (algebraMap R (FractionRing R) r) • em y
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, AlgHom.commutes] }
  refine GlobalTheory.Ex.AdicNormSum.main R I C hC Ix _ _ ?_
  obtain ⟨M, hfg, hs, hx, hn⟩ := h
  refine ⟨M.map f, hfg.map f, Submodule.mem_map_of_mem hs, fun i => Submodule.mem_map_of_mem (hx i), fun n => ?_⟩
  obtain ⟨S, hS⟩ := hn n
  refine ⟨S, fun T hT => ?_⟩
  have := Submodule.mem_map_of_mem (f := f) (hS T hT)
  rw [Submodule.map_smul''] at this
  simpa [f, map_sub, map_sum] using this

theorem theta_series_algebraic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (m : ℕ), Odd m → IsUnit (m : R) → ∀ (Ix : Type) (p : Ix → QkPt D.toPre (Kb R) (m ^ 2)), ∃ v : Ix → Kb R, ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [Algebra (FractionRing R) C], GlobalTheory.Ex.CExt R (maximalIdeal R) C → ∀ (em : Kb R →ₐ[FractionRing R] C) (N : GlobalTheory.Ex.NumD C) (nu : GlobalTheory.Ex.NumOf D.toPre C N) (p₁ : Ix → QkPt D.toPre C (m ^ 2)) (q : Ix → N.QT (m ^ 2)), (∀ i, QkExt em.toRingHom (p i) (p₁ i)) → (∀ i, nu.QPt (p₁ i) (q i)) → ∃ s : Cˣ, ∀ i, em (v i) = s * N.tx m (q i) := by
  intro R _ _ _ hB D m hm hu Ix p
  obtain ⟨⟨hN, -, -, hAC⟩, -⟩ := id hB
  haveI := hN
  have hL : Laws := GlobalTheory.lawsAndExpansions.1.1
  obtain ⟨N₀, ν₀, -⟩ := GlobalTheory.ValuesExist.exists_integral_values hL R D.toPre D.psi_even D.tau_bimult (Kb R) ⊤
    (fun _ => trivial)
  have hq₀ : ∀ i, ∃ q₀ : N₀.QT (m ^ 2), ν₀.QPt (p i) q₀ := fun i =>
    (((GlobalTheory.Ex.GtValues.points_correspond R D.toPre D.psi_even D.tau_bimult (Kb R) N₀ ν₀).2.2.2.2 (m ^ 2)).1 (p i)).exists
  choose q₀ hq₀ using hq₀
  have hv : ∀ i, ∃ v, GlobalTheory.UT.SumF (maximalIdeal R) (Kb R) (N₀.txT m (q₀ i)) v := fun i => by
    obtain ⟨Jx, _, g, c, hc, hfin⟩ := GlobalTheory.T.thetaSeriesTerms_torsionPoint_finite_adic_combination R hB D N₀ ν₀ m hm hu (p i) (q₀ i) (hq₀ i)
    obtain ⟨s, hs⟩ := GlobalTheory.T.exists_adic_sum_field_of_coeff_tendsto_zero R hAC (Kb R) Jx g N₀.X c hfin
    refine ⟨s, ?_⟩
    rwa [show N₀.txT m (q₀ i) = _ from funext hc]
  choose v hv using hv
  refine ⟨v, fun C _ _ _ _ _ hC em N nu p₁ q hp hq => ?_⟩
  obtain ⟨r, hr⟩ := ν₀.th_gen nu.th
  obtain ⟨N', ν', e, hth, htx⟩ := GlobalTheory.T.thetaSeries_terms_rescale_by_generator_multiple R D.toPre D.psi_even D.tau_bimult C N nu ν₀.th r hr ν₀.th_gen
  obtain ⟨I, hlam, -, hI⟩ := GlobalTheory.GaugeHom.exists_hom R D.toPre (Kb R) C em.toRingHom
    (RingHom.ext fun x => em.commutes x) N₀ N' ν₀ ν' hth
  have hq' : ∀ i, ∃ q' : N'.QT (m ^ 2), ν'.QPt (p₁ i) q' := fun i =>
    (((GlobalTheory.Ex.GtValues.points_correspond R D.toPre D.psi_even D.tau_bimult C N' ν').2.2.2.2 (m ^ 2)).1 (p₁ i)).exists
  choose q' hq' using hq'
  let a : C := algebraMap (FractionRing R) C (algebraMap R _ r)
  have hterm : ∀ i χ, N.txT m (q i) (e (I.e χ)) = a * em (N₀.txT m (q₀ i) χ) := fun i χ => by
    obtain ⟨h1, h2⟩ := hI (m ^ 2) (p i) (p₁ i) (q₀ i) (q' i) (hp i) (hq₀ i) (hq' i)
    rw [htx m (p₁ i) (q i) (q' i) (hq i) (hq' i), I.txT_eq hm (q₀ i) (q' i) h1 h2 χ, hlam, Units.val_one, _root_.one_mul]
    rfl
  have htx' : ∀ i, N.tx m (q i) = a * em (v i) := fun i => by
    have hs := (hasSum_map_of_sumF hC em (hv i)).mul_left a
    simp only [← hterm] at hs
    unfold GlobalTheory.Ex.NumD.tx
    rw [← (I.e.trans e).toEquiv.tsum_eq]
    exact hs.tsum_eq
  by_cases hr0 : r = 0
  · subst hr0
    have hz : ∀ j, nu.th.f j = 0 := fun j => by rw [hr j]; simp [scal]
    obtain ⟨r', hr'⟩ := nu.th_gen ν₀.th
    have hz₀ : ∀ j, ν₀.th.f j = 0 := fun j => by rw [hr' j, hz j, mul_zero]
    obtain ⟨N'', ν'', e'', -, htx''⟩ := GlobalTheory.T.thetaSeries_terms_rescale_by_generator_multiple R D.toPre D.psi_even D.tau_bimult (Kb R) N₀ ν₀ ν₀.th 0
      (fun j => by rw [hz₀ j, mul_zero]) ν₀.th_gen
    have h0 : ∀ i, em (v i) = 0 := fun i => by
      obtain ⟨q'', hq''⟩ := (((GlobalTheory.Ex.GtValues.points_correspond R D.toPre D.psi_even D.tau_bimult (Kb R) N'' ν'').2.2.2.2
        (m ^ 2)).1 (p i)).exists
      have hs := hasSum_map_of_sumF hC em (hv i)
      have e0 : (fun χ => em (N₀.txT m (q₀ i) χ)) = fun _ => 0 := funext fun χ => by
        rw [← e''.apply_symm_apply χ, htx'' m (p i) (q₀ i) q'' (hq₀ i) hq''] ; simp
      rw [e0] at hs
      exact hs.unique hasSum_zero
    refine ⟨1, fun i => ?_⟩
    rw [h0 i, htx' i, h0 i, mul_zero, mul_zero]
  · have ha : a ≠ 0 := by
      intro h
      apply hr0
      have h' : algebraMap R (FractionRing R) r = 0 := (algebraMap (FractionRing R) C).injective (by rw [map_zero]; exact h)
      exact (IsFractionRing.injective R (FractionRing R)) (by rw [h', map_zero])
    refine ⟨(Units.mk0 a ha)⁻¹, fun i => ?_⟩
    rw [htx' i, Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel_left₀ ha]

end GlobalTheory.Mum.ThetaSer
