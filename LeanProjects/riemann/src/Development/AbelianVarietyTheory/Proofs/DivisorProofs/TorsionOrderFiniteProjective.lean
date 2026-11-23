import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFunctionDenominatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionPrechartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPrechartGroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorFiniteAlgebra
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPrechartPointsSeparateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfLocallyFiniteFreeLocalizationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFiniteSemiabelianOverAlgClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionChartSpreadsToFiniteFreeStatement
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.ord_finite_projective_span : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N : ℕ), N ≠ 0 → Module.Finite R (ord G N K) ∧ Module.Projective R (ord G N K) ∧ ∀ f : Tors G N K → K, ∃ r : R, r ≠ 0 ∧ r • f ∈ ord G N K := by
  intro R K _ _ _ _ _ _ _ _ G _ _ hG N hN
  classical
  have hloc : ∀ q : PrimeSpectrum R, ∃ r : R, r ∉ q.asIdeal ∧ ∃ (F : Type) (_ : AddCommGroup F)
      (_ : Module R F) (_ : Module (Localization.Away r) F) (_ : IsScalarTower R (Localization.Away r) F)
      (_ : Module.Finite (Localization.Away r) F) (_ : Module.Free (Localization.Away r) F)
      (ϕ : ord G N K →ₗ[R] F), IsLocalizedModule (Submonoid.powers r) ϕ := fun q => by
    obtain ⟨c⟩ := GlobalTheory.T.exists_torsion_prechart R K G hG N hN q
    exact ⟨c.r, c.hr, GlobalTheory.T.torsion_chart_spreads_to_finite_free R K G hG N hN q c (GlobalTheory.T.torsion_prechart_group R K G hG N hN q c)⟩
  refine ⟨(GlobalTheory.T.finite_of_locally_finite_free_localizations R (ord G N K) hloc).1, (GlobalTheory.T.finite_of_locally_finite_free_localizations R (ord G N K) hloc).2, ?_⟩
  intro f
  haveI := GlobalTheory.T.torsion_finite_semiabelian_over_alg_closed R K G hG N hN
  haveI : Fintype (Tors G N K) := Fintype.ofFinite _
  obtain ⟨q⟩ : Nonempty (PrimeSpectrum R) := inferInstance
  obtain ⟨c⟩ := GlobalTheory.T.exists_torsion_prechart R K G hG N hN q
  have hgrp := GlobalTheory.T.torsion_prechart_group R K G hG N hN q c
  have hr0 : c.r ≠ 0 := fun h => c.hr (h ▸ q.asIdeal.zero_mem)
  haveI : Finite (c.C →ₐ[R] K) := (GlobalTheory.T.torsion_prechart_points_separate R K G hG N hN q c).1
  choose rs as hrs has using fun s : Tors G N K =>
    GlobalTheory.exists_element_eval_eq_const_mul_of_finite_points R K c.C (fun ψ => f (s * torsMap ψ c.j))
  have hr : (∏ s, rs s) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun s _ => hrs s
  obtain ⟨k, hk⟩ := GlobalTheory.T.torsion_function_denominator R K G hG N hN q c hgrp ((∏ s, rs s) • f) (fun s =>
    ⟨(∏ t ∈ Finset.univ.erase s, rs t) • as s, fun ψ => by
      rw [map_smul, Pi.smul_apply, Algebra.smul_def, Algebra.smul_def, has, ← _root_.mul_assoc, ← map_mul,
        Finset.prod_erase_mul _ _ (Finset.mem_univ s)]⟩)
  exact ⟨c.r ^ k * ∏ s, rs s, mul_ne_zero (pow_ne_zero _ hr0) hr, by rw [mul_smul]; exact hk⟩
