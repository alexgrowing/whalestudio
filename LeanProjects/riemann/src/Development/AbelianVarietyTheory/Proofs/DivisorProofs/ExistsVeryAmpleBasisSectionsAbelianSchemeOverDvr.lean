import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVeryAmpleBySectionsOfLinearSpanCombinationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisLineBundleSectionsProjectiveOverDvrStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.exists_veryAmpleBy_basis_of_dvr : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ (M : LB G.left) (m : ℕ) (t₀ : Fin (m + 1) → M.Sec), M.IsLB → GlobalTheory.AbLaw.VeryAmpleBy G.hom M t₀ → ∃ (N : ℕ) (t : Fin (N + 1) → M.Sec), GlobalTheory.AbLaw.VeryAmpleBy G.hom M t ∧ ∀ u : M.Sec, ∃! c : Fin (N + 1) → W, u = ∑ j, GlobalTheory.AbLaw.cst G.hom ⊤ (c j) • t j := by
  intro W _ _ _ G _ hG M m t₀ hM hv
  have hflat : Flat G.hom := by
    haveI := hG.smooth
    infer_instance
  obtain ⟨n, t, ht⟩ := GlobalTheory.T.exists_basis_lineBundleSections_projective_over_dvr W G.left G.hom M hflat ⟨M, hM, m, t₀, hv⟩ hM
  have hne : Nonempty G.left := by
    obtain ⟨x⟩ : Nonempty (Sp W) := inferInstance
    exact ⟨(η[G]).left x⟩
  obtain ⟨x⟩ := hne
  obtain ⟨i₀, hi₀⟩ := TopologicalSpace.Opens.mem_iSup.1 (hv.1.ge (Set.mem_univ x))
  have hn : n ≠ 0 := by
    rintro rfl
    obtain ⟨c, hc, -⟩ := ht (t₀ i₀)
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hc
    rw [hc] at hi₀
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hi₀
    have hk' : x ∈ G.left.basicOpen (0 : Γ(G.left, M.U k)) := hk
    rw [Scheme.basicOpen_zero] at hk'
    exact hk'
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  choose a ha using fun i => (ht (t₀ i)).exists
  exact ⟨N, t, GlobalTheory.T.isVeryAmpleBySections_of_linear_span_combination W G.left G.hom M m N t₀ t a hM hv ha, ht⟩
