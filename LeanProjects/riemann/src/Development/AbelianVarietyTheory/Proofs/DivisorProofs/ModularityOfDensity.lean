import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitChartAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelWithRatio
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlowupNormalizationCartierStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestPointLiftProperStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyIrreduciblePullbackIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitChartAtInvertiblePStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenImmersionRingFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationUnitsChartsStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel.Modif

theorem isTest_comp (p : ℕ) [Fact p.Prime] {X X' : Scheme.{0}} (π : X' ⟶ X) (Xw : X.Opens)
    (yb' : Sp 𝓞_ℂ_[p] ⟶ X') (h : IsTest p (π ⁻¹ᵁ Xw) yb') : IsTest p Xw (yb' ≫ π) := by
  obtain ⟨⟨T, kO, yT, hT, hk, e⟩, hr⟩ := h
  refine ⟨⟨T, kO, yT ≫ π, hT, hk, by rw [← Category.assoc, e]⟩, ?_⟩
  rintro _ ⟨z, rfl⟩
  have : (spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ yb') z ∈ π ⁻¹ᵁ Xw := hr ⟨z, rfl⟩
  simpa [Scheme.Hom.comp_apply] using this

theorem preimage_basicOpen_p (p : ℕ) {X X' : Scheme.{0}} (π : X' ⟶ X) :
    π ⁻¹ᵁ X.basicOpen (p : Γ(X, ⊤)) = X'.basicOpen (p : Γ(X', ⊤)) := by
  rw [Scheme.preimage_basicOpen, map_natCast]
  rfl

end GlobalTheory.FlatModel.Modif

namespace GlobalTheory.FlatModel

open Modif

theorem modSt_of_densSt : DensSt → ModSt := by
  intro hD F _ _ V p _ hp X s Xw hXi hXn hXp hXf hXw hGI n K hK hC
  have hDVR := (GlobalTheory.isDiscreteValuationRing_and_finite_residueField_of_numberField V (Fact.out : p.Prime).ne_zero hp).1
  have : LocallyOfFiniteType s := by
    obtain ⟨N, i, hi, rfl⟩ := hXp
    have := isProper_str V N
    infer_instance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace X := by
    obtain ⟨N, i, hi, rfl⟩ := hXp
    have := isProper_str V N
    exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str V N)
  choose R _ ξ J _ Q u hξ hx hcl using hC
  haveI : ∀ x, IsOpenImmersion (ξ x) := hξ
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover (fun x => ((ξ x).opensRange : Set X))
    fun x => (ξ x).opensRange.isOpen.mem_nhds (by simpa using hx x)
  choose e he using fun x => GlobalTheory.T.open_immersion_ring_factor X (R x) (ξ x)
  let U : t → X.Opens := fun j => (ξ j.1).opensRange
  let m : t → ℕ := fun j => Nat.card (J j.1) + 1
  let A : ∀ j : t, Fin (m j) → Γ(X, U j) := fun j =>
    Fin.cons ((p : Γ(X, U j)) ^ n) fun i => e j.1 (Q j.1 ((Finite.equivFin (J j.1)).symm i))
  obtain ⟨Jd, hJd, hPr⟩ := GlobalTheory.HTLine.princ_of_finite X p U m A (fun j => isAffineOpen_opensRange (ξ j.1))
    fun j => ⟨n, Ideal.subset_span ⟨0, rfl⟩⟩
  obtain ⟨X'', X', b, ν, hEff, hI', hN', hP', hF', hpr, hiso⟩ := GlobalTheory.T.exists_blowup_normalization_cartier F V p hp X s hXi hXn hXp hXf Jd hJd
  have hT : ∀ yb', IsTest p ((ν ≫ b) ⁻¹ᵁ Xw) yb' → IsTest p Xw (yb' ≫ (ν ≫ b)) := isTest_comp p (ν ≫ b) Xw
  have hle : (ν ≫ b) ⁻¹ᵁ Xw ≤ X'.basicOpen (p : Γ(X', ⊤)) := by
    rw [← preimage_basicOpen_p p (ν ≫ b)]
    exact fun x hx => hXw hx
  have : LocallyOfFiniteType (ν ≫ b ≫ s) := by
    obtain ⟨N, i, hi, e'⟩ := hP'
    have := isProper_str V N
    rw [← e']
    infer_instance
  refine ⟨X', ν ≫ b ≫ s, (ν ≫ b) ⁻¹ᵁ Xw, fun yb' => K (yb' ≫ (ν ≫ b)), hI', hN', hP', hF', hle, ?_,
    fun yb' h => hK _ (hT yb' h), ?_, fun yb h => ?_⟩
  · have := GlobalTheory.T.geometrically_irreducible_pullback_iso V X X' s (ν ≫ b) Xw _ hXw hiso hGI
    simpa only [Category.assoc] using this
  · intro x'
    by_cases hx' : x' ∈ X'.basicOpen (p : Γ(X', ⊤))
    · exact GlobalTheory.T.unit_chart_at_invertible_p p X' _ _ x' hx'
    have hmem : (ν ≫ b) x' ∈ ⋃ x ∈ t, ((ξ x).opensRange : Set X) := by rw [ht]; exact Set.mem_univ _
    simp only [Set.mem_iUnion] at hmem
    obtain ⟨x, hxt, hfx⟩ := hmem
    obtain ⟨V', hV', hxV', hVa, k, hk⟩ := hPr X'' X' b ν hEff x' ⟨x, hxt⟩ hfx
    have heq := he x X' (ν ≫ b) V' hVa hV'
    refine GlobalTheory.T.localization_units_charts p n X X' (ν ≫ b) Xw K (R x) (ξ x) (J x) (Q x) (u x) (hcl x) hT Γ(X', V') hVa.fromSpec
      _ x' inferInstance (by rw [hVa.range_fromSpec]; exact hxV') heq
      (fun hne => hD F V p hp X' (ν ≫ b ≫ s) _ hI' hF' inferInstance hle hne Γ(X', V') hVa.fromSpec inferInstance
        ⟨x', by rw [hVa.range_fromSpec]; exact hxV', hx'⟩) ?_
    have hA0 : ((ν ≫ b).appLE (ξ x).opensRange V' hV').hom ((p : Γ(X, (ξ x).opensRange)) ^ n) =
        (p : Γ(X', V')) ^ n := by rw [map_pow, map_natCast]
    revert hk
    refine Fin.cases (fun hk => Or.inr fun j => ?_) (fun i hk => Or.inl ⟨(Finite.equivFin (J x)).symm i,
      fun j => ?_, ?_⟩) k
    · have := hk ((Finite.equivFin (J x)) j).succ
      simpa [A, U, hA0] using this
    · have := hk ((Finite.equivFin (J x)) j).succ
      simpa [A, U] using this
    · have := hk 0
      simpa [A, U, hA0] using this
  · obtain ⟨yb', h1, h2⟩ := GlobalTheory.T.test_point_lift_proper p X X' (ν ≫ b) hpr Xw _ hXw hiso yb h
    exact ⟨yb', h1, fun κ hκ => by show κ ∈ K (yb' ≫ (ν ≫ b)); rw [h2]; exact hκ⟩

end GlobalTheory.FlatModel
