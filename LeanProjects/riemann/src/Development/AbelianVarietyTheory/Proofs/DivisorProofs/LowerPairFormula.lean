import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFormsCommensurableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodIntegralFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodIntegralSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodConjugateIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAuxiliarySetReductionGood
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsChernExistsUniqueAndIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodProductIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodIntegralThird
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Div.LowerPairFormula

theorem lower_pair_formula : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (R : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] [DecidableEq (E →+* K)] (H : Type) [AddCommGroup H]
    [Module R H] (I : Type) (φ : I → E →+* K) (ρ : orderC c →+* Module.End R H) (Fil : Submodule R H)
    (B : LinearMap.BilinForm R H) (e f : I → H) (N : Module.End K (K ⊗[R] H)) (i : I),
    GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsCMLattice φ ρ Fil B → DirectSum.IsInternal (fun σ : E →+* K ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ) →
    (∀ σ σ' : E →+* K, σ' ≠ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar σ → ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ,
      ∀ y ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ', B.baseChange K x y = 0) →
    GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsGens φ ρ e f → GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsLower ρ (φ i) (e i) (f i) N →
    B (e i) (f i) ≠ 0 ∧ ∀ w, N w = (B.baseChange K w (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK K H (f i)) / algebraMap R K (B (e i) (f i))) •
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK K H (f i) := by
  intro E _ _ _ c R _ _ _ K _ _ _ _ H _ _ I φ ρ Fil B e f N i hL hdir horth hG hN
  obtain ⟨hfree, -, -, hlines, -, -, hbij, -, -⟩ := hL
  have hBK : ∀ u v : H, B.baseChange K (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK K H u) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK K H v) = algebraMap R K (B u v) := by
    intro u v
    simp [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK, LinearMap.BilinForm.baseChange_tmul, Algebra.algebraMap_eq_smul_one]
  have he_mem : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK K H (e i) ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ (φ i) := by
    have hm : e i ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (K := K) ρ (φ i) := by rw [(hG i).1]; exact Submodule.mem_span_singleton_self _
    exact hm
  have hf_mem : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK K H (f i) ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i)) := by
    have hm : f i ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (K := K) ρ (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i)) := by
      rw [(hG i).2]; exact Submodule.mem_span_singleton_self _
    exact hm
  have hei : e i ≠ 0 := by
    intro h0
    obtain ⟨g, hg0, hg⟩ := GlobalTheory.EigenLattice.exists_ne_mem ρ (φ i) (hlines (φ i))
    rw [(hG i).1, h0, Submodule.span_singleton_eq_bot.2 rfl, Submodule.mem_bot] at hg
    exact hg0 hg
  have he0 : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK K H (e i) ≠ 0 := GlobalTheory.Div.eigen_line_bilinear.inK_ne_zero hfree hei
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hmem : ∀ z : K ⊗[R] H, z ∈ ⨆ σ : E →+* K, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ := fun z => by
    rw [hdir.submodule_iSup_eq_top]; exact Submodule.mem_top
  have hb : B (e i) (f i) ≠ 0 := by
    intro hb0
    have hBe : B (e i) ≠ 0 := fun h => hei (hbij.1 (by rw [h, map_zero]))
    obtain ⟨u, hu⟩ : ∃ u, B (e i) u ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hBe (LinearMap.ext hcon)
    have hall : ∀ v : K ⊗[R] H, B.baseChange K (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK K H (e i)) v = 0 := by
      intro v
      refine Submodule.iSup_induction (fun σ : E →+* K => GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ)
        (motive := fun v => B.baseChange K (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK K H (e i)) v = 0) (hmem v) ?_ (by simp) ?_
      · intro σ' v hv
        by_cases hσ : σ' = GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i)
        · subst hσ
          obtain ⟨k, rfl⟩ := GlobalTheory.Div.eigen_line_bilinear.eq_smul_of_line (hlines _) hf_mem
            (GlobalTheory.Div.eigen_line_bilinear.inK_ne_zero hfree (fun h0 => by
              obtain ⟨g, hg0, hg⟩ := GlobalTheory.EigenLattice.exists_ne_mem ρ (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i)) (hlines _)
              rw [(hG i).2, h0, Submodule.span_singleton_eq_bot.2 rfl, Submodule.mem_bot] at hg
              exact hg0 hg)) hv
          rw [map_smul, hBK, hb0, map_zero, smul_zero]
        · exact horth (φ i) σ' hσ _ he_mem v hv
      · intro x y hx hy
        rw [map_add, hx, hy, add_zero]
    have := hall (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK K H u)
    rw [hBK] at this
    exact hu (hinj (by rw [this, map_zero]))
  have hb' : algebraMap R K (B (e i) (f i)) ≠ 0 := fun h => hb (hinj (by rw [h, map_zero]))
  refine ⟨hb, fun w => ?_⟩
  refine Submodule.iSup_induction (fun σ : E →+* K => GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ)
    (motive := fun w => N w = (B.baseChange K w (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK K H (f i)) / algebraMap R K (B (e i) (f i))) •
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK K H (f i)) (hmem w) ?_ (by simp) ?_
  · intro σ w hw
    by_cases hσ : σ = φ i
    · subst hσ
      obtain ⟨k, rfl⟩ := GlobalTheory.Div.eigen_line_bilinear.eq_smul_of_line (hlines _) he_mem he0 hw
      rw [map_smul, hN.1, map_smul, LinearMap.smul_apply, hBK, smul_eq_mul, mul_div_assoc, div_self hb', _root_.mul_one]
    · have hne : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i) ≠ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar σ := by
        intro h
        apply hσ
        have := congrArg GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar h
        rw [GlobalTheory.Div.eigen_line_bilinear.bar_bar, GlobalTheory.Div.eigen_line_bilinear.bar_bar] at this
        exact this.symm
      rw [hN.2 σ hσ w hw, horth σ (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i)) hne w hw _ hf_mem, zero_div, zero_smul]
  · intro x y hx hy
    rw [map_add, hx, hy, map_add, LinearMap.add_apply, add_div, add_smul]

end GlobalTheory.Div.LowerPairFormula
