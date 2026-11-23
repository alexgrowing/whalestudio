import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.KerExistsStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ComponentModelWeightDimensionDictionaryStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.MemSpanCuspReadingsIffComponentsStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsMulNe

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

namespace GlobalTheory.UpperRecord

theorem finrank_le_of_parts {Y ι : Type} {Z : ι → Type} (V : Submodule ℂ (Y → ℂ)) (e : Y ≃ Σ k, Z k)
    (d : ι → ℕ) (C δ : ℕ) (en : Fin δ ≃ Σ k, Fin (d k))
    (hb : ∀ (k : ι) (m : ℕ) (g : Fin m → V),
      LinearIndependent ℂ (fun q (z : Z k) => (g q).1 (e.symm ⟨k, z⟩)) → m ≤ d k * C) :
    Module.finrank ℂ V ≤ δ * C := by
  classical
  let ρ : ∀ k, V →ₗ[ℂ] (Z k → ℂ) := fun k =>
    (LinearMap.funLeft ℂ ℂ fun z : Z k => e.symm ⟨k, z⟩).comp V.subtype
  have hr : ∀ k, Module.rank ℂ (LinearMap.range (ρ k)) ≤ (d k * C : ℕ) := fun k => by
    refine rank_le fun s hs => ?_
    have hs' := (hs.comp s.equivFin.symm s.equivFin.symm.injective).map' (LinearMap.range (ρ k)).subtype
      (Submodule.ker_subtype _)
    choose g hg using fun q : Fin s.card => (s.equivFin.symm q).1.2
    refine hb k s.card g ?_
    have heq : (fun q (z : Z k) => (g q).1 (e.symm ⟨k, z⟩)) = _ := funext hg
    rw [heq]
    exact hs'
  have hfin : ∀ k, Module.Finite ℂ (LinearMap.range (ρ k)) := fun k =>
    Module.rank_lt_aleph0_iff.1 ((hr k).trans_lt (Cardinal.natCast_lt_aleph0))
  have hfr : ∀ k, Module.finrank ℂ (LinearMap.range (ρ k)) ≤ d k * C := fun k =>
    Module.finrank_le_of_rank_le (hr k)
  let s : Finset ι := Finset.univ.image fun q => (en q).1
  have hs : ∀ k, k ∉ s → d k = 0 := fun k hk => by
    by_contra h0
    exact hk (Finset.mem_image.2 ⟨en.symm ⟨k, ⟨0, Nat.pos_of_ne_zero h0⟩⟩, Finset.mem_univ _, by simp⟩)
  let Φ : V →ₗ[ℂ] (∀ k : s, LinearMap.range (ρ k)) := LinearMap.pi fun k => (ρ k).rangeRestrict
  have hΦ : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro g hg
    have hk : ∀ k, ρ k g = 0 := fun k => by
      by_cases hk : k ∈ s
      · exact congrArg Subtype.val (congrFun hg ⟨k, hk⟩)
      · have h0 : Module.finrank ℂ (LinearMap.range (ρ k)) = 0 := by
          have := hfr k
          rw [hs k hk] at this
          omega
        have := Submodule.finrank_eq_zero.1 h0
        exact (Submodule.eq_bot_iff _).1 this _ ⟨g, rfl⟩
    ext y
    have := congrFun (hk (e y).1) (e y).2
    simpa [ρ, LinearMap.funLeft_apply] using this
  have hsum : ∑ k : s, d k ≤ δ := by
    have hinj : Function.Injective fun p : Σ k : s, Fin (d k) => en.symm ⟨p.1.1, p.2⟩ := by
      rintro ⟨⟨k, hk⟩, a⟩ ⟨⟨k', hk'⟩, a'⟩ hp
      have := en.symm.injective hp
      obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 this
      obtain rfl := eq_of_heq h2
      rfl
    simpa using Fintype.card_le_of_injective _ hinj
  calc Module.finrank ℂ V ≤ Module.finrank ℂ (∀ k : s, LinearMap.range (ρ k)) :=
        LinearMap.finrank_le_finrank_of_injective hΦ
    _ = ∑ k : s, Module.finrank ℂ (LinearMap.range (ρ k)) := Module.finrank_pi_fintype ℂ
    _ ≤ ∑ k : s, d k * C := Finset.sum_le_sum fun k _ => hfr k
    _ = (∑ k : s, d k) * C := (Finset.sum_mul _ _ _).symm
    _ ≤ δ * C := Nat.mul_le_mul_right _ hsum

theorem upper : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → Module.finrank ℂ (R.sp (addL wF wL Tn) Set.univ) ≤ δ * (Tn + 2 * WeightFamilies.dimY D j + 6).choose (WeightFamilies.dimY D j) := by
  intro D T h j hj n R e hR N wL wF w Tn c1 A t Fl δ xs en _
  refine finrank_le_of_parts _ e (fun k => (Fl.Fl k).δ) _ δ en fun k m g hg => ?_
  choose f hf hgf using fun q => (GlobalTheory.T.mem_span_cuspReadings_iff_components D T h j hj n R e hR (addL wF wL Tn)).1 (g q).1 (g q).2
  have hw := (GlobalTheory.T.componentModelWeight_dimension_dictionary D T h j hj k).2.2.1 wF wL Tn
  have := GlobalTheory.UpperModel.upper _ _ _ (A.Xa k) (Fl.Fl k) m (fun q => f q k) (fun q => by
    rw [A.hF, A.hL, A.hT, ← hw]
    exact (hf q k).1.1) (fun u hu => by
    funext q
    refine Fintype.linearIndependent_iff.1 hg u ?_ q
    funext z
    have := hu z.1 z.2
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← this]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hgf q, e.apply_symm_apply])
  rwa [A.hT, A.dim] at this

end GlobalTheory.UpperRecord
