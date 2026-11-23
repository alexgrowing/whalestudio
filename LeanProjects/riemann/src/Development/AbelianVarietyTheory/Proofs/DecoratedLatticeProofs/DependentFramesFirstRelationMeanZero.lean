import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransvectionLemmaOfWittCoreDescentStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagSubgroupsClosedNormalCocompactStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralTsumNormalEigenfunctionsEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedThetaSeriesTermsLawsUnipotentRationalStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTermSeriesSummableModerateGrowthUniformStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DependentFrameFirstColumnRelationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalFlagUnipotentIsotropicBlockUnitriangularStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GramMatrixOfColumnsUnitriangularConjEqStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransvectionTrivialAfterFlagUnipotentFixingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf.DepFrames

theorem gramQ_mul {D : D7} (W : HSp D) {ρ : ℕ} (x : Matrix (Fin W.rank) (Fin ρ) D.host.E) (u : Matrix (Fin ρ) (Fin ρ) D.host.E) :
    gramQ W (x * u) = uᴴ * gramQ W x * u := by
  simp only [gramQ, conjTranspose_mul, Matrix.mul_assoc]

theorem dep_frames_mean_zero : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (Th : GA D V → ℂ), IsBase W x₀ → IsTh ψ d W x₀ Th → ∀ Ψ : WO V W → ℂ, IsThetaFunO ψ V W Ψ → ∀ j : Fin ρ, ∫ n in vN.𝓝, ∑' x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x = gramQ W x₀ ∧ (∀ a : Fin ρ → D.host.E, (∀ i, j ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧ ∃ a : Fin ρ → D.host.E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0}, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1 ∂vN.ν = 0 := by
  intro D hDesc ψ V V₀ W ρ d χV χW om om' hw hw' vS vN x₀ Th hB hTh Ψ hΨ j
  classical
  have : Countable D.host.E := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableE
  have : Countable (Matrix (Fin W.rank) (Fin ρ) D.host.E) :=
    inferInstanceAs (Countable (Fin W.rank → Fin ρ → D.host.E))
  obtain ⟨hLC, hSC, -, -, -, hDisc, hCnt⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have h56 := GlobalTheory.T.flag_subgroups_closed_normal_cocompact' D V V₀ ρ d
  haveI : LocallyCompactSpace (flagN d) := h56.1.locallyCompactSpace
  haveI : SecondCountableTopology (flagN d) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : vN.ν.IsHaarMeasure := vN.unit.1
  obtain ⟨hle, hNcl, hNnorm, K, hK, hcov⟩ := h56.2 (Nfix d j) (Or.inr (Or.inr ⟨j, rfl⟩))
  have hT := GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hw hw' vS
  have hcont : ∀ x, Continuous fun n : flagN d => term ψ d W vS (om (n.1, 1) Ψ) x := fun x =>
    ((hT Ψ hΨ).2.2.2.1 x).comp (continuous_subtype_val.prodMk continuous_const)
  obtain ⟨C, A, hC⟩ := GlobalTheory.T.thetaTermSeries_summable_moderateGrowth_uniform D ψ V V₀ W ρ d χV χW om om' hw hw' vS Ψ hΨ
  obtain ⟨K0, hK0, hcov0⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D V ρ d.e (isIsoSub_e d)).1
  obtain ⟨Mb, hMb⟩ := hK0.exists_bound_of_continuousOn (f := fun n : flagN d => Th n.1) hTh.cont.continuousOn
  have hThb : ∀ n : flagN d, ‖Th n.1‖ ≤ Mb := by
    intro n
    obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov0 n
    have hγ' : (γ : GA D V) ∈ GQ V := Subgroup.mem_subgroupOf.1 hγ
    have : Th ((γ * k : flagN d) : GA D V) = Th k.1 := hTh.left γ.1 hγ' γ.2 k.1 k.2
    rw [this]
    exact hMb k hk
  have hbdS : ∀ (S : Set (Matrix (Fin W.rank) (Fin ρ) D.host.E)) (n : flagN d),
      ∑' x : S, ‖Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1‖ₑ ≤
        ((Mb.toNNReal * (C * (height V 1 * quotHeight W 1) ^ A).toNNReal : NNReal) : ENNReal) := by
    intro S n
    have h1 : ∑' x, ‖term ψ d W vS (om (n.1, 1) Ψ) x‖ₑ ≤ ENNReal.ofReal (C * (height V 1 * quotHeight W 1) ^ A) := by
      have := hC 1 1 n.1 n.2
      rwa [mul_one] at this
    simp_rw [enorm_mul]
    rw [ENNReal.tsum_mul_left, ENNReal.coe_mul]
    refine mul_le_mul' ?_ ((ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _).trans h1)
    rw [← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (hThb n)
  let Pj : Matrix (Fin W.rank) (Fin ρ) D.host.E → Prop := fun x => gramQ W x = gramQ W x₀ ∧
    (∀ a : Fin ρ → D.host.E, (∀ i, j ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧
    ∃ a : Fin ρ → D.host.E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0
  have huniq : ∀ x : Matrix (Fin W.rank) (Fin ρ) D.host.E,
      (∀ a : Fin ρ → D.host.E, (∀ i, j ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) →
      ∀ a a' : Fin ρ → D.host.E, a j = 1 → (∀ i, j < i → a i = 0) → x *ᵥ a = 0 →
        a' j = 1 → (∀ i, j < i → a' i = 0) → x *ᵥ a' = 0 → a = a' := by
    intro x hind a a' ha1 ha2 ha3 hb1 hb2 hb3
    refine sub_eq_zero.1 (hind (a - a') (fun i hi => ?_) (by rw [Matrix.mulVec_sub, ha3, hb3, sub_self]))
    rcases hi.lt_or_eq with h | h
    · simp [ha2 i h, hb2 i h]
    · subst h; simp [ha1, hb1]
  have hPu : ∀ u u' : Matrix (Fin ρ) (Fin ρ) D.host.E, u * u' = 1 → u' * u = 1 → (∀ i, u i i = 1) →
      (∀ i k, k < i → u i k = 0) → ∀ x, Pj x ↔ Pj (x * u) := by
    intro u u' huu' hu'u hdiag htri x
    have hG := GlobalTheory.T.gramMatrixOfColumns_unitriangular_conj_eq D W ρ x₀ hB u hdiag htri
    refine and_congr ⟨fun h => by rw [gramQ_mul, h, hG], fun h => ?_⟩ ((GlobalTheory.T.dependent_frame_first_column_relation D.host.E W.rank ρ x).2.2 j u hdiag htri)
    rw [gramQ_mul, ← hG] at h
    have h' := congrArg (fun M => u'ᴴ * M * u') h
    have e1 : ∀ M : Matrix (Fin ρ) (Fin ρ) D.host.E, u'ᴴ * (uᴴ * M * u) * u' = M := by
      intro M
      rw [show u'ᴴ * (uᴴ * M * u) * u' = (u * u')ᴴ * M * (u * u') by
        simp only [conjTranspose_mul, Matrix.mul_assoc]]
      rw [huu', conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    rwa [e1, e1] at h'

  have key : ∀ γ : flagN d, γ.1 ∈ GQ V → ∀ u : Matrix (Fin ρ) (Fin ρ) D.host.E, (rat u : Mx D ρ ρ) = blockX d γ.1 →
      ∀ (n : flagN d) (x : Matrix (Fin W.rank) (Fin ρ) D.host.E),
        Th (γ * n).1 * term ψ d W vS (om ((γ * n).1, 1) Ψ) x = Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) (x * u) := by
    intro γ hγ u hu n x
    have hom : om ((γ * n).1, 1) Ψ = om (γ.1, 1) (om (n.1, 1) Ψ) := by
      rw [show (((γ * n : flagN d) : GA D V), (1 : GA D W)) = (γ.1, 1) * (n.1, 1) by
        rw [Prod.mk_mul_mk, one_mul]; rfl, map_mul]
      rfl
    rw [hom, (hT _ (hw.om_pres _ _ hΨ)).2.1 γ.1 hγ γ.2 x (x * u) (by rw [rat_mul, hu]),
      show ((γ * n : flagN d) : GA D V) = γ.1 * n.1 from rfl, hTh.left γ.1 hγ γ.2 n.1 n.2]
  have hfixv : ∀ u : Matrix (Fin ρ) (Fin ρ) D.host.E, (∀ i k, k ≤ j → u i k = if i = k then 1 else 0) →
      ∀ c : Fin ρ → D.host.E, (∀ i, j < i → c i = 0) → u *ᵥ c = c := by
    intro u hu c hc
    funext i
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_congr rfl (g := fun k => if i = k then c k else 0) fun k _ => ?_, Finset.sum_ite_eq]
    · simp
    · rcases le_or_gt k j with h | h
      · rw [hu i k h]; split_ifs <;> simp
      · rw [hc k h]; simp
  refine GlobalTheory.T.integral_tsum_normal_eigenfunctions_eq_zero (flagN d) vN.ν ((GQ V).subgroupOf (flagN d)) ((Nfix d j).subgroupOf (flagN d)) ?_ ?_ hNnorm
    (hNcl.preimage continuous_subtype_val) ?_ vN.𝓝 vN.unit.2.1 (by rw [vN.unit.2.2]; exact ENNReal.one_ne_top)
    {x // Pj x} (Fin ρ → D.host.E) (fun x => Classical.choose x.2.2.2)
    (fun x n => Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1) (fun x => (hTh.cont.mul (hcont x.1)).measurable)
    ⟨_, fun n => hbdS {x | Pj x} n⟩ ?_ ?_ ?_
  · exact Function.Injective.countable (f := fun x : ((GQ V).subgroupOf (flagN d)) =>
      (⟨x.1.1, Subgroup.mem_subgroupOf.1 x.2⟩ : GQ V))
      (fun a b h => Subtype.ext (Subtype.ext (congrArg (fun y : GQ V => y.1) h)))
  · exact DiscreteTopology.of_continuous_injective (f := fun x : ((GQ V).subgroupOf (flagN d)) =>
      (⟨x.1.1, Subgroup.mem_subgroupOf.1 x.2⟩ : GQ V))
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
      (fun a b h => Subtype.ext (Subtype.ext (congrArg (fun y : GQ V => y.1) h)))
  · refine ⟨(fun m : Nfix d j => (⟨⟨m.1, hle m.2⟩, m.2⟩ : (Nfix d j).subgroupOf (flagN d))) '' K,
      hK.image ((continuous_subtype_val.subtype_mk _).subtype_mk _), fun m => ?_⟩
    obtain ⟨γ, hγ, k, hk, e⟩ := hcov ⟨m.1.1, Subgroup.mem_subgroupOf.1 m.2⟩
    refine ⟨⟨⟨γ.1, hle γ.2⟩, γ.2⟩, ?_, ⟨⟨k.1, hle k.2⟩, k.2⟩, ⟨k, hk, rfl⟩, ?_⟩
    · rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]; exact Subgroup.mem_subgroupOf.1 hγ
    · have e2 : m.1.1 = γ.1 * k.1 := congrArg Subtype.val e
      exact Subtype.ext (Subtype.ext e2)
  · intro γ hγ n
    have hγ' : γ.1 ∈ GQ V := Subgroup.mem_subgroupOf.1 hγ
    obtain ⟨u, u', hu, huu', hu'u, hdiag, htri, -⟩ := GlobalTheory.T.rational_flagUnipotent_isotropicBlock_unitriangular D V V₀ ρ d γ.1 hγ' γ.2
    let e : {x // Pj x} ≃ {x // Pj x} :=
      { toFun := fun x => ⟨x.1 * u, (hPu u u' huu' hu'u hdiag htri x.1).1 x.2⟩
        invFun := fun x => ⟨x.1 * u', (hPu u u' huu' hu'u hdiag htri (x.1 * u')).2
          (by rw [Matrix.mul_assoc, hu'u, Matrix.mul_one]; exact x.2)⟩
        left_inv := fun x => Subtype.ext (by simp only [Matrix.mul_assoc, huu', Matrix.mul_one])
        right_inv := fun x => Subtype.ext (by simp only [Matrix.mul_assoc, hu'u, Matrix.mul_one]) }
    show ∑' i : {x // Pj x}, Th (γ * n).1 * term ψ d W vS (om ((γ * n).1, 1) Ψ) i.1 =
      ∑' i : {x // Pj x}, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) i.1
    rw [← e.tsum_eq (fun i => Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) i.1)]
    exact tsum_congr fun i => key γ hγ' u hu n i.1
  · intro c γ hγ hγM n
    have hγ' : γ.1 ∈ GQ V := Subgroup.mem_subgroupOf.1 hγ
    obtain ⟨u, u', hu, huu', hu'u, hdiag, htri, hfix⟩ := GlobalTheory.T.rational_flagUnipotent_isotropicBlock_unitriangular D V V₀ ρ d γ.1 hγ' γ.2
    have hfu := hfixv u (hfix j (Subgroup.mem_subgroupOf.1 hγM))
    let e : {x // Pj x} ≃ {x // Pj x} :=
      { toFun := fun x => ⟨x.1 * u, (hPu u u' huu' hu'u hdiag htri x.1).1 x.2⟩
        invFun := fun x => ⟨x.1 * u', (hPu u u' huu' hu'u hdiag htri (x.1 * u')).2
          (by rw [Matrix.mul_assoc, hu'u, Matrix.mul_one]; exact x.2)⟩
        left_inv := fun x => Subtype.ext (by simp only [Matrix.mul_assoc, huu', Matrix.mul_one])
        right_inv := fun x => Subtype.ext (by simp only [Matrix.mul_assoc, hu'u, Matrix.mul_one]) }
    have hκ : ∀ x : {x // Pj x}, Classical.choose (e x).2.2.2 = Classical.choose x.2.2.2 := by
      intro x
      have s1 := Classical.choose_spec (e x).2.2.2
      have s0 := Classical.choose_spec x.2.2.2
      exact huniq _ (e x).2.2.1 _ _ s1.1 s1.2.1 s1.2.2 s0.1 s0.2.1
        (by show (x.1 * u) *ᵥ _ = 0; rw [← Matrix.mulVec_mulVec, hfu _ s0.2.1, s0.2.2])
    let e' := e.subtypeEquiv (p := fun x => Classical.choose x.2.2.2 = c) (q := fun x => Classical.choose x.2.2.2 = c)
      (fun x => by rw [hκ x])
    show ∑' i : {i : {x // Pj x} // Classical.choose i.2.2.2 = c}, Th (γ * n).1 * term ψ d W vS (om ((γ * n).1, 1) Ψ) i.1.1 =
      ∑' i : {i : {x // Pj x} // Classical.choose i.2.2.2 = c}, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) i.1.1
    rw [← e'.tsum_eq (fun i => Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) i.1.1)]
    exact tsum_congr fun i => key γ hγ' u hu n i.1.1
  · intro c
    by_cases hc : ∃ x : {x // Pj x}, Classical.choose x.2.2.2 = c
    · obtain ⟨x, hx⟩ := hc
      have s0 := Classical.choose_spec x.2.2.2
      rw [hx] at s0
      have hg : gramQ W x₀ *ᵥ c = 0 := by
        rw [← x.2.1, gramQ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, s0.2.2, Matrix.mulVec_zero,
          Matrix.mulVec_zero]
      obtain ⟨v, u, a, hform, htr, huN, ha, hTu⟩ := hTh.dep j c s0.1 s0.2.1 hg
      refine ⟨⟨u, hle huN⟩, huN, a, ha, fun y hy m hm n => ?_⟩
      have sy := Classical.choose_spec y.2.2.2
      rw [hy] at sy
      have hm' : m.1 ∈ Nfix d j := Subgroup.mem_subgroupOf.1 hm
      show Th (m.1 * u * n.1) * term ψ d W vS (om (m.1 * u * n.1, 1) Ψ) y.1 =
        a * (Th (m.1 * n.1) * term ψ d W vS (om (m.1 * n.1, 1) Ψ) y.1)
      rw [hTu m.1 m.2 n.1 n.2, GlobalTheory.T.transvection_trivial_after_flagUnipotentFixing D hDesc ψ V V₀ W ρ d χV χW om hw vS Ψ hΨ j c s0.2.1 v u hform htr y.1 sy.2.2
        m.1 hm' n.1, mul_assoc]
    · push_neg at hc
      exact ⟨1, one_mem _, 0, zero_ne_one, fun x hx => absurd hx (hc x)⟩

end GlobalTheory.Unf.DepFrames
