import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawLevelPrimeLawAllTuplesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawUnfoldedSupportAndValueAtFixedLevelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawPlaceLawsGiveFiniteIntegralLawsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawSupportOffLevelOfLatticeShapeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawUnfoldedVacuaOfShapeProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiBesselGroupsClosedHaarProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSawAll

variable {D : D7}

theorem real_pos_of_open_compact {X : Type} [TopologicalSpace X] [MeasurableSpace X] (μ : Measure X) [μ.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts μ] {S : Set X} (ho : IsOpen S) (hc : IsCompact S) (hn : S.Nonempty) : 0 < μ.real S :=
  ENNReal.toReal_pos (ho.measure_ne_zero μ hn) hc.measure_lt_top.ne

theorem level_open_compact (V : HSp D) (L : Lat V) (hL : IsSelfDualC V L) (gP : Finset (Pl D)) (JG : Subgroup (GA D V))
    (hJ : JG ≤ grpAt V (· ∈ gP)) (hJc : IsCompact (JG : Set (GA D V)))
    (hJo : IsOpen (((JG.subgroupOf (grpAt V (· ∈ gP))) : Subgroup _) : Set (grpAt V (· ∈ gP)))) :
    IsOpen {g : GfC V | ∃ κ, InK V L (· ∉ gP) κ ∧ ∃ k ∈ JG, g.1 = κ * k} ∧
      IsCompact {g : GfC V | ∃ κ, InK V L (· ∉ gP) κ ∧ ∃ k ∈ JG, g.1 = κ * k} ∧
      (1 : GfC V) ∈ {g : GfC V | ∃ κ, InK V L (· ∉ gP) κ ∧ ∃ k ∈ JG, g.1 = κ * k} := by
  obtain ⟨-, -, -, -, hcomm, ⟨e, he⟩, -, -, hK, -⟩ := GlobalTheory.FinPl.SetCut.grp_split D V gP
  obtain ⟨⟨K₁, hK₁, hK₁c, hK₁o⟩, -⟩ := hK L hL (· ∉ gP)
  have hS : {g : GfC V | ∃ κ, InK V L (· ∉ gP) κ ∧ ∃ k ∈ JG, g.1 = κ * k} =
      e '' ((((JG.subgroupOf (grpAt V (· ∈ gP))) : Subgroup _) : Set (grpAt V (· ∈ gP))) ×ˢ
        (((K₁.subgroupOf (grpAt V (· ∉ gP))) : Subgroup _) : Set (grpAt V (· ∉ gP)))) := by
    ext g
    constructor
    · rintro ⟨κ, hκ, k, hk, hg⟩
      have hκ' : κ ∈ grpAt V (· ∉ gP) := hκ.1
      refine ⟨(⟨k, hJ hk⟩, ⟨κ, hκ'⟩), ⟨Subgroup.mem_subgroupOf.2 hk, Subgroup.mem_subgroupOf.2 ((hK₁ κ).2 hκ)⟩, ?_⟩
      apply Subtype.ext
      rw [he, hg, hcomm k (hJ hk) κ hκ']
    · rintro ⟨p, ⟨hp1, hp2⟩, rfl⟩
      refine ⟨p.2.1, (hK₁ _).1 (Subgroup.mem_subgroupOf.1 hp2), p.1.1, Subgroup.mem_subgroupOf.1 hp1, ?_⟩
      rw [he, hcomm p.1.1 p.1.2 p.2.1 p.2.2]
  have hAc : IsCompact (((JG.subgroupOf (grpAt V (· ∈ gP))) : Subgroup _) : Set (grpAt V (· ∈ gP))) := by
    have h1 : ((JG.subgroupOf (grpAt V (· ∈ gP)) : Subgroup _) : Set (grpAt V (· ∈ gP))) =
        Subtype.val ⁻¹' (JG : Set (GA D V)) := rfl
    rw [h1, Topology.IsInducing.subtypeVal.isCompact_preimage_iff]
    · exact hJc
    · intro x hx; exact ⟨⟨x, hJ hx⟩, rfl⟩
  have hBc : IsCompact (((K₁.subgroupOf (grpAt V (· ∉ gP))) : Subgroup _) : Set (grpAt V (· ∉ gP))) := by
    have h1 : ((K₁.subgroupOf (grpAt V (· ∉ gP)) : Subgroup _) : Set (grpAt V (· ∉ gP))) =
        Subtype.val ⁻¹' (K₁ : Set (GA D V)) := rfl
    rw [h1, Topology.IsInducing.subtypeVal.isCompact_preimage_iff]
    · exact hK₁c
    · intro x hx; exact ⟨⟨x, ((hK₁ x).1 hx).1⟩, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hS]; exact e.isOpenMap _ (hJo.prod hK₁o)
  · rw [hS]; exact (hAc.prod hBc).image e.continuous
  · exact ⟨1, (hK₁ 1).1 (one_mem _), 1, one_mem _, by simp⟩

variable {c : Comm D}

theorem vr_ne_zero (v : VCom c) (hv : v.Is) (j : ℕ) (hj : j < D.R.m) (hμ : (c.μf j).IsHaarMeasure)
    (R : Subgroup (GA D (c.V j))) (hR : IsClosed (R : Set (GA D (c.V j))))
    (ρ : Measure (R.subgroupOf (GfC (c.V j)))) (hρ : ρ.IsHaarMeasure) : v.vr j R ρ ≠ 0 := by
  obtain ⟨hJle, hJc, hJo⟩ := hv.JG j hj
  obtain ⟨hSo, hSc, hS1⟩ := level_open_compact (c.V j) (v.N j) (hv.sd j hj) v.gP (v.JG j) hJle hJc hJo
  have h1 : 0 < (c.μf j).real {g | g.1 ∈ v.K j} := by
    exact real_pos_of_open_compact (c.μf j) hSo hSc ⟨1, hS1⟩
  have hT : IsClosed (((R.subgroupOf (GfC (c.V j))) : Subgroup _) : Set (GfC (c.V j))) :=
    hR.preimage continuous_subtype_val
  have h2 : 0 < ρ.real {g | g.1.1 ∈ v.K j} := by
    exact real_pos_of_open_compact ρ (hSo.preimage continuous_subtype_val)
      (hT.isClosedEmbedding_subtypeVal.isCompact_preimage hSc) ⟨1, hS1⟩
  unfold VCom.vr
  exact_mod_cast (div_pos h1 h2).ne'

theorem kap_ne_zero (v : VCom c) (hc : c.Is) (hv : v.Is) : ∀ j σ h, v.kap j σ h ≠ 0 := by
  intro j σ h
  unfold VCom.kap
  refine mul_ne_zero ?_ ?_
  · exact vr_ne_zero v hv (j + 1) (by omega) (hc.μf _) _ (GlobalTheory.jacGrp_isClosed _ _ _ _ _) _ (hc.ρJ _ _ _)
  · exact vr_ne_zero v hv (j + 1 + 1) (by omega) (hc.μf _) _ (GlobalTheory.BesClosed.besGrp_isClosed _ _ _ _ _ _ _ _) _ (hc.ρB _ _ _)

theorem is_withCG (v : VCom c) (a : ℕ → ℂ) (h : v.Is) : (v.withCG a).Is :=
  ⟨h.disj, h.sd, h.sdT, h.b, h.bT, h.Ψ, h.ΨT, h.JG, h.atG, h.atT, h.ram⟩

theorem weilOK_of_tau {t : Tup c} (v v' : VCom c) (hτ : v'.τ = v.τ) (h : WeilOK (t := t) v) : WeilOK (t := t) v' := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, by rw [hτ]; exact h3⟩

theorem unrOn_mono {t : Tup c} {P P' : Pl D → Prop} (h : t.UnrOn P) (hPP : ∀ x, P' x → P x) : t.UnrOn P' where
  bf j ρ hh x hx := h.bf j ρ hh x (hPP x hx)
  fb j σ hh x hx := h.fb j σ hh x (hPP x hx)
  top j hh := by
    obtain ⟨χS, χT, h1, h2⟩ := h.top j hh
    exact ⟨χS, χT, h1, fun x hx => h2 x (hPP x hx)⟩

end GlobalTheory.SeeSawAll

namespace GlobalTheory.SeeSaw

theorem pins_finiteIntegrals : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι) (n : ℕ) (G : Fin n → GLoc v), c.Is → c.VolLast → v.Is → ShapeOff v o → GPin G → ∃ (ε : ℕ → ι → 𝓀[k]ˣ) (op : ∀ j, BiOp (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1))) (r : ℕ → ι → ℝ) (e : ℕ → ι → ℤ) (a : ℕ → ℂ), (∀ j i, 0 < r j i) ∧ (∀ j, a j ≠ 0) ∧ (∀ j σ h, v.kap j σ h ≠ 0) ∧ ((v.withT (o.S ε) op).withCG a).Is ∧ ∀ (𝒯 : Type) (t : 𝒯 → Tup c) (w : ∀ s, VTup (t s)), (∀ s, (t s).Is ∧ VForm ((v.withT (o.S ε) op).withCG a) (w s) ∧ WeilOK (t := t s) v ∧ TopSph (t := t s) v ∧ (t s).UnrOn (offP v (w s)) ∧ (t s).UnrK (· ∈ v.tP) ∧ (∀ i, (G i).Chars (t s)) ∧ QLaw v (w s) ∧ QLast v (w s) ∧ QFin v (w s) ∧ (∀ j ρ h, (w s).cT j = o.mono (r j) (e j) ((t s).sBF j ρ h).χW) ∧ CVEq ((v.withT (o.S ε) op).withCG a) (w s)) → (∀ s, (t s).LocFin) ∧ ValX t ∧ ValLastX t := by
  intro D c v k _ _ _ _ ι o n G hc hvl hv hsh hG
  obtain ⟨ε, op, r, e, hr, hvT, hT⟩ := GlobalTheory.T.seesaw_levelPrime_law_all_tuples D c v k ι o hc hv hsh
  obtain ⟨a, ha, hGa⟩ := GlobalTheory.T.seeSawUnfolded_support_and_value_at_fixed_level D c v n G hc hv hG
  have hv' : ((v.withT (o.S ε) op).withCG a).Is := GlobalTheory.SeeSawAll.is_withCG _ a hvT
  refine ⟨ε, op, r, e, a, hr, ha, GlobalTheory.SeeSawAll.kap_ne_zero v hc hv, hv', ?_⟩
  intro 𝒯 t w hw
  refine GlobalTheory.T.seesaw_place_laws_give_finite_integral_laws D c ((v.withT (o.S ε) op).withCG a) 𝒯 t w hc hvl hv' (fun s => (hw s).1) (fun s => ?_)
  obtain ⟨hts, hform, hweil, hsph, hunr, hunrK, hch, hql, hqlast, hqfin, hcT, hcv⟩ := hw s
  have hdisjT : Disjoint (w s).Q v.tP := hform.disjT
  have hoff : OffLaw v (w s) := GlobalTheory.T.seesaw_support_off_level_of_lattice_shape D c v k ι o hc hv hsh (t s) (w s) hts hdisjT hunr
  have hvac : VacLaw (t := t s) v := GlobalTheory.T.seeSawUnfoldedVacuaOfShape_proof D c v k ι o hc hv hsh (t s)
  have hunrT : (t s).UnrOn (· ∈ v.tP) := GlobalTheory.SeeSawAll.unrOn_mono hunr fun x hx =>
    ⟨fun hg => Finset.disjoint_left.mp hv.disj hg hx, fun hq => Finset.disjoint_left.mp hdisjT hq hx⟩
  have htl : TLaw (v.withT (o.S ε) op) (w s) := hT (t s) (w s) hts hweil hunrT hunrK hcT
  obtain ⟨hgs, hgv⟩ := hGa (t s) hts hweil hch
  exact ⟨hform, GlobalTheory.SeeSawAll.weilOK_of_tau v _ rfl hweil, hoff, hgs, hgv, hvac, htl, hql, hqlast, hqfin, hcv, hsph⟩

end GlobalTheory.SeeSaw

end
