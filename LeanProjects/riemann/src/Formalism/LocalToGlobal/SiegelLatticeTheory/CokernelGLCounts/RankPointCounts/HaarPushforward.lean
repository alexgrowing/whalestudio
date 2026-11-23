import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CovariantRepresentation
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsMulRightInvariantOfLattice

noncomputable section

open MeasureTheory Topology NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.KappaOffDiagonal Formalism.L2.SG.TermOp.Vanish Formalism.L2.SG.CovariantRepresentation

namespace Formalism.L2.SG.HaarPushforward

section Core

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G]

theorem pushHaar (R : Subgroup G) (hR : IsClosed (R : Set G)) :
    ∃ ν : Measure G, SigmaFinite ν ∧ ν ≠ 0 ∧ ν (R : Set G)ᶜ = 0 ∧ (∀ K : Set G, IsCompact K → ν K < ⊤) ∧
      (∀ r ∈ R, ν.map (fun x => r * x) = ν) := by
  have hce : IsClosedEmbedding (Subtype.val : R → G) := hR.isClosedEmbedding_subtypeVal
  haveI : LocallyCompactSpace R := hce.locallyCompactSpace
  haveI : BorelSpace R := Subtype.borelSpace _
  haveI : SecondCountableTopology R := TopologicalSpace.Subtype.secondCountableTopology (R : Set G)
  let μ : Measure R := Measure.haar
  haveI : SigmaFinite μ := sigmaFinite_of_locallyFinite
  have hemb : MeasurableEmbedding (Subtype.val : R → G) := MeasurableEmbedding.subtype_coe hR.measurableSet
  refine ⟨μ.map Subtype.val, hemb.sigmaFinite_map, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [Measure.map_eq_zero_iff hemb.measurable.aemeasurable] at h
    exact (NeZero.ne μ) h
  · rw [hemb.map_apply]
    have e : (Subtype.val ⁻¹' ((R : Set G)ᶜ) : Set R) = ∅ := by
      ext x
      exact ⟨fun hx => (hx x.2).elim, fun h => h.elim⟩
    rw [e, measure_empty]
  · intro K hK
    rw [hemb.map_apply]
    exact (hce.isCompact_preimage hK).measure_lt_top
  · intro r hr
    have hm : Measurable (fun x : G => r * x) := (continuous_const.mul continuous_id).measurable
    have hm' : Measurable (fun y : R => (⟨r, hr⟩ : R) * y) := (continuous_const.mul continuous_id).measurable
    rw [Measure.map_map hm hemb.measurable]
    have e : (fun x : G => r * x) ∘ Subtype.val = Subtype.val ∘ (fun y : R => (⟨r, hr⟩ : R) * y) := rfl
    rw [e, ← Measure.map_map hemb.measurable hm', map_mul_left_eq_self]

theorem pushHaar_inv (R Γ : Subgroup G) [Countable Γ] [DiscreteTopology Γ] (hR : IsClosed (R : Set G)) (hΓ : Γ ≤ R)
    (hcov : ∃ K : Set G, IsCompact K ∧ ∀ r ∈ R, ∃ s ∈ Γ, s * r ∈ K) :
    ∃ ν : Measure G, SigmaFinite ν ∧ ν ≠ 0 ∧ ν (R : Set G)ᶜ = 0 ∧ (∀ K : Set G, IsCompact K → ν K < ⊤) ∧
      (∀ r ∈ R, ν.map (fun x => r * x) = ν) ∧ ν.map (fun x => x⁻¹) = ν := by
  have hce : IsClosedEmbedding (Subtype.val : R → G) := hR.isClosedEmbedding_subtypeVal
  haveI : LocallyCompactSpace R := hce.locallyCompactSpace
  haveI : BorelSpace R := Subtype.borelSpace _
  haveI : SecondCountableTopology R := TopologicalSpace.Subtype.secondCountableTopology (R : Set G)
  let μ : Measure R := Measure.haar
  haveI : SigmaFinite μ := sigmaFinite_of_locallyFinite
  have hemb : MeasurableEmbedding (Subtype.val : R → G) := MeasurableEmbedding.subtype_coe hR.measurableSet
  let Γ' : Subgroup R := Γ.subgroupOf R
  let ι : Γ' → Γ := fun x => ⟨x.1.1, Subgroup.mem_subgroupOf.1 x.2⟩
  have hι : Function.Injective ι := by
    intro a b e
    simp only [ι, Subtype.mk.injEq] at e
    exact Subtype.ext (Subtype.ext e)
  haveI : Countable Γ' := hι.countable
  haveI : DiscreteTopology Γ' :=
    DiscreteTopology.of_continuous_injective
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) hι
  obtain ⟨K, hK, hKc⟩ := hcov
  have hinv : μ.map (fun x => x⁻¹) = μ :=
    haar_map_inv_of_lattice μ Γ' (hce.isCompact_preimage hK) (fun x => by
      obtain ⟨s, hs, hsK⟩ := hKc x.1 x.2
      exact ⟨⟨s, hΓ hs⟩, Subgroup.mem_subgroupOf.2 hs, hsK⟩)
  refine ⟨μ.map Subtype.val, hemb.sigmaFinite_map, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [Measure.map_eq_zero_iff hemb.measurable.aemeasurable] at h
    exact (NeZero.ne μ) h
  · rw [hemb.map_apply]
    have e : (Subtype.val ⁻¹' ((R : Set G)ᶜ) : Set R) = ∅ := by
      ext x
      exact ⟨fun hx => (hx x.2).elim, fun h => h.elim⟩
    rw [e, measure_empty]
  · intro K hK
    rw [hemb.map_apply]
    exact (hce.isCompact_preimage hK).measure_lt_top
  · intro r hr
    have hm : Measurable (fun x : G => r * x) := (continuous_const.mul continuous_id).measurable
    have hm' : Measurable (fun y : R => (⟨r, hr⟩ : R) * y) := (continuous_const.mul continuous_id).measurable
    rw [Measure.map_map hm hemb.measurable]
    have e : (fun x : G => r * x) ∘ Subtype.val = Subtype.val ∘ (fun y : R => (⟨r, hr⟩ : R) * y) := rfl
    rw [e, ← Measure.map_map hemb.measurable hm', map_mul_left_eq_self]
  · rw [Measure.map_map continuous_inv.measurable hemb.measurable]
    have e : (fun x : G => x⁻¹) ∘ Subtype.val = Subtype.val ∘ (fun y : R => y⁻¹) := rfl
    rw [e, ← Measure.map_map hemb.measurable continuous_inv.measurable, hinv]

end Core

variable {D : D7} {X : HidaSetting D} {u u' : D.what₂.Word}

def RConjModC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')), ∀ h ∈ pointwiseStabilizerInfinite X t.rep, ∀ ν : Measure X.B.I.Ginf,
    SigmaFinite ν → ν ≠ 0 → ν (Rset t)ᶜ = 0 → (∀ K : Set X.B.I.Ginf, IsCompact K → ν K < ⊤) →
      (∀ r ∈ Rset t, ν.map (fun x => r * x) = ν) → ν.map (fun x => x⁻¹) = ν → ν.map (fun x => h⁻¹ * x * h) = ν

theorem rHaarC_of (hN : NLamNinf) (hG : PsiInfChar) (h1 : RClosedC) (h2 : RODiscreteC) (h3 : RCocompactC)
    (hM : RConjModC) : RHaarC := by
  intro D X Y u u' t h hh
  have hΓR : ROsub X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin ≤ Rsub hG t := by
    intro s hs
    have hs0 : s ∈ ROset X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin := hs
    obtain ⟨z, n, hz, hzs, hn, hn'⟩ := hs0
    have hl : RatLink X (t.pt⁻¹ * z * t.pt) (t.lin⁻¹ * n * t.lin) :=
      ratLink_mul X (ratLink_mul X (ratLink_inv X t.rep.2.1) hz) t.rep.2.1
    have hs2 := hN D X u' t.lam' _ _ hl hn'
    rw [Prod.fst_mul, Prod.fst_mul, Prod.fst_inv, ← hzs] at hs2
    exact ⟨hzs ▸ hN D X u t.lam z n hz hn, hs2⟩
  haveI := ROsub_countable X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin
  haveI := h2 D X Y u u' t
  obtain ⟨K, hK, hKc⟩ := h3 D X Y u u' t
  obtain ⟨ν, hs, h0, hc, hKf, hl, hi⟩ :=
    pushHaar_inv (Rsub hG t) (ROsub X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin) (h1 D X Y u u' t) hΓR
      ⟨K, hK, fun r hr => hKc r hr⟩
  exact ⟨ν, hs, h0, hc, hKf, hl, hi, hM D X Y u u' t h hh ν hs h0 hc hKf hl hi⟩

end Formalism.L2.SG.HaarPushforward
