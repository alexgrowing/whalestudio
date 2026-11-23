import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.TBlkEqTFMulProdTV

noncomputable section

namespace PI.IwaMeasEx.LP

open MeasureTheory MeasureTheory.Measure Topology Set NumberField
open scoped ENNReal NNReal
open Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma Formalism.L2.S.S7.WittLeviSubgroups PI.IwaMeasEx.AfT

section Uniq

variable {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem exists_coef (H : Subgroup G) (hc : IsClosed (H : Set G)) {μ : Measure G} (hs : μ (H : Set G)ᶜ = 0)
    (hcpt : ∀ s : Set G, IsCompact s → μ s ≠ ⊤) (hi : ∀ h ∈ H, μ.map (fun x => h * x) = μ) :
    haveI : LocallyCompactSpace H := hc.locallyCompactSpace
    ∃ a : ℝ≥0, μ = a • (Measure.haar : Measure H).map Subtype.val := by
  haveI : LocallyCompactSpace H := hc.locallyCompactSpace
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  have hme : MeasurableEmbedding (Subtype.val : H → G) := hc.isClosedEmbedding_subtypeVal.measurableEmbedding
  have hmap : (μ.comap (Subtype.val : H → G)).map Subtype.val = μ := by
    rw [hme.map_comap, Subtype.range_coe]
    exact restrict_eq_self_of_ae_mem ((ae_iff).2 hs)
  haveI : IsMulLeftInvariant (μ.comap (Subtype.val : H → G)) := ⟨fun h => by
    have e1 := map_val_mul' H h (μ.comap (Subtype.val : H → G))
    rw [hmap, hi (h : G) h.2] at e1
    calc (μ.comap (Subtype.val : H → G)).map (fun x => h * x)
        = (((μ.comap (Subtype.val : H → G)).map (fun x => h * x)).map Subtype.val).comap Subtype.val :=
          (hme.comap_map _).symm
      _ = μ.comap Subtype.val := by rw [e1]⟩
  haveI : IsFiniteMeasureOnCompacts (μ.comap (Subtype.val : H → G)) := ⟨fun K hK => by
    rw [hme.comap_apply]
    exact (hcpt _ (hK.image continuous_subtype_val)).lt_top⟩
  refine ⟨haarScalarFactor (μ.comap (Subtype.val : H → G)) Measure.haar, ?_⟩
  conv_lhs => rw [← hmap, isMulLeftInvariant_eq_smul (μ.comap (Subtype.val : H → G)) Measure.haar]
  rw [Measure.map_smul]

theorem eq_smul_of_sub (H : Subgroup G) (hc : IsClosed (H : Set G)) {μ1 μ2 : Measure G} (n1 : μ1 ≠ 0)
    (s1 : μ1 (H : Set G)ᶜ = 0) (c1 : ∀ s : Set G, IsCompact s → μ1 s ≠ ⊤) (i1 : ∀ h ∈ H, μ1.map (fun x => h * x) = μ1)
    (n2 : μ2 ≠ 0) (s2 : μ2 (H : Set G)ᶜ = 0) (c2 : ∀ s : Set G, IsCompact s → μ2 s ≠ ⊤)
    (i2 : ∀ h ∈ H, μ2.map (fun x => h * x) = μ2) : ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ⊤ ∧ μ2 = κ • μ1 := by
  obtain ⟨a1, h1⟩ := exists_coef H hc s1 c1 i1
  obtain ⟨a2, h2⟩ := exists_coef H hc s2 c2 i2
  have ha1 : (a1 : ℝ≥0∞) ≠ 0 := by
    intro h; apply n1; rw [h1, ENNReal.smul_def, h, zero_smul]
  have ha2 : (a2 : ℝ≥0∞) ≠ 0 := by
    intro h; apply n2; rw [h2, ENNReal.smul_def, h, zero_smul]
  refine ⟨(a2 : ℝ≥0∞) / a1, (ENNReal.div_pos ha2 ENNReal.coe_ne_top).ne', ENNReal.div_ne_top ENNReal.coe_ne_top ha1, ?_⟩
  rw [h1, h2, ENNReal.smul_def a1, ENNReal.smul_def a2, smul_smul, ENNReal.div_mul_cancel ha1 ENNReal.coe_ne_top]

end Uniq

theorem pi_smul_nn {ι : Type} [Fintype ι] {α : ι → Type} [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, SigmaFinite (μ i)] (c : ι → ℝ≥0) :
    Measure.pi (fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ := by
  refine Measure.pi_eq fun s _ => ?_
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, Measure.pi_pi, ENNReal.coe_finset_prod,
    Finset.prod_mul_distrib]

theorem ofReal_smul {α : Type} [MeasurableSpace α] (x : ℝ) (μ : Measure α) :
    ENNReal.ofReal x • μ = x.toNNReal • μ := by
  rfl

section Prod

variable {I : AutInst} {J : ℕ} (Fr : WittFrame I J) (c : Composition J)

theorem mem_uniA_iff (x : I.GA) : x ∈ Fr.uniA c ↔ (∀ v, x.1 v ∈ uniV Fr c v) ∧ x.2 ∈ uniF Fr c := by
  constructor
  · intro h
    exact ⟨fun v => Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 h).2 v, (Subgroup.mem_inf.1 h).1⟩
  · rintro ⟨h1, h2⟩
    exact Subgroup.mem_inf.2 ⟨h2, Subgroup.mem_iInf.2 h1⟩

end Prod

end PI.IwaMeasEx.LP

end
