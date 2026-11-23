import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
open MeasureTheory NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Global GroundTheory.Global.SemiLocal
open GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped ENNReal NumberField.AdeleRing TensorProduct

theorem UpperTheory.quotientIntegral_lt_top_of_invariant_closedEmbedding :
    Q1 → Q2 → ∀ (G T : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T] [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] (H : Subgroup G) [LocallyCompactSpace H], IsClosed (H : Set G) →
        ∀ (μ : Measure H) [μ.IsHaarMeasure] (ν : Measure T) [ν.IsHaarMeasure] [ν.IsInvInvariant] [ν.IsMulRightInvariant]
          (i : T →* H), Topology.IsClosedEmbedding i → ∀ Φ : H → ℂ, Continuous Φ → (∀ t x, Φ (i t * x) = Φ x) →
          (∀ ρ, IsNormAlong id i ν ρ → ∫⁻ x, ‖Φ x‖ₑ * ρ x ∂μ < ⊤) →
          quotInt μ (fun x : H => (x : G)) (fun t => ((i t : H) : G)) ν Φ = quotInt μ id i ν Φ := by
  intro q1 q2 G T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H _ hH μ _ ν _ _ _ i hi Φ hΦ hinv hfin
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨ρ, hρc, hρ, -⟩ := q2 H T ν i hi
  have hemb : MeasurableEmbedding (Subtype.val : H → G) :=
    MeasurableEmbedding.subtype_coe hH.measurableSet
  have hex : ∃ ρ', IsNormAlong (fun x : H => (x : G)) (fun t => ((i t : H) : G)) ν ρ' := by
    refine ⟨Function.extend (Subtype.val : H → G) (fun x => (ρ x : ℝ≥0∞)) 0,
      hemb.measurable_extend hρ.1 measurable_zero, fun x => ?_⟩
    rw [← hρ.2 x]
    refine lintegral_congr fun t => ?_
    exact Subtype.val_injective.extend_apply (fun x => (ρ x : ℝ≥0∞)) 0 (i t * x)
  have hn : IsNormAlong id i ν (fun x : H => hex.choose (x : G)) :=
    ⟨hex.choose_spec.1.comp measurable_subtype_coe, fun x => hex.choose_spec.2 x⟩
  have h1 := q1 H H T μ ν (MonoidHom.id H) i measurable_id hi.continuous Φ
    (fun x : H => hex.choose (x : G)) hΦ.measurable hinv hn (hfin _ hn)
  refine Eq.trans ?_ h1.symm
  unfold quotInt
  rw [dif_pos hex]
  rfl
