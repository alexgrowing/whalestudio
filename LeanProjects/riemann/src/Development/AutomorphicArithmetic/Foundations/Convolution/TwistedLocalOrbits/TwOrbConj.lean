import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Match
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.QuotConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.QuotIndep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.HaarComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.HeckeRepresentationSatake
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.ExtCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.CentComm

open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc

theorem UpperTheory.ConvolutionTheory.Loc.twOrbConj :
    ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
        [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
        [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E) (n : ℕ) [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)] (μE : Measure (GL (Fin n) E)), μE.IsHaarMeasure →
      ∀ (δ g : GL (Fin n) E) (μ : Measure (twCent (sigmaGL σ) δ)) (μ' : Measure (twCent (sigmaGL σ) (twConj (sigmaGL σ) g δ))),
        IsTwRegSemisimple σ δ → μ.IsHaarMeasure → μ'.IsHaarMeasure →
        Measure.map (fun x : twCent (sigmaGL σ) δ => g⁻¹ * (x : GL (Fin n) E) * g) μ =
          Measure.map (fun x : twCent (sigmaGL σ) (twConj (sigmaGL σ) g δ) => (x : GL (Fin n) E)) μ' →
        ∀ φ ∈ SB (GL (Fin n) E), twOrbIntegralC (sigmaGL σ) μE (twConj (sigmaGL σ) g δ) μ' φ = twOrbIntegralC (sigmaGL σ) μE δ μ φ := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ n _ _ μE hμE δ g μ μ' hδ hμ hμ' hmap φ hφ
  obtain ⟨h1, h2, h3, -, -⟩ := UpperTheory.V.Z.Tf.Orb.gLTop E n
  have hc : Continuous (sigmaGL σ : GL (Fin n) E → GL (Fin n) E) :=
    ((UpperTheory.V.Z.Tf.Orb.extCont k E).2.2 n).2 σ
  have htw : Continuous fun x : GL (Fin n) E => twConj (sigmaGL σ) x δ :=
    (continuous_inv.mul continuous_const).mul hc
  have hclosed : IsClosed (twCent (sigmaGL σ) δ : Set (GL (Fin n) E)) := isClosed_eq htw continuous_const
  have hℓ : σ ^ Module.finrank k E = 1 := by
    rw [← IsGalois.card_aut_eq_finrank]; exact pow_card_eq_one'
  have hθ : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank k E = 1 := by
    rw [← sigmaGL_pow, hℓ, sigmaGL_one]
  have hcomm : ∀ a ∈ twCent (sigmaGL σ) δ, ∀ b ∈ twCent (sigmaGL σ) δ, Commute a b := by
    intro a ha b hb
    have key : ∀ c ∈ twCent (sigmaGL σ) δ, Commute (c : Matrix (Fin n) (Fin n) E) (normGL σ δ : GL (Fin n) E) := by
      intro c hc
      have := congrArg Units.val (twCent_commute_twNorm (sigmaGL σ) hθ δ hc)
      exact this
    exact Units.ext (UpperTheory.V.Z.Tf.Orb.centComm E n _ _ _ hδ (key a ha) (key b hb))
  have hmem : ∀ x, x ∈ twCent (sigmaGL σ) δ ↔ g⁻¹ * x * g ∈ twCent (sigmaGL σ) (twConj (sigmaGL σ) g δ) := by
    intro x
    rw [mem_twCent, mem_twCent, twConj, map_mul, map_mul, map_inv]
    have e : (g⁻¹ * x * g)⁻¹ * (g⁻¹ * δ * sigmaGL σ g) * ((sigmaGL σ g)⁻¹ * sigmaGL σ x * sigmaGL σ g) =
        g⁻¹ * (x⁻¹ * δ * sigmaGL σ x) * sigmaGL σ g := by group
    rw [e, mul_left_inj, mul_right_inj]
  have hφc : Continuous φ := IsLocallyConstant.continuous hφ.1
  have main := UpperTheory.V.Z.Tf.Orb.quotConj UpperTheory.V.Z.Tf.Orb.haarComm UpperTheory.V.Z.Tf.Orb.quotIndep (GL (Fin n) E) μE hμE
    _ _ g hclosed hcomm hmem μ μ' hμ hμ' hmap (fun x => φ (twConj (sigmaGL σ) x δ)) (hφc.comp htw).measurable
    (fun h hh x => by rw [twConj_mul_left _ _ hh])
  unfold twOrbIntegralC
  rw [← main]
  congr 1
  funext x
  congr 1
  simp only [twConj, map_mul]
  group
