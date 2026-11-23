import Development.DiscreteGroups.GlobalIrreducibility.TameUniformizerPower
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SglobDzBigDef
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SplitLoc
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MRankOne
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MDzValue
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace DiscreteGroups.sglob.DzType.Rt
open ValuativeRel GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.DepthZeroRankOneLabel
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {g : ℕ} [Fact g.Prime]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
open GlobalTheory.WeilDeligne in
theorem lab_eq_of_tameRep_alt : _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (Γ : GrpSide D) (k : Fin 2) (v : D.nd.PlG k) (μ : ((D.naut.plGw k v).adicCompletion D.host.E)ˣ →* ℂˣ) (hμ : GlobalTheory.SmGL.IsSmoothChar μ), GlobalTheory.SplitWeil.IsTame μ → ∀ (u : 𝓞 D.host.E) (hu : (u : D.host.E) ≠ 0), (∃ (ϖ : 𝓞 D.host.E) (π : D.nd.Om), ϖ ∈ (D.naut.plGw k v).asIdeal ∧ ϖ ∉ (D.naut.plGw k v).asIdeal ^ 2 ∧ π ^ (normV (D.naut.plGw k v) - 1) = algebraMap D.host.E D.nd.Om (ϖ : D.host.E) ∧ (D.nd.plOm.1 (D.naut.plGw k v)).valuation (D.ntypes.tg k v π / π - algebraMap D.host.E D.nd.Om (u : D.host.E)) < 1) → ∀ c : ZMod (D.host.g k), D.ntypes.teichC k (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) c) = ((μ (Units.map (algebraMap D.host.E ((D.naut.plGw k v).adicCompletion D.host.E)).toMonoidHom (Units.mk0 (u : D.host.E) hu)) : ℂˣ) : ℂ) → _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v (Irr.ofDet 1 μ hμ) = X - C c := by
  intro hDZ hL D Γ k v μ hμ hT u hu hex c hc
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  haveI : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))); obtain ⟨a, ha, ε, hl⟩ := hOpn) | obtain ⟨a, ha, ε, hε, hl⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))
  have hSet : GlobalTheory.WeilDeligne.TeichmullerInertiaLabelCondition (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) (D.ntypes.teichC k)
      (D.ntypes.tg k v) :=
    .of_tameGenAt (GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k)
      (D.naut.plGw_over k v)) (D.ntypes.tg_gen k v) (D.ntypes.teichC_inj k)
  have e1 : _root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D (D.naut.plGw k v) 1 (Irr.ofDet 1 μ hμ) =
      GlobalTheory.WeilDeligne.WD.lpOfChar _ (μ.comp a) (ha.smooth hμ) := hl.one μ hμ
  have hwild : ∀ σ : GlobalTheory.WeilDeligne.Weil (D.nd.plOm.2 (D.naut.plGw k v)),
      (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) ∈ GlobalTheory.WeilDeligne.Wild D.host.E (D.nd.plOm.1 (D.naut.plGw k v)) → (μ.comp a) σ = 1 :=
    _root_.GlobalTheory.DepthZeroRankOneLabel.wild_trivial_m_alt D k v μ hμ hT a ha ε _ hl
  have hval : μ (a ⟨D.ntypes.tg k v, GlobalTheory.WeilDeligne.Ine_le_Weil _ hSet.2.1⟩) =
      μ (Units.map (algebraMap D.host.E ((D.naut.plGw k v).adicCompletion D.host.E)).toMonoidHom (Units.mk0 (u : D.host.E) hu)) := by
    obtain ⟨I⟩ := GlobalTheory.TypeRec.Model.nonempty_ident D
    have hw := D.naut.plGw_over k v
    have hN := GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k) hw
    have hw2 : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ (D.naut.plGw k v).asIdeal ^ 2 := fun h2 => by
      have h0 : Ideal.span {((D.host.g k : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
        rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
        exact_mod_cast (D.host.g_prime k).ne_zero
      have hs := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors h0).2
        (Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit.split_of_ncard (D.host.g_prime k) (D.nd.g_split k)).2
      have := hs (D.naut.plGw k v).asIdeal (by rw [← sq, Ideal.dvd_span_singleton]; exact h2)
      exact (D.naut.plGw k v).isPrime.ne_top (Ideal.isUnit_iff.1 this)
    obtain ⟨ϖ, π, hϖ, hϖ2, hπ, hv⟩ := hex
    obtain ⟨n, hn, hun, hgen⟩ := GlobalTheory.DepthZeroRankOneLabel.residue_of_cong _ _ _ (D.nd.plOm.2 _) hN hw hw2
      (Γ.kv k v) _ (Γ.ζ k) (D.ntypes.tg_mem k v) (Γ.ζ_gen k) (Γ.tg_tame k v) u ϖ π hϖ hϖ2 hπ hv
    have hx := GlobalTheory.DepthZeroRankOneLabel.val_lt_of_mem hun
    exact _root_.DiscreteGroups.sglob.DzType.Rt.character_inertia_eq_of_congruent_generator hDZ hl (I.i k v) (I.cont k v) hw (Γ.kv k v)
      (GlobalTheory.DepthZeroRankOneLabel.labDatum (D.ntypes.teichC k) (D.ntypes.teichC_inj k) (Γ.ζ k) (Γ.ζ_gen k))
      _ (D.ntypes.tg_mem k v) (Γ.tg_tame k v) μ hμ hT n hn hgen _ (by simpa using hx)
  unfold _root_.GlobalTheory.PendOf.localLabelPolynomial
  rw [e1, GlobalTheory.WeilDeligne.WD.lab_lpOfChar_eq_iff hSet _ hwild c, hc, MonoidHom.comp_apply, hval]
set_option maxHeartbeats 1000000 in
theorem tame_uniformizer_power_alt : _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (Γ : GrpSide D) (k : Fin 2) (v : D.nd.PlG k) (μ : ((D.naut.plGw k v).adicCompletion D.host.E)ˣ →* ℂˣ) (hμ : GlobalTheory.SmGL.IsSmoothChar μ), GlobalTheory.SplitWeil.IsTame μ → ∀ (u : 𝓞 D.host.E) (hu : (u : D.host.E) ≠ 0), (∃ (ϖ : 𝓞 D.host.E) (π : D.nd.Om), ϖ ∈ (D.naut.plGw k v).asIdeal ∧ ϖ ∉ (D.naut.plGw k v).asIdeal ^ 2 ∧ π ^ (normV (D.naut.plGw k v) - 1) = algebraMap D.host.E D.nd.Om (ϖ : D.host.E) ∧ (D.nd.plOm.1 (D.naut.plGw k v)).valuation (D.ntypes.tg k v π / π - algebraMap D.host.E D.nd.Om (u : D.host.E)) < 1) → ∀ c : ZMod (D.host.g k), D.ntypes.teichC k (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) c) = ((μ (Units.map (algebraMap D.host.E ((D.naut.plGw k v).adicCompletion D.host.E)).toMonoidHom (Units.mk0 (u : D.host.E) hu)) : ℂˣ) : ℂ) → _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v (Irr.ofDet 1 μ hμ) = X - C c :=
  _root_.DiscreteGroups.sglob.DzType.Rt.lab_eq_of_tameRep_alt
end DiscreteGroups.sglob.DzType.Rt
end
