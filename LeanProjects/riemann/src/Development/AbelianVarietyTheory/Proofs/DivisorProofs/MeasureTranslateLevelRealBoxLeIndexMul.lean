import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelMeasurePushforwardEqProductRealMeasures
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.VolBox

variable {D : D7}

theorem rp_eq_one (V : HSp D) (θ : InfFam D) (A : Frames V) (rp : GA D V →* (∀ ρ, Upq V ρ)) (hV : V.SigOK)
    (hA : IsFrames V A) (hrp : IsRealPart V θ A rp) (k : GA D V) (hk : k ∈ GfC V) : rp k = 1 := by
  funext ρ
  refine GlobalTheory.RealBoxMeasure.mat_cancel V hV A hA ρ ?_
  have h1 : infMat D.sp.cm.sig V.gram (θ ρ) k = 1 := by
    have h2 := congrArg Units.val ((MonoidHom.mem_ker).1 hk)
    show (Units.val (infHom V k)).map (θ ρ) = 1
    rw [h2]
    simp
  rw [hrp, h1, Pi.one_apply, GlobalTheory.Mem.VolExists.mat_one, Matrix.one_mul, Matrix.mul_one]

theorem rp_realElt (V : HSp D) (θ : InfFam D) (A : Frames V) (rp : GA D V →* (∀ ρ, Upq V ρ)) (hV : V.SigOK)
    (hθ : IsInfFam θ) (hA : IsFrames V A) (hrp : IsRealPart V θ A rp) (b : ∀ ρ, Upq V ρ) :
    rp (realElt θ V fun ρ => realMat V A ρ (b ρ)) = b := by
  funext ρ
  refine GlobalTheory.RealBoxMeasure.mat_cancel V hV A hA ρ ?_
  obtain ⟨C, h1, -⟩ := (GlobalTheory.Mem.SignatureFactor.exists_factor _ _ _ _ (hV (tauE D ρ))).2.2 (A ρ) (hA ρ)
  have e : UpqT.mat (b ρ) * A ρ = A ρ * (C * (UpqT.mat (b ρ) * A ρ)) := by
    rw [← Matrix.mul_assoc (A ρ), h1, Matrix.one_mul]
  rw [hrp, GlobalTheory.RealBoxMeasure.infMat_realElt θ hθ V _ (fun τ => GlobalTheory.RealBoxMeasure.realMat_mem V hV A hA τ _) ρ,
    GlobalTheory.RealBoxMeasure.realMat_of V A hA ρ _ _ e, ← e]

theorem exists_fin (V : HSp D) (θ : InfFam D) (A : Frames V) (rp : GA D V →* (∀ ρ, Upq V ρ)) (hV : V.SigOK)
    (hθ : IsInfFam θ) (hA : IsFrames V A) (hrp : IsRealPart V θ A rp) (h : GA D V) :
    ∃ k : GA D V, rp k = 1 ∧ finE V k = finE V h := by
  refine ⟨(realElt θ V fun ρ => realMat V A ρ (rp h ρ))⁻¹ * h, ?_, ?_⟩
  · rw [map_mul, map_inv, rp_realElt V θ A rp hV hθ hA hrp, inv_mul_cancel]
  · rw [map_mul, map_inv, GlobalTheory.RealBoxMeasure.finE_realElt, inv_one, one_mul]

theorem meas_level (V : HSp D) (θ : InfFam D) (A : Frames V) (m : ∀ ρ, Measure (Upq V ρ))
    (rp : GA D V →* (∀ ρ, Upq V ρ)) (K : Subgroup (GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))) (μ : Measure (GA D V))
    (hV : V.SigOK) (hθ : IsInfFam θ) (hA : IsFrames V A) (hm : ∀ ρ, IsMinf (m ρ)) (hc : Continuous rp)
    (hrp : IsRealPart V θ A rp) (hK : IsOpen {h : GA D V | finE V h ∈ K}) (hμ : IsMeasLev V K μ)
    (B : Set (∀ ρ, Upq V ρ)) (hB : MeasurableSet B) :
    μ {h | finE V h ∈ K ∧ rp h ∈ B} = Measure.pi m B := by
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  obtain ⟨-, hsc, hbo, -⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable V
  haveI := hsc
  haveI := hbo
  have hBm : MeasurableSet (rp ⁻¹' B) := hc.measurable hB
  have H := GlobalTheory.RealBoxMeasure.lintegral_levelSet_eq_pi D θ hθ V hV K μ hμ A hA m hm
    ((rp ⁻¹' B).indicator 1) (measurable_one.indicator hBm) (fun g k hk => by
      have : rp (g * k) = rp g := by rw [map_mul, rp_eq_one V θ A rp hV hA hrp k hk.1, mul_one]
      exact Set.indicator_eq_indicator (by rw [Set.mem_preimage, this, Set.mem_preimage]) rfl) hK.measurableSet
  rw [lintegral_indicator_one hBm, Measure.restrict_apply hBm] at H
  rw [← lintegral_indicator_one hB, show {h | finE V h ∈ K ∧ rp h ∈ B} = rp ⁻¹' B ∩ {h : GA D V | finE V h ∈ K} from
    Set.ext fun h => and_comm, H]
  refine lintegral_congr fun b => ?_
  exact Set.indicator_eq_indicator (by rw [Set.mem_preimage, rp_realElt V θ A rp hV hθ hA hrp]) rfl

theorem meas_translate_le : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (A : Frames V) (m : ∀ ρ, Measure (Upq V ρ)) (rp : GA D V →* (∀ ρ, Upq V ρ)) (K K₀ : Subgroup (GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))) (μ : Measure (GA D V)), V.SigOK → IsInfFam θ → IsFrames V A → (∀ ρ, IsMinf (m ρ)) → Continuous rp → IsRealPart V θ A rp → K ≤ K₀ → K.relIndex K₀ ≠ 0 → IsOpen {h : GA D V | finE V h ∈ K} → IsMeasLev V K μ → ∀ g ∈ GfC V, ∀ B : Set (∀ ρ, Upq V ρ), MeasurableSet B → μ {h | finE V (g⁻¹ * h) ∈ K₀ ∧ rp h ∈ B} ≤ (K.relIndex K₀ : ℝ≥0∞) * Measure.pi m B := by
  intro D V θ A m rp K K₀ μ hV hθ hA hm hc hrp _ hi hK hμ g _ B hB
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI := hμ.1
  haveI : (K.subgroupOf K₀).FiniteIndex := ⟨hi⟩
  haveI : Fintype (K₀ ⧸ K.subgroupOf K₀) := Fintype.ofFinite _
  let S : (K₀ ⧸ K.subgroupOf K₀) → Set (GA D V) := fun q =>
    {h | (∃ hh : finE V (g⁻¹ * h) ∈ K₀, (QuotientGroup.mk ⟨_, hh⟩ : K₀ ⧸ K.subgroupOf K₀) = q) ∧ rp h ∈ B}
  have hS : ∀ q, μ (S q) ≤ Measure.pi m B := by
    intro q
    rcases (S q).eq_empty_or_nonempty with h0 | ⟨h₀, ⟨hh₀, hq₀⟩, -⟩
    · rw [h0, measure_empty]; exact zero_le
    obtain ⟨k, hk1, hk2⟩ := exists_fin V θ A rp hV hθ hA hrp h₀
    rw [← meas_level V θ A m rp K μ hV hθ hA hm hc hrp hK hμ B hB, ← measure_preimage_mul μ k⁻¹ {h | finE V h ∈ K ∧ rp h ∈ B}]
    refine measure_mono ?_
    rintro h ⟨⟨hh, hq⟩, hb⟩
    have h1 := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 (hq₀.trans hq.symm))
    show finE V (k⁻¹ * h) ∈ K ∧ rp (k⁻¹ * h) ∈ B
    refine ⟨?_, ?_⟩
    · have h2 : finE V (k⁻¹ * h) = (finE V (g⁻¹ * h₀))⁻¹ * finE V (g⁻¹ * h) := by
        simp only [map_mul, map_inv, hk2]; group
      rw [h2]; exact h1
    · rwa [map_mul, map_inv, hk1, inv_one, one_mul]
  calc μ {h | finE V (g⁻¹ * h) ∈ K₀ ∧ rp h ∈ B} ≤ μ (⋃ q, S q) :=
        measure_mono fun h hh => Set.mem_iUnion.2 ⟨_, ⟨hh.1, rfl⟩, hh.2⟩
    _ ≤ ∑ q, μ (S q) := measure_iUnion_fintype_le μ S
    _ ≤ ∑ _q : K₀ ⧸ K.subgroupOf K₀, Measure.pi m B := Finset.sum_le_sum fun q _ => hS q
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]

end GlobalTheory.CovTop.VolBox
