import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.UnfoldMain
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.NuNeSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExStabNu
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.PosNear

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Set
open scoped TensorProduct ENNReal Pointwise

theorem thetaPos_of (hFin : ThetaFin) (hW : Witt) (hI : InvInv) (hMO : MeasOrb) (hMG : MeasGrp)
    (hTN : TestNear) : ThetaPos := by
  intro F E _ _ _ _ _ σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet μ hμ 𝓕 h𝓕
  haveI : MeasurableMul (HA (AF F) σ J) := (hMG F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet).1
  haveI : MeasurableInv (HA (AF F) σ J) := (hMG F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet).2
  haveI : μ.IsHaarMeasure := hμ
  haveI : μ.IsInvInvariant := (hI F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet).1 μ hμ
  haveI : Countable (HFinIn (AF F) σ J) := um_countable_HFinIn F E σ M J
  haveI hΓc : Countable (GamA σ J) := um_countable_HFinIn F E σ M J
  obtain ⟨φ, hφ0, hadm, U, hUo, hUne, hUpos⟩ := hTN F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet
  refine ⟨φ, hφ0, hadm, ?_⟩
  obtain ⟨e, he⟩ := gram_orbit_equiv σ J X0 (hW F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet)
  have hsub : orbS (GamA σ J) (ratTup (F := F) (AF F) X0) ⊆
      Set.range (fun γ : GamA σ J => (γ : HA (AF F) σ J) • ratTup (F := F) (AF F) X0) := by
    rintro x ⟨γ, hγ, e⟩
    exact ⟨⟨γ, hγ⟩, e⟩
  haveI hcO : Countable (orbS (GamA σ J) (ratTup (F := F) (AF F) X0)) :=
    ((Set.countable_range _).mono hsub).to_subtype
  have hmφ : Measurable fun g : HA (AF F) σ J => φ (g • ratTup (F := F) (AF F) X0) := by
    have := hMO F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet _ hadm.adm
    have h2 := Complex.measurable_re.comp this
    simp only [Function.comp_def, Complex.ofReal_re] at h2
    exact h2
  let θp : HA (AF F) σ J → ℝ≥0∞ := fun h => ∑' x : orbS (GamA σ J) (ratTup (F := F) (AF F) X0),
    ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E)))
  have hθS : ∀ h : HA (AF F) σ J, θp h =
      ∑' X : {X : Fin a → Fin M → E | gramE σ J X = gramE σ J X0},
        ENNReal.ofReal (φ (h⁻¹ • ratTup (F := F) (AF F) (X : Fin a → Fin M → E))) := by
    intro h
    show ∑' x : orbS (GamA σ J) (ratTup (F := F) (AF F) X0), _ = _
    rw [← e.tsum_eq (fun x => ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))))]
    exact tsum_congr fun X => by rw [he X]
  have hθm : Measurable θp := by
    refine Measurable.ennreal_tsum fun x => ?_
    have hx : (fun h : HA (AF F) σ J => ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E)))) =
        fun h => ENNReal.ofReal (φ ((h⁻¹ * repO _ _ x) • ratTup (F := F) (AF F) X0)) := by
      funext h
      rw [mul_smul, repO_smul]
    rw [hx]
    exact (hmφ.comp (measurable_inv.mul_const _)).ennreal_ofReal
  have hθeq : ∀ h, thetaS F E σ M J (fun X => (φ X : ℂ)) {X | gramE σ J X = gramE σ J X0} h =
      (((θp h).toReal : ℝ) : ℂ) := by
    intro h
    unfold thetaS
    rw [← Complex.ofReal_tsum, hθS h, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
    congr 1
    exact tsum_congr fun X => (ENNReal.toReal_ofReal (hφ0 _)).symm
  have hfinI : ∫⁻ h in 𝓕, θp h ∂μ ≠ ⊤ := by
    have := hFin F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet μ hμ 𝓕 h𝓕 φ hφ0 hadm.adm
    rw [lintegral_congr hθS]
    exact this.ne
  have hI1 : ∫ h in 𝓕, thetaS F E σ M J (fun X => (φ X : ℂ)) {X | gramE σ J X = gramE σ J X0} h ∂μ =
      (((∫⁻ h in 𝓕, θp h ∂μ).toReal : ℝ) : ℂ) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hθeq), integral_complex_ofReal,
      integral_toReal hθm.aemeasurable (ae_lt_top hθm hfinI)]

  have hinv : ∀ γ ∈ GamA σ J, ∀ h, θp (γ * h) = θp h := by
    intro γ hγ h
    let T : orbS (GamA σ J) (ratTup (F := F) (AF F) X0) ≃
        orbS (GamA σ J) (ratTup (F := F) (AF F) X0) :=
      { toFun := fun x => ⟨γ⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E), by
          obtain ⟨γ', hγ', e'⟩ := x.2
          exact ⟨γ⁻¹ * γ', (GamA σ J).mul_mem ((GamA σ J).inv_mem hγ) hγ', by rw [mul_smul, e']⟩⟩
        invFun := fun x => ⟨γ • (x : Fin a → Fin M → AF F ⊗[F] E), by
          obtain ⟨γ', hγ', e'⟩ := x.2
          exact ⟨γ * γ', (GamA σ J).mul_mem hγ hγ', by rw [mul_smul, e']⟩⟩
        left_inv := fun x => Subtype.ext (smul_inv_smul γ _)
        right_inv := fun x => Subtype.ext (inv_smul_smul γ _) }
    show ∑' x : orbS (GamA σ J) (ratTup (F := F) (AF F) X0), _ =
      ∑' x : orbS (GamA σ J) (ratTup (F := F) (AF F) X0), _
    rw [← T.tsum_eq (fun x => ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))))]
    refine tsum_congr fun x => ?_
    show _ = ENNReal.ofReal (φ (h⁻¹ • γ⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E)))
    rw [mul_inv_rev, mul_smul]

  let V : Set (HA (AF F) σ J) := Inv.inv ⁻¹' U
  have hVm : MeasurableSet V := hUo.measurableSet.preimage measurable_inv
  have hVpos : 0 < μ V := by
    show 0 < μ (Inv.inv ⁻¹' U)
    rw [Measure.measure_preimage_inv]
    exact hUo.measure_pos μ hUne
  have hθpos : ∀ h ∈ V, 0 < θp h := by
    intro h hV
    let x0 : orbS (GamA σ J) (ratTup (F := F) (AF F) X0) :=
      ⟨ratTup (F := F) (AF F) X0, ⟨1, (GamA σ J).one_mem, one_smul _ _⟩⟩
    refine lt_of_lt_of_le ?_ (ENNReal.le_tsum x0)
    exact ENNReal.ofReal_pos.2 (hUpos h⁻¹ hV)
  have h𝓕' : IsFundamentalDomain (GamA σ J) 𝓕 μ := h𝓕
  have hL0 : ∫⁻ h in 𝓕, θp h ∂μ ≠ 0 := by
    intro hL
    have hz : ∫⁻ g, V.indicator θp g ∂μ = 0 := by
      rw [h𝓕'.lintegral_eq_tsum'']
      refine ENNReal.tsum_eq_zero.2 fun γ => le_antisymm ?_ zero_le
      calc ∫⁻ h in 𝓕, V.indicator θp (γ • h) ∂μ ≤ ∫⁻ h in 𝓕, θp h ∂μ := by
            refine lintegral_mono fun h => ?_
            calc V.indicator θp (γ • h) ≤ θp (γ • h) := indicator_le_self _ _ _
              _ = θp h := hinv _ γ.2 h
        _ = 0 := hL
    rw [lintegral_eq_zero_iff (hθm.indicator hVm)] at hz
    have : μ V = 0 := by
      refine measure_mono_null (fun g hg => ?_) (ae_iff.1 hz)
      show V.indicator θp g ≠ (0 : HA (AF F) σ J → ℝ≥0∞) g
      rw [indicator_of_mem hg]
      exact (hθpos g hg).ne'
    exact hVpos.ne' this
  have hμ0 : (μ 𝓕).toReal ≠ 0 := by
    refine ENNReal.toReal_ne_zero.2 ⟨fun h0 => hL0 ?_, ((ha.2 μ hμ).2 𝓕 h𝓕).ne⟩
    rw [Measure.restrict_eq_zero.2 h0, lintegral_zero_measure]
  unfold meanC
  rw [hI1]
  refine smul_ne_zero (inv_ne_zero hμ0) ?_
  exact Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨hL0, hfinI⟩)

theorem nuNeZero_of_fin (hFin : ThetaFin) (hS : SWeqOm) (hW : Witt) (hI : InvInv) (hMO : MeasOrb)
    (hMG : MeasGrp) (hTN : TestNear) : NuNeZero :=
  nuNeZero_of hS (thetaPos_of hFin hW hI hMO hMG hTN)

end PI.VolStabS
