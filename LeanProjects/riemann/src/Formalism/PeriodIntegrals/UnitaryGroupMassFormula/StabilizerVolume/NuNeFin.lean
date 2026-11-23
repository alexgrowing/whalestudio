import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.NuNePos
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoMeas

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Set
open scoped TensorProduct ENNReal Pointwise

theorem thetaFin_of (hLam : LamEx) (hFV : FinVolStab) (hIS : InvStab) (hAC : AdmCpt)
    (hFD : ExFDStab) (hW : Witt) (hI : InvInv) (hMO : MeasOrb) (hMG : MeasGrp) : ThetaFin := by
  intro F E _ _ _ _ _ σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet μ hμ 𝓕 h𝓕 φ hφ0 hadm
  haveI : MeasurableMul (HA (AF F) σ J) := (hMG F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet).1
  haveI : MeasurableInv (HA (AF F) σ J) := (hMG F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet).2
  haveI : μ.IsHaarMeasure := hμ
  haveI : μ.IsInvInvariant := (hI F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet).1 μ hμ
  haveI : Countable (HFinIn (AF F) σ J) := um_countable_HFinIn F E σ M J
  haveI hΓc : Countable (GamA σ J) := um_countable_HFinIn F E σ M J
  obtain ⟨lam, μ'', hμ''H, hC, hLK⟩ := hLam F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet μ hμ
  haveI : μ''.IsHaarMeasure := hμ''H
  haveI : μ''.IsInvInvariant := hIS F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet μ'' hμ''H
  obtain ⟨𝓕'', h𝓕''⟩ := hFD F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet μ'' hμ''H
  obtain ⟨e, he⟩ := gram_orbit_equiv σ J X0 (hW F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet)
  have hmφ : Measurable fun g : HA (AF F) σ J => φ (g • ratTup (F := F) (AF F) X0) := by
    have := hMO F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet _ hadm
    have h2 := Complex.measurable_re.comp this
    simp only [Function.comp_def, Complex.ofReal_re] at h2
    exact h2
  have hφm : Measurable φ := by
    have h1 := TopoMeas.measurable_adm _ hadm
    have h2 := Complex.measurable_re.comp h1
    simp only [Function.comp_def, Complex.ofReal_re] at h2
    exact h2
  have key : ∫⁻ h in 𝓕, ∑' x : orbS (GamA σ J) (ratTup (F := F) (AF F) X0),
        ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))) ∂μ =
      μ'' 𝓕'' * ∫⁻ X, ENNReal.ofReal (φ X) ∂lam :=
    unfold_abs (Γ := GamA σ J) (H := stabT (AF F) σ J X0) μ μ'' (ratTup (F := F) (AF F) X0)
      (fun k => MulAction.mem_stabilizer_iff) lam (fun X => ENNReal.ofReal (φ X))
      hφm.ennreal_ofReal.aemeasurable hmφ.ennreal_ofReal hC.1 hC.2 𝓕 h𝓕 𝓕'' h𝓕''
  have hθS : ∀ h : HA (AF F) σ J, ∑' x : orbS (GamA σ J) (ratTup (F := F) (AF F) X0),
        ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))) =
      ∑' X : {X : Fin a → Fin M → E | gramE σ J X = gramE σ J X0},
        ENNReal.ofReal (φ (h⁻¹ • ratTup (F := F) (AF F) (X : Fin a → Fin M → E))) := by
    intro h
    rw [← e.tsum_eq (fun x => ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))))]
    exact tsum_congr fun X => by rw [he X]
  have lamfin : ∫⁻ X, ENNReal.ofReal (φ X) ∂lam < ⊤ := by
    obtain ⟨K, hK, C, hb⟩ := hAC F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet φ hφ0 hadm
    calc ∫⁻ X, ENNReal.ofReal (φ X) ∂lam
        ≤ ∫⁻ X, K.indicator (fun _ => ENNReal.ofReal C) X ∂lam := lintegral_mono fun X => by
          by_cases hX : X ∈ K
          · rw [indicator_of_mem hX]; exact ENNReal.ofReal_le_ofReal (hb X).1
          · rw [indicator_of_notMem hX]; simp [(hb X).2 hX]
      _ ≤ ENNReal.ofReal C * lam K := lintegral_indicator_const_le K _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hLK K hK)
  rw [← lintegral_congr hθS, key]
  exact ENNReal.mul_lt_top (hFV F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet μ'' hμ''H 𝓕'' h𝓕'') lamfin

theorem nuNeZero_of_route (hLam : LamEx) (hFV : FinVolStab) (hIS : InvStab) (hAC : AdmCpt)
    (hFD : ExFDStab) (hS : SWeqOm) (hW : Witt) (hI : InvInv) (hMO : MeasOrb) (hMG : MeasGrp)
    (hTN : TestNear) : NuNeZero :=
  nuNeZero_of_fin (thetaFin_of hLam hFV hIS hAC hFD hW hI hMO hMG) hS hW hI hMO hMG hTN

end PI.VolStabS
