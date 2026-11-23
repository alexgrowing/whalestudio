import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGaugeLinesCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepDatumUnit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLAtMost

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.PRho.GL

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep in
theorem gauge_left_line_holds : GLLeft := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk ζ hζ Fr hFr
  obtain ⟨-, hz, hz', hTz, hTz', -, -⟩ := hpl
  have hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
    rw [hTz, hTz']; exact hζ
  set μ := NF.muZ P.k P.r Bs.μsec ζ with hμ
  have hm := NFRadRedA.muZ_uwb Bs.sec hζ'
  have hG := NFRadRedA.uwb_glev hm
  have hU : μ ∈ UH (Hpk P.k P.r) := hG.1
  have hGi := FrameEntries.glev_inv hG
  have hUi : μ⁻¹ ∈ UH (Hpk P.k P.r) := hGi.1
  have hT := Bs.T_pos

  set y := μ *ᵥ Bs.z' with hydef
  have hy : inWb P.k P.r y := Qx8.inWb_mulVec hG hz'
  have hyz : herm (Hpk P.k P.r) y Bs.z = ζ := by
    rw [← NFRadRedA.zeta_eq]; exact NFRadRedA.zeta_muZ hz hz' Bs.sec hζ'
  have hyy : herm (Hpk P.k P.r) y y = -((Tz P.k P.r Bs.z' : ℝ) : ℂ) := by
    rw [Qx2.herm_uh hU, FrameEntries.herm_self]
  have hpos : 0 < Complex.normSq ζ / Tz P.k P.r Bs.z - Tz P.k P.r Bs.z' := by
    rw [sub_pos, lt_div_iff₀ hT]; linarith
  set p := SSn.prWv P.k P.r Bs.z y with hpdef
  have hpp := DU.prWv_norm hT hy hyy hyz
  have hre : (herm (Hpk P.k P.r) p p).re = Complex.normSq ζ / Tz P.k P.r Bs.z - Tz P.k P.r Bs.z' := by
    rw [hpp]; simp
  have hν : SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ =
      (((Real.sqrt (Complex.normSq ζ / Tz P.k P.r Bs.z - Tz P.k P.r Bs.z'))⁻¹ : ℝ) : ℂ) • p := by
    show SSn.unitH P.k P.r p = _
    unfold SSn.unitH
    rw [hre]
  have hsne : (((Real.sqrt (Complex.normSq ζ / Tz P.k P.r Bs.z - Tz P.k P.r Bs.z'))⁻¹ : ℝ) : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt (Complex.normSq ζ / Tz P.k P.r Bs.z - Tz P.k P.r Bs.z') := Real.sqrt_pos.2 hpos
    exact_mod_cast (inv_pos.2 this).ne'

  have hFz : ∀ a, herm (Hpk P.k P.r) (Fr a) Bs.z = 0 := fun a => hFr.2.2 a Bs.z (by simp)
  have hFy : ∀ a, herm (Hpk P.k P.r) (Fr a) y = 0 := by
    intro a
    have h1 : herm (Hpk P.k P.r) (Fr a) (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ) = 0 := hFr.2.2 a _ (by simp)
    rw [hν, DU.hsmul_r] at h1
    have h2 : herm (Hpk P.k P.r) (Fr a) p = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd ((map_eq_zero (starRingEnd ℂ)).1 h) hsne
      · exact h
    rw [hpdef, DU.prWv_of hy, DU.hadd_r, DU.hsmul_r, hFz a, mul_zero, add_zero] at h2
    exact h2
  have hmi : μ⁻¹ * μ = 1 := Gauge.GC.KLAM.inv_mul_uh hU
  have hmm : μ * μ⁻¹ = 1 := Gauge.GC.KLAM.mul_inv_uh hU
  have hz'e : Bs.z' = μ⁻¹ *ᵥ y := by
    rw [hydef, Matrix.mulVec_mulVec, hmi, Matrix.one_mulVec]
  have hF' : Q.IsFrameOf P.k P.r [μ⁻¹ *ᵥ Bs.z, Bs.z'] (fun a => μ⁻¹ *ᵥ Fr a) := by
    refine ⟨fun a => Qx8.inWb_mulVec hGi (hFr.1 a), fun a b => ?_, fun a w hw => ?_⟩
    · rw [Qx2.herm_uh hUi]; exact hFr.2.1 a b
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · rw [Qx2.herm_uh hUi]; exact hFz a
      · rw [hz'e, Qx2.herm_uh hUi]; exact hFy a
  refine ⟨hF', fun X hX w v => ?_⟩
  have hXF : X ∈ Gauge.GC.FibAt P.k P.r Bs.z Bs.z' Bs.π Bs.π' μ :=
    fun h hh h' hh' he => hX (h, h') ⟨hh, hh', he⟩
  have hint := Qx8.capRep_intertwine hF' Bs.π'_rep Bs.π'_cont hU X
    (fun h' hh' hy' u => Gauge.GC.KLAM.fib_intertwine Bs.π_rep hG hXF hh' hy' u) w v
  have hback : (fun a => μ *ᵥ (μ⁻¹ *ᵥ Fr a)) = Fr := by
    funext a
    rw [Matrix.mulVec_mulVec, hmm, Matrix.one_mulVec]
  rw [hint, hback]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.PRho.GL
