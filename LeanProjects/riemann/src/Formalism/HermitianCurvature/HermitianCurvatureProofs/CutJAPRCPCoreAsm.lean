import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCoreCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSLMat

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP

noncomputable section

theorem glc_single (k r : ℕ) (a b : Fin (k + 1)) : GLc k r (Matrix.single (wI k r a) (wI k r b) 1) := by
  have hm : mdim k r (Fin.last r) = k + 1 := by simp [mdim]
  have h := Formalism.FourierDecayAlt.P.Qx2.hpart_lev (k := k) (r := r) (Fin.last r) (Fin.cast hm.symm a) (Fin.cast hm.symm b)
  have ea : posL k r (Fin.last r) (Fin.cast hm.symm a) = wI k r a := by
    ext; simp [posL, wI, Fin.val_last]; omega
  have eb : posL k r (Fin.last r) (Fin.cast hm.symm b) = wI k r b := by
    ext; simp [posL, wI, Fin.val_last]; omega
  rw [ea, eb] at h
  exact h

theorem radSp_smoothLev {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
    [NormedSpace ℂ Wq] {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Q.Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} (Φ : Q.RadSp k r z z' π π') {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    Q.SmoothLev k r (Fin.last r) (Dp k r z z') ((Φ : Q.Fn k r (Wq →L[ℂ] Wp)) c) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := Φ.2.2.1 (c, g₀) ⟨hc, hg₀.1, hg₀.2⟩
  refine ⟨{g | (c, g) ∈ U}, fun g => F (c, g), hU.preimage (continuous_const.prodMk continuous_id), hxU, ?_, ?_⟩
  · exact hF.comp (contDiffOn_const.prodMk contDiffOn_id) (fun g hg => hg)
  · intro g hg hgl
    exact hΦ (c, g) hg hgl

theorem psv_congr {TT : ℝ} {V : Type*} [AddCommGroup V] [Module ℂ V] {f g : ℂ → V} (hf : PSV TT f)
    (h : ∀ ζ : ℂ, TT < Complex.normSq ζ → g ζ = f ζ) : PSV TT g := by
  obtain ⟨n, a, v, ha, hfe⟩ := hf
  exact ⟨n, a, v, ha, fun ζ hζ => by rw [h ζ hζ]; exact hfe ζ hζ⟩

theorem psv_sum {TT : ℝ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (hadd : ∀ f g : ℂ → V, PSV TT f → PSV TT g → PSV TT (fun ζ => f ζ + g ζ)) (h0 : PSV TT (fun _ => (0 : V)))
    {ι : Type*} (s : Finset ι) (F : ι → ℂ → V) (hF : ∀ i ∈ s, PSV TT (F i)) :
    PSV TT (fun ζ => ∑ i ∈ s, F i ζ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | @insert a s ha ih =>
    have := hadd _ _ (hF a (Finset.mem_insert_self a s)) (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))
    refine psv_congr this fun ζ _ => ?_
    simp [Finset.sum_insert ha]

theorem radial_polynomial_of_truncation : CorePolyOfCut := by
  intro hT hW hC Wp Wq _ _ _ _ _ _ P Bs hpl hk hsec Φ X₀ hX c hc Y
  have hTz : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := Gauge.GC.tz_TT P Bs hpl
  obtain ⟨n, κ, w, hκ, hw, hid⟩ := hT P.k P.r Bs.z Bs.z' Bs.k_pos Bs.z_mem Bs.z'_mem Bs.T_pos Bs.T'_pos Y
  rw [hTz] at hκ
  have hsm := radSp_smoothLev Φ hc
  have hwords : ∀ i, PSV P.TT (fun ζ =>
      wordR (w i) ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c) (NF.muZ P.k P.r Bs.μsec ζ)) := by
    intro i
    refine hW Wp Wq P Bs hpl hk hsec Φ X₀ hX c hc (w i) (fun Z hZ => ?_)
    obtain ⟨a, b, rfl⟩ := hw i Z hZ
    exact glc_single P.k P.r a b
  have hTT : 0 < P.TT := by rw [← hTz]; exact mul_pos Bs.T_pos Bs.T'_pos
  obtain ⟨-, -, -, -, -, -, -, hV⟩ := hC P.TT hTT
  obtain ⟨hadd, hsmul, -, -, hconst⟩ := hV (Wq →L[ℂ] Wp) (Wq →L[ℂ] Wp)
  have hsum := psv_sum hadd (hconst 0) Finset.univ
    (fun i ζ => κ i ζ • wordR (w i) ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c) (NF.muZ P.k P.r Bs.μsec ζ))
    (fun i _ => hsmul _ _ (hκ i) (hwords i))
  refine psv_congr hsum fun ζ hζ => ?_
  have hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by rw [hTz]; exact hζ
  have := hid (Wq →L[ℂ] Wp) ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c) hsm ζ hζ'
  simp only [mu0] at this
  rw [hsec]
  exact this

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP
