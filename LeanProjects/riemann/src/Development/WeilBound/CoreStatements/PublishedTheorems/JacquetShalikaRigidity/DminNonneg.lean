import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace PKIR

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem dt_pos (g : GA E k) : 0 < Dt g := (GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det g)).2

theorem ht_nonneg (g : GA E k) (ξ : Fin k → E) : 0 ≤ ht g ξ :=
  div_nonneg (height_nonneg _ _) (Real.rpow_nonneg (dt_pos g).le _)

theorem dmin_nonneg (g : GA E k) : 0 ≤ dmin g := by
  unfold dmin
  exact Real.iInf_nonneg fun ξ => ht_nonneg g ξ.1

theorem wt_nonneg (M : ℕ) (g : GA E k) : 0 ≤ wt M g := by
  unfold wt
  exact pow_nonneg (le_min zero_le_one (dmin_nonneg g)) M

end PKIR

theorem kir_of : jumpWindows.S2 → jumpWindows.G0 → jumpWindows.G2a → jumpWindows.G2c → jumpWindows.G5 → jumpWindows.G5b → K2 → K3 → K4 → K9 → KIR := by
  intro hS2 hG0 hG2a hG2c _hG5 hG5b hK2 hK3 hK4 hK9 E _ _ _ k hk ψ hψ hcof π hπ
  obtain ⟨S₀, hS₀⟩ := hK9 E k hk ψ hψ hcof π hπ
  refine ⟨S₀, fun S hS α hα M j hj U hU Y hYc hYi hYπ => ?_⟩
  obtain ⟨_hcond, h9⟩ := hS₀ S hS
  obtain ⟨φ, hφ, h, x, hhS, hx, hsat, hlev, hwh⟩ := h9 α hα
  obtain ⟨ρ, J, hW, hsm⟩ := hK2 E k hk M
  obtain ⟨x₀, hx₀, hsm₀⟩ := hK3 E k hk M ρ J hW π hπ φ hφ
  have hJx₀ : J x₀ = x := DFunLike.coe_injective (hx₀.trans hx.symm)

  obtain ⟨_, _, _, hSg, hST, _⟩ := hS2 _ k (XB E k) (ρ.comp (infGL E k)) hW.poly
  obtain ⟨g1, g2, _, _, _, _, g7, _⟩ := hG0 E k
  have hsm1 : SmV (ρ.comp (infGL E k)) (ρ h x₀) := by
    set y := cInf h
    set hf := (infGL E k y)⁻¹ * h
    have hcf : cInf hf = 1 := by simp only [hf, map_mul, map_inv, g1, y, inv_mul_cancel]
    have hc : ∀ (g : GL (Fin k) (Cinf E)) z, ρ hf ((ρ.comp (infGL E k)) g z) = (ρ.comp (infGL E k)) g (ρ hf z) := by
      intro g z
      simp only [MonoidHom.comp_apply]
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, g7 hf hcf g, map_mul, ContinuousLinearMap.mul_apply]
    have := hSg y _ (hST (ρ hf) hc x₀ hsm₀)
    simpa only [MonoidHom.comp_apply, ← ContinuousLinearMap.mul_apply, ← map_mul, hf, mul_inv_cancel_left] using this

  obtain ⟨Yg, hYgc, hYgi, hYgm⟩ := hG2a E k ψ hψ
  have hw := fun w : Off E S => hG2c E k w.1 (Finset.univ.val.map (α w)) (by simp)
  choose Yw hYwc hYwi hYwm using hw
  set Y' : Submodule ℂ (XB E k) := Y ⊓ Yg ⊓ ⨅ w, Yw w with hY'
  have hmem : ∀ z, z ∈ Y' ↔ (z ∈ Y ∧ z ∈ Yg) ∧ ∀ w, z ∈ Yw w := fun z => by
    simp only [Y', Submodule.mem_inf, Submodule.mem_iInf]
  have hYOK : YOK ψ S Y' := by
    refine ⟨?_, ?_, ?_⟩
    · rw [Submodule.coe_inf, Submodule.coe_inf, Submodule.coe_iInf]
      exact (hYc.inter hYgc).inter (isClosed_iInter hYwc)
    · intro g hg z hz
      rw [hmem] at hz ⊢
      exact ⟨⟨hYi g z hz.1.1, hYgi g z hz.1.2⟩, fun w => hYwi w g (hg w.1 w.2) z (hz.2 w)⟩
    · intro z hz
      exact ((hYgm z).1 ((hmem z).1 hz).1.2).1
  have hcusp := π.cusp φ hφ
  have hxY' : Rt E k h x ∈ Y' := by
    have hxg : x ∈ Yg := by
      refine (hYgm x).2 ⟨?_, fun γ g => ?_⟩
      · rw [hx]; exact GlobalTheory.T.isMirabolicWhittakerStage_of_isCuspForm E k ψ φ hcusp
      · rw [congrFun hx, congrFun hx]; exact hcusp.1.left γ g
    rw [hmem]
    exact ⟨⟨hYi h x (hYπ x ⟨φ, hφ, hx⟩), hYgi h x hxg⟩,
      fun w => hYwi w h (hhS w.1 w.2) x ((hYwm w x).2 (hsat w))⟩
  have hJ1 : J (ρ h x₀) = Rt E k h x := by rw [hW.inter, hJx₀]
  obtain ⟨x', C, hCU, hx'Y, hsm', hlev', hBlk, hBump⟩ := hK4 E k (wt M) ρ J hW ψ hψ S Y' hYOK j hj U hU (ρ h x₀)
    (hJ1 ▸ hxY') hsm1 (hJ1 ▸ (hG5b E k S).2.1 h x hlev) (hJ1 ▸ hwh)
  obtain ⟨⟨hx'1, hx'2⟩, hx'3⟩ := (hmem _).1 hx'Y
  obtain ⟨hgood, hinv⟩ := (hYgm _).1 hx'2
  refine ⟨J x', hx'1, ⟨hgood, hinv, fun w => (hYwm w _).1 (hx'3 w), hsm x' hsm', hlev', ?_, ⟨C, hCU, hBlk, hBump⟩⟩⟩
  refine ⟨‖x'‖, fun g => ?_⟩
  have hw0 := PKIR.wt_nonneg M g
  rw [hW.mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hw0, mul_comm ‖x'‖]
  exact mul_le_mul_of_nonneg_left (x'.norm_coe_le_norm g) hw0

end PositivityTheory.AdelicQuotientData

end
