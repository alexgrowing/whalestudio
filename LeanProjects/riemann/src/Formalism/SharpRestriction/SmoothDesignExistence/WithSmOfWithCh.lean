import Formalism.SharpRestriction.DesignExistsOfChoices
import Formalism.SharpRestriction.GlobalSchurBounds.AlgebraicJets
import Formalism.SharpRestriction.Divisibility.PrinLevClass
import Formalism.SharpRestriction.LevelLetterCocycles.AlignN
import Formalism.SharpRestriction.AdmissibleParameterJoins.DGamMink
import Formalism.SharpRestriction.SmoothDesignExistence.DesignExistsDes

noncomputable section

namespace Formalism.MainNotions.Pk

open Formalism.BasicNotions

def LLKerE {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), AlgebraicJets.LLKer (Fm.D x i) (Fm.ex x hx i).tw

abbrev WithCh (𝒞 : FamClass) : FamClass :=
  fun Fm => 𝒞 Fm ∧ DGamDvdF Fm ∧ LLKerE Fm ∧ TameDistinctF Fm ∧ (∀ PL, DIV.Align.FanGal Fm PL) ∧ BoxesF Fm ∧ QDRowsF Fm ∧ Fm.CYL ≤ 9

abbrev WithCh0 (𝒞 : FamClass) : FamClass := fun Fm => 𝒞 Fm ∧ LLKerE Fm ∧ (∀ PL, DIV.Align.FanGal Fm PL)

theorem withSm_of_withCh {𝒞 : FamClass} {eps : ℝ} (Fm : FamP eps) (h : WithCh 𝒞 Fm) : WithSm (WithCh 𝒞) Fm :=
  ⟨h, J.dGamSmooth_of_dvd Fm h.2.1⟩

theorem DesignChoices.mono {𝒞 𝒞' : FamClass} {C0 : ℝ} {cT : ℝ → ℝ → ℝ} (h : DesignChoices 𝒞 C0 cT)
    (hs : ∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → 𝒞' Fm) : DesignChoices 𝒞' C0 cT := by
  obtain ⟨ε0, h0, h⟩ := h
  refine ⟨ε0, h0, fun eps he hle K => ?_⟩
  obtain ⟨Fm, CH, C5, Cb, hc, rest⟩ := h eps he hle K
  exact ⟨Fm, CH, C5, Cb, hs Fm hc, rest⟩

theorem DesignChoices.up {𝒞 : FamClass} {C0 : ℝ} {cT : ℝ → ℝ → ℝ} (h : DesignChoices (WithTw (WithCh0 𝒞)) C0 cT) :
    DesignChoices (WithTw (WithSm (WithCh 𝒞))) C0 cT := by
  obtain ⟨ε0, h0, h⟩ := h
  refine ⟨ε0, h0, fun eps he hle K => ?_⟩
  obtain ⟨Fm, CH, C5, Cb, hc, hCH, hL, h5, hb, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := h eps he hle K
  exact ⟨Fm, CH, C5, Cb, ⟨withSm_of_withCh Fm ⟨hc.1.1, a8, hc.1.2.1, a10, hc.1.2.2, a6, a7, a13⟩, hc.2⟩, hCH, hL, h5, hb, a1, a2, a3,
    a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩

theorem kRatE_of {eps : ℝ} {Fm : FamP eps} (h : LLKerE Fm) :
    ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, StandardLatticesGL3.kRat (Fm.D x i) := by
  obtain ⟨x0, h⟩ := h
  exact ⟨x0, fun x hx h1 i => ((AlgebraicJets.llKer_iff _ _).1 (h x hx h1 i)).1⟩

end Formalism.MainNotions.Pk

end
