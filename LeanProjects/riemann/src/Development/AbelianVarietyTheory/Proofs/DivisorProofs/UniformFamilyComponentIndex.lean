import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPinnedOfIsUnf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightTranslationLiftEqLevelMoveUnitConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodCoordinatesFrameRationalIsometry

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp GlobalTheory.FrameUnif
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

namespace GlobalTheory.GeoLevel

set_option maxHeartbeats 1000000 in

theorem moveMatch_of_markRel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ), Formalism.L2.PjFree.GoodEmb c σ → 1 ≤ Dw.p + Dw.q → l.A = 1 → Pinned U e F ik φ → ∀ (k k' : U.Comp) (δ : GL (Fin r) E) (h : IsMatch (U.X k) (U.X k') δ) (γ : Dw.La →ₗ[𝓞 E] Dw.La) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ), MarkRel l (φ k) (φ k') (F.t (ik k)) (F.t (ik k')) γ δ → IsLevMove ρ ν γ LinearMap.id → MoveMatch U U k k' h ρ ν := by
  intro E _ _ _ H Dw l Xo c σ r U g e F ik φ hσ hr hA hP k k' δ h γ ρ ν hM hν x y' hm
  obtain ⟨gam, hgam, t₁⟩ := hM
  have e₁ : ∀ a b, (F.Di (ik k')).EF (gam a) (gam b) = (F.Di (ik k)).EF a b := fun a b => by
    apply Int.cast_injective (α := ℚ)
    rw [hP.1, hP.1, hgam, hgam, h.iso, h.xi]
  obtain ⟨P, hPe, p, hy, hd⟩ := hP.2 k x
  obtain ⟨P', hPe', p', hy', hd'⟩ := hP.2 k' ⟨_, h.mem_dom x.2⟩
  obtain ⟨k₁, k₂⟩ := GlobalTheory.DictMove.exp_of_levMove F hr hσ ((GlobalTheory.Relab.relab_good _ H l c σ hσ).2.2.2 Dw g e) hA hν p p'
    gam e₁ t₁ fun v => funext fun j => by
      rw [hPe, hPe', hgam]
      exact GlobalTheory.GeoLevel.perFr_lact_of_isMatch E r _ _ δ h x.1 _ _ _
  refine ⟨by rw [hm.1, hy, hy']; exact k₁, funext fun τ => funext fun i => ?_⟩
  have d0 := GlobalTheory.FibreDeriv.isDerivAt0_comp (hd τ i) ν.φ
  simp only [← k₂] at d0
  rw [hm.2.1]
  exact ((GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ P' p').2.1 _).unique d0 (hd' τ i)

end GlobalTheory.GeoLevel
