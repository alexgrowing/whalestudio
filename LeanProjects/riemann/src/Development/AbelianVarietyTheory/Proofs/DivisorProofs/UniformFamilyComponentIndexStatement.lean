import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformFamilyComponentIndex
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPinnedOfIsUnf
open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp GlobalTheory.FrameUnif
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moveMatch_of_markRel_of_isLevMove : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ), Formalism.L2.PjFree.GoodEmb c σ → 1 ≤ Dw.p + Dw.q → l.A = 1 → Pinned U e F ik φ → ∀ (k k' : U.Comp) (δ : GL (Fin r) E) (h : IsMatch (U.X k) (U.X k') δ) (γ : Dw.La →ₗ[𝓞 E] Dw.La) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ), MarkRel l (φ k) (φ k') (F.t (ik k)) (F.t (ik k')) γ δ → IsLevMove ρ ν γ LinearMap.id → MoveMatch U U k k' h ρ ν := by
  first | exact @GlobalTheory.GeoLevel.moveMatch_of_markRel | exact GlobalTheory.GeoLevel.moveMatch_of_markRel | (intros; apply GlobalTheory.GeoLevel.moveMatch_of_markRel <;> assumption)
