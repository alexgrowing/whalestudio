import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsBasisMem
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.GramDetDivIndexEqOfSpanEqStatement

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.SubspaceHeight

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem det_gram_reindex {r : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : κ ≃ ι) (A : Matrix (Fin r) (Fin r) ℂ) (f : ι → Fin r → ℂ) :
    ((A * (Matrix.of fun k a => f (e a) k))ᴴ * (A * (Matrix.of fun k a => f (e a) k))).det =
      ((A * (Matrix.of fun k a => f a k))ᴴ * (A * (Matrix.of fun k a => f a k))).det := by
  rw [← Matrix.det_submatrix_equiv_self e]
  congr 1

theorem exists_height : (∀ (r : ℕ) (X : Data E r), ∃ d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ, (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ)))) := by
  intro r X
  choose b hb hΛ hsp using GlobalTheory.LatBasis.exists_basis_mem r X
  refine ⟨fun x W => ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (b W a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (b W a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range (b W))).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range (b W))).toAddSubgroup)) : ℝ)), ?_⟩
  intro x _ ι _ _ w hw hwΛ
  have hc : Module.finrank E (Submodule.span E (Set.range w)) = Fintype.card ι :=
    finrank_span_eq_card hw
  let e : Fin (Module.finrank E (Submodule.span E (Set.range w))) ≃ ι :=
    (Fintype.equivFinOfCardEq hc.symm).symm
  have hr : Set.range (fun a => w (e a)) = Set.range w := e.surjective.range_comp w
  have key := GlobalTheory.T.gramDet_div_index_eq_of_span_eq r X x _ (b (Submodule.span E (Set.range w))) (fun a => w (e a))
    (hb _) (hΛ _) (hw.comp e e.injective) (fun a => hwΛ _) (by rw [hr, hsp])
  refine key.trans ?_
  rw [hr]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  exact congrArg Complex.re (det_gram_reindex e _ (fun a k => τ.1 (w a k)))

end GlobalTheory.SubspaceHeight
