import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFrameProperties
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMatrixOfIsLattice

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

namespace GlobalTheory.StairFrameFJ

private theorem isIntegral_sqrtMinusD' (D : D7) : IsIntegral ℤ D.host.sqrtMinusD := by
  refine IsIntegral.of_pow (n := 2) two_pos ?_
  have hsq : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := by
    unfold Host.sqrtMinusD
    exact D.host.sqd_sq
  rw [hsq]
  refine IsIntegral.neg ?_
  simpa using (isIntegral_algebraMap (R := ℤ) (A := D.host.E) (x := (D.host.d : ℤ)))

theorem isIntegral_inv_neg_xi0 (D : D7) : IsIntegral ℤ (-D.host.xi0)⁻¹ := by

  unfold Host.xi0
  rw [neg_div, neg_neg, one_div, inv_inv]
  refine IsIntegral.mul ?_ (isIntegral_sqrtMinusD' D)
  simpa using (isIntegral_algebraMap (R := ℤ) (A := D.host.E) (x := ((Ideal.absNorm D.host.ccK : ℕ) : ℤ)))

private theorem mem_integer_of_isIntegral_int {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {y : k} (hy : IsIntegral ℤ y) : y ∈ 𝒪[k] := by
  have h2 : IsIntegral 𝒪[k] y := hy.tower_top
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  exact hz ▸ z.2

theorem exists_inv {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.FinPl.SplitPt D k) {x : D.host.E} (hx : x ≠ 0) (h : IsIntegral ℤ x⁻¹) :
    ∃ u : 𝒪[k], (u : k) * p.pr (incA D x) = 1 := by
  have hy : IsIntegral ℤ (p.pr (incA D x⁻¹)) := h.map ((p.pr.comp (incA D)).toIntAlgHom)
  refine ⟨⟨_, mem_integer_of_isIntegral_int hy⟩, ?_⟩
  show p.pr (incA D x⁻¹) * p.pr (incA D x) = 1
  rw [← map_mul, ← map_mul, inv_mul_cancel₀ hx, map_one, map_one]

theorem exists_frame : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h' : 2 * σ + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0,
  ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k)
    (p : GlobalTheory.FinPl.SplitPt D k) (β : GlobalTheory.FinPl.Frame p (G.V (.grid (2 * σ + 2) 0)) (Fin (G.V (.grid (2 * σ + 2) 0)).rank))
    (j : Fin (2 * σ + 2 - 1) → Fin (G.V (.grid (2 * σ + 2) 0)).rank) (ϖ : 𝒪[k]),
  p.v = v ∧ Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v) ∧
  β.IsLat (G.Λ (.grid (2 * σ + 2) 0)) (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)) ∧
  IsLocalRing.maximalIdeal 𝒪[k] = Ideal.span {ϖ} ∧
  (∃ u : 𝒪[k], (u : k) * p.pr (incA D (-D.host.xi0)) = 1) ∧
  (∃ u : 𝒪[k], (u : k) * p.pr (incA D (star (-D.host.xi0))) = 1) ∧
  Function.Injective j ∧
  (∀ r i, β.b i (j r) = (ϖ : k) ^ (G.pl.depth sc v * (r.1 + 1)) * p.pr (incA D ((G.colDec (2 * σ + 2) (by omega) h').a i r))) ∧
  (∀ m, m ∉ Set.range j → ∀ r, ((fun i => p.pr (incA D (star ((G.colDec (2 * σ + 2) (by omega) h').a i r)))) ᵥ* (((G.V (.grid (2 * σ + 2) 0)).gram.map (fun c => p.pr (incA D c))) * β.b)) m = 0) := by
  unfold OnStd All
  intro D hq T L μ₀ hL sc G W M _ F _ σ h' v hv
  obtain ⟨k, _, _, _, _, p, hpv, hpe⟩ := GlobalTheory.LatticeMembershipValuation.exists_splitPoint_at_S0 G.pl hv
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  obtain ⟨β, j, hβ, hj, hcol, horth⟩ := GlobalTheory.LatticeMembershipValuation.exists_stairFrame (p := p) hq hL G hv (2 * σ + 2) (by omega) h'
    hpv hpe hϖ
  have hx0 : D.host.xi0 ≠ 0 := by
    exact GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  have hs : IsIntegral ℤ (star (-D.host.xi0))⁻¹ := by
    have h1 : IsIntegral ℤ (star (-D.host.xi0)⁻¹) :=
      (isIntegral_inv_neg_xi0 D).map ((starRingEnd D.host.E).toIntAlgHom)
    rwa [star_inv₀] at h1
  refine ⟨k, inferInstance, inferInstance, inferInstance, inferInstance, p, β, j, ϖ, hpv, hpe, hβ,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ,
    exists_inv p (neg_ne_zero.2 hx0) (isIntegral_inv_neg_xi0 D),
    exists_inv p (star_ne_zero.2 (neg_ne_zero.2 hx0)) hs, hj, hcol, ?_⟩
  intro m hm r
  have hmr := horth m hm r
  have hf : (fun x => p.pr (incA D x)) = ⇑(p.pr.comp (incA D)) := rfl
  rw [hf, Matrix.map_mul, Matrix.mul_assoc] at hmr
  simpa [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply] using hmr

end GlobalTheory.StairFrameFJ
