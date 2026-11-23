import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitTorsOfGenericLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelLocallyNoetherianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointLiftToFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrallyClosedPointExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisFrameMapStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

theorem charZero_of_pt {R : Type} [CommRing R] [IsDomain R] (F : IntermediateField ℚ ℂ)
    (f : Sp (FractionRing R) ⟶ Sp F) : CharZero R := by
  letI : Algebra F (FractionRing R) := (Spec.preimage f).hom.toAlgebra
  haveI : CharZero (FractionRing R) := charZero_of_injective_algebraMap (algebraMap F (FractionRing R)).injective
  exact (algebraMap R (FractionRing R)).charZero_iff (IsFractionRing.injective R (FractionRing R)) |>.2 inferInstance

theorem htLocSt_of_hodgeTateKernel (hK : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint) : HTLocSt := by
  intro E _ _ _ H Dw l' Xo' c' W Y p _ n _ hstar hpW hA R _ _ _ ξ hgen g e he N a 𝔭 h𝔭
  have hp : p.Prime := Fact.out
  obtain ⟨y, hy⟩ := GlobalTheory.T.generic_point_lift_to_field E H Dw l' Xo' c' W Y p hp hpW R ξ hgen
  haveI : IsLocallyNoetherian Y.X := GlobalTheory.T.integral_model_locally_noetherian E H Dw l' Xo' c' W Y p hp hpW
  haveI : CharZero R := charZero_of_pt c'.F (y ≫ pullback.snd _ _)
  have hS : SplitTors Y.t ξ (p ^ n) :=
    GlobalTheory.T.splitTors_of_generic_level E H Dw l' Xo' c' _ _ Y R ξ y hy (p ^ n) (hA ▸ dvd_rfl)
  have hq : p ^ n ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hF := GlobalTheory.HTMap.ex_full hq hS
  choose κ hκ hW using fun m => GlobalTheory.T.integrally_closed_point_extension E H Dw l' Xo' c' W Y p n hstar hpW hA R ξ y hy (a m)
  choose h' hh' using fun m => GlobalTheory.HTMap.ex_dlog hF (hκ m) he.1
  refine ⟨1, fun m k => algebraMap R _ (-(h' m k)), fun h1 => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h1), ?_⟩
  intro φ yy P π ψ hPt m tt hlev k x hx
  let x0 : R →+* 𝓞_ℂ_[p] := φ.comp (algebraMap R _)
  obtain ⟨P', hP'⟩ := hF ((IsLocalRing.maximalIdeal 𝓞_ℂ_[p]).comap x0) inferInstance
  obtain ⟨b, hb⟩ := P'.ex_gl (hκ m)
  obtain ⟨c, hc⟩ := GlobalTheory.HTMap.ex_char hP' hb
  have hd := hh' m 𝓞_ℂ_[p] x0 P' b hP' hb c hc
  have htan : ∀ i, IsTanAtG Y.t (spMap x0 ≫ ξ) (spMap (dualMap x0) ≫ e i) := (isTanBasis_bc he x0).1
  have hD : ∀ (k : Fin g) (β : P'.B →+* DualNumber (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n})),
      P'.At ((algebraMap 𝓞_ℂ_[p] (DualNumber (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}))).comp x0)
        (spMap (dualMap (Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}))) ≫ spMap (dualMap x0) ≫ e k) β →
      (β b).snd = Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}) (x0 (h' m k)) := by
    intro k β hβ
    let w := GlobalTheory.HTMap.mkPt (G := Y.t.G) _ (hβ.over.trans (GlobalTheory.HTMap.spc_assoc _ _ _).symm)
    have h2 := hd _ _ (GlobalTheory.HTMap.comb_single htan k) w rfl
    rw [hc _ w β hβ] at h2
    rw [h2]
    simp [Pi.single_apply]
  have key := GlobalTheory.T.tangent_basis_frame_map E H Dw l' Xo' c' W Y p n R ξ g e he P' (κ m) b hb x0 hP' yy P π ψ hPt
    (hK p ℂ_[p] Valued.v 𝓞_ℂ_[p] (𝓞 E) P).1 tt (hW m P' b hb x0 yy P π ψ hPt tt hlev) (fun k => x0 (h' m k)) hD
    k x hx
  have e1 : φ (algebraMap R _ (-(h' m k))) - (P.al₀ tt).1 x = -(x0 (h' m k) + (P.al₀ tt).1 x) := by
    simp only [x0, RingHom.comp_apply, map_neg]; ring
  rw [e1]
  exact neg_mem key

end GlobalTheory.FlatModel
