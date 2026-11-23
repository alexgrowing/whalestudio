import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecValAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelEmbeddingFirstStatement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Formalism.LocalToGlobal.ProjectiveLattices.SatLeaves
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartFlagBaseHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFrameBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OverInclusionBaseChangeModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointModelOverDvrStatement

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel.DetUnit

theorem isUnit_det_of_factor {R : Type} [CommRing R] {m g : ℕ} (h U : Fin m → Fin g → R)
    (M : Matrix (Fin m) (Fin m) R) (C : Fin m → Fin g → R) (hU : ∀ k b, U k b = ∑ j, M k j * C j b)
    (hP : IsUnit (pairDet h U)) : IsUnit M.det := by
  have e : (Matrix.of fun k k' : Fin m => ∑ b, h k' b * U k b) =
      M * Matrix.of (fun j k' => ∑ b, C j b * h k' b) := by
    ext k k'
    simp only [Matrix.of_apply, Matrix.mul_apply, hU, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => by ring
  rw [pairDet, e, Matrix.det_mul] at hP
  exact isUnit_of_mul_isUnit_left hP

theorem det_isUnit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c) (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle → ∀ (σ : E →+* ℂ) (A : Type) [CommRing A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A), ξ ≫ Y.s = spMap β → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)) (U h : Fin (Dw.mult σ) → Fin g → A), IsTanBasis Y.t ξ e → (∀ (S : Type) [CommRing S] (φ : A →+* S), EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W σ))) (bcV Y.t φ e) (fun k b => φ (U k b))) → IsUnit (pairDet h U) → ∀ (T : CDVR) (α : A →+* T.V) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io) (yy : Sp T.Fr ⟶ Xo'.XF c'), yy ≫ Y.j = spMap ((algebraMap T.V T.Fr).comp α) ≫ ξ → (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y₀.1 = yy ≫ r) → ∀ (w : Fin (Dw.mult σ) → (Sp (DualNumber T.Fr) ⟶ Y.oF.t.G.left)) (gm : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr), (∀ i, IsCombAtG Y.t (yy ≫ Y.j) (bcV Y.t ((algebraMap T.V T.Fr).comp α) e) (fun b => (algebraMap T.V T.Fr).comp α (U i b)) (w i ≫ Y.m.φ)) → (letI := io.toAlgebra; ∀ i, IsCombAt y₀.1.x (y₀.1.u σ) (gm i) (w i ≫ ν.φ)) → ∃ u : T.Vˣ, algebraMap T.V T.Fr u = gm.det := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν hle hOI σ A _ ξ β hξ g e U h he hU hP T α io y₀ yy hyy hpt w gm hw hgmC
  letI := io.toAlgebra
  have hyV : yy ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ (spMap α ≫ ξ) := by rw [hyy, sp_sp]
  obtain ⟨v, hvt, hvb, hvg⟩ := GlobalTheory.T.integral_point_model_over_dvr E H Dw l l' Xo Xo' c c' W Y r ν σ T io y₀ (spMap α ≫ ξ) yy hyV hpt
  have he' := isTanBasis_bc he α
  have hchar := GlobalTheory.T.overInclusion_base_change_model E H Dw l l' Xo Xo' c c' W Y r hle hOI σ A ξ β hξ T.Fr ((algebraMap T.V T.Fr).comp α) io y₀.1 yy
    hyy hpt
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective T.V T.Fr
  choose u hut hu using fun k : Fin (Dw.mult σ) =>
    GlobalTheory.ShFam.Pad.Guard.exists_comb he'.1 (fun b => α (U k b))
  have hue : ∀ k (a : 𝓞 E) (z : T.V), algebraMap T.V T.Fr z = io (embK c σ a) →
      u k ≫ (Y.t.act.act a).left = spMap (epsMul z) ≫ u k := by
    intro k a z hz
    have hz' : z = α (β (embV c' W σ a)) := hinj (by rw [hz, ← hchar a]; rfl)
    subst hz'
    exact (hU T.V α) k (u k) (hu k) a
  choose M hM using fun k => hvb (u k) (hut k) (hue k)
  choose C hC using fun j => (he.2 T.V α (v j) (hvt j)).exists
  have hrel : ∀ k b, α (U k b) = ∑ j, M k j * C j b := by
    intro k b
    have h1 : IsCombAtG Y.t (spMap α ≫ ξ) (bcV Y.t α e) ((Matrix.of fun b j => C j b).mulVec (M k)) (u k) :=
      tanLinG (bcV Y.t α e) he'.1 v (Matrix.of fun b j => C j b) (M k) (u k) (fun j => hC j) (hM k)
    have h2 := congrFun ((he.2 T.V α (u k) (hut k)).unique (hu k) h1) b
    rw [h2]
    simp [Matrix.mulVec, dotProduct, mul_comm]
  have hwu : ∀ k, w k ≫ Y.m.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ u k := by
    intro k
    have h2 := GlobalTheory.LocM.Cht.FlagBase.isCombAtG_bc Y.t (algebraMap T.V T.Fr) (hu k)
    have h3 := hw k
    rw [hyV] at h3
    have e1 : (fun j => spMap (dualMap (algebraMap T.V T.Fr)) ≫ bcV Y.t α e j) =
        bcV Y.t ((algebraMap T.V T.Fr).comp α) e := bcV_bcV (t := Y.t) α (algebraMap T.V T.Fr) e
    rw [e1] at h2
    exact GlobalTheory.FlatModel.LiftBC.isCombAtG_unique Y.t h3 h2
  have hgm : ∀ k, gm k = fun j => algebraMap T.V T.Fr (M k j) := by
    intro k
    have hte := GlobalTheory.T.integral_model_embedding_first E H Dw l l' Xo Xo' c c' W Y r ν hle hOI σ A ξ β hξ g (Dw.mult σ) e U he hU T.Fr
      ((algebraMap T.V T.Fr).comp α) io y₀.1 yy hyy hpt k (w k) (hw k)
    exact (y₀.1.basis σ (w k ≫ ν.φ) hte.1 hte.2).unique (hgmC k) (hvg (M k) (u k) (w k) (hM k) (hwu k))
  have hP' : IsUnit (pairDet (fun k b => α (h k b)) (fun k b => α (U k b))) := by
    have e2 : α (pairDet h U) = pairDet (fun k b => α (h k b)) (fun k b => α (U k b)) := by
      rw [pairDet, pairDet, RingHom.map_det]
      congr 1
      ext k k'
      simp [map_sum]
    exact e2 ▸ hP.map α
  have hMu : IsUnit (Matrix.of M).det :=
    isUnit_det_of_factor _ _ (Matrix.of M) C (fun k b => hrel k b) hP'
  refine ⟨hMu.unit, ?_⟩
  rw [IsUnit.unit_spec, RingHom.map_det]
  congr 1
  ext k j
  simp [hgm k]

end GlobalTheory.FlatModel.DetUnit
