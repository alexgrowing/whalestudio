import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelPAdicComparisonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BLieLieComb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCombinationLieGroupPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCombAtGBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointOnModelPullbackCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicPointModelAbelianMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackTangentCombinationStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatModel

theorem exists_denom (p : ℕ) [Fact p.Prime] : ∀ (m : ℕ) (d : Fin m → ℂ_[p]), ∃ δ : 𝓞_ℂ_[p],
    (δ : ℂ_[p]) ≠ 0 ∧ ∀ l, (δ : ℂ_[p]) * d l ∈ 𝓞_ℂ_[p] := by
  intro m
  induction m with
  | zero => exact fun d => ⟨1, by simp, fun l => l.elim0⟩
  | succ m ih =>
    intro d
    obtain ⟨δ, hδ, hl⟩ := ih (Fin.tail d)
    by_cases ha : (δ : ℂ_[p]) * d 0 ∈ 𝓞_ℂ_[p]
    · refine ⟨δ, hδ, fun l => ?_⟩
      refine Fin.cases ha (fun l => ?_) l
      exact hl l
    · have hne : (δ : ℂ_[p]) * d 0 ≠ 0 := fun h => ha (h ▸ (𝓞_ℂ_[p]).zero_mem)
      have hinv : ((δ : ℂ_[p]) * d 0)⁻¹ ∈ 𝓞_ℂ_[p] := ((𝓞_ℂ_[p]).mem_or_inv_mem _).resolve_left ha
      refine ⟨δ * ⟨_, hinv⟩, ?_, fun l => ?_⟩
      · change (δ : ℂ_[p]) * ((δ : ℂ_[p]) * d 0)⁻¹ ≠ 0
        exact mul_ne_zero hδ (inv_ne_zero hne)
      · change (δ : ℂ_[p]) * ((δ : ℂ_[p]) * d 0)⁻¹ * d l ∈ 𝓞_ℂ_[p]
        refine Fin.cases ?_ (fun l => ?_) l
        · rw [show (δ : ℂ_[p]) * ((δ : ℂ_[p]) * d 0)⁻¹ * d 0 = 1 by
            rw [_root_.mul_comm (δ : ℂ_[p]), _root_.mul_assoc]; exact inv_mul_cancel₀ hne]
          exact (𝓞_ℂ_[p]).one_mem
        · rw [show (δ : ℂ_[p]) * ((δ : ℂ_[p]) * d 0)⁻¹ * d l.succ = ((δ : ℂ_[p]) * d 0)⁻¹ * ((δ : ℂ_[p]) * Fin.tail d l) by
            simp only [Fin.tail]; ring]
          exact (𝓞_ℂ_[p]).mul_mem _ _ hinv (hl l)

theorem exists_denom_alg : ∀ (p : ℕ) [Fact p.Prime] (m : ℕ) (d : Fin m → ℂ_[p]), ∃ δ : 𝓞_ℂ_[p],
    algebraMap 𝓞_ℂ_[p] ℂ_[p] δ ≠ 0 ∧ ∀ l, ∃ e : 𝓞_ℂ_[p], algebraMap 𝓞_ℂ_[p] ℂ_[p] e = algebraMap 𝓞_ℂ_[p] ℂ_[p] δ * d l := by
  intro p _ m d
  obtain ⟨δ, hδ, hl⟩ := exists_denom p m d
  exact ⟨δ, hδ, fun l => ⟨⟨_, hl l⟩, rfl⟩⟩

set_option maxHeartbeats 1000000 in

theorem htComb_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle →
    ∀ (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] [Algebra c.F ℂ_[p]] (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c')
      (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left) (y : FrPt Xo c ℂ_[p]),
      HTAt Y r ν yb yy P π ψ y →
    ∀ (z : FrPt Xo c ℂ_[p]) (gm : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ_[p]) (am : ℂ_[p])
      (x : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → LieG P.Gt), GlobalTheory.Frames.FrChg gm am z y →
      (∀ τ j, LieTie P (ψ ≫ ν.φ) (x τ j) (z.u τ j)) →
    ∀ (β : c'.V W →+* 𝓞_ℂ_[p]), yb ≫ Y.s = spMap β →
    ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left)), IsTanBasis Y.t yb e →
    ∀ (xb : Fin g → LieG P.Gt), (∀ b, ITie P π (xb b) (e b)) →
    ∀ (σ : E →+* ℂ) (U : Fin g → 𝓞_ℂ_[p]), (∀ u, IsCombAtG Y.t yb e U u → IsEigG Y.t (β.comp (embV c' W σ)) u) →
    ∃ (w : Sp (DualNumber ℂ_[p]) ⟶ Y.oF.t.G.left) (cf : Fin (Dw.mult σ) → ℂ_[p]),
      IsCombAtG Y.t (yy ≫ Y.j) (bcV Y.t (algebraMap 𝓞_ℂ_[p] ℂ_[p]) e) (fun b => (U b : ℂ_[p])) (w ≫ Y.m.φ) ∧
      IsCombAt y.x (y.u σ) cf (w ≫ ν.φ) ∧
      ∑ b, (U b : ℂ_[p]) • P.bLie (xb b) = ∑ j, cf j • ∑ l, gm σ j l • P.bLie (x σ l) := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν hle hOI p _ _ _ yb yy P π ψ y hHT z gm am x hchg hx β hβ g e _ xb hxb σ U hU
  obtain ⟨hPt, hTs, hptF, hHC⟩ := hHT
  obtain ⟨u0, hu0c, hu0t⟩ := GlobalTheory.T.exists_combination_lie_group_pullback E H Y.X Y.t p P yb π hPt.2.1 g e xb hxb U
  have hu0e := hU u0 hu0c
  obtain ⟨w, hw1, hw2, hw3, hwt⟩ := GlobalTheory.T.point_on_model_pullback_compatible E H Dw l' Xo' c' W Y p yb yy P π ψ hPt _ u0 hu0t
  have hbc := GlobalTheory.T.isCombAtG_base_change E H Y.X Y.t 𝓞_ℂ_[p] ℂ_[p] (algebraMap 𝓞_ℂ_[p] ℂ_[p]) yb g e U (β.comp (embV c' W σ)) u0
  have hA : IsCombAtG Y.t (yy ≫ Y.j) (bcV Y.t (algebraMap 𝓞_ℂ_[p] ℂ_[p]) e) (fun b => (U b : ℂ_[p])) (w ≫ Y.m.φ) := by
    rw [hw1, ← hPt.1]
    exact hbc.1 hu0c
  have hemb := GlobalTheory.T.integral_model_p_adic_comparison E H Dw l l' Xo Xo' c c' W Y r ν hle hOI p yb yy P π ψ y ⟨hPt, hTs, hptF, hHC⟩ β hβ σ
  have hE : ∀ a : 𝓞 E, (w ≫ Y.m.φ) ≫ (Y.t.act.act a).left =
      spMap (epsMul (algebraMap c.F ℂ_[p] (embK c σ a))) ≫ w ≫ Y.m.φ := by
    intro a
    have h := hbc.2 hu0e a
    have hs : algebraMap 𝓞_ℂ_[p] ℂ_[p] (β (embV c' W σ a)) = algebraMap c.F ℂ_[p] (embK c σ a) := by
      rw [← algebraMap_embInt P.integers σ a, ← hemb]; rfl
    rw [hw1, h, RingHom.comp_apply, RingHom.comp_apply, hs]
  obtain ⟨hT, hEig⟩ := GlobalTheory.T.padic_point_model_abelian_map E H Dw l l' Xo Xo' c c' W Y r ν p yy y hptF w hw2 hw3 σ hE
  obtain ⟨cf, hcf, -⟩ := y.basis σ (w ≫ ν.φ) hT hEig
  refine ⟨w, cf, hA, hcf, ?_⟩
  have hyx : y.x = yy ≫ r ≫ pullback.fst _ _ := by
    rw [← Category.assoc, ← hptF]
    exact (pullback.lift_fst _ _ _).symm
  have hzx : y.x = z.x := hchg.1
  have hψ' : IsGrpPullback P.A.A Xo.univ.t.G z.x (ψ ≫ ν.φ) := by
    rw [← hzx, hyx]
    exact hPt.2.2.2.1.comp ν.cart
  have hXt : LieTie P (ψ ≫ ν.φ) (lieComb P.Gt U xb) (w ≫ ν.φ) := by
    obtain ⟨xG, u', h1, h2, h3⟩ := hwt
    exact ⟨xG, u', h1, by rw [← h2, Category.assoc], h3⟩
  have hdc : IsCombAtG Xo.univ.t z.x (z.u σ) ((Matrix.of fun l j => gm σ j l).mulVec cf) (w ≫ ν.φ) :=
    tanLinG (z.u σ) (fun j => z.tan σ j) (y.u σ) (Matrix.of fun l j => gm σ j l) cf (w ≫ ν.φ)
      (fun j => hchg.2.1 σ j) (hzx ▸ hcf)
  obtain ⟨δ, hδ0, hδ⟩ := exists_denom_alg p _ ((Matrix.of fun l j => gm σ j l).mulVec cf)
  choose ee hee using hδ
  have hsc : IsCombAtG Xo.univ.t z.x (z.u σ) (fun l => algebraMap 𝓞_ℂ_[p] ℂ_[p] (ee l))
      (spMap (epsMul (algebraMap 𝓞_ℂ_[p] ℂ_[p] δ)) ≫ (w ≫ ν.φ)) := by
    have h := (isCombAtG_iff Xo.univ.t z.x (fun j => ovT (z.tan σ j)) _ (w ≫ ν.φ)).1 hdc
    refine (isCombAtG_iff Xo.univ.t z.x (fun j => ovT (z.tan σ j)) _ _).2 ?_
    rw [show (fun l => algebraMap 𝓞_ℂ_[p] ℂ_[p] (ee l)) =
      fun l => algebraMap 𝓞_ℂ_[p] ℂ_[p] δ * (Matrix.of fun l j => gm σ j l).mulVec cf l from funext hee,
      ← smT_combT, smT_left, h]
  have hL1 := hXt.scale δ
  have hL2 := GlobalTheory.T.isGrpPullback_tangent_combination E H Xo.X Xo.univ.t p P z.x (ψ ≫ ν.φ) hψ' _ (x σ) (z.u σ) ee _ (hx σ) hsc
  have heq := hL1.unique hψ'.1 hL2
  have hb := congrArg P.bLie heq
  rw [P.bLie_scale, bLie_lieComb, bLie_lieComb] at hb
  have hb' : algebraMap 𝓞_ℂ_[p] ℂ_[p] δ • ∑ b, (U b : ℂ_[p]) • P.bLie (xb b) =
      algebraMap 𝓞_ℂ_[p] ℂ_[p] δ • ∑ l, (Matrix.of fun l j => gm σ j l).mulVec cf l • P.bLie (x σ l) := by
    have e1 : algebraMap 𝓞_ℂ_[p] ℂ_[p] δ • ∑ b, (U b : ℂ_[p]) • P.bLie (xb b) = δ • ∑ b, U b • P.bLie (xb b) := by
      rw [algebraMap_smul]
      congr 1
    have e2 : ∑ l, ee l • P.bLie (x σ l) =
        algebraMap 𝓞_ℂ_[p] ℂ_[p] δ • ∑ l, (Matrix.of fun l j => gm σ j l).mulVec cf l • P.bLie (x σ l) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [smul_smul, ← hee, algebraMap_smul]
    rw [e1, hb, e2]
  have h2 := smul_right_injective P.V hδ0 hb'
  rw [h2]
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  rw [mul_comm]

end GlobalTheory.FlatModel

end
