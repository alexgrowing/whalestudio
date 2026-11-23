import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtEqOfPtOfFrameEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtOfFrameEqOfPointEq

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix
open TopologicalSpace
open Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo Formalism.L2.PjFree
open Formalism.L2.Pj (FrPt CAt embK)
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory.HodgeDomain GlobalTheory.LieMet GlobalTheory.CxPts
open GlobalTheory.AllWt (Psi ptF framesOn LiesOn)
open scoped ComplexOrder

namespace GlobalTheory.TrueCx

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r j : ℕ} {Tau : Type}

section Std

variable (X : Data E r) (hj : j ≤ r) (κ : Tau ≃ X.Ψ)

def stdMat (z : Pt Tau j (r - j)) : Frame X.Ψ r := fun τ =>
  (mat (x0F X) τ * reindex (idx hj).symm (idx hj).symm (fromBlocks 1 (z (κ.symm τ)) 0 1) : Matrix (Fin r) (Fin r) ℂ)

theorem frameCo_stdMat (z : Pt Tau j (r - j)) (τ : X.Ψ) :
    frameCo X hj (stdMat X hj κ z) τ = fromBlocks 1 (z (κ.symm τ)) 0 1 := by
  show reindex _ _ (_ * (mat (x0F X) τ * _)) = _
  rw [nonsing_inv_mul_cancel_left _ _ (det_x0F X τ).isUnit]
  simp

theorem domPt_stdMat (z : Pt Tau j (r - j)) : domPt X hj κ (stdMat X hj κ z) = z := by
  funext t
  simp [domPt, frameCo_stdMat, moeb_zero]

theorem stdMat_mem (hp : X.p0 = r - j) {z : Pt Tau j (r - j)} (hz : z ∈ DomI Tau j (r - j)) :
    stdMat X hj κ z ∈ X.dom := by
  refine ExF.mem_dom_of_gramPos X fun τ => ⟨?_, ?_⟩
  · show (mat (x0F X) τ * _).det ≠ 0
    rw [det_mul, det_reindex_self, det_fromBlocks_zero₂₁]
    simpa using det_x0F X τ
  have h0 := congrArg transpose (isOrth_x0F X τ)
  rw [gram_eq_mul, diagonal_transpose, hp] at h0
  set N : Matrix (Fin j ⊕ Fin (r - j)) (Fin j ⊕ Fin (r - j)) ℂ := fromBlocks 1 (z (κ.symm τ)) 0 1 with hN
  have h1 : reindex (idx hj) (idx hj) (gram τ.1 X.Gm (mat (stdMat X hj κ z) τ))ᵀ = Nᴴ * -Jpq j (r - j) * N := by
    rw [gram_eq_mul, ← reindex_sgn hj, ← h0]
    show reindex _ _ ((mat (x0F X) τ * reindex _ _ N)ᴴ * _ * (mat (x0F X) τ * reindex _ _ N)) = _
    simp only [conjTranspose_mul, reindex_apply, conjTranspose_submatrix, ← submatrix_mul_equiv _ _ _ (idx hj).symm,
      submatrix_submatrix, Equiv.symm_symm, Equiv.self_comp_symm, submatrix_id_id, Matrix.mul_assoc]
  have h2 : (Nᴴ * -Jpq j (r - j) * N).toBlocks₂₂ = hQ (z (κ.symm τ)) := by
    simp [hN, Jpq, fromBlocks_conjTranspose, fromBlocks_neg, fromBlocks_multiply, hQ, sub_eq_neg_add]
  have h3 : X.gramPos (stdMat X hj κ z) τ = ((hQ (z (κ.symm τ))).submatrix (finCongr hp) (finCongr hp))ᵀ := by
    ext a b
    have e : ∀ a : Fin X.p0, (idx hj).symm (Sum.inr (finCongr hp a)) = Fin.castLE X.p0_le a :=
      fun a => Fin.ext (idx_symm_inr hj _)
    rw [← h2, ← h1]
    simp only [transpose_apply, submatrix_apply, toBlocks₂₂, of_apply, reindex_apply, e, Data.gramPos]
  rw [h3]
  exact (PosDef.submatrix (hz (κ.symm τ)) (finCongr hp).injective).transpose

example : stdMat X hj κ 0 = x0F X := by
  funext τ
  simp [stdMat, mat]
  rfl

open Classical in

def stdFrame (hp : X.p0 = r - j) (z : Pt Tau j (r - j)) : X.dom :=
  if h : z ∈ DomI Tau j (r - j) then ⟨stdMat X hj κ z, stdMat_mem X hj κ hp h⟩
  else ⟨stdMat X hj κ 0, stdMat_mem X hj κ hp fun _ => zero_mem_hcDom _ _⟩

theorem stdFrame_val (hp : X.p0 = r - j) {z : Pt Tau j (r - j)} (hz : z ∈ DomI Tau j (r - j)) :
    (stdFrame X hj κ hp z).1 = stdMat X hj κ z := by rw [stdFrame, dif_pos hz]

theorem domPt_stdFrame (hp : X.p0 = r - j) {z : Pt Tau j (r - j)} (hz : z ∈ DomI Tau j (r - j)) :
    domPt X hj κ (stdFrame X hj κ hp z).1 = z := by rw [stdFrame_val X hj κ hp hz, domPt_stdMat]

end Std

section Tor

variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  (Y : Model Xo c (RingHom.id c.F)) (σ : c.F →+* ℂ)

abbrev torC : Scheme.{0} := pullback Y.s (spMap σ)

abbrev torStr : torC Y σ ⟶ Sp ℂ := pullback.snd Y.s (spMap σ)

abbrev torPr : torC Y σ ⟶ Y.X := pullback.fst Y.s (spMap σ)

instance smooth_torStr {D : ℕ} [h : SmoothOfRelativeDimension D Y.s] : SmoothOfRelativeDimension D (torStr Y σ) :=
  (smoothOfRelativeDimension_isStableUnderBaseChange D).of_isPullback (IsPullback.of_hasPullback _ _) h

abbrev TorPts : Type := CxPts (torStr Y σ) (RingHom.id ℂ)

def bdSet : Set (torC Y σ) := torPr Y σ ⁻¹' (LogKS.interior Y : Set Y.X)ᶜ

theorem isClosed_bdSet : IsClosed (bdSet Y σ) :=
  (LogKS.interior Y).isOpen.isClosed_compl.preimage (torPr Y σ).continuous

abbrev BdComp : Type := irreducibleComponents (bdSet Y σ)

variable {Y σ}

def BdComp.closed (C : BdComp Y σ) : Closeds (torC Y σ) :=
  ⟨Subtype.val '' C.1, (isClosed_bdSet Y σ).isClosedMap_subtype_val _ (isClosed_of_mem_irreducibleComponents _ C.2)⟩

variable (Y)

def ptC (y : FrPt Xo c (CAt σ)) : Sp ℂ ⟶ Xo.XF c := ptF (S := CAt σ) y

def xC (y : FrPt Xo c (CAt σ)) : Sp ℂ ⟶ Xo.X := y.x

theorem ptC_fst (y : FrPt Xo c (CAt σ)) : ptC y ≫ pullback.fst _ _ = xC y := pullback.lift_fst _ _ _

theorem ptC_snd (y : FrPt Xo c (CAt σ)) : ptC y ≫ pullback.snd _ _ = spMap σ := pullback.lift_snd _ _ _

def torPt (y : FrPt Xo c (CAt σ)) : TorPts Y σ :=
  ⟨pullback.lift (ptC y ≫ Y.j) (spMap (RingHom.id ℂ)) (by
      rw [Model.j, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over,
        ← Category.assoc, ptC_snd, ← Spec.map_comp, ← Spec.map_comp]
      rfl), pullback.lift_snd _ _ _⟩

theorem torPt_pr (y : FrPt Xo c (CAt σ)) : (torPt Y y).1 ≫ torPr Y σ = ptC y ≫ Y.j := pullback.lift_fst _ _ _

theorem torPt_eq_iff {y y' : FrPt Xo c (CAt σ)} : torPt Y y = torPt Y y' ↔ y.x = y'.x := by
  constructor
  · intro h
    have h1 : ptC y = ptC y' := (cancel_mono Y.j).1 ((torPt_pr Y y).symm.trans (h ▸ torPt_pr Y y'))
    exact (ptC_fst y).symm.trans (h1 ▸ ptC_fst y')
  · intro h
    have h1 : ptC y = ptC y' := pullback.hom_ext ((ptC_fst y).trans (h.trans (ptC_fst y').symm))
      ((ptC_snd y).trans (ptC_snd y').symm)
    exact Subtype.ext (pullback.hom_ext ((torPt_pr Y y).trans (h1 ▸ (torPt_pr Y y').symm))
      ((torPt Y y).2.trans (torPt Y y').2.symm))

abbrev LieAt (y : TorPts Y σ) : Type := TanM (y.1 ≫ torPr Y σ) Y.t.G

variable (σ) in

abbrev LieForm : Type := ∀ y : TorPts Y σ, LieAt Y y →ₗ[ℂ] LieAt Y y →ₗ⋆[ℂ] ℂ

def lieEquiv (y : FrPt Xo c (CAt σ)) : TanM (xC y) Xo.univ.t.G ≃ₗ[ℂ] LieAt Y (torPt Y y) :=
  (pushE Y.m0.toSABMap (ptC y) (ptC_fst y)).symm.trans (pushE Y.m (ptC y) (torPt_pr Y y).symm)

def frVec (y : FrPt Xo c (CAt σ)) (i : Σ τ : E →+* ℂ, Fin (Dw.mult τ)) : TanM (xC y) Xo.univ.t.G := fullB y i

def torBasis (y : FrPt Xo c (CAt σ)) : Module.Basis (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ℂ (LieAt Y (torPt Y y)) :=
  (Module.Basis.mk (R := ℂ) (v := frVec y)
    (Fintype.linearIndependent_iff.2 fun a ha => congrFun
      ((fullB_basis y 0).unique (y₁ := a) (y₂ := 0) ha.symm (by simp)))
    (fun w _ => by
      obtain ⟨a, ha, -⟩ := fullB_basis y w
      exact ha ▸ Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ (show ℂ from a i)
        (Submodule.subset_span ⟨i, rfl⟩))).map (lieEquiv Y y)

def vecW (y : FrPt Xo c (CAt σ)) (τ : Psi H) (e : Dw.p = j) (a : Fin j) : LieAt Y (torPt Y y) :=
  torBasis Y y ⟨τ.1, a.cast (e.symm.trans (if_pos τ.2).symm)⟩

def vecC (y : FrPt Xo c (CAt σ)) (τ : Psi H) {q : ℕ} (e : Dw.q = q) (a : Fin q) : LieAt Y (torPt Y y) :=
  torBasis Y y ⟨conjEmb τ.1, a.rev.cast (e.symm.trans (if_neg (AllWt.conj_not_mem τ)).symm)⟩

end Tor

section Bd

variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  (Y : Model Xo c (RingHom.id c.F)) {σ : c.F →+* ℂ}

def IsTorData (R : AnRead (torStr Y σ) (RingHom.id ℂ) Dw.dim) (D : BdComp Y σ → EffCartierData (torC Y σ))
    (φ : ∀ C, Weight (torStr Y σ) (RingHom.id ℂ) (D C).lb) {L : LB (torC Y σ)}
    (ψ : Weight (torStr Y σ) (RingHom.id ℂ) L) (h : LieForm Y σ) : Prop :=
  (∀ C, (D C).idealSheaf = Scheme.IdealSheafData.vanishingIdeal C.closed) ∧ (∀ C, (φ C).IsSmooth R) ∧
    (∀ C y, (φ C).nsq (secVal _ _ (D C).canonical) y ≤ 1) ∧ ψ.IsSmooth R ∧ ψ.StrictPos R ∧
    IsLieMetric Y.t (torPr Y σ) R h

variable (U : Unf Xo c σ r) (hU : IsUnf U) (e : Dw.p = j) (hσ : GoodEmb c σ) (T : Tau ≃ Psi H)

include hU e in

theorem q_of_isUnf : Dw.q = r - j := by have := hU.1; omega

def letter (t : Tau) : Psi H := (letterAt hσ).symm (T t)

def domFr (k : U.Comp) (z : Pt Tau j (r - j)) : FrPt Xo c (CAt σ) :=
  U.un k (stdFrame (U.X k) (le_of_isUnf U hU e) (cmEquiv U hU T k) (first_index_eq_of_unfolded U hU e k) z)

def domTor (k : U.Comp) (z : Pt Tau j (r - j)) : TorPts Y σ := torPt Y (domFr U hU e T k z)

include hσ in

theorem domTor_domPt (k : U.Comp) (x : (U.X k).dom) :
    domTor Y U hU e T k (domPt (U.X k) (le_of_isUnf U hU e) (cmEquiv U hU T k) x.1) = torPt Y (U.un k x) := by
  have hp := first_index_eq_of_unfolded U hU e k
  have h0 := domPt_stdFrame (U.X k) (le_of_isUnf U hU e) (cmEquiv U hU T k) hp
    (domPt_mem _ (le_of_isUnf U hU e) (cmEquiv U hU T k) hp x.2)
  have h1 := fun τ => congrFun h0 ((cmEquiv U hU T k).symm τ)
  simp only [domPt, Equiv.apply_symm_apply] at h1
  exact (torPt_eq_iff Y).2 (PointWell.pt_eq_of_block hU hσ k _ x
    (fun τ => PointWell.block_of_moeb_eq _ _ hp (Subtype.prop _) x.2 τ (h1 τ))
    fun τ => PointWell.block_of_moeb_eq _ _ hp x.2 (Subtype.prop _) τ (h1 τ).symm)

variable [Fintype Tau]

include hσ in

theorem domTor_moeb (k : U.Comp) {g : Tau → GL (Fin j ⊕ Fin (r - j)) ℂ}
    (hg : g ∈ gammaU (U.X k) (le_of_isUnf U hU e) (cmEquiv U hU T k)) {z : Pt Tau j (r - j)}
    (hz : z ∈ DomI Tau j (r - j)) : domTor Y U hU e T k (moebI g z) = domTor Y U hU e T k z := by
  obtain ⟨g, hg, rfl⟩ := hg
  have hp := first_index_eq_of_unfolded U hU e k
  set x := stdFrame (U.X k) (le_of_isUnf U hU e) (cmEquiv U hU T k) hp z
  have h0 : domPt _ _ _ x.1 = z := domPt_stdFrame (U.X k) (le_of_isUnf U hU e) (cmEquiv U hU T k) hp hz
  conv_lhs => rw [← h0, ← domPt_lact _ _ _ hp g x.2]
  exact (domTor_domPt Y U hU e hσ T k ⟨_, KU.lact_dom _ hg x.2⟩).trans
    ((torPt_eq_iff Y).2 (PointWell.pt_lact hU k x hg))

variable (B : ∀ k, BdData Tau j (r - j) (gammaU (U.X k) (le_of_isUnf U hU e) (cmEquiv U hU T k)))

def ReadsTor (D : BdComp Y σ → EffCartierData (torC Y σ)) (φ : ∀ C, Weight (torStr Y σ) (RingHom.id ℂ) (D C).lb)
    {L : LB (torC Y σ)} (ψ : Weight (torStr Y σ) (RingHom.id ℂ) L)
    (h : LieForm Y σ) : Prop :=
  (∀ k k', (B k).cst = (B k').cst) ∧ ∀ k,
    (∃ ε : Fin (B k).m ≃ BdComp Y σ, ∀ i, ∀ z ∈ DomI Tau j (r - j),
      (B k).nrm i z = √((φ (ε i)).nsq (secVal _ _ (D (ε i)).canonical) (domTor Y U hU e T k z))) ∧
    (∀ z ∈ DomI Tau j (r - j), ∀ a : L.ι, domTor Y U hU e T k z ∈ ptsIn _ _ (L.U a) →
      ∀ ξ, ((B k).kae z ξ ξ).re = ddc (fun w => ψ.φ a (domTor Y U hU e T k w)) z ξ) ∧
    ∀ z ∈ DomI Tau j (r - j), ∀ t,
      (B k).metW z t = gramOf (h _) (vecW Y (domFr U hU e T k z) (letter hσ T t) e) ∧
      (B k).metOm z t = ((hodgeC (U.X k) (cmEquiv U hU T k) t : ℂ) ^ 2) •
        dualGram (gramOf (h _) (vecC Y (domFr U hU e T k z) (letter hσ T t) (q_of_isUnf U hU e)))

def IsTorBd : Prop :=
  ∃ (R : AnRead (torStr Y σ) (RingHom.id ℂ) Dw.dim) (D : BdComp Y σ → EffCartierData (torC Y σ))
    (φ : ∀ C, Weight (torStr Y σ) (RingHom.id ℂ) (D C).lb) (L : LB (torC Y σ))
    (ψ : Weight (torStr Y σ) (RingHom.id ℂ) L) (h : LieForm Y σ),
    IsTorData Y R D φ ψ h ∧ ReadsTor Y U hU e hσ T B D φ ψ h

variable {Y U hU e hσ T B}

end Bd

section Flat

open GlobalTheory.FlatLine GlobalTheory.AllWt

variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) {x : ℝ}
  (sig : ∀ (Z : Formalism.L2.Pj.Comp Xo c) (τ : Psi H), FlatSec (fun σ => (U σ).toPj) x Z τ)
  {σ : c.F →+* ℂ} (hU : IsUnf (U σ)) (hσ : GoodEmb c σ) (T : Tau ≃ Psi H)

def IsFlatSec (s : (U σ).Comp → Tau → ℂˣ) : Prop :=
  ∀ (Z : Formalism.L2.Pj.Comp Xo c) (k : (U σ).Comp) (t : Tau) (y : Frame ((U σ).X k).Ψ r),
    (⟨k, y⟩ : Σ k, Frame ((U σ).toPj.X k).Ψ r) ∈ framesOn (U σ).toPj Z →
      rdU (U σ) (sig Z (letter hσ T t)).sig k y =
        (hodgeC ((U σ).X k) (cmEquiv (U σ) hU T k) t : ℂ) ^ Dw.q * s k t * horizGen (cmEquiv (U σ) hU T k t) y

theorem exists_mem_framesOn (V : Unf Xo c σ r) (k : V.Comp) (y : (V.X k).dom) :
    ∃ Z, (⟨k, y.1⟩ : Σ k, Frame (V.toPj.X k).Ψ r) ∈ framesOn V.toPj Z :=
  ⟨⟨_, irreducibleComponent_mem_irreducibleComponents (ptC (V.un k y) default)⟩, y.2, fun s => by
    obtain rfl : s = (default : Sp ℂ) := Subsingleton.elim (α := Sp ℂ) _ _
    exact mem_irreducibleComponent (x := ptC (V.un k y) default)⟩

variable {U sig hU hσ T}

theorem IsFlatSec.unique {s s' : (U σ).Comp → Tau → ℂˣ} (h : IsFlatSec U sig hU hσ T s)
    (h' : IsFlatSec U sig hU hσ T s') : s = s' := by
  funext k t
  obtain ⟨Z, hZ⟩ := exists_mem_framesOn (U σ) k ⟨x0F _, KU.orth_dom _ (isOrth_x0F _)⟩
  exact Units.ext (mul_left_cancel₀ (pow_ne_zero _ (Complex.ofReal_ne_zero.2 (hodgeC_pos _ _ t).ne'))
    (mul_right_cancel₀ (inv_ne_zero (det_x0F _ _)) ((h Z k t _ hZ).symm.trans (h' Z k t _ hZ))))

end Flat

end GlobalTheory.TrueCx
