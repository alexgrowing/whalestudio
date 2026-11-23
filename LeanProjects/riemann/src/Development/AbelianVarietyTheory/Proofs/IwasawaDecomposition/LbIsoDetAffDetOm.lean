import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeCoordinatesStep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.GrCl GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod
open GlobalTheory.Twist (resM resM_resM)

namespace GlobalTheory.HodgeCech

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

section Dual

variable {X : Scheme.{0}} (t : SAB H X) {S : Type} [CommRing S] {g : ℕ}

theorem tanLin_bijective (c : VB.Chart (LieVB.omega t.G) g) (x : Sp S ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ c.U) :
    Function.Bijective (tanLin t h c.e) := by
  refine ⟨tanLin_injective t h c.e le_rfl h (c.isFrame.res le_rfl), fun a => ?_⟩
  obtain ⟨v, ⟨hv, e⟩, -⟩ := GlobalTheory.TanFibre.existsUnique_tanEv E H X t S x c.U h g c.e c.isFrame a
  exact ⟨tanOf hv, funext e⟩

def dualBasis (c : VB.Chart (LieVB.omega t.G) g) (x : Sp S ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ c.U) :
    Module.Basis (Fin g) S (TanM x t.G) :=
  Module.Basis.ofEquivFun (LinearEquiv.ofBijective _ (tanLin_bijective t c x h))

theorem dualBasis_repr (c : VB.Chart (LieVB.omega t.G) g) (x : Sp S ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ c.U) (v : TanM x t.G)
    (i : Fin g) : (dualBasis t c x h).repr v i = tanLin t h c.e v i := rfl

theorem ev_detUnit (c c' : VB.Chart (LieVB.omega t.G) g) (x : Sp S ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ c.U) (h' : ⊤ ≤ x ⁻¹ᵁ c'.U)
    (hh : ⊤ ≤ x ⁻¹ᵁ (c.U ⊓ c'.U)) :
    ev x _ hh (c.isFrame.detUnit c'.isFrame inf_le_left inf_le_right).val =
      rdet ((dualBasis t c' x h').toMatrix (dualBasis t c x h)) := by
  show ev x _ hh ((c.isFrame.basis inf_le_left).det (c'.isFrame.basis inf_le_right)) = _
  rw [Module.Basis.det_apply, RingHom.map_det, rdet_self, ← Matrix.det_transpose]
  congr 1
  ext l i
  rw [Module.Basis.toMatrix_apply, dualBasis_repr, tanLin_apply, ← tanEv_resM t _ hh inf_le_right,
    sum_frMat c'.isFrame c.isFrame inf_le_right inf_le_left, tanEv_sum_smul]
  simp only [tanEv_resM t _ hh inf_le_left]
  have e : ∀ k, tanEv t (isTan_tv (dualBasis t c x h i)) h (c.e k) = if i = k then 1 else 0 := fun k => by
    rw [← tanLin_apply, ← dualBasis_repr, Module.Basis.repr_self, Finsupp.single_apply]
  simp only [e, mul_ite, _root_.mul_one, MulZeroClass.mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rfl

def detAff (t : SAB H X) (g : ℕ) : LB X :=
  ⟨{c : VB.Chart (LieVB.omega t.G) g // IsAffineOpen c.U}, fun c => c.1.U,
    fun c c' => c.1.isFrame.detUnit c'.1.isFrame inf_le_left inf_le_right⟩

theorem isLB_detAff (h : VB.IsVB (LieVB.omega t.G) g) : (detAff t g).IsLB := by
  refine ⟨top_le_iff.1 fun x _ => ?_, fun c => h.isLB_det.g_self c.1, fun c c' c'' => h.isLB_det.cocycle c.1 c'.1 c''.1⟩
  obtain ⟨U, e, hx, he⟩ := h x
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := U) (x := x) hx
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨V, _, he.res hVU⟩, hV⟩, hxV⟩

theorem lbIso_detAff (h : VB.IsVB (LieVB.omega t.G) g) : LBIso (detAff t g) (VB.det (LieVB.omega t.G) g) :=
  (VB.lbIso_det_of_frames (isLB_detAff t h) (fun c => c.1.e) (fun c => c.1.isFrame) fun _ _ => rfl).2

end Dual

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  (Y : Model Xo c β) {g : ℕ} {S : Type} [CommRing S]

theorem isAffineOpen_inf' {U V : Y.X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) : IsAffineOpen (U ⊓ V) := by
  have := projProper _ _ _ Y.proj
  have : Y.X.IsSeparated := ⟨by
    rw [← terminal.comp_from Y.s]
    infer_instance⟩
  exact hU.inf hV

variable {Y}

def pairDet (M : MChart Y) (a : (detAff Y.t g).ι) : Γ(Y.X, M.U ⊓ a.1.U)ˣ :=
  (isUnit_rdet_toMatrix (dualBasis Y.t a.1 (tau (isAffineOpen_inf' Y M.hU a.2)) (tau_le _ inf_le_right))
    (lieBasis M (tau (isAffineOpen_inf' Y M.hU a.2)) (tau_le _ inf_le_left))).unit

theorem ev_pairDet (M : MChart Y) (a : (detAff Y.t g).ι) (x : Sp S ⟶ Y.X) (h : ⊤ ≤ x ⁻¹ᵁ M.U) (h' : ⊤ ≤ x ⁻¹ᵁ a.1.U)
    (hh : ⊤ ≤ x ⁻¹ᵁ (M.U ⊓ a.1.U)) :
    ev x _ hh (pairDet M a).val = rdet ((dualBasis Y.t a.1 x h').toMatrix (lieBasis M x h)) := by
  have e : spMap (ev x _ hh) ≫ tau (isAffineOpen_inf' Y M.hU a.2) = x := spMap_ev x _ hh
  refine (map_rdet _ _).trans (congrArg rdet ?_)
  ext i j
  rw [Matrix.map_apply, Module.Basis.toMatrix_apply, Module.Basis.toMatrix_apply, dualBasis_repr, dualBasis_repr,
    ← tanPull_lieBasis M _ e (tau_le _ inf_le_left) h, tanLin_tanPull Y.t _ e (tau_le _ inf_le_right) h']
  rfl

variable (Y)

theorem lbIso_detAff_detOm : LBIso (detAff Y.t g) (detOm Y) := by
  refine ⟨⟨fun p => pairDet p.1 p.2⟩, fun p q => ?_⟩
  refine Eq.trans ?_ (mul_right_comm _ _ _)
  refine eq_mul_inv_of_mul_eq ?_
  refine Eq.trans ?_ (congrArg (· * _) (map_inv _ (detChg p.1 q.1)).symm)
  refine eq_inv_mul_of_mul_eq (Units.ext (ext_ev fun S _ z hz => ?_))
  have hp := le_preimage_mono inf_le_left hz
  have hq := le_preimage_mono inf_le_right hz
  have hp1 : ⊤ ≤ z ⁻¹ᵁ (p.1 : MChart Y).U := le_preimage_mono inf_le_left hp
  have hq1 : ⊤ ≤ z ⁻¹ᵁ (q.1 : MChart Y).U := le_preimage_mono inf_le_left hq
  have hp2 : ⊤ ≤ z ⁻¹ᵁ p.2.1.U := le_preimage_mono inf_le_right hp
  have hq2 : ⊤ ≤ z ⁻¹ᵁ q.2.1.U := le_preimage_mono inf_le_right hq
  refine (map_mul (ev z _ hz) _ _).trans ?_
  refine (congrArg₂ (· * ·) ((ev_res z _ hz (le_preimage_inf hp1 hq1) _).trans (ev_detChg _ _ z hp1 hq1 _))
    ((map_mul (ev z _ hz) _ _).trans (congrArg₂ (· * ·) ((ev_res z _ hz hp _).trans (ev_pairDet _ _ z hp1 hp2 hp))
      ((ev_res z _ hz (le_preimage_inf hp2 hq2) _).trans (ev_detUnit Y.t _ _ z hp2 hq2 _))))).trans
    (Eq.trans ?_ ((ev_res z _ hz hq _).trans (ev_pairDet _ _ z hq1 hq2 hq)).symm)
  rw [_root_.mul_comm, _root_.mul_comm (rdet _) (rdet _), rdet_toMatrix_mul, rdet_toMatrix_mul]

theorem lbIso_detOm_det (hO : (detOm Y).IsLB) (h : VB.IsVB (LieVB.omega Y.t.G) g) :
    LBIso (detOm Y) (VB.det (LieVB.omega Y.t.G) g) :=
  (lbIso_detAff_detOm Y).symm.trans hO (isLB_detAff Y.t h) h.isLB_det (lbIso_detAff Y.t h)

end GlobalTheory.HodgeCech
