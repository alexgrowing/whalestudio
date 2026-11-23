import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsEqSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovFn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetIdlVal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GivenLevelInner
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetUnitaryConjAtPlaceEqDetLatticeBasisComponent
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.RowVacScalar
namespace GlobalTheory.RowDetLocal
variable {D : D7}

theorem toFinAd_eq (z : TensorProduct D.host.F (Af D.host.F) D.host.E) :
    GlobalTheory.LFun.toFinAd D.host.F D.host.E z = GlobalTheory.StdFrames.toAd D (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [Algebra.TensorProduct.comm_tmul, GlobalTheory.StdFrames.toAd_spec, mul_comm]
    rfl
  | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]

theorem compAt_eq_cpt (w : Pl D.host.E) (a : AE D) :
    GlobalTheory.LFun.compAt D.host.F w (finPart D a) = GlobalTheory.StdFrames.cpt w (toEAf D a) := by
  show (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.E w) (GlobalTheory.LFun.toFinAd D.host.F D.host.E (finPart D a)) = _
  rw [toFinAd_eq]
  rfl

theorem gdet_inBasis_val (V : HSp D) {n' : ℕ} (h : n' = V.rank) (β : GL (Fin V.rank) (Lev.EAf D)) (w : Pl D.host.E) (k : GfC V) :
    ((gdet (inBasis h β w (finG V k)) : (Kw w)ˣ) : Kw w) =
      GlobalTheory.StdFrames.cpt w (toEAf D (Formalism.L2.Theta.mt V (k : GA D V)).det) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  rw [GlobalTheory.FunObj.inBasis, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, GlobalTheory.TopLevelInv.det_val_reGL, GlobalTheory.TopLevelInv.val_loc, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    GlobalTheory.TopLevelInv.det_val_conj_inv, GlobalTheory.TopLevelInv.val_finG, ← RingHom.mapMatrix_apply, ← RingHom.map_det]

theorem detIdl_eq_locIdele (V : HSp D) (g : GA D V) (w : Pl D.host.E) (hs : ∃ e : AE D, Formalism.L2.NTheta.IsIdemAt e w)
    (z : (Kw w)ˣ) (hz : (z : Kw w) = GlobalTheory.StdFrames.cpt w (toEAf D (Formalism.L2.Theta.mt V g).det)) :
    detIdl (idemAt w) V g = GlobalTheory.LFun.locIdele D.host.F w z := by
  have he : Formalism.L2.NTheta.IsIdemAt (idemAt w) w := Classical.epsilon_spec hs
  have hee : idemAt w * idemAt w = idemAt w := he.1.1
  have hP : Formalism.IndefR.Mult.IsPrimeIdem w (idemAt w) (idemAt w + cA D (idemAt w)) := Or.inl ⟨he, rfl⟩
  have hx := detIdl_val hee V g
  obtain ⟨y, hy, hxy⟩ := GlobalTheory.WeilAtPlace.exists_eq_locIdele (GlobalTheory.WeilAtPlace.isPrimeIdem_infPart hP)
    (GlobalTheory.LFun.finPart_of_isPrimeIdem hP) (detIdl (idemAt w) V g) (by
      rw [hx]
      linear_combination ((Formalism.L2.Theta.mt V g).det - 1) * hee)
  have hyz : y = z := by
    apply Units.ext
    rw [hy, hx, GlobalTheory.WeilAtPlace.compAt_cut (GlobalTheory.LFun.finPart_of_isPrimeIdem hP), compAt_eq_cpt]
    exact hz.symm
  rw [hxy, hyz]

theorem detIdl_conj_eq_locIdele (V : HSp D) {n' : ℕ} (h : n' = V.rank) (β : GL (Fin V.rank) (Lev.EAf D)) (k u : GfC V)
    (w : Pl D.host.E) (hs : ∃ e : AE D, Formalism.L2.NTheta.IsIdemAt e w) :
    detIdl (idemAt w) V ((u⁻¹ * k * u : GfC V) : GA D V) =
      GlobalTheory.LFun.locIdele D.host.F w (gdet (inBasis h β w (finG V k))) :=
  detIdl_eq_locIdele V _ w hs _ (by rw [gdet_inBasis_val, GlobalTheory.TopLevelInv.det_mt_conj])
end GlobalTheory.RowDetLocal

theorem GlobalTheory.RowDetLocal.detIdl_moved_eq_locIdele : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) (t : T) (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)) (w : Pl D.host.E),
    (∃ e : AE D, Formalism.L2.NTheta.IsIdemAt e w) →
    detIdl (idemAt w) (G.V (.grid (j + 1) D.R.m)) (moved S j k) =
      GlobalTheory.LFun.locIdele D.host.F w (gdet (inBasis (rank_vertex G t w (X := (j + 1, D.R.m)) ⟨hj.le, le_rfl⟩)
        (S.B.β (j + 1) D.R.m) w (finG (G.V (.grid (j + 1) D.R.m)) k))) := by
  intro D T L sc G W U S t j hj k w hs
  exact GlobalTheory.RowDetLocal.detIdl_conj_eq_locIdele _ _ _ k (S.N.u (.grid (j + 1) D.R.m)) w hs
