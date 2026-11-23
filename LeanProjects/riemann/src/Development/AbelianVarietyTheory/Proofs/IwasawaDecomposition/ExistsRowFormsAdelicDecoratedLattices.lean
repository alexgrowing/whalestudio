import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsDeco
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStdWtCast
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormsFiniteGroupActionEqFlagLevelRightTranslaStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitHeckeRowsEqDoubleCosetOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjHeckeFamIApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryFiniteAdelicPointAsMatrixMemFlagIwahori
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.RowsRead

theorem decoPt_eq_decoAd (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) {U : Set I.ι} (t : TupU I U)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hβ : L.βX = 1) (hc : CMData X.B.fields.F X.B.fields.E)
    (h : Bridge.Gf X.toD7.sp.X') (x : Formalism.L2.Col.UAd hc (X.B.R.N X.B.R.m - 1))
    (hM : MatEq (matIn X.toD7.sp.X' L.βX h) (show GL (Fin (X.B.R.N X.B.R.m - 1)) (Lev.EAf X.toD7) from x.1)) :
    Formalism.L2.Col.decoPt hc (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) (QuotientGroup.mk x) =
      GlobalTheory.Mem.R3.RowAd.decoAd X I t h := by
  have hx : x.1 = GlobalTheory.Mem.R3.RowAd.ptE X h := by
    ext i j
    have := hM.2 (Fin.cast (GlobalTheory.Mem.R3.RowAd.rank_X' X).symm i) (Fin.cast (GlobalTheory.Mem.R3.RowAd.rank_X' X).symm j) i j rfl rfl
    rw [hβ, matIn, mul_one] at this
    exact this.symm
  rw [Formalism.L2.Col.decoPt_mk, hx]
  rfl

theorem exists_matEq_ptE (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hI : I.Ok) {U : Set I.ι}
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hβ : L.βX = 1) :
    ∃ hc : CMData X.B.fields.F X.B.fields.E, ∀ h : Bridge.Gf X.toD7.sp.X', ∃ x : Formalism.L2.Col.UAd hc (X.B.R.N X.B.R.m - 1),
      MatEq (matIn X.toD7.sp.X' L.βX h) (show GL (Fin (X.B.R.N X.B.R.m - 1)) (Lev.EAf X.toD7) from x.1) := by
  refine ⟨X.toD7.sp.cm, fun h => ⟨⟨GlobalTheory.Mem.R3.RowAd.ptE X h, GlobalTheory.Mem.R3.RowDeco.ptE_mem_UAd X I hI h⟩, GlobalTheory.Mem.R3.RowAd.rank_X' X, ?_⟩⟩
  intro i j i' j' hi hj
  obtain rfl : i = Fin.cast (GlobalTheory.Mem.R3.RowAd.rank_X' X).symm i' := Fin.ext hi
  obtain rfl : j = Fin.cast (GlobalTheory.Mem.R3.RowAd.rank_X' X).symm j' := Fin.ext hj
  rw [hβ, matIn, mul_one]
  rfl

set_option maxHeartbeats 4000000 in

theorem exists_rowSide : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cX : CoefA X.toD7.sp.X') (gramR : Matrix (Fin X.toD7.sp.X'.rank) (Fin X.toD7.sp.X'.rank) X.toD7.host.E)
    (c0R : VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) →ₛₗ[X.toD7.what₂.embLL] cX.W),
    cX.Is → (gramR = X.toD7.sp.X'.gram ∨ gramR = -X.toD7.sp.X'.gram) →
    Bridge.CoefMapTie X.toD7.sp.X' cX.coef c0R (rhoV (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0R x) (c0R y) = X.toD7.what₂.embLL (pairV (labLL X.toD7) _ gramR x y)) →
    L.βX = 1 → Seed.FrmC.StdLat X.toD7.sp.X' → ∃ s : ∀ t, Seed.RowSideT (famR X I hX U Xg tr) L cX (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) t, (∀ t,       (∀ q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q,
        eG ((s t).act_tie.red q) = rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf X.toD7.sp.X') : GL _ _))) ∧
      Bridge.CoefTie X.toD7.sp.X' cX.coef (s t).pres (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) c0R (pairV (labLL X.toD7) _ gramR)
        (nabAt (labLL X.toD7) _) (delAt (labLL X.toD7) _) ∧
      Nonempty (Bridge.HeckeTie (Bridge.ratF X.toD7.sp.X') (s t).pres ((famR X I hX U Xg tr).heckeRI t)
        (fun i => Formalism.L2.Col.InertTypeOk X.toD7.sp.X'.rank i.2)
        (fun i => IsLabElt X.toD7.sp.X' (i.1.1 : PlI X.B px).1 (labIn X.toD7.sp.X'.rank i.2))
        fun i => IsLocElt X.toD7.sp.X' (i.1.1 : PlI X.B px).1)) ∧ BrgStdR X I hX U Xg tr L cX (fun t φ => (s t).pres.extL φ) := by
  intro X px I hX U Xg tr L eG hI hV hL hG cX gramR c0R hcX hgr hmap hin hβ _
  obtain ⟨c, -, hli, -, -, hcI, hP⟩ := GlobalTheory.Mem.R3.RowStd.exists_std_wtCast X px I hX U Xg tr L eG hI hV hL hG cX gramR c0R hcX hgr hmap hin hβ
  choose P hPr hCo using hP
  have hRd : ∀ t, GlobalTheory.Mem.R3.RowAd.ReadsDeco X I hX Xg tr cX t (P t) := fun t => ⟨c, hPr t⟩
  choose a ha using fun t => GlobalTheory.T.rowFormsFiniteGroupAction_eq_flagLevelRightTranslation X px I hX U Xg tr L eG hI hV hL hG cX gramR c0R hcX hgr hmap hin t (P t) (hRd t)
  refine ⟨fun t => { pres := P t, act_tie := a t, hecke := (GlobalTheory.T.splitHecke_rows_eq_doubleCoset_operators X px I hX U Xg tr L eG hI hV hL hG cX gramR c0R hcX hgr hmap hin t (P t) (hRd t)).some },
    fun t => ⟨ha t, hCo t, GlobalTheory.Mem.R3.RowAd.Inert.exists_inertTie X px I hX U Xg tr L eG hI hV hL hG cX gramR c0R hcX hgr hmap hin t (P t) (hRd t)⟩, c, hcI, ?_, hli, exists_matEq_ptE X I hI L hβ⟩
  intro hc t φ h x hM
  refine (hPr t _ h).trans ?_
  rw [LinearEquiv.symm_apply_apply]
  exact congrArg (fun d => c (φ.2.1 d)) (decoPt_eq_decoAd X I t L hβ hc h x hM).symm

end GlobalTheory.Mem.R3.RowsRead
