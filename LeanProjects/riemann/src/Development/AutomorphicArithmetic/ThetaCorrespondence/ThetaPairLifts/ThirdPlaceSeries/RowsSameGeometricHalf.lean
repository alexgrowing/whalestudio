import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowsSameGeometricHalf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MMvDmvAll

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting.SerCopy
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
namespace GlobalTheory.LayerMove.SerUp
variable {B : GlobalTheory.Mem.Base} {C : Cols B} {W : RowsRest B C} (o : Oth W) (V' : DivStage B C W) (S' : SStage B C W)
variable {o} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 o.L.D.what₂.LL G Pl0 I0 (List ℕ) T o.L.D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks o.L.D.what₂.LL] {R : RealDat3 o.L.D A3 Ks}
  {cG : G0 R.Pg o.L.D.R.r ≃* G0g o.L.D.nd} {S : RatDat o.L.D.ntw} {YS : NExpRealS R cG S}
  {v₀ : ∀ (j : Fin o.L.D.R.m) (σ : o.L.D.what₂.LL →+* ℂ), (R.MW j σ).Vec}
set_option hygiene false in
local notation "bb" => Oth.L (o2 o V' S')
end GlobalTheory.LayerMove.SerUp
end
end
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
open GlobalTheory.LayerMove
set_option maxHeartbeats 1000000
theorem _root_.GlobalTheory.T.geo_heq_geoHalf_of_same : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (nch : NChoice (w.D Z)) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (p0' : BaseLevelRowSide (w.D (upL Z S' N h))) (t' : RowsT K w (upL Z S' N h) Wt p0'), RowsSame t t' → HEq t'.r.z.geo (R3.Tr.geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo) → ∀ (kKs : ↥t.r.z.core.Q.c.F →+* ↥(w.st Z).toD7.LL0) (hk : ∀ x, ((kKs x : ↥(w.st Z).toD7.LL0) : (w.st Z).toD7.what₂.LL) = algebraMap _ (w.st Z).toD7.what₂.LL x) (YS : Formalism.IndefR.NX.NExpRealS t.r.z.R t.r.z.cG (Formalism.IndefR.NX.ratDatR t.r.z.R t.r.z.cG kKs hk)) (kKs' : ↥t'.r.z.core.Q.c.F →+* ↥(w.st (upL Z S' N h)).toD7.LL0) (hk' : ∀ x, ((kKs' x : ↥(w.st (upL Z S' N h)).toD7.LL0) : (w.st (upL Z S' N h)).toD7.what₂.LL) = algebraMap _ (w.st (upL Z S' N h)).toD7.what₂.LL x) (YS' : Formalism.IndefR.NX.NExpRealS t'.r.z.R t'.r.z.cG (Formalism.IndefR.NX.ratDatR t'.r.z.R t'.r.z.cG kKs' hk')), HEq kKs' kKs → HEq YS'.fi YS.fi → HEq YS'.eF YS.eF → ∀ (a : _root_.GlobalTheory.HeightCounting.NAllCAlt (w.D Z) nch) (X' : Formalism.L2.NExpTied (w.st (upL Z S' N h)).toD7), HEq X' ((_root_.UpperTheory.One.M.mvAll_alt trivial) (mvOf w Z S' N h) a).exp → ∀ (PV : ∀ i : Fin (w.st Z).toD7.R.m, Formalism.IndefR.principalLevelFrame.RowPsi (Formalism.IndefR.Links.Vc (w.st Z).toD7 i) (w.st Z).toD7.R.nV) (PV' : ∀ i : Fin (w.st (upL Z S' N h)).toD7.R.m, Formalism.IndefR.principalLevelFrame.RowPsi (Formalism.IndefR.Links.Vc (w.st (upL Z S' N h)).toD7 i) (w.st (upL Z S' N h)).toD7.R.nV), HEq (fun i => (PV' i).ψ) (fun i => (PV i).ψ) → ∀ Pq Pq', HEq Pq' Pq → SerAt (D := (w.st Z).toD7) YS t.r.z.geo.v₀ a.exp PV (TC.cf w.I w.l Z) Pq → Nonempty (SerAt (D := (w.st (upL Z S' N h)).toD7) YS' t'.r.z.geo.v₀ X' PV' (TC.cf w.I w.l (upL Z S' N h)) Pq') := by
  intro K B f T w Z Wt S' N h nch p0 t p0' t' hs hg
  cases t' with | mk hX' r' exAt' inGeo' grpAt' grp' mu' exact' untw' emt0' emt' etaF' rowInt' idx' => ?_
  cases r' with | mk z' holds' Y' ZZ' tupix' => ?_
  cases z' with | mk Xg' tr' core' alg_eq' R' cG' geo' pins' lev' idG' good' muz' le' ks' => ?_
  rename_i alg'
  have e1 : Xg' = t.r.z.Xg := hs.Xg
  have e2 : tr' = t.r.z.tr := hs.tr
  subst e1 e2
  have e3 : core' = R3.Tr.coreJ (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (upL Z S' N h) t.r.z.core := eq_of_heq hs.core
  subst e3
  have e4 : alg' = t.r.z.alg := by
    apply Algebra.algebra_ext
    intro y
    apply (w.D Z).what₂.embLL.injective
    exact (alg_eq' y).trans (t.r.z.alg_eq y).symm
  subst e4
  have e5 : R' = R3.Tr.real3 (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (upL Z S' N h) (iK := t.r.z.alg) t.r.z.R := eq_of_heq hs.R
  subst e5
  have e6 : cG' = t.r.z.cG := eq_of_heq hs.cG
  subst e6
  have e7 : geo' = (by with_unfolding_all exact ((R3.Tr.geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo) :)) := eq_of_heq ((by with_unfolding_all exact (hg :)))
  subst e7
  intro kKs hk YS kKs' hk' YS' hkk hfi heF a X' hX PV PV' hPV Pq Pq' hPq s
  have e8 : kKs' = (by with_unfolding_all exact (kKs :)) := eq_of_heq ((by with_unfolding_all exact (hkk :)))
  subst e8
  obtain ⟨fi', geq', rho', chi', eF', bsup', act'⟩ := YS'
  have e9 : fi' = (by with_unfolding_all exact (YS.fi :)) := eq_of_heq ((by with_unfolding_all exact (hfi :)))
  have e10 : eF' = (by with_unfolding_all exact (YS.eF :)) := eq_of_heq ((by with_unfolding_all exact (heF :)))
  subst e9 e10
  have e11 : X' = (by with_unfolding_all exact (((_root_.UpperTheory.One.M.mvAll_alt trivial) (mvOf w Z S' N h) a).exp :)) := eq_of_heq ((by with_unfolding_all exact (hX :)))
  have e12 : Pq' = (by with_unfolding_all exact (Pq :)) := eq_of_heq ((by with_unfolding_all exact (hPq :)))
  subst e11 e12
  have e13 : (fun i => (PV' i).ψ) = (by with_unfolding_all exact ((fun i => (PV i).ψ) :)) := eq_of_heq ((by with_unfolding_all exact (hPV :)))
  have e14 : PV' = fun j => @Formalism.IndefR.principalLevelFrame.RowPsi.mk _ _ _ ((by with_unfolding_all exact ((PV ((j))).ψ : _))) ((by with_unfolding_all exact ((PV ((j))).inj : _))) ((by with_unfolding_all exact ((PV ((j))).into : _)))
      ((by with_unfolding_all exact ((PV ((j))).onto : _))) := funext fun j => SerUp.rowPsi_ext ((by with_unfolding_all exact ((congrFun e13 j) :)))
  subst e14
  exact ⟨@SerAt.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (ex := (by with_unfolding_all exact ((@SerUp.ex B w.C Z.W ⟨Z.V, Z.S, Z.N, Z.G⟩ (upL Z S' N h).V S' _ _ _ _ _ _ _ _ _ _ t.r.z.alg t.r.z.R t.r.z.cG _ YS
      t.r.z.geo.v₀ s.ex) :)))
    (bad := (by with_unfolding_all exact (s.bad :))) (ch := (by with_unfolding_all exact (s.ch :))) (join := (by with_unfolding_all exact (s.join :))) (sup := (by with_unfolding_all exact (s.sup :))) (off := (by with_unfolding_all exact (s.off :)))
    (lam := (by with_unfolding_all exact (((mvOf w Z S' N h).lam s.lam) :)))
    (lam_ok := (by with_unfolding_all exact (((mvOf w Z S' N h).lam_ok s.lam_ok) :)))
    (lam_teich := (by with_unfolding_all exact (((mvOf w Z S' N h).lam_teich s.lam_teich) :)))
    (lam_C := (by with_unfolding_all exact ((congrArg (mvOf w Z S' N h).cf s.lam_C) :)))
    (lam_q := (by with_unfolding_all exact (s.lam_q :)))
    (lam_tie := (by with_unfolding_all exact (((mvOf w Z S' N h).lam_tie s.lam_tie) :)))⟩
end
