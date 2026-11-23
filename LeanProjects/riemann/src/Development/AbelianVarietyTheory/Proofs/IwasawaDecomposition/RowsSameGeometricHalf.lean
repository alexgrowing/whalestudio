import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChoiceSide
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CongrFunHeq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumEq

noncomputable section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting.SerCopy
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

namespace GlobalTheory.LayerMove.SerUp

theorem rowPsi_ext {D : D7} {V : HSp D} {n : ℕ} {p q : principalLevelFrame.RowPsi V n} (h : p.ψ = q.ψ) : p = q := by
  cases p; cases q; cases h; rfl

variable {B : GlobalTheory.Mem.Base} {C : Cols B} {W : RowsRest B C} (o : Oth W) (V' : DivStage B C W) (S' : SStage B C W)

def o2 : Oth W := ⟨V', S', o.N, o.G⟩

variable {o} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 o.L.D.what₂.LL G Pl0 I0 (List ℕ) T o.L.D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks o.L.D.what₂.LL] {R : RealDat3 o.L.D A3 Ks}
  {cG : G0 R.Pg o.L.D.R.r ≃* G0g o.L.D.nd} {S : RatDat o.L.D.ntw} {YS : NExpRealS R cG S}
  {v₀ : ∀ (j : Fin o.L.D.R.m) (σ : o.L.D.what₂.LL →+* ℂ), (R.MW j σ).Vec}

set_option hygiene false in
local notation "bb" => Oth.L (o2 o V' S')

variable (YS) in

def ys : @NExpRealS (Late.D bb) G _ _ Pl0 I0 T (famInThreeCoefficientChange bb A3) Ks _ _ (alg bb iK) (real3 bb R) ((cG)) ((S)) :=
  @NExpRealS.mk (Late.D bb) G _ _ Pl0 I0 T (famInThreeCoefficientChange bb A3) Ks _ _ (alg bb iK) (real3 bb R) ((by with_unfolding_all exact (cG :))) ((by with_unfolding_all exact (S :)))
    (fi := (by with_unfolding_all exact (YS.fi :))) (geq := (by with_unfolding_all exact (YS.geq :))) (rho := (by with_unfolding_all exact (YS.rho :))) (chi := (by with_unfolding_all exact (YS.chi :))) (eF := (by with_unfolding_all exact (YS.eF :))) (bsup := (by with_unfolding_all exact (YS.bsup :)))
    (act := (by with_unfolding_all exact (YS.act :)))

def rho (ρ : Setup o.L.D.ntw) : Setup (Late.D bb).ntw := (by with_unfolding_all exact ((seT (o2 o V' S') ρ) :))

theorem good {ρ : Setup o.L.D.ntw} (h : ρ.Good) : (rho V' S' ρ).Good := (by with_unfolding_all exact ((seGood (o2 o V' S') h) :))

theorem pin {ρ : Setup o.L.D.ntw} (p : RealPin R cG ρ) :
    @RealPin (Late.D bb) G _ _ Pl0 I0 T (famInThreeCoefficientChange bb A3) Ks _ _ (alg bb iK) (real3 bb R) ((cG)) (rho V' S' ρ) :=
  @RealPin.mk (Late.D bb) G _ _ Pl0 I0 T (famInThreeCoefficientChange bb A3) Ks _ _ (alg bb iK) (real3 bb R) ((by with_unfolding_all exact (cG :))) (rho V' S' ρ)
    ((by with_unfolding_all exact (p.psi :))) ((by with_unfolding_all exact (p.inf :))) ((by with_unfolding_all exact (p.cartT :))) ((by with_unfolding_all exact (p.onbS :))) ((by with_unfolding_all exact (p.onbT :))) ((by with_unfolding_all exact (p.latS :))) ((by with_unfolding_all exact (p.latT :))) ((by with_unfolding_all exact (p.frS :)))
    ((by with_unfolding_all exact (p.frT :))) ((by with_unfolding_all exact (p.vac :))) ((by with_unfolding_all exact (p.Pg :))) ((by with_unfolding_all exact (p.grp :))) ((by with_unfolding_all exact (p.mu0 :))) ((by with_unfolding_all exact (p.eta :))) ((by with_unfolding_all exact (p.delta :))) ((by with_unfolding_all exact (p.deltaPl :)))
    ((by with_unfolding_all exact (p.ap :))) ((by with_unfolding_all exact (p.am :)))

variable (R v₀) in
theorem norm_iff (ρ : Setup o.L.D.ntw) (i : o.L.D.ntw.Tw) (j : Fin o.L.D.R.m) (b : Bool) (ν : ℂ) :
    @IsNorm (Late.D bb) G _ _ Pl0 I0 T (famInThreeCoefficientChange bb A3) Ks _ _ (alg bb iK) (real3 bb R) ((v₀)) ((j))
      ((rho V' S' ρ).B ((i)) ((j)) b) ν ↔ IsNorm R v₀ (ρ.B i j b) ν := by
  constructor
  · rintro ⟨h0, c, ⟨g, c0R, c0L, hF, u, hu, hh⟩, hn⟩
    exact ⟨h0, c, ⟨(by with_unfolding_all exact (g :)), (by with_unfolding_all exact (c0R :)), (by with_unfolding_all exact (c0L :)),
      kc% (famTie_imp (a := bb) o.L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hF), (by with_unfolding_all exact (u :)), (by with_unfolding_all exact (hu :)), (by with_unfolding_all exact (hh :))⟩, (by with_unfolding_all exact (hn :))⟩
  · rintro ⟨h0, c, ⟨g, c0R, c0L, hF, u, hu, hh⟩, hn⟩
    exact ⟨h0, c, ⟨(by with_unfolding_all exact (g :)), (by with_unfolding_all exact (c0R :)), (by with_unfolding_all exact (c0L :)),
      kc% (famTie_imp (a := o.L) bb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hF), (by with_unfolding_all exact (u :)), (by with_unfolding_all exact (hu :)), (by with_unfolding_all exact (hh :))⟩, (by with_unfolding_all exact (hn :))⟩

variable (YS v₀) in
theorem rat_iff {ρ : Setup o.L.D.ntw} (hρ : ρ.Good) (i : o.L.D.ntw.Tw) (j : Fin o.L.D.R.m) (b : Bool) (ν : ℂ) :
    SeriesTie.Rat (good V' S' hρ) (@realRd (Late.D bb) G _ _ Pl0 I0 T (famInThreeCoefficientChange bb A3) Ks _ _ (alg bb iK) (real3 bb R) ((cG)) ((S))
      (ys V' S' YS) ((v₀)) _ (good V' S' hρ) ((i)) ((j)) b ν) ↔ SeriesTie.Rat hρ (realRd YS v₀ hρ i j b ν) :=
  ⟨fun h => @ratT' B C W o (o2 o V' S') _ _ ρ i j b _ (realRd YS v₀ hρ i j b ν) hρ ((by with_unfolding_all exact (h :))),
    fun h => (by with_unfolding_all exact ((@ratT B C W o (o2 o V' S') _ _ ρ i j b _ (realRd YS v₀ hρ i j b ν) hρ h) :))⟩

theorem scalar {ρ : Setup o.L.D.ntw} {hρ : ρ.Good} {i : o.L.D.ntw.Tw} {j : Fin o.L.D.R.m} {b : Bool} {ν : ℂ}
    (h : IsScalar YS v₀ hρ i j b ν) :
    @IsScalar (Late.D bb) G _ _ Pl0 I0 T (famInThreeCoefficientChange bb A3) Ks _ _ (alg bb iK) (real3 bb R) ((cG)) ((S))
      (ys V' S' YS) ((v₀)) _ (good V' S' hρ) ((i)) ((j)) b ν :=
  @IsScalar.mk (Late.D bb) G _ _ Pl0 I0 T (famInThreeCoefficientChange bb A3) Ks _ _ (alg bb iK) (real3 bb R) ((by with_unfolding_all exact (cG :))) ((by with_unfolding_all exact (S :)))
      (ys V' S' YS) ((by with_unfolding_all exact (v₀ :))) _ (good V' S' hρ) ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b ν h.ne
    (fun h' => (norm_iff V' S' R v₀ ρ i j b _).2 (h.norm (h'.imp fun ν => (norm_iff V' S' R v₀ ρ i j b ν).1)))
    (fun h' => (rat_iff V' S' YS v₀ hρ i j b _).2 (h.rat (h'.imp fun ν h'' =>
      ⟨(norm_iff V' S' R v₀ ρ i j b ν).1 h''.1, (rat_iff V' S' YS v₀ hρ i j b ν).1 h''.2⟩)))

def ex (p : ExportTie YS v₀) :
    @ExportTie (Late.D bb) G _ _ Pl0 I0 T (famInThreeCoefficientChange bb A3) Ks _ _ (alg bb iK) (real3 bb R) ((cG)) ((S)) (ys V' S' YS) ((v₀)) :=
  @ExportTie.mk (Late.D bb) G _ _ Pl0 I0 T (famInThreeCoefficientChange bb A3) Ks _ _ (alg bb iK) (real3 bb R) ((by with_unfolding_all exact (cG :))) ((by with_unfolding_all exact (S :))) (ys V' S' YS) ((by with_unfolding_all exact (v₀ :)))
    (ρ := rho V' S' p.ρ)
    (good := good V' S' p.good)
    (pin := pin V' S' p.pin)
    (vec := (by with_unfolding_all exact (p.vec :)))
    (ν := (by with_unfolding_all exact (p.ν :)))
    (scalar := fun i j b => (by with_unfolding_all exact ((scalar V' S' (p.scalar ((i)) ((j)) b)) : _)))
    (tie := fun i j b => (by with_unfolding_all exact ((cellT (o2 o V' S') (p.tie ((i)) ((j)) b)) : _)))
    (hecke := fun i j b => (by with_unfolding_all exact ((heckeTieT (o2 o V' S') (p.hecke ((i)) ((j)) b)) : _)))
    (univ := (by with_unfolding_all exact (p.univ :)))

end GlobalTheory.LayerMove.SerUp
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
open GlobalTheory.LayerMove
set_option maxHeartbeats 1000000
theorem _root_.GlobalTheory.T.rows_same_geometric_half : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (nch : NChoice (w.D Z)) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (p0' : BaseLevelRowSide (w.D (upL Z S' N h))) (t' : RowsT K w (upL Z S' N h) Wt p0'), RowsSame t t' → HEq t'.r.z.geo (R3.Tr.geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo) → ∀ (kKs : ↥t.r.z.core.Q.c.F →+* ↥(w.st Z).toD7.LL0) (hk : ∀ x, ((kKs x : ↥(w.st Z).toD7.LL0) : (w.st Z).toD7.what₂.LL) = algebraMap _ (w.st Z).toD7.what₂.LL x) (YS : Formalism.IndefR.NX.NExpRealS t.r.z.R t.r.z.cG (Formalism.IndefR.NX.ratDatR t.r.z.R t.r.z.cG kKs hk)) (kKs' : ↥t'.r.z.core.Q.c.F →+* ↥(w.st (upL Z S' N h)).toD7.LL0) (hk' : ∀ x, ((kKs' x : ↥(w.st (upL Z S' N h)).toD7.LL0) : (w.st (upL Z S' N h)).toD7.what₂.LL) = algebraMap _ (w.st (upL Z S' N h)).toD7.what₂.LL x) (YS' : Formalism.IndefR.NX.NExpRealS t'.r.z.R t'.r.z.cG (Formalism.IndefR.NX.ratDatR t'.r.z.R t'.r.z.cG kKs' hk')), HEq kKs' kKs → HEq YS'.fi YS.fi → HEq YS'.eF YS.eF → ∀ (a : NAllC (w.D Z) nch) (X' : Formalism.L2.NExpTied (w.st (upL Z S' N h)).toD7), HEq X' ((mvOf w Z S' N h).all a).exp → ∀ (PV : ∀ i : Fin (w.st Z).toD7.R.m, Formalism.IndefR.principalLevelFrame.RowPsi (Formalism.IndefR.Links.Vc (w.st Z).toD7 i) (w.st Z).toD7.R.nV) (PV' : ∀ i : Fin (w.st (upL Z S' N h)).toD7.R.m, Formalism.IndefR.principalLevelFrame.RowPsi (Formalism.IndefR.Links.Vc (w.st (upL Z S' N h)).toD7 i) (w.st (upL Z S' N h)).toD7.R.nV), HEq (fun i => (PV' i).ψ) (fun i => (PV i).ψ) → ∀ Pq Pq', HEq Pq' Pq → SerAt (D := (w.st Z).toD7) YS t.r.z.geo.v₀ a.exp PV (TC.cf w.I w.l Z) Pq → Nonempty (SerAt (D := (w.st (upL Z S' N h)).toD7) YS' t'.r.z.geo.v₀ X' PV' (TC.cf w.I w.l (upL Z S' N h)) Pq') := by
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
  have e11 : X' = (by with_unfolding_all exact (((mvOf w Z S' N h).all a).exp :)) := eq_of_heq ((by with_unfolding_all exact (hX :)))
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
