import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.Mem.R3.Tr Formalism.BasicNotions.TH

set_option maxHeartbeats 4000000
noncomputable section
namespace GlobalTheory.Mem.GridMove
open GlobalTheory.ChiGrid
variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {T : Type}

def plC {L : Formalism.IndefR.Links.LevCh a.D T} (P : Places L) : Places (levCh b L) where
  v0 := (by with_unfolding_all exact (P.v0 :))
  basePlace_over_qZero := (by with_unfolding_all exact (P.basePlace_over_qZero :))
  w := (by with_unfolding_all exact (P.w :))
  w_over := (by with_unfolding_all exact (P.w_over :))
  w_split := (by with_unfolding_all exact (P.w_split :))
  w_g := (by with_unfolding_all exact (P.w_g :))
  w_de := (by with_unfolding_all exact (P.w_de :))
  w_Q := (by with_unfolding_all exact (P.w_Q :))
  levelPlace_ne_basePlace := (by with_unfolding_all exact (P.levelPlace_ne_basePlace :))

def chC {L : Formalism.IndefR.Links.LevCh a.D T} {P : Places L} {c : ℝ} (X : Chars P c) : Chars (plC b P) c where
  chiH := (by with_unfolding_all exact (X.chiH :))
  chi := (by with_unfolding_all exact (X.chi :))
  chi_eq := (by with_unfolding_all exact (X.chi_eq :))
  triv := (by with_unfolding_all exact (X.triv :))
  inf := (by with_unfolding_all exact (X.inf :))
  unr := (by with_unfolding_all exact (X.unr :))
  lev1 := (by with_unfolding_all exact (X.lev1 :))
  wild := (by with_unfolding_all exact (X.wild :))
  lev0 := (by with_unfolding_all exact (X.lev0 :))

def lsC (X : LSp a.D) : LSp b.D := ⟨(by with_unfolding_all exact (X.sp :)), (by with_unfolding_all exact (X.lat :))⟩

theorem isVC {X : LSp a.D} {ν q : ℕ} (h : X.IsV ν q) : (lsC b X).IsV ν q :=
  ⟨(by with_unfolding_all exact (h.rank :)), (by with_unfolding_all exact (h.sigOK :)), (by with_unfolding_all exact (h.sig :)), (by with_unfolding_all exact (h.sd :))⟩

def adC {A B' : HSp a.D} {c : ℕ} {ε : a.D.host.E} (d : HermitianOrthogonalExtensionData A B' c ε) :
    @HermitianOrthogonalExtensionData b.D ((A)) ((B')) c ((ε)) where
  ι := (by with_unfolding_all exact (d.ι :))
  isom := (by with_unfolding_all exact (d.isom :))
  a := (by with_unfolding_all exact (d.a :))
  gram := (by with_unfolding_all exact (d.gram :))
  perp := (by with_unfolding_all exact (d.perp :))
  rank := (by with_unfolding_all exact (d.rank :))

section V
open scoped nonZeroDivisors
variable {L : Formalism.IndefR.Links.LevCh a.D T} (Vs : ℕ → ℕ → LSp a.D) (Xs : ℕ → LSp a.D)

def gridColumnVertexDecompTransport (P : ℕ → LSp a.D) : ∀ (i : ℕ) (_ : 1 ≤ i) (_ : HermitianOrthogonalExtensionData (P i).sp (vtxOf L Vs i 0).sp (i - 1) (-1)),
    HermitianOrthogonalExtensionData (lsC b (P i)).sp (vtxOf (levCh b L) (fun i j => lsC b (Vs i j)) i 0).sp (i - 1) (-1)
  | 0, h, _ => absurd h (by omega)
  | _ + 1, _, d => (adC b d :)

theorem gridStaircaseLattice_firstColumn_transportStages (P : ℕ → LSp a.D) : ∀ (i : ℕ) (h : 1 ≤ i) (d : HermitianOrthogonalExtensionData (P i).sp (vtxOf L Vs i 0).sp (i - 1) (-1))
    (𝔟 : Fin (i - 1) → FractionalIdeal (𝓞 a.D.host.E)⁰ a.D.host.E),
    (vtxOf L Vs i 0).lat = d.lat (P i).lat 𝔟 →
    (vtxOf (levCh b L) (fun i j => lsC b (Vs i j)) i 0).lat = (gridColumnVertexDecompTransport b Vs P i h d).lat (lsC b (P i)).lat ((𝔟))
  | 0, h, _, _, _ => absurd h (by omega)
  | _ + 1, _, _, _, e => (e)

def gridInteriorVertexDecompTransport (j : ℕ) : ∀ (n : ℕ) (_ : j + 1 < n) (_ : HermitianOrthogonalExtensionData (Xs (j + 1)).sp (vtxOf L Vs n (j + 1)).sp (n - 1 - (j + 1)) (-1)),
    HermitianOrthogonalExtensionData (lsC b (Xs (j + 1))).sp (vtxOf (levCh b L) (fun i j => lsC b (Vs i j)) n (j + 1)).sp (n - 1 - (j + 1)) (-1)
  | 0, h, _ => absurd h (by omega)
  | _ + 1, _, d => (adC b d :)

theorem gridLastRowVertexLattice_transportStages (j : ℕ) : ∀ (n : ℕ) (h : j + 1 < n) (d : HermitianOrthogonalExtensionData (Xs (j + 1)).sp (vtxOf L Vs n (j + 1)).sp (n - 1 - (j + 1)) (-1))
    (𝔟 : Fin (n - 1 - (j + 1)) → FractionalIdeal (𝓞 a.D.host.E)⁰ a.D.host.E),
    (vtxOf L Vs n (j + 1)).lat = d.lat (Xs (j + 1)).lat 𝔟 →
    (vtxOf (levCh b L) (fun i j => lsC b (Vs i j)) n (j + 1)).lat = (gridInteriorVertexDecompTransport b Vs Xs j n h d).lat (lsC b (Xs (j + 1))).lat ((𝔟))
  | 0, h, _, _, _ => absurd h (by omega)
  | _ + 1, _, _, _, e => (e)

def gridDiagonalVertexDecompTransport (X0 : LSp a.D) : ∀ (n : ℕ) (_ : 1 ≤ n) (_ : HermitianOrthogonalExtensionData (vtxOf L Vs n n).sp (xOf X0 Xs n).sp 1 1),
    HermitianOrthogonalExtensionData (vtxOf (levCh b L) (fun i j => lsC b (Vs i j)) n n).sp (xOf (lsC b X0) (fun j => lsC b (Xs j)) n).sp 1 1
  | 0, h, _ => absurd h (by omega)
  | _ + 1, _, d => (adC b d :)

theorem gridTopVertexLattice_transportStages (X0 : LSp a.D) : ∀ (n : ℕ) (h : 1 ≤ n) (d : HermitianOrthogonalExtensionData (vtxOf L Vs n n).sp (xOf X0 Xs n).sp 1 1),
    (xOf X0 Xs n).lat = d.lat (vtxOf L Vs n n).lat (fun _ => 1) →
    (xOf (lsC b X0) (fun j => lsC b (Xs j)) n).lat = (gridDiagonalVertexDecompTransport b Vs Xs X0 n h d).lat (vtxOf (levCh b L) (fun i j => lsC b (Vs i j)) n n).lat (fun _ => 1)
  | 0, h, _, _ => absurd h (by omega)
  | _ + 1, _, _, e => (e)

end V

section W
open scoped nonZeroDivisors
variable {L : Formalism.IndefR.Links.LevCh a.D T}

def vtC {𝔞 𝔞' : FractionalIdeal (𝓞 a.D.host.E)⁰ a.D.host.E} (V : Vertices L 𝔞 𝔞') :
    Vertices (levCh b L) ((𝔞)) ((𝔞')) where
  Vs i j := lsC b (V.Vs i j)
  P i := lsC b (V.P i)
  Xs j := lsC b (V.Xs j)
  V_is i j h1 h2 h3 := (by with_unfolding_all exact ((isVC b (V.V_is i j h1 h2 h3)) :))
  P_is i h := (by with_unfolding_all exact ((isVC b (V.P_is i h)) :))
  X_is j h1 h2 := (by with_unfolding_all exact ((isVC b (V.X_is j h1 h2)) :))
  dec0 := (by with_unfolding_all exact ((adC b V.dec0) :))
  lat0 := (by with_unfolding_all exact (V.lat0 :))
  colDec i h h' := gridColumnVertexDecompTransport b V.Vs V.P i h (V.colDec i h h')
  colLat i h h' := (by with_unfolding_all exact ((gridStaircaseLattice_firstColumn_transportStages b V.Vs V.P i h (V.colDec i h h') _ (V.colLat i h h')) :))
  rowDecS j h := (by with_unfolding_all exact ((gridInteriorVertexDecompTransport b V.Vs V.Xs j a.D.R.m h (V.rowDecS j h)) :))
  rowLat j h := (by with_unfolding_all exact ((gridLastRowVertexLattice_transportStages b V.Vs V.Xs j a.D.R.m h (V.rowDecS j h) _ (V.rowLat j h)) :))
  topDec := (by with_unfolding_all exact ((gridDiagonalVertexDecompTransport b V.Vs V.Xs (V.P a.D.R.m) a.D.R.m (by have := a.D.R.two_le_m; omega) V.topDec) :))
  topLat := (by with_unfolding_all exact ((gridTopVertexLattice_transportStages b V.Vs V.Xs (V.P a.D.R.m) a.D.R.m (by have := a.D.R.two_le_m; omega) V.topDec V.topLat) :))

def gdC {sc : Consts} (G : GridData L sc) : GridData (levCh b L) sc where
  pl := plC b G.pl
  ch := chC b G.ch
  sp := (by with_unfolding_all exact ((vtC b G.sp) :))

end W

section Y
variable {L : Formalism.IndefR.Links.LevCh a.D T}

theorem listPin_upL (S' : SStage B C a.W) (Nn : ∀ u, Submodule (𝓞 B.LL) (a.V.div.Nu u).V) (hh : B.Word → ℝ) (c bb : ℝ)
    (h : ListPin a.D L c bb) : ListPin (upL a S' Nn hh).D (levCh (upL a S' Nn hh) L) c bb := by
  obtain ⟨G, h1, h2⟩ := h
  exact ⟨gdC _ G, ⟨(by with_unfolding_all exact (h1.values :)), (by with_unfolding_all exact (h1.roots :))⟩, (by with_unfolding_all exact (h2 :))⟩
end Y

set_option maxHeartbeats 4000000 in

theorem listPin_rowsSame : ∀ (cDep b : ℝ) (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (p0' : BaseLevelRowSide (w.D (upL Z S' N h))) (t' : RowsT K w (upL Z S' N h) Wt p0'), RowsSame t t' → ListPin (w.st Z).toD7 t.r.z.R.toRealDat.toLevCh cDep b → ListPin (w.st (upL Z S' N h)).toD7 t'.r.z.R.toRealDat.toLevCh cDep b := by
  intro cDep b K B f T w Z Wt S' N h p0 t p0' t' hs hp
  cases t' with | mk hX' r' => ?_
  cases r' with | mk z' => ?_
  cases z' with | @mk Xg' tr' core' alg' alg_eq' R' => ?_
  have hXg := hs.Xg
  have htr := hs.tr
  have hcore := hs.core
  have hR := hs.R
  clear hs
  change Xg' = t.r.z.Xg at hXg
  change tr' = t.r.z.tr at htr
  subst hXg htr
  change HEq core' _ at hcore
  have hc := eq_of_heq hcore
  subst hc
  have ha : alg' = GlobalTheory.Mem.R3.Tr.alg (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩)
      ⟨(upL Z S' N h).W, (upL Z S' N h).V, (upL Z S' N h).S, (upL Z S' N h).N, (upL Z S' N h).G⟩ t.r.z.alg := by
    apply Algebra.algebra_ext
    intro r
    apply (w.st (upL Z S' N h)).B.embLL.injective
    exact (by with_unfolding_all exact (((alg_eq' r).trans (t.r.z.alg_eq r).symm) :))
  subst ha
  change HEq R' _ at hR
  have hR2 := eq_of_heq hR
  subst hR2
  exact (by with_unfolding_all exact ((listPin_upL (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) S' N h cDep b hp) :))

end GlobalTheory.Mem.GridMove

end
