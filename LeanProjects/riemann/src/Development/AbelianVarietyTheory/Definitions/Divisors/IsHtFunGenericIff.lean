import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveV
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjectiveRepresentationPullbackCoordinates

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial Filter Topology TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.Points GlobalTheory.CovTest

namespace GlobalTheory.VdmRec

section Free

variable {k : Type} [CommRing k] {X : Scheme.{0}} {ι : Type} [Fintype ι]

abbrev clo (z : X) : Closeds X := ⟨closure {z}, isClosed_closure⟩

instance isIntegral_clo (z : X) : IsIntegral (Scheme.IdealSheafData.vanishingIdeal (clo z)).subscheme :=
  isIntegral_red (Z := clo z) isIrreducible_singleton.closure

open Classical in

def cutMult [IsLocallyNoetherian X] {L : LB X} (hL : L.IsLB) (s : L.Sec) (z w : X) : ℤ :=
  haveI : IsLocallyNoetherian (Scheme.IdealSheafData.vanishingIdeal (clo z)).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (redι (clo z))
  if h : genericPoint _ ∈ Out.nonzeroLocus (GlobalTheory.ZM.RepBC.secPull L (redι (clo z)) s) then
    Function.extend (redι (clo z)) (divOfSec (LB.isLB_pull hL _) _ h).mult 0 w
  else 0

def degAt (p : X ⟶ Sp k) (L : LB X) (z : X) (n : ℕ) : ℤ :=
  topSelfIntersection ℂ ((L.pull (redι (clo z))).pull (cxFibre.fst (redι (clo z) ≫ p))) n

def IsHtFun {p : X ⟶ Sp k} (L : ι → HermLB p) (y : X) (D : ℕ) (Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) : Prop :=
  (∀ n : ι → ℤ, ∃ h, (comb L n).IsArithHeight h ∧ h y = Φ (lin (fun i => (n i : ℝ)) ^ D)) ∧
    ∀ (P : MvPolynomial ι ℝ) (d : ℕ), d ≠ D → P.IsHomogeneous d → Φ P = 0

def IsIntFun {p : X ⟶ Sp k} (L : ι → HermLB p) (f : ∀ σ : k →+* ℂ, CxPts p σ → ℝ) (D : ℕ)
    (Λ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) : Prop :=
  (∀ n : ι → ℤ, Λ (lin (fun i => (n i : ℝ)) ^ D) = chInt (comb L n) D f) ∧
    ∀ (P : MvPolynomial ι ℝ) (d : ℕ), d ≠ D → P.IsHomogeneous d → Λ P = 0

theorem isHtFun_generic_iff [IsIntegral X] {p : X ⟶ Sp k} (L : ι → HermLB p) (D : ℕ) (Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) :
    IsHtFun L (genericPoint X) (D + 1) Φ ↔ IsArFun L D Φ :=
  Iff.rfl

theorem isIntFun_one_iff {p : X ⟶ Sp k} (L : ι → HermLB p) (D : ℕ) (Λ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) :
    IsIntFun L (fun _ _ => 1) D Λ ↔ IsGeoFun L D Λ :=
  Iff.rfl

def vdmPol (r e : ℕ) : MvPolynomial (Option (Fin r)) ℝ :=
  C ((r.factorial : ℝ)⁻¹) * (∑ i : Fin r, MvPolynomial.X (some i) ^ 2) *
    (∏ i : Fin r, ∏ i' ∈ Finset.Ioi i, (MvPolynomial.X (some i') - MvPolynomial.X (some i))) * MvPolynomial.X none ^ e

theorem vdmPol_one (e : ℕ) : vdmPol 1 e = MvPolynomial.X (some 0) ^ 2 * MvPolynomial.X none ^ e := by
  simp [vdmPol]

structure FlagSp (E : X.Modules) (r : ℕ) : Type 1 where

  Y : Scheme.{0}

  π : Y ⟶ X

  fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) r
  univ : IsFlagBundle π (fun _ : Unit => E) (fun _ => r) (fun _ => fl)

def FlagSp.ofRankOne {E : X.Modules} (hE : IsVB E 1) : FlagSp E 1 :=
  ⟨X, 𝟙 X, .ofRankOne (hE.pullback _), isFlagBundle_rank_one X (fun _ : Unit => E) _⟩

namespace FlagSp

variable {p : X ⟶ Sp k} {E : X.Modules} {r : ℕ} (F : FlagSp E r) {h : VMetric p E r}

def IsTop (z : X) (y : F.Y) : Prop := F.π y = z ∧ ∀ y', F.π y' = z → y ⤳ y'

def fam (H : h.IsCInf) (N : HermLB p) : Option (Fin r) → HermLB (F.π ≫ p) :=
  fun o => o.elim (N.pull F.π rfl) fun i => VMetric.grLB F.fl i (H.pull F.π rfl)

def IsVal (H : h.IsCInf) (N : HermLB p) (z : X) (e : ℕ) (a : ℝ) : Prop :=
  ∃ y Φ, F.IsTop z y ∧ IsHtFun (F.fam H N) y (e + 2 + r.choose 2) Φ ∧ Φ (vdmPol r e) = a

def val (H : h.IsCInf) (N : HermLB p) (z : X) (e : ℕ) : ℝ := Classical.epsilon (F.IsVal H N z e)

def IsArch (H : h.IsCInf) (N M : HermLB p) (s : M.B.Sec) (z : X) (e : ℕ) (a : ℝ) : Prop :=
  ∃ y Λ, F.IsTop z y ∧ IsIntFun (fun o => (F.fam H N o).restr (redι (clo y)))
    (fun σ v => Real.log ((M.φ σ).nsq (secVal p σ s)
      (PtsOver.map (redι (clo y) ≫ F.π) (Category.assoc _ _ _) (spMap σ) v)) / 2) (e + 2 + r.choose 2) Λ ∧
    Λ (vdmPol r e) = a

def arch (H : h.IsCInf) (N M : HermLB p) (s : M.B.Sec) (z : X) (e : ℕ) : ℝ := Classical.epsilon (F.IsArch H N M s z e)

end FlagSp

end Free

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal
open GlobalTheory.LieVB (omega unitSec dUnit)

def IsDualEig {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l}
    {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz] {β : Oz →+* c.F}
    {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} (G : ∀ σ', EigMet Z σ') {g : ℕ} (h : VMetric Z.s (omega Z.t.G) g) : Prop :=
  ∀ (σ' : c.F →+* ℂ) (yc : CxPts (genStr Z) σ') (y : CxPts Z.s (σ'.comp β)), y.1 = yc.1 ≫ genι Z →
    ∀ (u : EigFrame Z σ' (yc.1 ≫ genι Z)) (U : Z.X.Opens) (W : Z.t.G.left.Opens) (hU : U ≤ unitSec Z.t.G ⁻¹ᵁ W)
      (f f' : Γ(Z.t.G.left, W)), y ∈ ptsIn Z.s (σ'.comp β) U →
      (h.met (σ'.comp β)).form (dUnit Z.t.G hU f) (dUnit Z.t.G hU f') y =
        ∑ τ : E →+* ℂ, HermFrame.form ((G σ').gram yc u τ)⁻¹ (fun i => (valR (u.v τ i) W f).snd)
          fun i => (valR (u.v τ i) W f').snd

structure DRBase {D : D7} (O : Setup D) (c : O.s.Comp) : Type 1 where

  x : ToroidalCompactificationData O.s

  P : PolOf x O.Φ
  core : O.CoreWith x P

  B : Scheme.{0}
  [int : IsIntegral B]

  b : B ⟶ O.s.T.Z.X
  [cl : IsClosedImmersion b]
  gen : b (genericPoint B) = genι O.s.T.Z ((O.Φ.C c).π (genericPoint (O.Φ.C c).Y.X))
  ar : IsArithVar (b ≫ O.s.T.Z.s) (dimGr D.what₂.Tau O.N O.j)

  h : ℝ → VMetric O.s.T.Z.s (omega O.s.T.Z.t.G) (D.R.f * O.N)
  H : ∀ R, (h R).IsCInf
  dual : ∀ R, IsDualEig (fun σ' => x.eigMetAt σ' (some R)) (h R)

  F : FlagSp ((Scheme.Modules.pullback b).obj (omega O.s.T.Z.t.G)) (D.R.f * O.N)

namespace DRBase

attribute [instance] int cl

variable {D : D7} {O : Setup D} {c : O.s.Comp} (M : DRBase O c)

instance : IsLocallyNoetherian M.B := M.ar.isLocallyNoetherian

abbrev q : M.B ⟶ Sp (𝓞 O.κ.c.F) := M.b ≫ O.s.T.Z.s

def lam (R : ℝ) : HermLB M.q := VMetric.det ((M.H R).pull M.b rfl)

def lamB : LB M.B := VB.det ((Scheme.Modules.pullback M.b).obj (omega O.s.T.Z.t.G)) (D.R.f * O.N)

theorem lam_B (R : ℝ) : (M.lam R).B = M.lamB :=
  rfl

theorem isLB_pow (m : ℕ) : (lbPow M.lamB m).IsLB :=
  M.lam_B 0 ▸ ((M.lam 0).pow m).isLB

def bd : Set M.B := {w | M.b w ∉ abLocus O.s.T.Z.t.G}

def val (R : ℝ) (z : M.B) (e : ℕ) : ℝ := M.F.val ((M.H R).pull M.b rfl) (M.lam R) z e

def arch (R : ℝ) (m : ℕ) (s : (lbPow M.lamB m).Sec) (z : M.B) (e : ℕ) : ℝ :=
  M.F.arch ((M.H R).pull M.b rfl) (M.lam R) ((M.lam R).pow m) s z e

def deg (z : M.B) (n : ℕ) : ℤ := degAt M.q M.lamB z n

structure Emb : Type where

  a : ℕ
  a_pos : 0 < a

  n : ℕ

  f : M.B ⟶ PSpace (𝓞 O.κ.c.F) n
  f_str : f ≫ PSpace.str _ n = M.q
  iso : LBIso ((ProjSpace.hermitianTwistingSheaf (𝓞 O.κ.c.F) n).B.pull f) (lbPow M.lamB a)

variable {M} in

def Emb.Good (I : M.Emb) (z : M.B) (e : ℕ) : Prop :=
  topologicalKrullDim (closure ({z} : Set M.B)) = (e + 2 : ℕ) ∧
    topologicalKrullDim (I.f '' (closure {z} ∩ M.bd)) + 3 ≤ (e + 2 : ℕ) ∧ (CharZero (M.B.residueField z) → z ∉ M.bd)

variable {M} in

def Emb.Cuts (I : M.Emb) {m : ℕ} (s : (lbPow M.lamB m).Sec) (z : M.B) (e : ℕ) : Prop :=
  z ∈ Out.nonzeroLocus s ∧ ∀ w, cutMult (M.isLB_pow m) s z w ≠ 0 → I.Good w e

end DRBase

def cNum {D : D7} (O : Setup D) (c : O.s.Comp) : MvPolynomial (Sym D.host.E →₀ ℤ) ℝ →ₗ[ℝ] ℝ :=
  numL ((arIn O.s O.Φ O.met.hm).num c) (dimFl D.what₂.Tau O.N + 1)

def termL {D : D7} (O : Setup D) (c : O.s.Comp) (R : ℝ) : ℝ :=
  cNum O c ((arIn O.s O.Φ O.met.hm).mixEv ∅ R 1 c
    (MvPolynomial.X (Sum.inr (false, 2)) * tagDR D.what₂.Tau _ (CovTestDR.curveV D.what₂.Tau O.N O.j)))

def termW {D : D7} (O : Setup D) (c : O.s.Comp) (R : ℝ) : ℝ :=
  cNum O c ((arIn O.s O.Φ O.met.hm).mixEv ∅ R 1 c
      (MvPolynomial.X (Sum.inr (false, 2)) * tagDR D.what₂.Tau _ (CovTestDR.vdmCl D.what₂.Tau O.N O.j)) *
    (∑ i : Fin (D.R.f * O.N), MvPolynomial.X (wholeSym (fun _ => false) (some R)
      (.inr i : Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N)))) ^ (dimGr D.what₂.Tau O.N O.j - 1))

end GlobalTheory.VdmRec

end
