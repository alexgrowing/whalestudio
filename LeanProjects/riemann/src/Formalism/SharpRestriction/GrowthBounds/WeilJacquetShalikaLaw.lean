import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.HostCls
import Formalism.LocalRingCardinality.DataDIVDefs
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.DvdCondNIffCls
import Development.AutomorphicArithmetic.OrbitLabellings.NotIsCsOfGIdx

noncomputable section

open scoped BigOperators
open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G

namespace Formalism.MainNotions.WeilJacquetShalikaLaw

def VGe (D : D7) (w : D.what₂.places.Pl) {V : Type} [AddCommGroup V] [Module D.what₂.LL V] [Module (𝓞 D.what₂.LL) V]
    (Λ : Submodule (𝓞 D.what₂.LL) V) (y : V) (s : ℝ) : Prop :=
  ∃ (a : D.what₂.LL) (z : V), z ∈ locW D.what₂.places w Λ ∧ y = a • z ∧
    (a = 0 ∨ ur D w s ≤ (vAdd (D.plEq w) a : ℝ))

def ColGe0 (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (x : ((D.fm u).lat 0).V) (s : ℝ) : Prop :=
  ∃ y : ((D.fm u).lat D.R.m).V, (D.fm u).emb D.R.m y = (D.mem u).C.col ((D.fm u).emb 0 x) ∧
    VGe D w ((D.fm u).lat D.R.m).L y s

def ColGeTw {D : D7} (T : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
    (x : ((D.fm u).lat 0).V) (s : ℝ) : Prop :=
  ∃ y : ((T.fm u μ).lat D.R.m).V, (T.fm u μ).emb D.R.m y = (D.chTw u μ).col (D.e0Tw u μ ((D.fm u).emb 0 x)) ∧
    VGe D w ((T.fm u μ).lat D.R.m).L y s

def ColGe {D : D7} (T : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
    (x : ((D.fm u).lat 0).V) (s : ℝ) : Prop :=
  (μ = D.what₂.mu0 → ColGe0 D u w x s) ∧ (μ ≠ D.what₂.mu0 → ColGeTw T u μ w x s)

def Exc (D : D7) (p : ℕ) : Prop := p ∣ D.host.condN * D.host.g 0 * D.host.g 1

theorem used_muAt (D : D7) (w : D.what₂.places.Pl) : DV.Used D (D.what₂.muAt w) := by
  exact Or.inr (Or.inr (Or.inr ⟨w, rfl⟩))

theorem reference_tuple_used (D : D7) : DV.Used D D.what₂.mu0 := by
  exact Or.inl rfl

variable {D : D7} {L : SizeData₂ D}

open Classical in

def gainS (X : Inst D L) (K : Consts) (p j : ℕ) : ℝ :=
  if (IsResidueClassZero D p ∨ IsSg D p) ∧ ¬ Exc D p then (if IsCs D p then 0 else gainP X K (aL L) (bL L) p j) else 0

open Classical in

def g0S (X : Inst D L) (K : Consts) (p j : ℕ) : ℝ :=
  if IsCs D p then 0 else ∑ t0 ∈ reps X p, max (g0 X K (aL L) (bL L) p j t0) 0

def GainZero (D : D7) (L : SizeData₂ D) (p : ℕ) : Prop :=
  Exc D p ∨ ¬ (IsResidueClassZero D p ∨ IsSg D p) ∨ (IsResidueClassZero D p ∧ hP D p = 0) ∨ L.sc.X'' D.R.n < (p : ℝ) ∨ IsCs D p

def InNP (X : Inst D L) (Y : LatInst D) (K : Consts) (c : LatCmp D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (x : ((D.fm u).lat 0).V) : Prop :=
  (∃ hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w), c.cmp u w hg x ∈ NP X Y K u w hg) ∨
  (VV X K (aL L) (bL L) (D.what₂.places.resChar w) = ∅ ∧ x ∈ LT.Sram D u w)

def FkindA (D : D7) (j p : ℕ) : ℝ := (∑ z ∈ kindA D p, FOrb D j p z) / (nP D p : ℝ)

def vDG (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) : ℝ :=
  (padicValNat (D.what₂.places.resChar w) (D.mem u).C.DGam : ℝ)

def ES (L : SizeData₂ D) (Xe : ErrX D) (K : Consts) (ce : ErrC) (u : D.what₂.Word) (j : ℕ) (w : D.what₂.places.Pl) : ℝ :=
  Eval L Xe K ce u j w

def lowS (L : SizeData₂ D) (Xe : ErrX D) (K : Consts) (ce : ErrC) (sp : ℝ) (u : D.what₂.Word) (w : D.what₂.places.Pl) : ℝ :=
  (∑ j ∈ SizeData₂.lifts D, (L.F j w - ES L Xe K ce u j w)) + sp * vDG D u w

def totS (X : Inst D L) (K : Consts) (Xe : ErrX D) (ce : ErrC) (sp : ℝ) (u : D.what₂.Word) (w : D.what₂.places.Pl) : ℝ :=
  (∑ j ∈ SizeData₂.lifts D, (gainS X K (D.what₂.places.resChar w) j + L.F j w - ES L Xe K ce u j w)) + sp * vDG D u w

structure TwLoc (D : D7) (Y : LatInst D) where
  LC : D.what₂.Tup → ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    Σ Lv : Levels (Y.Fl u w hg), Chain Lv
  LC_muAt : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    LC (D.what₂.muAt w) u w hg = ⟨Y.Lv u w hg, Y.Ch u w hg⟩

def TwLoc.Yt {D : D7} {Y : LatInst D} (W : TwLoc D Y) (μ : D.what₂.Tup) : LatInst D where
  vOf := Y.vOf
  Fl := Y.Fl
  Lv := fun u w hg => (W.LC μ u w hg).1
  Ch := fun u w hg => (W.LC μ u w hg).2
  Vram := Y.Vram

structure Ties9 (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (c : LatCmp D) : Prop where
  tied : ∃ hT : GatTies D, LatTied hT X Y
  vram : c.VramDef Y
  fdef : L.FDef

def Conclusion1 (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) (c : LatCmp D) (Dx : DivX D)
    (T : TwForms D) (lev : LevelData D) (Xe : ErrX D) (ce : ErrC) (sp : ℝ) : Prop :=
  Ties9 D L X Y c → ErrDefs D L Xe lev K ce → ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w ≠ (D.mem u).A.T →
    D.what₂.places.resChar w ∉ ({D.host.g 0, D.host.g 1} : Finset ℕ) →
    ∀ μ, DV.Used D μ → D.what₂.places.resChar w ∉ Dx.Qp μ → ∀ x, InNP X Y K c u w x → ColGe T u μ w x (totS X K Xe ce sp u w)

def ZeroGainValuation (D : D7) (L : SizeData₂ D) (K : Consts) (Dx : DivX D) (T : TwForms D) (lev : LevelData D) (Xe : ErrX D) (ce : ErrC) (sp : ℝ) : Prop :=
  L.FDef → ErrDefs D L Xe lev K ce → ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w ≠ (D.mem u).A.T →
    D.what₂.places.resChar w ∉ ({D.host.g 0, D.host.g 1} : Finset ℕ) → GainZero D L (D.what₂.places.resChar w) →
    ∀ μ, DV.Used D μ → D.what₂.places.resChar w ∉ Dx.Qp μ → ∀ x ∈ LT.Sram D u w, ColGe T u μ w x (lowS L Xe K ce sp u w)

def ColumnValuationAwayFromTypePrimes (D : D7) (L : SizeData₂ D) (K : Consts) (Dx : DivX D) (T : TwForms D) (lev : LevelData D) (Xe : ErrX D) (ce : ErrC) (sp : ℝ) : Prop :=
  L.FDef → ErrDefs D L Xe lev K ce → ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w ≠ (D.mem u).A.T →
    D.what₂.places.resChar w ∉ ({D.host.g 0, D.host.g 1} : Finset ℕ) →
    ∀ μ, DV.Used D μ → D.what₂.places.resChar w ∉ Dx.Qp μ → ∀ x ∈ LT.Sram D u w, ColGe T u μ w x (lowS L Xe K ce sp u w)

def IntegralKernelValuation (D : D7) (Dx : DivX D) (T : TwForms D) (sp : ℝ) : Prop :=
  DGamDef D → ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w ≠ D.host.d →
    D.what₂.places.resChar w ∉ ({D.host.g 0, D.host.g 1} : Finset ℕ) →
    D.what₂.places.resChar w ≠ (D.mem u).A.T → ∀ i < D.R.m,
    (∀ x ∈ ((D.fm u).lat i).L, ∃ y, (D.fm u).emb (i + 1) y = (D.mem u).C.K i ((D.fm u).emb i x) ∧
      VGe D w ((D.fm u).lat (i + 1)).L y (-((if i = 0 then 1 - sp else 1) * vDG D u w))) ∧
    ∀ μ, DV.Used D μ → μ ≠ D.what₂.mu0 → D.what₂.places.resChar w ∉ Dx.Qp μ →
      ∀ x ∈ ((T.fm u μ).lat i).L, ∃ y, (T.fm u μ).emb (i + 1) y = (D.chTw u μ).K i ((T.fm u μ).emb i x) ∧
        VGe D w ((T.fm u μ).lat (i + 1)).L y (-((if i = 0 then 1 - sp else 1) * vDG D u w))

def KindA (D : D7) (L : SizeData₂ D) : Prop :=
  ∀ j ∈ SizeData₂.lifts D, ∀ t : HH D, wPl D j (false, t) ≤ if t ∈ D.host.TT then 2 * L.sc.b' else 2 * L.sc.w'' D.R.n

def ErrorFirstTermSize (D : D7) (L : SizeData₂ D) (C : ℝ) : Prop :=
  Formalism.MainNotions.SizesAt L → KindA D L → ∀ j ∈ SizeData₂.lifts D,
    (∀ p : ℕ, p.Prime → IsResidueClassZero D p → hP D p ≠ 0 →
      max 0 (FkindA D j p) ≤
        2 * (D.R.k : ℝ) / p * (2 * (D.host.TT.card : ℝ) * L.sc.b' + 2 * (D.R.n : ℝ) * L.sc.w'' D.R.n) ∧
      2 * (D.R.k : ℝ) / p * (2 * (D.host.TT.card : ℝ) * L.sc.b' + 2 * (D.R.n : ℝ) * L.sc.w'' D.R.n) ≤
        8 * (D.R.k : ℝ) * D.R.n * L.sc.b' / p) ∧
    ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ IsResidueClassZero D p ∧ hP D p ≠ 0 ∧ (p : ℝ) ≤ L.sc.X'' D.R.n) →
      ∑ p ∈ S, Real.log p * max 0 (FkindA D j p) ≤
        C * (D.R.k : ℝ) * D.R.f * L.sc.b' * Real.log (L.sc.X'' D.R.n)

def LatticeGrowthAtPlace (X : Inst D L) (Y' : LatInst D) (K : Consts) (low : ℝ) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) : Prop :=
  ∀ F ∈ NP X Y' K u w hg,
    Y'.vKge u w hg F ((∑ j ∈ SizeData₂.lifts D, gainP X K (aL L) (bL L) (D.what₂.places.resChar w) j) + low)

def BaseChangeDefiniteGood (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) : Prop :=
  ∀ hT : GatTies D, LatTied hT X Y → ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), LatticeGrowthAtPlace X Y K (lowFE L u w) u w hg

def TupleLatticeValuation (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) (Dx : DivX D) (W : TwLoc D Y)
    (lev : LevelData D) (Xe : ErrX D) (ce : ErrC) (sp : ℝ) : Prop :=
  ErrDefs D L Xe lev K ce → ∀ μ, DV.Used D μ → ∀ (hT : GatTies D), LatTied hT X (W.Yt μ) → ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), D.what₂.places.resChar w ∉ Dx.Qp μ →
    LatticeGrowthAtPlace X (W.Yt μ) K (lowS L Xe K ce sp u w) u w hg

def ThinScalesBoundExists (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) : Prop := Formalism.MainNotions.AuxBlock8.UnitBoundDifferenceTerm D L X Y K

def Conclusion2 (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) : Prop := Formalism.MainNotions.FormalGroupSystem.LemmaVVolumeGeneral D L X Y K

def CmpV (c : LatCmp D) (Dx : DivX D) (T : TwForms D) {Y : LatInst D} (W : TwLoc D Y) : Prop :=
  ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) μ,
    DV.Used D μ → D.what₂.places.resChar w ∉ Dx.Qp μ →
    ∀ (x : ((D.fm u).lat 0).V) (s : ℝ), (W.Yt μ).vKge u w hg (c.cmp u w hg x) s → ColGe T u μ w x s

def UAt (X : Inst D L) (Y' : LatInst D) (K : Consts) (low : ℝ) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) : Prop :=
  ∀ VVs VV' : Finset (HH D), VVs ⊆ reps X (D.what₂.places.resChar w) → VV' ⊆ VVs → ∀ F ∈ (D.gat u w hg).M,
    Y'.vKge u w hg (yProd Y' u w hg VV' F) ((∑ j ∈ SizeData₂.lifts D,
        ((∑ t0 ∈ VV', max (gU X K (aL L) (bL L) (D.what₂.places.resChar w) j t0 -
              Pr X K (bL L) (D.what₂.places.resChar w) j t0)
            (max (g0 X K (aL L) (bL L) (D.what₂.places.resChar w) j t0) 0)) +
          (∑ t0 ∈ VVs \ VV', max (g0 X K (aL L) (bL L) (D.what₂.places.resChar w) j t0) 0) +
          ∑ t0 ∈ reps X (D.what₂.places.resChar w) \ VVs,
            max (g0 X K (aL L) (bL L) (D.what₂.places.resChar w) j t0) 0)) + low)

def unitBoundAtTwistedPlaces (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) (Dx : DivX D) (W : TwLoc D Y)
    (lev : LevelData D) (Xe : ErrX D) (ce : ErrC) (sp : ℝ) : Prop :=
  ErrDefs D L Xe lev K ce → ∀ μ, DV.Used D μ → ∀ (hT : GatTies D), LatTied hT X (W.Yt μ) → ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), D.what₂.places.resChar w ∉ Dx.Qp μ →
    UAt X (W.Yt μ) K (lowS L Xe K ce sp u w) u w hg

def SysAt (D : D7) (Y' : LatInst D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) [Fact (D.what₂.places.resChar w).Prime]
    (Xs : Formalism.MainNotions.FormalGroupSystem.Sys (D.what₂.places.resChar w)) : Prop :=
  ∃ std vp unif eO eO_spec dG dG_spec om,
    Xs = Formalism.MainNotions.FormalGroupSystem.Sys.mk (D.gat u w hg) (Y'.Fl u w hg) (Y'.Lv u w hg) (Y'.Ch u w hg) std vp unif eO eO_spec dG
      dG_spec om

def SmallInertPrimeSmallOrderLengthBound (D : D7) {Y : LatInst D} (W : TwLoc D Y) : Prop :=
  ∀ (μ : D.what₂.Tup), DV.Used D μ → ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    ∀ (Xs : Formalism.MainNotions.FormalGroupSystem.Sys (D.what₂.places.resChar w)) (Ys : Formalism.MainNotions.FormalGroupSystem.Pend Xs), SysAt D (W.Yt μ) u w hg Xs →
      Formalism.MainNotions.FormalGroupSystem.admitted D Xs Ys → Formalism.MainNotions.FormalGroupSystem.LowTermBound D Xs Ys

def IsotypicPartsInternalDirectSum (D : D7) (Dx : DivX D) (T : TwForms D) (sp : ℝ) : Prop := IntegralKernelValuation D Dx T sp

def OrbitsWithoutOperator (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (Dx : DivX D) (T : TwForms D) (lev : LevelData D) (Xe : ErrX D) (ce : ErrC)
    (sp : ℝ) : Prop :=
  L.FDef → ErrDefs D L Xe lev K ce → ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w ≠ (D.mem u).A.T →
    ((IsResidueClassZero D (D.what₂.places.resChar w) ∧ hP D (D.what₂.places.resChar w) ≠ 0) ∨ IsSg D (D.what₂.places.resChar w)) →
    ¬ Exc D (D.what₂.places.resChar w) → (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n →
    ∀ μ, DV.Used D μ → D.what₂.places.resChar w ∉ Dx.Qp μ → ∀ x ∈ LT.Sram D u w,
      ColGe T u μ w x ((∑ j ∈ SizeData₂.lifts D, g0S X K (D.what₂.places.resChar w) j) + lowS L Xe K ce sp u w)

def MediumInertPrimeLengthBound (D : D7) (L : SizeData₂ D) (K : Consts) (Dx : DivX D) (T : TwForms D) (lev : LevelData D) (Xe : ErrX D) (ce : ErrC) (sp : ℝ) : Prop :=
  L.FDef → ErrDefs D L Xe lev K ce → ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w ≠ (D.mem u).A.T →
    IsResidueClassZero D (D.what₂.places.resChar w) → hP D (D.what₂.places.resChar w) = 0 → ¬ Exc D (D.what₂.places.resChar w) →
    (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n →
    ∀ μ, DV.Used D μ → D.what₂.places.resChar w ∉ Dx.Qp μ → ∀ x ∈ LT.Sram D u w,
      ColGe T u μ w x ((∑ j ∈ SizeData₂.lifts D, (L.F j w - EatC L ce j (D.what₂.places.resChar w) - vDG D u w)) + sp * vDG D u w)

def LossAtDiscriminant (D : D7) (L : SizeData₂ D) (K : Consts) (Dx : DivX D) (T : TwForms D) (lev : LevelData D) (Xe : ErrX D) (ce : ErrC) (sp : ℝ) : Prop :=
  L.FDef → ErrDefs D L Xe lev K ce → ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w ≠ (D.mem u).A.T →
    D.host.cls (D.what₂.places.resChar w) = PrimeClass.ramD →
    ∀ μ, DV.Used D μ → D.what₂.places.resChar w ∉ Dx.Qp μ → ∀ x ∈ LT.Sram D u w,
      ColGe T u μ w x ((∑ j ∈ SizeData₂.lifts D, (L.F j w - EatD D j - vDG D u w)) + sp * vDG D u w)

def TypePrimeSizeConds (D : D7) (L : SizeData₂ D) (K : Consts) (ce : ErrC) (C : ℝ) : Prop :=
  (∀ j ∈ SizeData₂.lifts D, ∀ u : D.what₂.Word, ∑ t : HH D, ctD D u j t ≤
    2 * (D.host.TT.card : ℝ) * L.sc.b + 2 * (D.R.f : ℝ) * D.R.k * L.sc.b') ∧
  FactDGam D C ∧
  (∀ j ∈ SizeData₂.lifts D, ∀ S : Finset ℕ,
    (∀ p ∈ S, p.Prime ∧ (IsResidueClassZero D p ∨ IsSg D p) ∧ ¬ (IsResidueClassZero D p ∧ hP D p = 0) ∧ (p : ℝ) ≤ L.sc.X'' D.R.n) →
    ∑ p ∈ S, Real.log p * (EatI L K ce j p - max 0 (FkindA D j p)) ≤
      C * (D.R.f : ℝ) * L.sc.b * Real.log (L.sc.X'' D.R.n))

def admitted (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) (Dx : DivX D) (T : TwForms D)
    (W : TwLoc D Y) (lev : LevelData D) (Xe : ErrX D) (ce : ErrC) (sp : ℝ) : Prop :=
  unitBoundAtTwistedPlaces D L X Y K Dx W lev Xe ce sp ∧ SmallInertPrimeSmallOrderLengthBound D W ∧ IsotypicPartsInternalDirectSum D Dx T sp ∧ OrbitsWithoutOperator D L X K Dx T lev Xe ce sp ∧
    MediumInertPrimeLengthBound D L K Dx T lev Xe ce sp ∧ LossAtDiscriminant D L K Dx T lev Xe ce sp

def Conclusion₂ (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) (c : LatCmp D) (Dx : DivX D)
    (T : TwForms D) (W : TwLoc D Y) (lev : LevelData D) (Xe : ErrX D) (ce : ErrC) (sp : ℝ) : Prop :=
  Conclusion1 D L X Y K c Dx T lev Xe ce sp ∧ ZeroGainValuation D L K Dx T lev Xe ce sp ∧ ColumnValuationAwayFromTypePrimes D L K Dx T lev Xe ce sp ∧
    TupleLatticeValuation D L X Y K Dx W lev Xe ce sp

def Stmt (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) (c : LatCmp D) (Dx : DivX D) : Prop :=
  ∀ (T : TwForms D) (W : TwLoc D Y) (lev : LevelData D) (Xe : ErrX D) (ce : ErrC), CmpV c Dx T W → ∀ sp ∈ ({0, 1} : Set ℝ),
    admitted D L X Y K Dx T W lev Xe ce sp → Conclusion₂ D L X Y K c Dx T W lev Xe ce sp

def ClosedFormOfAdmitted (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) (c : LatCmp D) (Dx : DivX D) : Prop :=
  Stmt D L X Y K c Dx ∧ ∃ C : ℝ, 0 ≤ C ∧ ErrorFirstTermSize D L C

def Serv (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) (c : LatCmp D) (Dx : DivX D)
    (T : TwForms D) (lev : LevelData D) (Xe : ErrX D) (ce : ErrC) (C : ℝ) : Prop :=
  TypePrimeSizeConds D L K ce C ∧ Conclusion1 D L X Y K c Dx T lev Xe ce 1 ∧ ColumnValuationAwayFromTypePrimes D L K Dx T lev Xe ce 1

def KudlaFamilyStatement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    Stmt (Fm.D x i) (Fm.L x i) (Fm.Gx x i) (Fm.Gy x i) Fm.GK (Fm.ex x hx i).cmp (Fm.X x i)

def FamilyClosedForm {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  KudlaFamilyStatement Fm ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ErrorFirstTermSize (Fm.D x i) (Fm.L x i) C

def ServF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    Serv (Fm.D x i) (Fm.L x i) (Fm.Gx x i) (Fm.Gy x i) Fm.GK (Fm.ex x hx i).cmp (Fm.X x i) (Fm.ex x hx i).tw
      (Fm.ex x hx i).lev (Fm.ex x hx i).errX Fm.cX.err C

def ServClosed (𝒞 : Formalism.MainNotions.FamClass) : Prop := Formalism.MainNotions.Closed 𝒞 fun Fm _ => ServF Fm

def ClosedAbsoluteShare (𝒞 : Formalism.MainNotions.FamClass) : Prop := Formalism.MainNotions.Closed 𝒞 fun Fm _ => FamilyClosedForm Fm

section Relations

variable {X : Inst D L} {Y : LatInst D} {K : Consts} {c : LatCmp D} {Dx : DivX D} {T : TwForms D}
  {lev : LevelData D} {Xe : ErrX D} {ce : ErrC} {sp : ℝ}

theorem difference_bound_iff_forall_place : Formalism.MainNotions.AuxBlock8.UnitBoundDifferenceTerm D L X Y K ↔
    ∀ hT : GatTies D, LatTied hT X Y → ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
      (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), UAt X Y K (lowFE L u w) u w hg := by
  exact Iff.rfl

theorem unit_bound_iff_forall_place : Formalism.MainNotions.AuxBlock8.unitBoundAtTwistedPlaces D L X Y K ↔
    ∀ hT : GatTies D, LatTied hT X Y → ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
      (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), UAt X Y K (Formalism.MainNotions.AuxBlock8.lowU D u w) u w hg := by
  exact Iff.rfl

theorem lattice_valuation_of_growth (h : Formalism.MainNotions.AuxBlock8.admG1 D L X Y K) : BaseChangeDefiniteGood D L X Y K := by
  exact fun hT hL u w hg => (h hT hL u w hg).2.2

theorem zero_gain_of_no_served_orbit (h : ColumnValuationAwayFromTypePrimes D L K Dx T lev Xe ce sp) : ZeroGainValuation D L K Dx T lev Xe ce sp := by
  exact fun hF hE u w h1 h2 _ μ hμ hq x hx => h hF hE u w h1 h2 μ hμ hq x hx

theorem lowS_eq_lowFE (hE : L.EDef Xe K ce) (u : D.what₂.Word) (w : D.what₂.places.Pl) :
    lowS L Xe K ce sp u w = lowFE L u w + sp * vDG D u w := by
  unfold lowS lowFE ES
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [hE u j hj w]

theorem residue_char_ne_level {u : D.what₂.Word} {w : D.what₂.places.Pl}
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) : D.what₂.places.resChar w ≠ (D.mem u).A.T := by
  intro h
  exact hg.2.2.2.2.2 ⟨1, by rw [h, mul_one]⟩

theorem NP_tw (W : TwLoc D Y) (μ : D.what₂.Tup) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) : NP X (W.Yt μ) K u w hg = NP X Y K u w hg := rfl

theorem LatTied_congr {Y1 Y2 : LatInst D} (hT : GatTies D) (h1 : Y1.vOf = Y2.vOf) (h2 : Y1.Fl = Y2.Fl) :
    LatTied hT X Y1 ↔ LatTied hT X Y2 := by
  obtain ⟨v1, f1, l1, c1, r1⟩ := Y1
  obtain ⟨v2, f2, l2, c2, r2⟩ := Y2
  dsimp only at h1 h2
  subst h1 h2
  exact Iff.rfl

theorem LatTied_tw (W : TwLoc D Y) (μ : D.what₂.Tup) (hT : GatTies D) :
    LatTied hT X (W.Yt μ) ↔ LatTied hT X Y := by
  exact LatTied_congr hT rfl rfl

theorem vKge_muAt (W : TwLoc D Y) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (F : (D.gat u w hg).Fn) (g : ℝ) :
    (W.Yt (D.what₂.muAt w)).vKge u w hg F g ↔ Y.vKge u w hg F g := by
  have key : ∀ s : (Σ Lv : Levels (Y.Fl u w hg), Chain Lv), s = ⟨Y.Lv u w hg, Y.Ch u w hg⟩ →
      (vGeLat (D.gat u w hg) (s.1.Int D.R.m) (s.2.chainK D.R.m F) g ↔ Y.vKge u w hg F g) := by
    rintro s rfl
    exact Iff.rfl
  exact key _ (W.LC_muAt u w hg)

theorem lattice_valuation_of_tuples (W : TwLoc D Y) (hE : ErrDefs D L Xe lev K ce) (h : TupleLatticeValuation D L X Y K Dx W lev Xe ce 0) :
    BaseChangeDefiniteGood D L X Y K := by
  intro hT hL u w hg F hF
  have h1 := h hE (D.what₂.muAt w) (used_muAt D w) hT ((LatTied_tw W _ hT).2 hL) u w hg (Dx.Qp_muAt w) F hF
  rw [vKge_muAt, lowS_eq_lowFE hE.edef, zero_mul, add_zero] at h1
  exact h1

theorem VGe_mono {w : D.what₂.places.Pl} {V : Type} [AddCommGroup V] [Module D.what₂.LL V] [Module (𝓞 D.what₂.LL) V]
    {Λ : Submodule (𝓞 D.what₂.LL) V} {y : V} {s s' : ℝ} (hs : s' ≤ s) (h : VGe D w Λ y s) : VGe D w Λ y s' := by
  obtain ⟨a, z, hz, hy, ha⟩ := h
  refine ⟨a, z, hz, hy, ha.imp id fun h' => le_trans ?_ h'⟩
  unfold DV.ur
  exact mul_le_mul_of_nonneg_left hs (by positivity)

theorem ColGe_mono {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {x : ((D.fm u).lat 0).V} {s s' : ℝ}
    (hs : s' ≤ s) (h : ColGe T u μ w x s) : ColGe T u μ w x s' := by
  refine ⟨fun h0 => ?_, fun h1 => ?_⟩
  · obtain ⟨y, hy, hv⟩ := h.1 h0
    exact ⟨y, hy, VGe_mono hs hv⟩
  · obtain ⟨y, hy, hv⟩ := h.2 h1
    exact ⟨y, hy, VGe_mono hs hv⟩

private theorem gainP_nonneg' (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p j : ℕ) :
    0 ≤ gainP X K a b p j := by
  unfold gainP
  split_ifs
  · exact le_rfl
  · refine add_nonneg (Finset.sum_nonneg fun t _ => ?_) (Finset.sum_nonneg fun t _ => le_max_right _ _)
    exact le_trans (le_max_right _ _) (le_max_right _ _)

theorem kernel_valuation_served (W : TwLoc D Y) (hV : CmpV c Dx T W) (hG : TupleLatticeValuation D L X Y K Dx W lev Xe ce sp) (ht : Ties9 D L X Y c)
    (hE : ErrDefs D L Xe lev K ce)
    (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (hExc : ¬ Exc D (D.what₂.places.resChar w)) (μ : D.what₂.Tup) (hUs : DV.Used D μ)
    (hμ : D.what₂.places.resChar w ∉ Dx.Qp μ)
    (x : ((D.fm u).lat 0).V) (hx : c.cmp u w hg x ∈ NP X Y K u w hg) : ColGe T u μ w x (totS X K Xe ce sp u w) := by
  obtain ⟨hT, hL⟩ := ht.tied
  have h1 := hG hE μ hUs hT ((LatTied_tw W μ hT).2 hL) u w hg hμ (c.cmp u w hg x) hx
  refine ColGe_mono ?_ (hV u w hg μ hUs hμ x _ h1)
  unfold totS lowS
  have hs : ∀ j, gainS X K (D.what₂.places.resChar w) j + L.F j w - ES L Xe K ce u j w =
      gainS X K (D.what₂.places.resChar w) j + (L.F j w - ES L Xe K ce u j w) := fun j => by ring
  simp only [hs, Finset.sum_add_distrib]
  have hle : ∑ j ∈ SizeData₂.lifts D, gainS X K (D.what₂.places.resChar w) j ≤
      ∑ j ∈ SizeData₂.lifts D, gainP X K (aL L) (bL L) (D.what₂.places.resChar w) j :=
    Finset.sum_le_sum fun j _ => by
      unfold gainS
      split_ifs
      · exact gainP_nonneg' _ _ _ _ _ _
      · exact le_rfl
      · exact gainP_nonneg' _ _ _ _ _ _
  linarith

theorem local_theorem_of_statement (W : TwLoc D Y) (h : Formalism.MainNotions.FormalGroupSystem.ErrorExponentStatement D) : SmallInertPrimeSmallOrderLengthBound D W := by
  intro μ _ u w hg Xs Ys hXs hA
  obtain ⟨std, vp, unif, eO, eO_spec, dG, dG_spec, om, rfl⟩ := hXs
  exact (@h u w ⟨D.what₂.places.resChar_prime w⟩ hg _ Ys rfl hA).2.2.2.2.2.2.2.2.2.2

theorem serv_of {C : ℝ} (hS : Stmt D L X Y K c Dx) (W : TwLoc D Y) (hV : CmpV c Dx T W)
    (hA : admitted D L X Y K Dx T W lev Xe ce 1) (hZ : TypePrimeSizeConds D L K ce C) : Serv D L X Y K c Dx T lev Xe ce C := by
  have h1 := hS T W lev Xe ce hV 1 (by simp) hA
  exact ⟨hZ, h1.1, h1.2.2.1⟩

end Relations

def PairInt (D : D7) (Dx : DivX D) (T : TwForms D) : Prop :=
  DGamDef D → (∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w ≠ (D.mem u).A.T →
    ∀ z ∈ locW D.what₂.places w ((D.fm u).lat D.R.m).L,
    ∀ F ∈ (D.what₂.Mtilde D.what₂.mu0).carrier, F ∈ D.what₂.V0 D.what₂.mu0 →
      ∃ y : D.what₂.LL, D.what₂.embLL y = (D.mem u).P.Ptil ((D.fm u).emb D.R.m z) ((D.eMt u).symm F) ∧
        (y = 0 ∨ -ur D w (vDG D u w) ≤ (vAdd (D.plEq w) y : ℝ))) ∧
  ∀ u μ, DV.Used D μ → μ ≠ D.what₂.mu0 → ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w ≠ (D.mem u).A.T →
    D.what₂.places.resChar w ∉ Dx.Qp μ → ∀ z ∈ locW D.what₂.places w ((T.fm u μ).lat D.R.m).L,
    ∀ F ∈ (D.what₂.Mtilde μ).carrier, F ∈ D.what₂.V0 μ →
      ∃ y : D.what₂.LL, D.what₂.embLL y = (D.PTw u μ).Ptil ((T.fm u μ).emb D.R.m z) ((D.eMtTw u μ).symm F) ∧
        (y = 0 ∨ -ur D w (vDG D u w) ≤ (vAdd (D.plEq w) y : ℝ))

theorem vAdd_mul' {Kk : Type} [Field Kk] [NumberField Kk] (w : HeightOneSpectrum (𝓞 Kk)) {x y : Kk} (hx : x ≠ 0)
    (hy : y ≠ 0) : vAdd w (x * y) = vAdd w x + vAdd w y := by
  unfold vAdd
  rw [Valuation.map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 hx) ((Valuation.ne_zero_iff _).2 hy)]
  ring

theorem val_step (D : D7) (w : D.what₂.places.Pl) {a y0 : D.what₂.LL} {s v : ℝ}
    (ha : a = 0 ∨ ur D w s ≤ (vAdd (D.plEq w) a : ℝ)) (hy : y0 = 0 ∨ -ur D w v ≤ (vAdd (D.plEq w) y0 : ℝ)) :
    a * y0 = 0 ∨ ur D w (s - v) ≤ (vAdd (D.plEq w) (a * y0) : ℝ) := by
  rcases ha with ha | ha
  · exact Or.inl (by rw [ha, zero_mul])
  rcases hy with hy | hy
  · exact Or.inl (by rw [hy, mul_zero])
  by_cases ha0 : a = 0
  · exact Or.inl (by rw [ha0, zero_mul])
  by_cases hy0 : y0 = 0
  · exact Or.inl (by rw [hy0, mul_zero])
  right
  rw [vAdd_mul' _ ha0 hy0]
  push_cast
  unfold DV.ur at *
  rw [mul_sub]
  linarith

theorem period_ge {D : D7} {Dx : DivX D} {T : TwForms D} (hP : PairInt D Dx T) (hD : DGamDef D) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (hw : D.what₂.places.resChar w ≠ (D.mem u).A.T) (φ : (D.div.Nu u).V) (s : ℝ) :
    ∀ μ, DV.Used D μ → D.what₂.places.resChar w ∉ Dx.Qp μ → ColGe T u μ w (D.nuIn u φ) s →
    ∀ F ∈ (D.what₂.Mtilde μ).carrier, F ∈ D.what₂.V0 μ →
      ∃ y : D.what₂.LL, D.what₂.embLL y = D.what₂.perCol u μ (D.jN u φ) F ∧
        (y = 0 ∨ ur D w (s - vDG D u w) ≤ (vAdd (D.plEq w) y : ℝ)) := by
  intro μ hUs hQ hc F hF hF0
  by_cases hμ : μ = D.what₂.mu0
  · subst hμ
    obtain ⟨y, hy, a, z, hz, rfl, ha⟩ := hc.1 rfl
    obtain ⟨y0, hy0, hv0⟩ := (hP hD).1 u w hw z hz F hF hF0
    refine ⟨a * y0, ?_, val_step D w ha hv0⟩
    rw [D.perCol_base_eq_PtilCol, D.nuIn_jN, PeriodMap.PtilCol, ← hy, map_mul, hy0, LinearMap.map_smulₛₗ]
    simp [PeriodMap.Ptil]
  · obtain ⟨y, hy, a, z, hz, rfl, ha⟩ := hc.2 hμ
    obtain ⟨y0, hy0, hv0⟩ := (hP hD).2 u μ hUs hμ w hw hQ z hz F hF hF0
    refine ⟨a * y0, ?_, val_step D w ha hv0⟩
    rw [D.perCol_tie u μ hμ, D.nuIn_jN, PeriodMap.PtilCol, ← hy, map_mul, hy0, LinearMap.map_smulₛₗ]
    simp [PeriodMap.Ptil]

theorem nuIn_mem_Sram (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (φ : (D.div.Nu u).V) (hφ : φ ∈ MramL D u) :
    D.nuIn u φ ∈ LT.Sram D u w := by
  refine ⟨Submodule.subset_span hφ, ?_⟩
  have : D.nuIn u φ ∈ LinearMap.range (D.nuIn u) := ⟨φ, rfl⟩
  rw [D.nuIn_range] at this
  exact this

theorem inv_mem_intW_of (D : D7) (w : D.what₂.places.Pl) (s : 𝓞 D.what₂.LL) (hs : s ∉ (D.plEq w).asIdeal) :
    ((s : D.what₂.LL))⁻¹ ∈ intW D.what₂.places w := by
  have hs0 : (s : D.what₂.LL) ≠ 0 := by
    intro h
    apply hs
    have : s = 0 := by exact_mod_cast h
    rw [this]; exact Ideal.zero_mem _
  show (0 : WithTop ℤ) ≤ D.what₂.places.val w ((s : D.what₂.LL))⁻¹
  rw [D.val_eq w _ (inv_ne_zero hs0)]
  have h1 : (D.plEq w).valuation D.what₂.LL (s : D.what₂.LL) = 1 := by
    have := (D.plEq w).valuation_of_algebraMap (K := D.what₂.LL) s
    rw [show (s : D.what₂.LL) = algebraMap (𝓞 D.what₂.LL) D.what₂.LL s from rfl, this]
    exact (HeightOneSpectrum.intValuation_eq_one_iff).2 hs
  unfold vAdd
  rw [map_inv₀, h1]
  simp

theorem nuIn_mem_Sram_of_locLe (D : D7) (L : SizeData₂ D) (u : D.what₂.Word) (w : D.what₂.places.Pl) (φ : (D.div.Nu u).V)
    (hφ : φ ∈ L.NuLat u) (h : LocLe (D.plEq w) 0 (L.NuLat u) (MramL D u)) : D.nuIn u φ ∈ LT.Sram D u w := by
  obtain ⟨s, hs, hm⟩ := h φ hφ
  rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul] at hm
  have hs0 : (s : D.what₂.LL) ≠ 0 := by
    intro h0
    apply hs
    have : s = 0 := by exact_mod_cast h0
    rw [this]; exact Ideal.zero_mem _
  have h1 : D.nuIn u (s • φ) ∈ ((D.fm u).lat 0).L := hm
  refine ⟨?_, ?_⟩
  · have h2 : D.nuIn u φ =
        (⟨((s : D.what₂.LL))⁻¹, inv_mem_intW_of D w s hs⟩ : intW D.what₂.places w) • D.nuIn u (s • φ) := by
      rw [Subring.smul_def]
      show D.nuIn u φ = ((s : D.what₂.LL))⁻¹ • D.nuIn u (s • φ)
      rw [show s • φ = (s : D.what₂.LL) • φ from (algebraMap_smul D.what₂.LL s φ).symm, map_smul, smul_smul,
        inv_mul_cancel₀ hs0, one_smul]
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)
  · have : D.nuIn u φ ∈ LinearMap.range (D.nuIn u) := ⟨φ, rfl⟩
    rw [D.nuIn_range] at this
    exact this

theorem stable_lattice_of_no_served_orbit {K : Consts} {Dx : DivX D} {T : TwForms D} {lev : LevelData D} {Xe : ErrX D} {ce : ErrC}
    (hP : PairInt D Dx T) (hE : ErrDefs D L Xe lev K ce) (hF : L.FDef)
    (h : ColumnValuationAwayFromTypePrimes D L K Dx T lev Xe ce 1) :
    ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w ≠ (D.mem u).A.T →
      D.what₂.places.resChar w ∉ ({D.host.g 0, D.host.g 1} : Finset ℕ) →
      ∀ (φ : (D.div.Nu u).V), φ ∈ MramL D u →
      ∀ F ∈ (D.what₂.Mtilde (D.what₂.muAt w)).carrier, F ∈ D.what₂.V0 (D.what₂.muAt w) →
        ∃ y : D.what₂.LL, D.what₂.embLL y = D.what₂.perCol u (D.what₂.muAt w) (D.jN u φ) F ∧
          (y = 0 ∨ ur D w (∑ j ∈ SizeData₂.lifts D, (L.F j w - L.E u j w)) ≤ (vAdd (D.plEq w) y : ℝ)) := by
  intro u w hT' hg' φ hφ Fv hFv hV0
  have hc := h hF hE u w hT' hg' (D.what₂.muAt w) (used_muAt D w) (Dx.Qp_muAt w) (D.nuIn u φ)
    (nuIn_mem_Sram D u w φ hφ)
  obtain ⟨y, hy1, hy2⟩ := period_ge hP hE.dgam u w hT' φ _ (D.what₂.muAt w) (used_muAt D w) (Dx.Qp_muAt w) hc
    Fv hFv hV0
  refine ⟨y, hy1, ?_⟩
  rw [lowS_eq_lowFE hE.edef, one_mul, add_sub_cancel_right] at hy2
  exact hy2

theorem off_level_bound {X : Inst D L} {Y : LatInst D} {K : Consts} {c : LatCmp D} {Dx : DivX D} {T : TwForms D}
    {lev : LevelData D} {Xe : ErrX D} {ce : ErrC}
    (hP : PairInt D Dx T) (hE : ErrDefs D L Xe lev K ce) (ht : Ties9 D L X Y c) (hS : c.NuServedDef X Y K)
    (hN : ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w ≠ (D.mem u).A.T →
      LocLe (D.plEq w) 0 (L.NuLat u) (MramL D u))
    (hGI : ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w ≠ (D.mem u).A.T →
      VV X K (aL L) (bL L) (D.what₂.places.resChar w) ≠ ∅ → GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (hgain : ∀ (w : D.what₂.places.Pl), ∀ j ∈ SizeData₂.lifts D, L.gainD j w ≤ gainS X K (D.what₂.places.resChar w) j)
    (h : Conclusion1 D L X Y K c Dx T lev Xe ce 1) :
    ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w ≠ (D.mem u).A.T →
      D.what₂.places.resChar w ∉ ({D.host.g 0, D.host.g 1} : Finset ℕ) → ∀ φ : (D.div.Nu u).V, φ ∈ L.NuLat u →
      ∀ F ∈ (D.what₂.Mtilde (D.what₂.muAt w)).carrier, F ∈ D.what₂.V0 (D.what₂.muAt w) →
        ∃ y : D.what₂.LL, D.what₂.embLL y = D.what₂.perCol u (D.what₂.muAt w) (D.jN u φ) F ∧
          (y = 0 ∨ ur D w (L.sg u w) ≤ (vAdd (D.plEq w) y : ℝ)) := by
  intro u w hTne hgne φ hφ Fv hFv hV0
  have hIn : InNP X Y K c u w (D.nuIn u φ) := by
    by_cases hVV : VV X K (aL L) (bL L) (D.what₂.places.resChar w) = ∅
    · exact Or.inr ⟨hVV, nuIn_mem_Sram_of_locLe D L u w φ hφ (hN u w hTne)⟩
    · have hg := hGI u w hTne hVV
      refine Or.inl ⟨hg, (hS u w hg hVV φ).1 ⟨1, fun h1 => (D.plEq w).isPrime.ne_top
        ((Ideal.eq_top_iff_one _).2 h1), by rw [one_smul]; exact hφ⟩⟩
  have hc := h ht hE u w hTne hgne (D.what₂.muAt w) (used_muAt D w) (Dx.Qp_muAt w) _ hIn
  obtain ⟨y, hy1, hy2⟩ := period_ge hP hE.dgam u w hTne φ _ (D.what₂.muAt w) (used_muAt D w)
    (Dx.Qp_muAt w) hc Fv hFv hV0
  refine ⟨y, hy1, hy2.imp id fun h2 => le_trans ?_ h2⟩
  unfold DV.ur
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  unfold SizeData₂.sg totS
  rw [one_mul, add_sub_cancel_right]
  refine Finset.sum_le_sum fun j hj => ?_
  have h3 := hgain w j hj
  rw [show ES L Xe K ce u j w = L.E u j w from (hE.edef u j hj w).symm]
  linarith

theorem pair_gain_nonneg {X : Inst D L} {K : Consts} (a b : HH D → ℤ) (p j : ℕ) : 0 ≤ gainP X K a b p j := by
  unfold gainP
  split_ifs
  · exact le_rfl
  · refine add_nonneg (Finset.sum_nonneg fun t _ => ?_) (Finset.sum_nonneg fun t _ => le_max_right _ _)
    exact le_trans (le_max_right _ _) (le_max_right _ _)

theorem served_gain_nonneg {X : Inst D L} {K : Consts} (p j : ℕ) : 0 ≤ gainS X K p j := by
  unfold gainS
  split_ifs
  · exact le_rfl
  · exact pair_gain_nonneg _ _ p j
  · exact le_rfl

theorem gainD_le_gainS {X : Inst D L} {K : Consts} (hF : ∀ w, ParametersFill X K w)
    (hcs : ∀ p : ℕ, p.Prime → IsCs D p → p ∈ L.drop) (w : D.what₂.places.Pl) (j : ℕ)
    (hj : j ∈ SizeData₂.lifts D) : L.gainD j w ≤ gainS X K (D.what₂.places.resChar w) j := by
  unfold SizeData₂.gainD
  split_ifs with hd
  · exact served_gain_nonneg _ _
  by_cases hs : w ∈ L.supp
  swap
  · rw [L.gain_supp j w hs]; exact served_gain_nonneg _ _
  by_cases hin : IsResidueClassZero D (D.what₂.places.resChar w) ∨ IsSg D (D.what₂.places.resChar w)
  swap
  · rw [(L.not_inert w (fun h => hin (Or.inr h)) (fun h => hin (Or.inl h))).1 j]; exact served_gain_nonneg _ _
  have hg : L.gain j w = gainP X K (aL L) (bL L) (D.what₂.places.resChar w) j := (hF w).2.2.2.1 hs hin j hj
  by_cases hE : Exc D (D.what₂.places.resChar w)
  · have hp := D.what₂.places.resChar_prime w
    have hgz : L.gain j w = 0 := by
      unfold Exc at hE
      rcases (Nat.Prime.dvd_mul hp).1 hE with h | h
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
        · exact absurd hin (D.host.not_inert_of_dvd hp h)
        · exact L.gain_g j w (by rw [(Nat.prime_dvd_prime_iff_eq hp (D.host.g_prime 0)).1 h]; simp)
      · exact L.gain_g j w (by rw [(Nat.prime_dvd_prime_iff_eq hp (D.host.g_prime 1)).1 h]; simp)
    rw [hgz]; exact served_gain_nonneg _ _
  · rw [hg, gainS, if_pos ⟨hin, hE⟩, if_neg (fun h => hd (hcs _ (D.what₂.places.resChar_prime w) h))]

theorem gIdx_of_served {X : Inst D L} {K : Consts}
    (hC : ∀ (u : D.what₂.Word) (p : ℕ), Cand D L K p → p ≠ (D.mem u).A.T → GIdx D.host (D.mem u).A.T p)
    (u : D.what₂.Word) (w : D.what₂.places.Pl) (hw : D.what₂.places.resChar w ≠ (D.mem u).A.T)
    (hVV : VV X K (aL L) (bL L) (D.what₂.places.resChar w) ≠ ∅) :
    GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) := by
  apply hC u _ _ hw
  unfold VV at hVV
  split_ifs at hVV with h1
  · exact h1.1
  · exact absurd rfl hVV

theorem local_compatibility_family {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) :
    Ties9 (Fm.D x i) (Fm.L x i) (Fm.Gx x i) (Fm.Gy x i) (Fm.ex x hx i).cmp := by
  exact ⟨⟨Fm.gatT x i, Fm.latTied x hx i⟩, (Fm.ex x hx i).lat.vram, (Fm.ex x hx i).fdef⟩

theorem stable_lattice_family {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (C : ℝ)
    (hP : PairInt (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).tw)
    (h : Serv (Fm.D x i) (Fm.L x i) (Fm.Gx x i) (Fm.Gy x i) Fm.GK (Fm.ex x hx i).cmp (Fm.X x i) (Fm.ex x hx i).tw
      (Fm.ex x hx i).lev (Fm.ex x hx i).errX Fm.cX.err C) :
    ∀ u (w : (Fm.D x i).what₂.places.Pl), (Fm.D x i).what₂.places.resChar w ≠ ((Fm.D x i).mem u).A.T →
      (Fm.D x i).what₂.places.resChar w ∉ ({(Fm.D x i).host.g 0, (Fm.D x i).host.g 1} : Finset ℕ) →
      ∀ (φ : ((Fm.D x i).div.Nu u).V), φ ∈ MramL (Fm.D x i) u →
      ∀ F ∈ ((Fm.D x i).what₂.Mtilde ((Fm.D x i).what₂.muAt w)).carrier, F ∈ (Fm.D x i).what₂.V0 ((Fm.D x i).what₂.muAt w) →
        ∃ y : (Fm.D x i).what₂.LL,
          (Fm.D x i).what₂.embLL y = (Fm.D x i).what₂.perCol u ((Fm.D x i).what₂.muAt w) ((Fm.D x i).jN u φ) F ∧
          (y = 0 ∨ ur (Fm.D x i) w (∑ j ∈ SizeData₂.lifts (Fm.D x i), ((Fm.L x i).F j w - (Fm.L x i).E u j w)) ≤
            (vAdd ((Fm.D x i).plEq w) y : ℝ)) := by
  exact stable_lattice_of_no_served_orbit hP (Fm.ex x hx i).err (Fm.ex x hx i).fdef h.2.2

theorem isCs_drop {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : ℕ) (hp : p.Prime)
    (h : IsCs (Fm.D x i) p) : p ∈ (Fm.L x i).drop := by
  refine (Fm.drop_iff x hx i p hp).2 ⟨Or.inr (Or.inr (Or.inr h)), fun u hu => ?_⟩
  have hs := (Fm.params x hx i).level_split _ ((Fm.D x i).T_level u)
  have hc : (Fm.D x i).host.cls p = PrimeClass.inertClass := h.1
  rw [← hu, hc] at hs
  cases hs

theorem off_level_bound_family {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x)
    (hC : ∀ (u : (Fm.D x i).what₂.Word) (p : ℕ), Cand (Fm.D x i) (Fm.L x i) Fm.GK p → p ≠ ((Fm.D x i).mem u).A.T →
      GIdx (Fm.D x i).host ((Fm.D x i).mem u).A.T p)
    (hP : PairInt (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).tw)
    (h : Conclusion1 (Fm.D x i) (Fm.L x i) (Fm.Gx x i) (Fm.Gy x i) Fm.GK (Fm.ex x hx i).cmp (Fm.X x i) (Fm.ex x hx i).tw
      (Fm.ex x hx i).lev (Fm.ex x hx i).errX Fm.cX.err 1) :
    ∀ u (w : (Fm.D x i).what₂.places.Pl), (Fm.D x i).what₂.places.resChar w ≠ ((Fm.D x i).mem u).A.T →
      (Fm.D x i).what₂.places.resChar w ∉ ({(Fm.D x i).host.g 0, (Fm.D x i).host.g 1} : Finset ℕ) →
      ∀ φ : ((Fm.D x i).div.Nu u).V, φ ∈ (Fm.L x i).NuLat u →
      ∀ F ∈ ((Fm.D x i).what₂.Mtilde ((Fm.D x i).what₂.muAt w)).carrier, F ∈ (Fm.D x i).what₂.V0 ((Fm.D x i).what₂.muAt w) →
        ∃ y : (Fm.D x i).what₂.LL,
          (Fm.D x i).what₂.embLL y = (Fm.D x i).what₂.perCol u ((Fm.D x i).what₂.muAt w) ((Fm.D x i).jN u φ) F ∧
          (y = 0 ∨ ur (Fm.D x i) w ((Fm.L x i).sg u w) ≤ (vAdd ((Fm.D x i).plEq w) y : ℝ)) := by
  exact off_level_bound hP (Fm.ex x hx i).err (local_compatibility_family Fm x hx i) (Fm.ex x hx i).lat.served
    (Fm.nuDef x hx i).1 (fun u w hw hVV => gIdx_of_served hC u w hw hVV)
    (fun w j hj => gainD_le_gainS (Fm.fills x hx i) (fun p hp hc => isCs_drop Fm x hx i p hp hc) w j hj) h

end Formalism.MainNotions.WeilJacquetShalikaLaw

end
