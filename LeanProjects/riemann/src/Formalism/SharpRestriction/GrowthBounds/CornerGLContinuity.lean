import Formalism.LocalRingCardinality.DataParams₂
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.ElevenLe
import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SegRing
import Formalism.SharpRestriction.GrowthBounds.SelectionLemmas
import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Formalism.SharpRestriction.GlobalSchurBounds.CMFieldLemmas
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSa

noncomputable section

open scoped BigOperators

namespace Formalism.MainNotions.CornerGLContinuity

open Formalism.BasicNotions Formalism.MainNotions.G

def fwd (n' a b : ℕ) : ℕ := (b + n' - a) % n'

def OrbitRaw (n' : ℕ) (TT : Finset (Fin n')) (r L₁ L₂ u M₀ G' N₁ : ℕ) : Prop :=
  L₁ ≤ L₂ ∧ L₂ < u ∧ G' = (M₀ + 5) * ((6 * r + 1) * u) ∧ 3 * G' ≤ n' ∧
    Formalism.G0.GoodOrbitIntervalTileCondition n' (TT.map Fin.valEmbedding) L₂ (r - 1) r u M₀ G' N₁

def Enum (T : Finset ℕ) (r u s : ℕ) (f : Fin (3 * r) → ℕ) : Prop :=
  StrictMono f ∧ T ∩ Finset.Ico (s * ((6 * r + 1) * u)) ((s + 1) * ((6 * r + 1) * u)) = Finset.univ.image f

def NextMarked (n' : ℕ) (T : Finset ℕ) (r u s s' : ℕ) : Prop :=
  s < n' / ((6 * r + 1) * u) ∧ s' < n' / ((6 * r + 1) * u) ∧ Formalism.G0.Marked T r u s ∧ Formalism.G0.Marked T r u s' ∧
    ∀ j, 0 < j → j < (if s < s' then s' - s else s' + n' / ((6 * r + 1) * u) - s) →
      ¬ Formalism.G0.Marked T r u ((s + j) % (n' / ((6 * r + 1) * u)))

def MarkedTileMaxima (n' : ℕ) (T : Finset ℕ) (r u : ℕ) : Prop :=
  ∀ s < n' / ((6 * r + 1) * u), Formalism.G0.Marked T r u s →
    ∃ f : Fin (3 * r) → ℕ, Enum T r u s f ∧ (∀ i, Even (f i)) ∧
      (∀ (i : Fin (3 * r)) (hi : i.val + 1 < 3 * r), f i + u < f ⟨i.val + 1, hi⟩) ∧
      (∀ i, s * ((6 * r + 1) * u) + u ≤ f i ∧ f i + u < (s + 1) * ((6 * r + 1) * u)) ∧
      ∀ i, ∀ y ∈ T, y ≠ f i → u < fwd n' y (f i) ∧ u < fwd n' (f i) y

def SegmentLengthCondition (n' : ℕ) (T : Finset ℕ) (r L₂ u G' N₁ : ℕ) (hr : 1 ≤ r) : Prop :=
  ∀ s s' (f f' : Fin (3 * r) → ℕ), NextMarked n' T r u s s' → Enum T r u s f → Enum T r u s' f' →
    let a := f ⟨r, by omega⟩
    let b := f' ⟨2 * r - 1, by omega⟩
    let Dd := fwd n' a b
    Dd + 1 ≤ G' ∧ (T ∩ (Finset.range (Dd + 1)).image (fun j => (a + j) % n')).card ≤ N₁ ∧
      (∀ i : Fin (3 * r), 2 * r ≤ i.val → Even (f i)) ∧ (∀ i : Fin (3 * r), i.val < r → Even (f' i)) ∧
      (∀ (i : Fin (3 * r)) (hi : i.val + 1 < 3 * r), 2 * r ≤ i.val + 1 → f i + L₂ < f ⟨i.val + 1, hi⟩) ∧
      (∀ (i : Fin (3 * r)) (hi : i.val + 1 < 3 * r), i.val < r → f' i + L₂ < f' ⟨i.val + 1, hi⟩)

def EarliestMaximumFar (n' : ℕ) (T : Finset ℕ) (r L₁ : ℕ) : Prop :=
  ∀ i ∈ T, (T.filter fun y => Even y ∧ 1 ≤ fwd n' y i ∧ fwd n' y i ≤ L₁).card < r

def ConsecutiveMaximaClose (n' : ℕ) (T : Finset ℕ) (G' N₁ : ℕ) : Prop :=
  ∀ y ∈ T, Even y → ∃ d, 1 ≤ d ∧ d ≤ G' ∧ (y + d) % n' ∈ T ∧ Even ((y + d) % n') ∧
    (∀ d', 1 ≤ d' → d' < d → (y + d') % n' ∈ T → ¬ Even ((y + d') % n')) ∧
    (T ∩ (Finset.Ioo 0 d).image (fun j => (y + j) % n')).card ≤ N₁

def OrbitFrames (n' : ℕ) [NeZero n'] (TT : Finset (Fin n')) (r L₁ L₂ u G' N₁ : ℕ) : Prop :=
  ∃ F : Frames n' r, F.TT = TT ∧ F.Valid L₁ N₁ ∧
    (∀ j : ℤ, ∃ s < n' / ((6 * r + 1) * u), Formalism.G0.Marked (TT.map Fin.valEmbedding) r u s ∧
      ∀ i < r, (F.fr j i % (n' : ℤ)).toNat ∈ Formalism.G0.cell r u s (2 * r + 2 + 2 * i)) ∧
    (∀ s < n' / ((6 * r + 1) * u), Formalism.G0.Marked (TT.map Fin.valEmbedding) r u s →
      ∃ j : ℤ, (F.fr j 0 % (n' : ℤ)).toNat ∈ Formalism.G0.cell r u s (2 * r + 2)) ∧
    (∀ j : ℤ, F.fr j (r - 1) - F.fr (j - 1) 0 < G' ∧ (F.letters j).card ≤ N₁) ∧
    (∀ j : ℤ, ∀ x ∈ F.LLset j, (((F.LLset j).filter (· ≤ x)).card ≤ r ∨
        (F.LLset j).card < ((F.LLset j).filter (· ≤ x)).card + r) → F.GapGt L₂ j x) ∧
    (∀ j : ℤ, F.GapGt L₂ j (F.fr j 0))

def SegmentCountBounds (n' N G' N₁ : ℕ) : Prop := n' ≤ N * G' ∧ N * G' ≤ N₁ * (n' + G')

def OrbitPositions (_D : D7) : Prop :=
  ∀ (n' : ℕ) [NeZero n'] (TT : Finset (Fin n')) (r L₁ L₂ u M₀ G' N₁ : ℕ) (hr : 1 ≤ r),
    OrbitRaw n' TT r L₁ L₂ u M₀ G' N₁ →
    MarkedTileMaxima n' (TT.map Fin.valEmbedding) r u ∧
    SegmentLengthCondition n' (TT.map Fin.valEmbedding) r L₂ u G' N₁ hr ∧
    EarliestMaximumFar n' (TT.map Fin.valEmbedding) r L₁ ∧
    ConsecutiveMaximaClose n' (TT.map Fin.valEmbedding) G' N₁ ∧
    SegmentCountBounds n' TT.card G' N₁ ∧
    (Even n' → 2 ≤ r → OrbitFrames n' TT r L₁ L₂ u G' N₁)

def OrbitSizeBounds (_D : D7) : Prop :=
  (∀ (r : ℕ) (h : ℝ), 1 ≤ r → 0 ≤ h → ∃ Ce : ℝ, 0 < Ce ∧ ∀ de x : ℝ, 0 < de → de ≤ 1 → 3 ≤ x →
    (goodG' r de h x : ℝ) ≤ Ce * Real.log x / de ∧ (orbitWindowCount r de h x : ℝ) ≤ Ce * Real.log x ∧
    (orbitWindowCount r de h x : ℝ) ≤ 20 * (goodG' r de h x : ℝ) * de ∧
    ∀ (n' : ℕ) (TT : Finset (Fin n')) (L₂ K : ℕ), 3 * goodG' r de h x ≤ n' → IsGoodOrbit n' TT L₂ K r de h x →
      (n' : ℝ) * de / (Ce * Real.log x) ≤ TT.card ∧ (TT.card : ℝ) ≤ 40 * n' * de) ∧
  ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ n' : ℕ, x ^ (eps / 4) ≤ n' →
    3 * goodG' (⌈8 * ((2 + 8 * eps) + 2) / eps⌉₊ + 1) (x ^ (-(eps / 8))) (2 + 8 * eps) x ≤ n'

def OrbitPositionsAndSizeBounds (D : D7) : Prop := OrbitPositions D ∧ OrbitSizeBounds D

def LargeScaleConditions (D : D7) (L : SizeData₂ D) : Prop :=
  L2 D L.sc < goodU L.sc.delta1 ∧
  (∀ p : ℕ, p.Prime → IsResidueClassZero D p → 2 * L1 D L.sc p ≤ L2 D L.sc) ∧
  ∀ n' : ℕ, L.sc.x ^ (L.sc.eps / 4) ≤ (n' : ℝ) → 3 * Gp L.sc ≤ n'

def EstimatedPrimesExceedScale (D : D7) (L : SizeData₂ D) : Prop :=
  ∀ p : ℕ, p.Prime → IsResidueClassZero D p → L.sc.x ^ (L.sc.ez / 5) < (p : ℝ)

def TypePrimeSizeConds (D : D7) (L : SizeData₂ D) : Prop := Formalism.MainNotions.SizesAt L

def BadPrimeBound (D : D7) (L : SizeData₂ D) (X : Inst D L) (Cb : ℝ) : Prop := Formalism.MainNotions.J.BadProb X Cb

def SegmentEndpointChoiceExists (D : D7) (L : SizeData₂ D) : Prop := Formalism.MainNotions.UnusedSlot33.Conclusion6 D L.sc

def MertensBound (_D : D7) : Prop :=
  ∀ y : ℝ, 1 ≤ y → ∑ p ∈ (Finset.range ⌈y⌉₊).filter Nat.Prime, Real.log p / p ≤ 2 * Real.log y

def SegmentEndpointChoiceWithConstant (D : D7) (L : SizeData₂ D) (X : Inst D L) (Cb : ℝ) : Prop :=
  ∃ T : Finset (HH D), Formalism.MainNotions.J.TopsOK X Cb T

open Classical in

def SegmentEndpointChoiceAtInstance (D : D7) (L : SizeData₂ D) (X : Inst D L) : Prop :=
  ∃ T : Finset (HH D), L.sc.delta1 * D.R.n / 2 ≤ (T.card : ℝ) ∧ (T.card : ℝ) ≤ 2 * L.sc.delta1 * D.R.n ∧
    ∑ p ∈ largeOrderResiduePrimes L, Real.log p / p * ((T.filter (fun t => Formalism.MainNotions.J.BadOrb X (hP D p) t T)).card : ℝ) ≤
      (T.card : ℝ) * L.sc.x ^ (-2 + L.sc.eps)

open Classical in

def OrdersSmallPrimeBound (D : D7) (L : SizeData₂ D) : Prop :=
  ∑ p ∈ (Finset.range ⌈L.sc.X'' D.R.n⌉₊).filter (fun p => p.Prime ∧ p ≠ 2 ∧
      (addOrderOf (Formalism.MainNotions.GlobalTheoryTheory.hOf D.R.e p) : ℝ) < L.sc.x ^ (L.sc.eps / 4)), Real.log p / p ≤
    L.sc.x ^ (-hG L.sc + L.sc.eps)

def GlobalOrderEstimate (D : D7) (C₄ : ℝ) : Prop := Formalism.MainNotions.UnusedSlot33.Conclusion4 D C₄

def FrobeniusClassCompatibility (D : D7) : Prop := ∀ p : ℕ, p.Prime → IsResidueClassZero D p →
  p ≠ 2 ∧ D.R.h (hP D p) = Additive.ofMul (iotaH _ (Formalism.MainNotions.GlobalTheoryTheory.hOf D.R.e p))

open Classical in

def OrdersLargePrimeBound (D : D7) (L : SizeData₂ D) (K : Consts) : Prop :=
  rho D K L.sc ≤ L.sc.x ^ (-2 : ℝ) ∧
  ∑ p ∈ (Finset.range ⌈L.sc.X'⌉₊).filter (fun p => p.Prime ∧ InBand0 D K L.sc p), Real.log p / p ≤
    L.sc.x ^ (-1 : ℝ) ∧
  rho D K L.sc ≤ rhoB D K L.sc ∧ rhoB D K L.sc ≤ L.sc.x ^ (-2 : ℝ) ∧
  ∑ p ∈ (Finset.range ⌈L.sc.X'⌉₊).filter (fun p => p.Prime ∧ InBand D K L.sc p), Real.log p / p ≤
    L.sc.x ^ (-1 : ℝ)

def WindowLogBound (D : D7) (L : SizeData₂ D) (K : Consts) : Prop := CbLarge K L.sc

def LatticeGrowthBound (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) : Prop :=
  Formalism.MainNotions.AuxBlock8.admG1 D L X Y K

def unitBoundAtTwistedPlaces (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) : Prop :=
  Formalism.MainNotions.AuxBlock8.unitBoundAtTwistedPlaces D L X Y K

def ServiceLowerValuation (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) : Prop :=
  ∀ hT : GatTies D, LatTied hT X Y → ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), ∀ F ∈ NP X Y K u w hg,
      Y.vKge u w hg F
        ((∑ j ∈ SizeData₂.lifts D, gainP X K (aL L) (bL L) (D.what₂.places.resChar w) j) + lowFE L u w)

open Classical in

def IMP {D : D7} {L : SizeData₂ D} (X : Inst D L) (Y : LatInst D) (K : Consts) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    Submodule (D.gat u w hg).O (D.gat u w hg).Fn :=
  Submodule.span (D.gat u w hg).O {F' | ∃ VV' ⊆ VV X K (aL L) (bL L) (D.what₂.places.resChar w), ∃ F ∈ (D.gat u w hg).M,
    F' = yProd Y u w hg VV' ((((D.what₂.places.resChar w : ℕ) : (D.gat u w hg).O) ^
      (∑ t0 ∈ VV X K (aL L) (bL L) (D.what₂.places.resChar w) \ VV',
        ⌈Sv X K (aL L) (bL L) (D.what₂.places.resChar w) t0⌉.toNat)) • F)}

def LatticeGrowthBound' (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) : Prop :=
  ∀ hT : GatTies D, LatTied hT X Y → ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), ∀ F ∈ IMP X Y K u w hg,
      Y.vKge u w hg F
        ((∑ j ∈ SizeData₂.lifts D, gainP X K (aL L) (bL L) (D.what₂.places.resChar w) j) + Formalism.MainNotions.AuxBlock8.lowU D u w)

def MLatticeCond (D : D7) : Prop :=
  ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    Formalism.MainNotions.SelectionLemmas.Conclusion1 D (D.gat u w hg)

def ServiceLatticeCondition (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) : Prop :=
  Formalism.MainNotions.FormalGroupSystem.LemmaVVolumeGeneral D L X Y K

def OrbitLatticeBounds (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) : Prop :=
  ∀ hT : GatTies D, LatTied hT X Y → ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    let p := D.what₂.places.resChar w
    let G := D.gat u w hg
    ∀ t0 ∈ VV X K (aL L) (bL L) p,
      LPprime (W := G.P.W (Y.vOf u w hg t0)) (Qq := G.P.Qq (Y.vOf u w hg t0)) (O := G.O) (Kf := G.Kf) p
        (G.P.n' (Y.vOf u w hg t0)) (G.P.ι (Y.vOf u w hg t0)) (G.P.σ (Y.vOf u w hg t0)) G.P.w G.P.r
        (G.P.lam0 (Y.vOf u w hg t0)) ⌈tv X K (aL L) (bL L) p t0⌉₊ (Dp K L p) (kapv X K (aL L) (bL L) p t0)
        (8 * (Dp K L p + 1))

def LatticeSandwich (D : D7) (L : SizeData₂ D) (X : Inst D L) : Prop :=
  ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    (D.gat u w hg).Mna.map ((((D.what₂.places.resChar w : ℕ) : (D.gat u w hg).O) ^
        X.ep (D.what₂.places.resChar w)) • LinearMap.id) ≤ (D.gat u w hg).M ∧
      (D.gat u w hg).M ≤ (D.gat u w hg).Mna

def RamifiedPartSaturated (D : D7) (Y : LatInst D) : Prop :=
  ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    Formalism.MainNotions.SelectionLemmas.IsSaturatedIn ((D.gat u w hg).M ⊓ Y.Vram u w hg) (D.gat u w hg).M

def LargeScaleSmallness (D : D7) (L : SizeData₂ D) : Prop := 1 ≤ D.R.m ∧ L.sc.x ^ (-L.sc.eps) ≤ 1 / 2

def CutSizes (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (C : ℝ) : Prop :=
  ∀ p : ℕ, (p : ℝ) < L.sc.X' →
    (∀ t0 ∈ VV X K (aL L) (bL L) p,
      ((⌈tv X K (aL L) (bL L) p t0⌉₊ : ℕ) : ℝ) ≤ C * (Nv X p t0 : ℝ) * L.sc.a / (p : ℝ) ∧
      (Dp K L p : ℝ) ≤ C * (Nv X p t0 : ℝ) * L.sc.a / (p : ℝ)) ∧
    (VV X K (aL L) (bL L) p ≠ ∅ → (X.ep p : ℝ) ≤ C * D.R.f * (D.R.k : ℝ) ^ 2 * Real.logb p L.sc.a)

def WeightSumBound (D : D7) (L : SizeData₂ D) (C bo : ℝ) : Prop :=
  ∑ w ∈ L.supp, SizeData₂.sz w (L.tau w) ≤ C * D.R.m * (D.host.TT.card : ℝ) * L.sc.a * Real.log L.sc.X' + bo

def RamificationSandwich (D : D7) (L : SizeData₂ D) (X : Inst D L) (Ce : ℝ) : Prop := Formalism.MainNotions.AuxBlock8.adm9 D L X Ce

def ParametersFillsEverywhere (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) : Prop := ∀ w, ParametersFill X K w

def CutSizesAtParams (D : D7) (L : SizeData₂ D) (K : Consts) (Ce C : ℝ) : Prop :=
  K.Nonneg → ∀ X : Inst D L, TypePrimeSizeConds D L ∧ RamificationSandwich D L X Ce → CutSizes D L X K C

def WeightSumAtParams (D : D7) (L : SizeData₂ D) (K : Consts) (C C' bo : ℝ) : Prop :=
  K.Nonneg → ∀ X : Inst D L, TypePrimeSizeConds D L ∧ MertensBound D ∧ ParametersFillsEverywhere D L X K ∧ CutSizes D L X K C → WeightSumBound D L C' bo

def OrbitStructureBounds (D : D7) : Prop := OrbitPositionsAndSizeBounds D

def LargeScaleOfPrimeConditions (D : D7) (L : SizeData₂ D) : Prop := TypePrimeSizeConds D L ∧ EstimatedPrimesExceedScale D L → LargeScaleConditions D L

def BadPrimeBoundOfPrimeSizes (D : D7) (L : SizeData₂ D) (Cb : ℝ) : Prop :=
  ∀ X : Inst D L, TypePrimeSizeConds D L ∧ EstimatedPrimesExceedScale D L → BadPrimeBound D L X Cb

def SegmentEndpointChoiceWithConstantAt (D : D7) (L : SizeData₂ D) (Cb : ℝ) : Prop :=
  ∀ X : Inst D L, SegmentEndpointChoiceExists D L ∧ 16 ≤ L.sc.delta1 * D.R.n ∧ BadPrimeBound D L X Cb → SegmentEndpointChoiceWithConstant D L X Cb

def SegmentEndpointChoiceAt (D : D7) (L : SizeData₂ D) (Cb : ℝ) : Prop :=
  ∀ X : Inst D L, SegmentEndpointChoiceExists D L ∧ MertensBound D ∧ 16 ≤ L.sc.delta1 * D.R.n ∧ 0 ≤ Cb ∧
    16 * Cb * L.sc.x ^ (L.sc.eps / 3) ≤ L.sc.x ^ L.sc.eps ∧ BadPrimeBound D L X Cb → SegmentEndpointChoiceAtInstance D L X

def OrdersSmallPrimeLemma (D : D7) (L : SizeData₂ D) (C₄ : ℝ) : Prop := GlobalOrderEstimate D C₄ ∧ TypePrimeSizeConds D L → OrdersSmallPrimeBound D L

def ParametersSecondOrderCondition (D : D7) (L : SizeData₂ D) (K : Consts) : Prop :=
  K.Nonneg → TypePrimeSizeConds D L ∧ OrbitSizeBounds D ∧ WindowLogBound D L K → OrdersLargePrimeBound D L K

def GrowthHypotheses (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) : Prop :=
  unitBoundAtTwistedPlaces D L X Y K ∧ MLatticeCond D ∧ ServiceLatticeCondition D L X Y K ∧ OrbitLatticeBounds D L X Y K ∧ LatticeSandwich D L X ∧ RamifiedPartSaturated D Y ∧ LargeScaleSmallness D L ∧
    ServiceLowerValuation D L X Y K

def LatticeGrowthOfGrowthHypotheses (D : D7) (L : SizeData₂ D) (K : Consts) : Prop :=
  ∀ (X : Inst D L) (Y : LatInst D), GrowthHypotheses D L X Y K → LatticeGrowthBound D L X Y K ∧ LatticeGrowthBound' D L X Y K

def admitted (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) (C₄ : ℝ) : Prop :=
  TypePrimeSizeConds D L ∧ EstimatedPrimesExceedScale D L ∧ SegmentEndpointChoiceExists D L ∧ MertensBound D ∧ GlobalOrderEstimate D C₄ ∧ GrowthHypotheses D L X Y K ∧ WindowLogBound D L K

def Conclusion₂ (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) (Cb : ℝ) : Prop :=
  OrbitPositionsAndSizeBounds D ∧ LargeScaleConditions D L ∧ BadPrimeBound D L X Cb ∧ SegmentEndpointChoiceWithConstant D L X Cb ∧ SegmentEndpointChoiceAtInstance D L X ∧ OrdersSmallPrimeBound D L ∧ OrdersLargePrimeBound D L K ∧
    LatticeGrowthBound D L X Y K ∧ LatticeGrowthBound' D L X Y K

def Stmt (D : D7) (L : SizeData₂ D) (K : Consts) (C₄ Cb : ℝ) : Prop :=
  K.Nonneg → ∀ (X : Inst D L) (Y : LatInst D), admitted D L X Y K C₄ → Conclusion₂ D L X Y K Cb

def ClosedFormOfAdmitted (D : D7) (L : SizeData₂ D) : Prop :=
  ∀ K : Consts, K.Nonneg → ∀ C₄ : ℝ, ∃ Cb : ℝ, 0 ≤ Cb ∧
    ∀ (X : Inst D L) (Y : LatInst D), admitted D L X Y K C₄ → Conclusion₂ D L X Y K Cb

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def FamilyOrbitPositionsAndSizeBounds : Prop := ∀ x (i : Fm.Ix x), OrbitPositionsAndSizeBounds (Fm.D x i)

def FamilyLargeScale : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, LargeScaleConditions (Fm.D x i) (Fm.L x i)

def FamilyBadPrimeBound : Prop := ∃ Cb : ℝ, 0 ≤ Cb ∧ ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, BadPrimeBound (Fm.D x i) (Fm.L x i) (Fm.Gx x i) Cb

def FamilyMaximaChoiceWithConstant : Prop := ∃ Cb : ℝ, 0 ≤ Cb ∧ ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, SegmentEndpointChoiceWithConstant (Fm.D x i) (Fm.L x i) (Fm.Gx x i) Cb

def FamilyMaximaChoice : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, SegmentEndpointChoiceAtInstance (Fm.D x i) (Fm.L x i) (Fm.Gx x i)

def FamilyOrdersSmallPrimeBoundConstant : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, OrdersSmallPrimeBound (Fm.D x i) (Fm.L x i)

def FamilyOrdersLargePrimeBoundConstant : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, OrdersLargePrimeBound (Fm.D x i) (Fm.L x i) Fm.GK

def FamilyLatticeGrowth : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, LatticeGrowthBound (Fm.D x i) (Fm.L x i) (Fm.Gx x i) (Fm.Gy x i) Fm.GK

def FamilyLatticeValuationLowerBound : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, LatticeGrowthBound' (Fm.D x i) (Fm.L x i) (Fm.Gx x i) (Fm.Gy x i) Fm.GK

def FamilyWindowLogBound : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, WindowLogBound (Fm.D x i) (Fm.L x i) Fm.GK

def FamilyInertPrimesLarge : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, EstimatedPrimesExceedScale (Fm.D x i) (Fm.L x i)

def FamilyMaximaSpacing : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, SegmentEndpointChoiceExists (Fm.D x i) (Fm.L x i)

def FamilyMertensBound : Prop := ∀ x (i : Fm.Ix x), MertensBound (Fm.D x i)

def FamilyGlobalOrderEstimate (C₄ : ℝ) : Prop := ∀ x (i : Fm.Ix x), GlobalOrderEstimate (Fm.D x i) C₄

def FamilyFirstGrowthBound : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, GrowthHypotheses (Fm.D x i) (Fm.L x i) (Fm.Gx x i) (Fm.Gy x i) Fm.GK

def FamilyCutSizes : Prop :=
  ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, CutSizes (Fm.D x i) (Fm.L x i) (Fm.Gx x i) Fm.GK C

def FamilyWeightSumBound : Prop :=
  ∃ (C x0 : ℝ) (δ : ℝ → ℝ), Filter.Tendsto δ Filter.atTop (nhds 0) ∧
    ∀ x ≥ x0, ∀ i : Fm.Ix x, WeightSumBound (Fm.D x i) (Fm.L x i) C ((Fm.L x i).sc.b ^ δ x)

def FamilyRamificationSandwich : Prop :=
  ∃ Ce : ℝ, 0 ≤ Ce ∧ ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, RamificationSandwich (Fm.D x i) (Fm.L x i) (Fm.Gx x i) Ce

def FamilyCutSizesOfRamificationSandwich : Prop := FamilyRamificationSandwich Fm → FamilyCutSizes Fm

def FamilyWeightSum : Prop := FamilyMertensBound Fm → FamilyCutSizes Fm → FamilyWeightSumBound Fm

def FamilyLargeScaleOfInertPrimesLarge : Prop := FamilyInertPrimesLarge Fm → FamilyLargeScale Fm

def FamilyBadPrimeBoundOfInertPrimesLarge : Prop := FamilyInertPrimesLarge Fm → FamilyBadPrimeBound Fm

def FamilyMaximaChoiceBound : Prop := FamilyMaximaSpacing Fm → FamilyMertensBound Fm → FamilyBadPrimeBound Fm → FamilyMaximaChoiceWithConstant Fm ∧ FamilyMaximaChoice Fm

def FamilyOrdersSmallPrimeBound (C₄ : ℝ) : Prop := FamilyGlobalOrderEstimate Fm C₄ → FamilyOrdersSmallPrimeBoundConstant Fm

def FamilyOrdersLargePrimeBound : Prop := FamilyOrbitPositionsAndSizeBounds Fm → FamilyWindowLogBound Fm → FamilyOrdersLargePrimeBoundConstant Fm

def FamilyLatticeGrowthOfGrowthHypotheses : Prop := FamilyFirstGrowthBound Fm → FamilyLatticeGrowth Fm ∧ FamilyLatticeValuationLowerBound Fm

def AdmF (C₄ : ℝ) : Prop :=
  FamilyInertPrimesLarge Fm ∧ FamilyMaximaSpacing Fm ∧ FamilyMertensBound Fm ∧ FamilyGlobalOrderEstimate Fm C₄ ∧ FamilyFirstGrowthBound Fm ∧ FamilyRamificationSandwich Fm ∧ FamilyWindowLogBound Fm

def ConclusionOnFamily : Prop :=
  FamilyOrbitPositionsAndSizeBounds Fm ∧ FamilyLargeScale Fm ∧ FamilyBadPrimeBound Fm ∧ FamilyMaximaChoiceWithConstant Fm ∧ FamilyMaximaChoice Fm ∧ FamilyOrdersSmallPrimeBoundConstant Fm ∧ FamilyOrdersLargePrimeBoundConstant Fm ∧ FamilyLatticeGrowth Fm ∧
    FamilyCutSizes Fm ∧ FamilyWeightSumBound Fm ∧ FamilyLatticeValuationLowerBound Fm

def KudlaFamilyStatement (C₄ : ℝ) : Prop := AdmF Fm C₄ → ConclusionOnFamily Fm

def FamilyClosedForm : Prop := ∀ C₄ : ℝ, KudlaFamilyStatement Fm C₄

end Family

end Formalism.MainNotions.CornerGLContinuity

end
