import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.GrowthBounds.ObjPol
import Formalism.SharpRestriction.GrowthBounds.SegRing
import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees
import Formalism.SharpRestriction.GrowthBounds.StatementOfDegreeAndBound
import Formalism.SharpRestriction.GrowthBounds.ConclusionA2
import Formalism.SharpRestriction.GrowthBounds.ValuationLowestDegreeRename

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.SourceCleaning

open Formalism.MainNotions.G

def LLT (n' : ℕ) : LiftLetters (Fin n') where
  vec := fun s => decide (Even s.val)
  pos := fun s => (s.val : ℤ)

abbrev TV (n' k : ℕ) := Fin n' × Fin k

def IsNormal {n' k : ℕ} (r : ℕ) (v : TV n' k) : Prop := if Even v.1.val then r ≤ v.2.val else v.2.val < r

def IsT {n' k : ℕ} (r : ℕ) (v : TV n' k) : Prop := Even v.1.val ∧ v.2.val < r

def normDeg {n' k : ℕ} (r : ℕ) (m : TV n' k →₀ ℕ) : ℕ := ∑ v ∈ m.support, if IsNormal r v then m v else 0

def InTV {O : Type*} [CommRing O] {n' k : ℕ} (r : ℕ) (h : MvPolynomial (TV n' k) O) : Prop :=
  ∀ v ∈ h.vars, ¬ IsNormal r v

def InT {O : Type*} [CommRing O] {n' k : ℕ} (r : ℕ) (h : MvPolynomial (TV n' k) O) : Prop :=
  ∀ v ∈ h.vars, IsT r v

def HasMultideg {R : Type*} [CommRing R] {n' k : ℕ} (F : MvPolynomial (TV n' k) R) (d : Fin n' → ℕ) : Prop :=
  F ∈ Formalism.MainNotions.G.Pol R k d

def OnTops {R : Type*} [CommRing R] {n' r k : ℕ} (Fr : Frames n' r) (h : MvPolynomial (TV n' k) R) : Prop :=
  ∀ v ∈ h.vars, v.1 ∈ Fr.TT

section Frames

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r)

def zF (j : ℤ) : ℤ := Fr.fr j (r - 1)

def Qj (p : ℕ) (j : ℤ) : ℕ := p ^ (zF Fr (j + 1) - zF Fr j).toNat

def evensBefore (s : ℤ) : List ℤ :=
  (((Finset.Ico (s - (r : ℤ) * n') s).filter fun y => posOf n' y ∈ Fr.TT ∧ Even y).sort (· ≤ ·)).reverse

def Arow (s : ℤ) (l : ℕ) : ℤ := (evensBefore Fr s).getD l s

end Frames

section Rings

variable (p f : ℕ) [Fact p.Prime] (O : Type*) [CommRing O] [IsDomain O] [Algebra (WF p f) O] (w : O)

def subst (n' r : ℕ) {k : ℕ} (g : Matrix (Fin k) (Fin k) (WF p f)) :
    MvPolynomial (TV n' k) (KK O) →ₐ[KK O] MvPolynomial (TV n' k) (KK O) :=
  liftSubst p f O w r (LLT n') g

def ordGe (n' r : ℕ) {k : ℕ} (g : Matrix (Fin k) (Fin k) (WF p f)) (F : MvPolynomial (TV n' k) (KK O))
    (j : ℕ) : Prop :=
  InWjRg p f O w r (LLT n') g F j

def xg (n' : ℕ) [NeZero n'] {k : ℕ} (g : Matrix (Fin k) (Fin k) (WF p f)) (a : ℤ) (b : Fin k) :
    MvPolynomial (TV n' k) (KK O) :=
  ∑ c : Fin k, X (posOf n' a, c) * C (sigMat p f O g a c b)

def yg (n' : ℕ) [NeZero n'] {k : ℕ} (g : Matrix (Fin k) (Fin k) (WF p f)) (a : ℤ) (b : Fin k) :
    MvPolynomial (TV n' k) (KK O) :=
  ∑ c : Fin k, X (posOf n' a, c) * C ((sigMat p f O g a)⁻¹ b c)

def newCoord (n' : ℕ) [NeZero n'] {k : ℕ} (g : Matrix (Fin k) (Fin k) (WF p f)) (v : TV n' k) :
    MvPolynomial (TV n' k) (KK O) :=
  if Even v.1.val then xg p f O n' g v.1.val v.2 else yg p f O n' g v.1.val v.2

def hTrue (n' : ℕ) [NeZero n'] {k : ℕ} (g : Matrix (Fin k) (Fin k) (WF p f)) (h : MvPolynomial (TV n' k) O) :
    MvPolynomial (TV n' k) (KK O) :=
  aeval (newCoord p f O n' g) (MvPolynomial.map (algebraMap O (KK O)) h)

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r)

def twRow {k : ℕ} (g : Matrix (Fin k) (Fin k) (WF p f)) (j : ℤ) (l : ℕ) (b : Fin k) :
    MvPolynomial (TV n' k) (KK O) :=
  (xg p f O n' g (Fr.fr j l) b) ^ (p ^ (zF Fr j - Fr.fr j l).toNat)

def minorI {k : ℕ} (g : Matrix (Fin k) (Fin k) (WF p f)) (j : ℤ) (I : Finset (Fin k)) :
    MvPolynomial (TV n' k) (KK O) :=
  if h : I.card = r then (Matrix.of fun l i : Fin r => twRow p f O Fr g j l.val (I.orderEmbOfFin h i)).det
  else 0

def Ifirst (r k : ℕ) : Finset (Fin k) := univ.filter fun b => b.val < r

def Del {k : ℕ} (g : Matrix (Fin k) (Fin k) (WF p f)) (j : ℤ) : MvPolynomial (TV n' k) (KK O) :=
  minorI p f O Fr g j (Ifirst r k)

def II (r k : ℕ) : Finset (Finset (Fin k)) := univ.filter fun I => I.card = r ∧ (I ∩ Ifirst r k).card = r - 1

def Rloc {k : ℕ} (g : Matrix (Fin k) (Fin k) (WF p f)) : MvPolynomial (TV n' k) (KK O) :=
  Del p f O Fr g 0 * ∏ I ∈ II r k,
    (∏ j ∈ Finset.range Fr.J, Del p f O Fr g j ^ (Qj Fr p j - 1) -
      ∏ j ∈ Finset.range Fr.J, minorI p f O Fr g j I ^ (Qj Fr p j - 1))

def alpha (k : ℕ) (j : ℤ) : ℕ := (if j = 0 then 1 else 0) + r * (k - r) * (Qj Fr p j - 1)

def R0 {k : ℕ} (g : Matrix (Fin k) (Fin k) (WF p f)) : MvPolynomial (TV n' k) (KK O) :=
  ∏ j ∈ Finset.range Fr.J, Del p f O Fr g j ^ alpha p Fr k j

def Dtop {k : ℕ} (hrk : r ≤ k) (g : Matrix (Fin k) (Fin k) (WF p f)) (s : ℤ) : MvPolynomial (TV n' k) (KK O) :=
  (Matrix.of fun l b : Fin r =>
    (xg p f O n' g (Arow Fr s l.val) (Fin.castLE hrk b)) ^ (p ^ (s - Arow Fr s l.val).toNat)).det

def DtopProd {k : ℕ} (hrk : r ≤ k) (g : Matrix (Fin k) (Fin k) (WF p f)) (mu : ℕ) : MvPolynomial (TV n' k) (KK O) :=
  ∏ s ∈ Fr.TT, Dtop p f O Fr hrk g (s.val : ℤ) ^ mu

end Rings

section Keys

def OHyp (p f : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF p f) O] (S : UniformizedDVR p O) : Prop :=
  S.SqP ∧ Module.Finite (WF p f) O ∧ Function.Injective (algebraMap (WF p f) O)

def TwistBound {n' r : ℕ} [NeZero n'] (p : ℕ) (Fr : Frames n' r) (Q : ℕ) : Prop :=
  (∀ j : ℤ, Qj Fr p j ≤ Q) ∧ ∀ s ∈ Fr.TT, ∀ l < r, p ^ ((s.val : ℤ) - Arow Fr s.val l).toNat ≤ Q

structure Term (n' k : ℕ) (O : Type) [CommRing O] [IsDomain O] where
  i : ℕ
  n : ℕ
  ka : Fin n → MvPolynomial (TV n' k) (KK O)
  o : Fin n → ℕ
  ka0 : Fin n → MvPolynomial (TV n' k) (KK O)
  h : MvPolynomial (TV n' k) O

def Term.level {n' k : ℕ} {O : Type} [CommRing O] [IsDomain O] (τ : Term n' k O) : ℕ := τ.i + ∑ l, τ.o l

def wInv {O : Type} [CommRing O] [IsDomain O] (w : O) : KK O := (algebraMap O (KK O) w)⁻¹

variable (p f : ℕ) [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF p f) O]

def IsKey (w : O) (n' r : ℕ) {k : ℕ} (Q : ℕ) (g : Matrix (Fin k) (Fin k) (WF p f))
    (ka : MvPolynomial (TV n' k) (KK O)) (o : ℕ) (ka0 : MvPolynomial (TV n' k) (KK O)) : Prop :=
  InA ka ∧ o ≤ 2 * Q ∧ (∀ m ∈ ka0.support, normDeg r m = o) ∧ InWj w ka0 o ∧
    InWj w (subst p f O w n' r g ka - ka0) (o + 1) ∧
    ∀ g' : Matrix (Fin k) (Fin k) (WF p f), IsGLW g' → ordGe p f O w n' r g' ka o

def Term.Valid (w : O) (n' r : ℕ) {k : ℕ} (Q : ℕ) (g : Matrix (Fin k) (Fin k) (WF p f)) (τ : Term n' k O) :
    Prop :=
  (∀ l, IsKey p f w n' r Q g (τ.ka l) (τ.o l) (τ.ka0 l)) ∧ InTV r τ.h

def Term.InTops {n' r k : ℕ} (Fr : Frames n' r) (τ : Term n' k O) : Prop :=
  (∀ l, OnTops Fr (τ.ka l) ∧ OnTops Fr (τ.ka0 l)) ∧ OnTops Fr τ.h

variable {n' r : ℕ} [NeZero n']

def Term.sym (w : O) (Fr : Frames n' r) {k : ℕ} (hrk : r ≤ k) (g : Matrix (Fin k) (Fin k) (WF p f))
    (c' mu la : ℕ) (τ : Term n' k O) : MvPolynomial (TV n' k) (KK O) :=
  C (algebraMap O (KK O) (w ^ τ.i)) * (∏ l, τ.ka0 l) * (subst p f O w n' r g (R0 p f O Fr g)) ^ c' *
    (∏ j ∈ Finset.range Fr.J, (subst p f O w n' r g (Del p f O Fr g j)) ^ la) *
    subst p f O w n' r g (DtopProd p f O Fr hrk g mu) * MvPolynomial.map (algebraMap O (KK O)) τ.h

def Term.raw (w : O) (Fr : Frames n' r) {k : ℕ} (hrk : r ≤ k) (g : Matrix (Fin k) (Fin k) (WF p f))
    (c' mu la : ℕ) (τ : Term n' k O) : MvPolynomial (TV n' k) (KK O) :=
  C (algebraMap O (KK O) (w ^ τ.i)) * (∏ l, τ.ka l) * (Rloc p f O Fr g) ^ c' *
    (∏ j ∈ Finset.range Fr.J, (Del p f O Fr g j) ^ la) * DtopProd p f O Fr hrk g mu * hTrue p f O n' g τ.h

end Keys

def CommonHypotheses (p n' r k : ℕ) : Prop := 13 ≤ p ∧ 2 ≤ r ∧ r ≤ k ∧ 2 ≤ n' ∧ Even n'

def Conclusion1 (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p n' r k : ℕ) [Fact p.Prime] [NeZero n'] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF p n') O] (S : UniformizedDVR p O), OHyp p n' O S → CommonHypotheses p n' r k →
  ∀ (Fr : Frames n' r) (L₁ N₁ : ℕ), Fr.Valid L₁ N₁ →
  ∀ g g' : Matrix (Fin k) (Fin k) (WF p n'), IsGLW g → IsGLW g' →
    ratPlane p n' r g' ≠ ratPlane p n' r g → ordGe p n' O S.w n' r g' (Rloc p n' O Fr g) 1

def Conclusion2 (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p n' r k : ℕ) [Fact p.Prime] [NeZero n'] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF p n') O] (S : UniformizedDVR p O), OHyp p n' O S → CommonHypotheses p n' r k →
  ∀ (Fr : Frames n' r) (L₁ N₁ : ℕ), Fr.Valid L₁ N₁ →
  ∀ g : Matrix (Fin k) (Fin k) (WF p n'), IsGLW g →
    ∃ (n : ℕ) (e : Fin n → ℕ) (ex : Fin n → ℕ → ℕ) (nu : Fin n → (TV n' k →₀ ℕ))
      (H : Fin n → MvPolynomial (TV n' k) O),
      (∀ i, 1 ≤ e i ∧ (∀ v ∈ (nu i).support, IsNormal r v ∧ v.1 ∈ Fr.TT) ∧ (nu i).sum (fun _ m => m) ≤ e i ∧
        InT r (H i) ∧ OnTops Fr (H i) ∧ ∀ j < Fr.J, (alpha p Fr k j : ℤ) - e i ≤ ex i j) ∧
      subst p n' O S.w n' r g (Rloc p n' O Fr g - R0 p n' O Fr g) =
        ∑ i, C (algebraMap O (KK O) (S.w ^ e i)) * monomial (nu i) 1 *
          (∏ j ∈ Finset.range Fr.J, (subst p n' O S.w n' r g (Del p n' O Fr g j)) ^ ex i j) *
          MvPolynomial.map (algebraMap O (KK O)) (H i)

def PointsLemma (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p n' r k : ℕ) [Fact p.Prime] [NeZero n'] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF p n') O] (S : UniformizedDVR p O), OHyp p n' O S → ∀ hH : CommonHypotheses p n' r k,
  ∀ (Fr : Frames n' r) (L₁ N₁ : ℕ), Fr.Valid L₁ N₁ → ∀ Q : ℕ, TwistBound p Fr Q →
  ∀ g : Matrix (Fin k) (Fin k) (WF p n'), IsGLW g →
  ∀ s ∈ Fr.TT, ∀ b : Fin k, IsNormal r (s, b) →
    ∃ (n : ℕ) (ka ka0 : Fin n → MvPolynomial (TV n' k) (KK O)) (H : Fin n → MvPolynomial (TV n' k) O),
      (∀ i, IsKey p n' S.w n' r Q g (ka i) 1 (ka0 i) ∧ InT r (H i) ∧
        OnTops Fr (ka i) ∧ OnTops Fr (ka0 i) ∧ OnTops Fr (H i)) ∧
      X (s, b) * subst p n' O S.w n' r g (Dtop p n' O Fr hH.2.2.1 g (s.val : ℤ)) =
        ∑ i, MvPolynomial.map (algebraMap O (KK O)) (H i) * (C (wInv S.w) * ka0 i)

def Conclusion4 (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p n' r k : ℕ) [Fact p.Prime] [NeZero n'] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF p n') O] (S : UniformizedDVR p O), OHyp p n' O S → ∀ hH : CommonHypotheses p n' r k,
  ∀ (Fr : Frames n' r) (L₁ N₁ : ℕ), Fr.Valid L₁ N₁ → ∀ Q : ℕ, TwistBound p Fr Q →
  ∀ g : Matrix (Fin k) (Fin k) (WF p n'), IsGLW g →
  ∀ (c' o : ℕ) (d : Fin n' → ℕ) (n : ℕ) (τ : Fin n → Term n' k O),
    (∀ i, (τ i).Valid p n' S.w n' r Q g ∧ (τ i).InTops Fr ∧ o ≤ (τ i).level ∧
      HasMultideg ((τ i).sym p n' S.w Fr hH.2.2.1 g c' ((2 * Q + 3) * c') c') d ∧
      HasMultideg ((τ i).raw p n' S.w Fr hH.2.2.1 g c' ((2 * Q + 3) * c') c') d) →
    ∃ F : MvPolynomial (TV n' k) (KK O), InA F ∧ OnTops Fr F ∧ HasMultideg F d ∧
      InWj S.w (subst p n' O S.w n' r g F - ∑ i, (τ i).sym p n' S.w Fr hH.2.2.1 g c' ((2 * Q + 3) * c') c')
        (o + c') ∧
      ∀ g' : Matrix (Fin k) (Fin k) (WF p n'), IsGLW g' → ratPlane p n' r g' ≠ ratPlane p n' r g →
        ordGe p n' O S.w n' r g' F (o + c')

def Bprime {O : Type} [CommRing O] {σN : Type} {M r : ℕ} (LL : Letters (Fin M)) (Jset : Set (Fin M))
    (A : Fin r → Fin M) (G : MvPolynomial (Fin M × Fin r) (MvPolynomial σN O)) : ℕ :=
  G.support.sup fun m => ∑ v ∈ m.support, if v.1 ∈ Jset ∧ LL.vec v.1 = true ∧ v.1 ∉ Set.range A then m v else 0

def Dhat {O : Type} [CommRing O] {σN : Type} {M r : ℕ} (A : Fin r → Fin M) :
    MvPolynomial (Fin M × Fin r) (MvPolynomial σN O) :=
  (Matrix.of fun l b : Fin r => X (A l, b)).det

def Conclusion5 (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (σN : Type) (M r : ℕ) [NeZero r]
    (LL : Letters (Fin M)) (s : Fin M) (A : Fin r → Fin M)
    (G : MvPolynomial (Fin M × Fin r) (MvPolynomial σN O)) (th : ℤ),
    Function.Injective A → (∀ l, LL.vec (A l) = true ∧ A l < s) →
    (∀ i, LL.vec i = true → i < s → (∃ l, A l ≤ i) → i ∈ Set.range A) →
    ((th : ℤ) : WithTop ℤ) ≤ valS LL {i | i < s} G → (Bprime LL {i | i < s} A G : ℤ) < th →
    ∃ Qt : MvPolynomial (Fin M × Fin r) (MvPolynomial σN O),
      G = (Dhat A) ^ (th - Bprime LL {i | i < s} A G).toNat * Qt ∧
      ∀ (J' : Set (Fin M)) (t : ℤ), ((t : ℤ) : WithTop ℤ) ≤ valS LL J' G →
        (((t - (th - Bprime LL {i | i < s} A G)) : ℤ) : WithTop ℤ) ≤ valS LL J' Qt

section Real

variable {n' r : ℕ} [NeZero n']

def levDeg (p : ℕ) (Fr : Frames n' r) (deg : Fin n' → ℕ) (j x : ℤ) : ℝ :=
  (deg (posOf n' x) : ℝ) / (p : ℝ) ^ (Fr.dist j x)

def Bo (p : ℕ) (Fr : Frames n' r) (deg : Fin n' → ℕ) (j x : ℤ) : ℝ := levDeg p Fr deg j (Fr.oldest j x)

def sl (p : ℕ) (Fr : Frames n' r) (deg : Fin n' → ℕ) (Y : ℝ) (k : ℕ) (j x : ℤ) : ℤ :=
  ⌊Bo p Fr deg j x / (Y * (k : ℝ) ^ 2)⌋

def alphaMax (p : ℕ) (Fr : Frames n' r) (k : ℕ) : ℕ := (Finset.range Fr.J).sup fun j => alpha p Fr k j

def cPrime (n' r N c0 c'' cStar : ℕ) : ℕ := cStar + (r * N * c0 + 2 * r * n' * c'')

def mStar (p : ℕ) (Fr : Frames n' r) (k N₁ Q c' : ℕ) : ℕ :=
  (N₁ + 1) * ((2 * Q + 3) * c' + k * Q + c' * alphaMax p Fr k + 3 * c')

def HypII (CLa CD Csz : ℝ) (p : ℕ) (Fr : Frames n' r) (k L₁ N₁ G' : ℕ) (deg : Fin n' → ℕ) (a : ℕ)
    (Y : ℝ) (c0 c'' cStar : ℕ) (Dd : ℝ) : Prop :=
  let N : ℝ := Fr.TT.card
  let Q : ℝ := (p : ℝ) ^ G'
  let La : ℝ := CLa * (N₁ : ℝ) ^ 2 * Real.log a
  let om : ℝ := (r : ℝ) * N * c0 + 2 * r * n' * c''
  (∀ j : ℤ, zF Fr j - Fr.fr (j - 1) 0 ≤ G') ∧ (N₁ : ℝ) ^ 2 ≤ r * N ∧
  (∀ s ∈ Fr.TT, (a : ℝ) + c'' ≤ deg s ∧ (deg s : ℝ) ≤ 2 * a - c'') ∧
  (r : ℝ) ≤ Y ∧ La ≤ k ∧ N₁ + 2 * r ≤ k - r ∧ 256 * (k : ℝ) ^ 2 * N * Y ^ 2 ≤ (p : ℝ) ^ ((L₁ : ℤ) - 1) ∧
  CD * N * (k : ℝ) ^ 2 * Real.logb p a ≤ Dd ∧ 8 * (Dd + 1) ≤ (cStar : ℝ) ∧
  Csz * (k : ℝ) ^ 3 * (r : ℝ) ^ 2 * N * Q ^ 5 * ((cStar : ℝ) + om) * Y ≤ a

def monPh (O : Type) [CommRing O] (K p : ℕ) (Fr : Frames n' r) (mon : TV n' (r + K) →₀ ℕ) {n : ℕ}
    (xi : Fin n → ℤ → SegRing O r K) : MvPolynomial (TV n' (r + K)) O :=
  monomial mon 1 * ∑ i, ∏ j ∈ Finset.range Fr.J, phSeg O K p Fr (j : ℤ) (xi i j)

variable (p f : ℕ) [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF p f) O]

def Realisable (w : O) (n' r : ℕ) {k : ℕ} (g : Matrix (Fin k) (Fin k) (WF p f)) (c' o : ℕ)
    (sig : MvPolynomial (TV n' k) (KK O)) : Prop :=
  ∃ F : MvPolynomial (TV n' k) (KK O), InA F ∧ (∀ d, HasMultideg sig d → HasMultideg F d) ∧
    InWj w (subst p f O w n' r g F - C (algebraMap O (KK O) (w ^ o)) * sig) (o + c') ∧
    ∀ g' : Matrix (Fin k) (Fin k) (WF p f), IsGLW g' → ratPlane p f r g' ≠ ratPlane p f r g →
      ordGe p f O w n' r g' F (o + c')

end Real

def Conclusion6 (_D : Formalism.BasicNotions.D7) (CLa CD Csz : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [Fact p.Prime] [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra (WF p n') O] (S : UniformizedDVR p O), OHyp p n' O S →
    CommonHypotheses p n' r (r + K) →
  ∀ (Fr : Frames n' r) (L₁ N₁ G' : ℕ), Fr.Valid L₁ N₁ → TwistBound p Fr (p ^ G') →
  ∀ (deg : Fin n' → ℕ) (a : ℕ) (Y : ℝ) (c0 c'' cStar : ℕ) (Dd : ℝ),
    HypII CLa CD Csz p Fr (r + K) L₁ N₁ G' deg a Y c0 c'' cStar Dd →
  let c' := cPrime n' r Fr.TT.card c0 c'' cStar
  ∀ g : Matrix (Fin (r + K)) (Fin (r + K)) (WF p n'), IsGLW g →
  ∀ (n : ℕ) (obd : ℤ → ℤ → ℝ) (xi : Fin n → ℤ → SegRing O r K) (dd : ℤ → ℤ → ℕ),
    (∀ (i : Fin n) (j : ℕ), j < Fr.J →
      xi i j ∈ XX' O r K Fr j (fun _ => (mStar p Fr (r + K) N₁ (p ^ G') c' : ℤ))
        (fun x => Bo p Fr deg j x / 2 - sl p Fr deg Y (r + K) j x) (obd j) ∧
      xi i j ∈ restrictSupport O {mm | ∀ x ∈ Fr.letters j, ∑ c : Fin (r + K), mm (x, c) = dd j x}) →
    (∀ j : ℕ, j < Fr.J → ∀ x ∈ Fr.letters j, (Fr.IsW j x ∨ x ∈ Fr.LLset j) →
        |(dd j x : ℝ) - levDeg p Fr deg j x| ≤ levDeg p Fr deg j x / 100) →
  ∀ (mon : Fin n' × Fin (r + K) →₀ ℕ), IsLabel p Fr mon → (∀ v ∈ mon.support, v.1 ∈ Fr.TT) →
  ∀ o : ℕ, (∀ m ∈ (monPh O K p Fr mon xi).support, normDeg r m = o) →
    Realisable p n' S.w n' r g c' o (MvPolynomial.map (algebraMap O (KK O)) (monPh O K p Fr mon xi))

def GoodOrbitPositions (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (r : ℕ) (h : ℝ), 2 ≤ r → 0 ≤ h → ∃ Ce : ℝ, 0 < Ce ∧
  ∀ (n' : ℕ) [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de x : ℝ),
    Even n' → 1 ≤ L₁ → 2 * L₁ ≤ L₂ → 0 < de → de ≤ 1 → 3 ≤ x → L₂ < goodU de →
    3 * goodG' r de h x ≤ n' → IsGoodOrbit n' TT L₂ (r - 1) r de h x →
    let u := goodU de
    let G' := goodG' r de h x
    let N₁ := orbitWindowCount r de h x
    let T := TT.map Fin.valEmbedding
    let ell := (6 * r + 1) * u

    (∀ s < n' / ell, Formalism.G0.Marked T r u s →
      ∃ f : Fin (3 * r) → ℕ, StrictMono f ∧ T ∩ Finset.Ico (s * ell) ((s + 1) * ell) = Finset.univ.image f ∧
        (∀ i, Even (f i)) ∧ (∀ (i : Fin (3 * r)) (hi : i.val + 1 < 3 * r), f i + u < f ⟨i.val + 1, hi⟩) ∧
        (∀ i, s * ell + u ≤ f i ∧ f i + u < (s + 1) * ell)) ∧

    (∃ F : Frames n' r, F.TT = TT ∧ F.Valid L₁ N₁ ∧
      (∀ j : ℤ, ∀ i < r, ∃ s < n' / ell, Formalism.G0.Marked T r u s ∧
        (F.fr j i % (n' : ℤ)).toNat ∈ Formalism.G0.cell r u s (2 * r + 2 + 2 * i)) ∧
      (∀ s < n' / ell, Formalism.G0.Marked T r u s → ∃ j : ℤ, (F.fr j 0 % (n' : ℤ)).toNat ∈ Formalism.G0.cell r u s (2 * r + 2)) ∧
      (∀ j : ℤ, F.fr j (r - 1) - F.fr (j - 1) 0 ≤ G' ∧ (F.letters j).card ≤ N₁) ∧
      (∀ j : ℤ, ∀ x ∈ F.LLset j, (((F.LLset j).filter (· ≤ x)).card ≤ r ∨
          (F.LLset j).card < ((F.LLset j).filter (· ≤ x)).card + r) → F.GapGt L₂ j x) ∧
      (∀ j : ℤ, F.GapGt L₂ j (F.fr j 0))) ∧

    (∀ y z : ℤ, y < z → posOf n' y ∈ TT → Even y → posOf n' z ∈ TT → Even z →
      (∀ t : ℤ, y < t → t < z → ¬ (posOf n' t ∈ TT ∧ Even t)) →
      z - y ≤ G' ∧ ((Finset.Ioo y z).filter fun t => posOf n' t ∈ TT).card ≤ N₁) ∧

    (n' : ℝ) * de / (Ce * Real.log x) ≤ TT.card ∧ (TT.card : ℝ) ≤ 40 * n' * de ∧

    (∀ y : ℤ, ((Finset.Ico y (y + L₂)).filter fun t => posOf n' t ∈ TT).card ≤ r - 1)

def BlochKatoExtensionCriterion (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.adm5 D

def InvariantProjectionLemma (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.InvariantProjectionField D

def NablaDeltaComparison (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.NablaDeltaComparisonField D

def IsotypicProjectorTheorem (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.IsotypicProjectorTheoremField D

def TranslateCorollary (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.TranslateCorollaryField D

def FilteredProjectorCorollary (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.FilteredProjectorCorollaryField D

def ValuationLemma (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.ValuationLemmaField D

def ValuationsOfProducts (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.AutomorphicSideConclusion D

def PathColumnBasis (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.HyperplaneRank D

def StandardMonomialSpanBis (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D

def PathPairCorrespondence (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.RotatedSumBound D

def admB2 (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.PathWeightComponents D

def admB3 (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.ConclusionB3 D

def CoefficientDependenceLemma (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.CoefficientDependence D

def CoefficientValuationLemma (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.CanonicalTranslateJetIdentity D

def LargePrimeLengthVanishing (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.ConclusionE D

def CharpolyCoeffsLemmaFamily (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.UnitFunctionExpansion D

def SpanQuotientLemma (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.UnitProductSecondLemma D

def DividedDerivativeLemma (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.DerivativeLemma D

def SegmentPositions (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.SelectionLemmas.PathPairCorrespondence D

def ValuationsOnPolynomials (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.SelectionLemmas.admB2 D

def SpaceCriterionModuloUniformiser (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O)
    (n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K]
    (Fr : Frames n' r) (j : ℤ) (m : ℤ → ℤ) (th o : ℤ → ℝ),
  (∀ (A : MvPolynomial (ℤ × Fin r) O) (G : MvPolynomial (ℤ × Fin K) O) (M : ℤ → ℤ),
    A ∈ supported O {v : ℤ × Fin r | v.1 ∈ Fr.letters j} →
    G ∈ supported O {v : ℤ × Fin K | v.1 ∈ Fr.letters j ∧ ¬ Fr.IsW j v.1} →
    (∀ x ∈ Fr.letters j, ¬ Fr.IsW j x →
      (Even x → lam1S LZ {y | y ≤ x} G ≤ ((M x : ℤ) : WithBot ℤ) ∧
          ((M x + m x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y < x} A) ∧
      (¬ Even x → lam1S LZ {y | y < x} G ≤ ((M x : ℤ) : WithBot ℤ) ∧
          ((M x + m x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y ≤ x} A) ∧
      geR (valS LZ {y | y < x} A) (th x)) →
    (∀ mm ∈ (plEmb O r K A * nmEmb O r K G).support, ∀ x ∈ Fr.letters j, ¬ Fr.IsW j x → (ordDeg mm x : ℝ) ≤ o x) →
    plEmb O r K A * nmEmb O r K G ∈ XX' O r K Fr j m th o) ∧
  (∀ (A : MvPolynomial (ℤ × Fin r) (FF O)) (G : MvPolynomial (ℤ × Fin K) (FF O)) (M : ℤ → ℤ),
    A ∈ supported (FF O) {v : ℤ × Fin r | v.1 ∈ Fr.letters j} →
    G ∈ supported (FF O) {v : ℤ × Fin K | v.1 ∈ Fr.letters j ∧ ¬ Fr.IsW j v.1} →
    (∀ x ∈ Fr.letters j, ¬ Fr.IsW j x →
      (Even x → lam1S LZ {y | y ≤ x} G ≤ ((M x : ℤ) : WithBot ℤ) ∧
          ((M x + m x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y < x} A) ∧
      (¬ Even x → lam1S LZ {y | y < x} G ≤ ((M x : ℤ) : WithBot ℤ) ∧
          ((M x + m x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y ≤ x} A) ∧
      geR (valS LZ {y | y < x} A) (th x)) →
    (∀ mm ∈ (plEmb (FF O) r K A * nmEmb (FF O) r K G).support, ∀ x ∈ Fr.letters j, ¬ Fr.IsW j x →
      (ordDeg mm x : ℝ) ≤ o x) →
    ∃ P ∈ XX' O r K Fr j m th o,
      MvPolynomial.map (IsLocalRing.residue O) P = plEmb (FF O) r K A * nmEmb (FF O) r K G)

def admG2 (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : Prop := Formalism.MainNotions.SelectionLemmas.Conclusion2 D CLa Ck Crk Cdeg

def admitted (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : Prop :=
  GoodOrbitPositions D ∧ BlochKatoExtensionCriterion D ∧ InvariantProjectionLemma D ∧ NablaDeltaComparison D ∧ IsotypicProjectorTheorem D ∧ TranslateCorollary D ∧ FilteredProjectorCorollary D ∧ ValuationLemma D ∧ ValuationsOfProducts D ∧ PathColumnBasis D ∧
    StandardMonomialSpanBis D ∧ PathPairCorrespondence D ∧ admB2 D ∧ admB3 D ∧ CoefficientDependenceLemma D ∧ CoefficientValuationLemma D ∧ LargePrimeLengthVanishing D ∧ CharpolyCoeffsLemmaFamily D ∧ SpanQuotientLemma D ∧ DividedDerivativeLemma D ∧
    SegmentPositions D ∧ ValuationsOnPolynomials D ∧ SpaceCriterionModuloUniformiser D ∧ admG2 D CLa Ck Crk Cdeg

def aux₃ (D : Formalism.BasicNotions.D7) (CLa' CD Csz : ℝ) : Prop :=
  Conclusion1 D ∧ Conclusion2 D ∧ PointsLemma D ∧ Conclusion4 D ∧ Conclusion5 D ∧ Conclusion6 D CLa' CD Csz

def Stmt (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz : ℝ) : Prop :=
  admitted D CLa Ck Crk Cdeg → aux₃ D CLa' CD Csz

def ClosedFormOfAdmitted (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ CLa Ck Crk Cdeg : ℝ, admitted D CLa Ck Crk Cdeg →
    ∃ CLa' CD Csz : ℝ, 0 < CLa' ∧ 0 < CD ∧ 0 < Csz ∧ aux₃ D CLa' CD Csz

def AdmF (CLa Ck Crk Cdeg : ℝ) {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ∀ x (i : Fm.Ix x), admitted (Fm.D x i) CLa Ck Crk Cdeg

def OrbitValuationBound (CLa' CD Csz : ℝ) {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ i : Fm.Ix x, aux₃ (Fm.D x i) CLa' CD Csz

def KudlaFamilyStatement (CLa Ck Crk Cdeg CLa' CD Csz : ℝ) {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  AdmF CLa Ck Crk Cdeg Fm → OrbitValuationBound CLa' CD Csz Fm

def DerivativeStatementDesign (CLa Ck Crk Cdeg CLa' CD Csz : ℝ) (Fm : Formalism.MainNotions.DFamP) : Prop :=
  ∀ (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 52), KudlaFamilyStatement CLa Ck Crk Cdeg CLa' CD Csz (Fm ε h0 h1)

def FamilyClosedForm {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ∀ CLa Ck Crk Cdeg : ℝ, AdmF CLa Ck Crk Cdeg Fm →
    ∃ CLa' CD Csz : ℝ, 0 < CLa' ∧ 0 < CD ∧ 0 < Csz ∧ OrbitValuationBound CLa' CD Csz Fm

def DerivativeStatementClosedDesign (Fm : Formalism.MainNotions.DFamP) : Prop :=
  ∀ CLa Ck Crk Cdeg : ℝ, (∀ (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 52), AdmF CLa Ck Crk Cdeg (Fm ε h0 h1)) →
    ∃ CLa' CD Csz : ℝ, 0 < CLa' ∧ 0 < CD ∧ 0 < Csz ∧
      ∀ (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 52), OrbitValuationBound CLa' CD Csz (Fm ε h0 h1)

end Formalism.MainNotions.SourceCleaning
