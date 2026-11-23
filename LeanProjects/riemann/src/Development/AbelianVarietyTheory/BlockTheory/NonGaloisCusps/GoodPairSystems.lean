import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Formalism.LocalRingCardinality.DataNChoice
import Formalism.LocalRingCardinality.DataNChTie
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems

variable (D : D7)

abbrev TwDatum : Type :=
  Σ (i : D.ntw.Tw) (Q : Finset (PlE D.host)) (k : ℕ), (D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ)

def Twisted (w : D.what₂.places.Pl) : Prop := D.what₂.muAt w ≠ D.what₂.mu0

def SameBelow (w w' : D.what₂.places.Pl) : Prop :=
  ∀ x : ↥D.LL0, 0 ≤ D.what₂.places.val w (x : D.what₂.LL) ↔ 0 ≤ D.what₂.places.val w' (x : D.what₂.LL)

def SamePair (w w' : D.what₂.places.Pl) : Prop :=
  SameBelow D w w' ∨ SameBelow D (D.what₂.places.conj w) w'

def LiesUnder (i : D.ntw.Tw) (w : D.what₂.places.Pl) : Prop :=
  ∀ x : 𝓞 ↥D.LL0,
    (∃ y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i),
      algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y = D.ntw.emb0 i (x : ↥D.LL0)) ↔
    0 < D.what₂.places.val w ((x : ↥D.LL0) : D.what₂.LL)

def TwistedPlaceSettings (twI : D.what₂.places.Pl → D.ntw.Tw) : Prop :=
  (∀ w, Twisted D w → D.ntw.l (twI w) = D.what₂.places.resChar w ∧
    (LiesUnder D (twI w) w ∨ LiesUnder D (twI w) (D.what₂.places.conj w))) ∧
  ∀ w w', Twisted D w → Twisted D w' → SamePair D w w' → twI w = twI w'

def namedPrimes : Set ℕ :=
  {2, 3, 5, D.host.g 0, D.host.g 1, D.host.pde, D.host.pde'} ∪ Set.range fun u : D.what₂.Word => (D.mem u).A.T

variable {D}

def expDat (xd : ThData D) : IntegralHeckeForms.XD D := ⟨xd.xd0, xd.thetaBase_invariant_action⟩

def GoodDatum (xd : ThData D) (N0 : D.ntw.Tw → ℕ) (A : Finset (PlE D.host)) (t : TwDatum D) : Prop :=
  (∀ P ∈ t.2.1, ∀ P', IsConjPl D.host P P' → P' ∈ t.2.1) ∧
  (∀ P ∈ t.2.1, ∀ p ∈ namedPrimes D, P ∉ placesOver D.host.E p) ∧
  (∀ lam : D.ntw.abelian₂ t.1, (∑ δ, D.ntw.th t.1 ∅ lam δ) ≠ 0) ∧
  (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool,
    IntegralHeckeForms.FullRk D.nexp (expDat xd) t.1 j b (IntegralHeckeForms.SgJ D.nexp (expDat xd) t.1 j b)) ∧
  ∃ S : ∀ (j : ℕ) (b : Bool), Finset (D.nexp.Dat t.1 j b),
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool,
      IntegralHeckeForms.BasisOf D.nexp t.1 j b (IntegralHeckeForms.SgJ D.nexp (expDat xd) t.1 j b) (S j b)) ∧
    ∀ a : ℤ, IsCoprime a (D.ntw.l t.1 : ℤ) →
      IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) (expDat xd) N0 t.1 (((D.ntw.l t.1 : ℝ) ^ 2)⁻¹) S A t.2.1 t.2.2.1
        (t.2.2.2 ^ a)

def GoodSystem (xd : ThData D) (N0 : D.ntw.Tw → ℕ) (A : D.ntw.Tw → Finset (PlE D.host))
    (t : D.what₂.places.Pl → TwDatum D) : Prop :=
  TwistedPlaceSettings D (fun w => (t w).1) ∧
  (∀ w, Twisted D w → GoodDatum xd N0 (A (t w).1) (t w)) ∧
  (∀ w w', Twisted D w → Twisted D w' → SamePair D w w' → t w = t w') ∧
  ∀ w w', Twisted D w → Twisted D w' → ¬ SamePair D w w' →
    ∀ P ∈ (t w).2.1, ∀ P' ∈ (t w').2.1, ∀ p : ℕ, p.Prime →
      ¬ (P ∈ placesOver D.host.E p ∧ P' ∈ placesOver D.host.E p)

def recorded (c : NChoice D) (w : D.what₂.places.Pl) : TwDatum D :=
  ⟨c.twI w, c.Q w, c.k' w, BlochKatoReduction.Gen.psiAt (c.sd w) (c.psi' w)⟩

def TwGoodAt (c : NChoice D) (xd : ThData D) (N0 : D.ntw.Tw → ℕ) : Prop :=
  GoodSystem xd N0 (fun _ => ∅) (recorded c) ∧
  ∀ w, Twisted D w → D.what₂.places.conj w ≠ w → c.sd (D.what₂.places.conj w) = !c.sd w

def ExistsChoice (xd : ThData D) (N0 : D.ntw.Tw → ℕ) : Prop :=
  (∃ twI, TwistedPlaceSettings D twI) ∧
  ∀ twI, TwistedPlaceSettings D twI → ∀ A : D.ntw.Tw → Finset (PlE D.host),
    ∃ t : D.what₂.places.Pl → TwDatum D, (∀ w, (t w).1 = twI w) ∧ GoodSystem xd N0 A t

def WithToricIntegralityConstant (D : D7) (P : (D.ntw.Tw → ℕ) → Prop) : Prop :=
  (∃ N0, BlochKatoReduction.adm9 D N0) ∧ ∀ N0, BlochKatoReduction.adm9 D N0 → P N0

def FamTwGood {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    WithToricIntegralityConstant (Fm.D x i) fun N0 => TwGoodAt (Fm.ex x hx i).nch (Fm.ex x hx i).xd N0

def FamExistsChoice {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    WithToricIntegralityConstant (Fm.D x i) fun N0 => ExistsChoice (Fm.ex x hx i).xd N0

def TwGoodClosed (𝒞 : FamClass) : Prop := Closed 𝒞 fun Fm _ => FamTwGood Fm

def ExistsChoiceClosed (𝒞 : FamClass) : Prop := Closed 𝒞 fun Fm _ => FamExistsChoice Fm

def Statement (𝒞 : FamClass) : Prop := ExistsChoiceClosed 𝒞 ∧ TwGoodClosed 𝒞

theorem samePair_conj (w : D.what₂.places.Pl) : SamePair D w (D.what₂.places.conj w) :=
  Or.inr fun _ => Iff.rfl

open NumberField IsDedekindDomain in
variable (D : _root_.Formalism.BasicNotions.D7) in
variable {D} in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.twisted_conj (w : D.what₂.places.Pl) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D (D.what₂.places.conj w) ↔ _root_.GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted
  rw [_root_.Formalism.BasicNotions.Rows.Data.muAt_conj]

theorem TwistedPlaceSettings.inW1 {twI : D.what₂.places.Pl → D.ntw.Tw} (h : TwistedPlaceSettings D twI) {w : D.what₂.places.Pl}
    (hw : Twisted D w) : D.ntw.NonzeroIndexPlace (twI w) := by
  rcases (h.1 w hw).2 with h1 | h1
  · exact ⟨w, hw, h1⟩
  · exact ⟨_, (twisted_conj w).2 hw, h1⟩

theorem TwGoodAt.goodTw {c : NChoice D} {xd : ThData D} {N0 : D.ntw.Tw → ℕ} (h : TwGoodAt c xd N0)
    {w : D.what₂.places.Pl} (hw : Twisted D w) :
    ∃ S, IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) (expDat xd) N0 (c.twI w) (((D.ntw.l (c.twI w) : ℝ) ^ 2)⁻¹) S ∅
      (c.Q w) (c.k' w) (BlochKatoReduction.Gen.psiAt (c.sd w) (c.psi' w)) := by
  obtain ⟨-, -, -, -, S, -, hS⟩ := h.1.2.1 w hw
  have := hS 1 isCoprime_one_left
  rw [zpow_one] at this
  exact ⟨S, this⟩

end GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems

end
