import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LocalRingCardinality.DataJet
import Formalism.LocalRingCardinality.DataForced
import Formalism.LocalRingCardinality.DataDIVDefs
import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero

noncomputable section

open scoped BigOperators
open Classical

namespace PI.OrbJet.OJ

open Formalism.BasicNotions

def rootsPrimeTo (l : ℕ) [Fact l.Prime] : Set ℂ_[l] :=
  {ζ | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n l ∧ ζ ^ n = 1}

def Wfrac (l : ℕ) [Fact l.Prime] : Subalgebra ℚ_[l] ℂ_[l] :=
  (Algebra.adjoin ℚ_[l] (rootsPrimeTo l)).topologicalClosure

def Wint (l : ℕ) [Fact l.Prime] : Set ℂ_[l] := {x | x ∈ Wfrac l ∧ ‖x‖ ≤ 1}

def rho (l : ℕ) : ℝ := 1 / ((l : ℝ) ^ 2 - 1)

def gam (l : ℕ) : ℝ := (l : ℝ) / ((l : ℝ) ^ 2 - 1)

def expS (K : Type*) [Field K] [CharZero K] {τ : Type*} (f : MvPowerSeries τ K) : MvPowerSeries τ K :=
  PowerSeries.subst f (PowerSeries.exp K)

section Be

variable (l d : ℕ) [Fact l.Prime] [NeZero d]

def bideg (m : ZMod d →₀ ℕ) : ℕ × ℕ :=
  (m.sum fun s n => if Even s.val then n else 0, m.sum fun s n => if Even s.val then 0 else n)

def B1 (be : MvPowerSeries (ZMod d) ℂ_[l]) : Prop :=
  ∀ m, MvPowerSeries.coeff m be ∈ Wfrac l

def twist (u : ℂ_[l]) (s : ZMod d) : ℂ_[l] :=
  if Even s.val then u ^ (l ^ s.val) else (u ^ (l ^ s.val))⁻¹

def B2 (be : MvPowerSeries (ZMod d) ℂ_[l]) : Prop :=
  ∀ u : ℂ_[l], u ^ (l ^ d - 1) = 1 → ∀ m : ZMod d →₀ ℕ,
    MvPowerSeries.coeff m be * (m.prod fun s n => twist l d u s ^ n) = MvPowerSeries.coeff m be

def B3 (be : MvPowerSeries (ZMod d) ℂ_[l]) : Prop :=
  ∀ m : ZMod d →₀ ℕ, MvPowerSeries.coeff m be ≠ 0 →
    (bideg d m).1 ≠ 0 ∧ (bideg d m).2 ≠ 0 ∧ bideg d m ≠ (1, 1)

def cobX (be : MvPowerSeries (ZMod d) ℂ_[l]) : MvPowerSeries (ZMod d × Fin 2) ℂ_[l] :=
  MvPowerSeries.subst (fun s : ZMod d => if Even s.val then
      (MvPowerSeries.X (s, 0) + MvPowerSeries.X (s, 1) : MvPowerSeries (ZMod d × Fin 2) ℂ_[l])
      else MvPowerSeries.X (s, 0)) be -
    MvPowerSeries.subst (fun s : ZMod d => (MvPowerSeries.X (s, 0) : MvPowerSeries (ZMod d × Fin 2) ℂ_[l])) be -
    MvPowerSeries.subst (fun s : ZMod d => if Even s.val then
      (MvPowerSeries.X (s, 1) : MvPowerSeries (ZMod d × Fin 2) ℂ_[l]) else MvPowerSeries.X (s, 0)) be

def cobY (be : MvPowerSeries (ZMod d) ℂ_[l]) : MvPowerSeries (ZMod d × Fin 2) ℂ_[l] :=
  MvPowerSeries.subst (fun s : ZMod d => if Even s.val then
      (MvPowerSeries.X (s, 0) : MvPowerSeries (ZMod d × Fin 2) ℂ_[l])
      else MvPowerSeries.X (s, 0) + MvPowerSeries.X (s, 1)) be -
    MvPowerSeries.subst (fun s : ZMod d => (MvPowerSeries.X (s, 0) : MvPowerSeries (ZMod d × Fin 2) ℂ_[l])) be -
    MvPowerSeries.subst (fun s : ZMod d => if Even s.val then
      (MvPowerSeries.X (s, 0) : MvPowerSeries (ZMod d × Fin 2) ℂ_[l]) else MvPowerSeries.X (s, 1)) be

def OverWOne {τ : Type*} (f : MvPowerSeries τ ℂ_[l]) : Prop :=
  (∀ m, MvPowerSeries.coeff m f ∈ Wint l) ∧ MvPowerSeries.constantCoeff f = 1

def B4 (be : MvPowerSeries (ZMod d) ℂ_[l]) : Prop :=
  OverWOne l (MvPowerSeries.subst (jetLogG l d (β := Fin 2)) (expS ℂ_[l] (cobX l d be))) ∧
    OverWOne l (MvPowerSeries.subst (jetLogG l d (β := Fin 2)) (expS ℂ_[l] (cobY l d be)))

end Be

section Kmap

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 : ℕ)

abbrev XZ (Lt : Type) (N0 N1 : ℕ) : Type := (Lt × ℕ × Fin N0) ⊕ (Lt × Fin N0 × Fin N1)

def minorXZ (s : Lt) (p : ℕ) (I : Fin p ↪o Fin N1) : MvPolynomial (XZ Lt N0 N1) ℤ :=
  Matrix.det (Matrix.of fun i k : Fin p => ∑ a : Fin N0,
    MvPolynomial.X (Sum.inl (s, (i : ℕ), a)) * MvPolynomial.X (Sum.inr (s, a, I k)))

def ColChoice (nu : Lt → YoungDiagram) : Type :=
  ∀ (s : Lt) (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) ↪o Fin N1

def Gxz (nu : Lt → YoungDiagram) (I : ColChoice N1 nu) : MvPolynomial (XZ Lt N0 N1) ℤ :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), minorXZ N0 N1 s ((nu s).colLen c) (I s c)

def applyAt0 (l : ℕ) [Fact l.Prime] (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (P : MvPolynomial (XZ Lt N0 N1) ℤ) : MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l] :=
  ∑ μ ∈ P.support, MvPolynomial.monomial (Finsupp.sumFinsuppEquivProdFinsupp μ).1
    (((MvPolynomial.coeff μ P : ℤ) : ℂ_[l]) *
      ((Finsupp.sumFinsuppEquivProdFinsupp μ).2.prod fun _ n => (n.factorial : ℂ_[l])) *
      MvPowerSeries.coeff (Finsupp.sumFinsuppEquivProdFinsupp μ).2 Th)

def KvalGe (l : ℕ) [Fact l.Prime] (nu : Lt → YoungDiagram)
    (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (B : ℝ) : Prop :=
  ∀ (I : ColChoice N1 nu) (m : Lt × ℕ × Fin N0 →₀ ℕ),
    ‖MvPolynomial.coeff m (applyAt0 N0 N1 l Th (Gxz N0 N1 nu I))‖ ≤ (l : ℝ) ^ (-B)

def nablaX (nu : Lt → YoungDiagram) (J : ColChoice N0 nu) : MvPolynomial (Lt × ℕ × Fin N0) ℤ :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), Matrix.det (Matrix.of fun i k : Fin ((nu s).colLen c) =>
    (MvPolynomial.X (s, (i : ℕ), J s c k) : MvPolynomial (Lt × ℕ × Fin N0) ℤ))

def ExpansionCoeffValuationGe (l : ℕ) [Fact l.Prime] (nu : Lt → YoungDiagram)
    (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (B : ℝ) : Prop :=
  ∀ I : ColChoice N1 nu, ∃ c : ColChoice N0 nu →₀ ℂ_[l], (∀ J, ‖c J‖ ≤ (l : ℝ) ^ (-B)) ∧
    applyAt0 N0 N1 l Th (Gxz N0 N1 nu I) =
      c.sum fun J a => a • MvPolynomial.map (Int.castRingHom ℂ_[l]) (nablaX N0 nu J)

end Kmap

def minorX (R : Type) [CommRing R] (N p : ℕ) (I : Fin p ↪o Fin N) : MvPolynomial (ℕ × Fin N) R :=
  Matrix.det (Matrix.of fun i k : Fin p => MvPolynomial.X ((i : ℕ), I k))

def nablaSpan (R : Type) [CommRing R] (N : ℕ) (nu : YoungDiagram) :
    Submodule R (MvPolynomial (ℕ × Fin N) R) :=
  Submodule.span R (Set.range fun I : ∀ c : Fin (nu.rowLen 0), Fin (nu.colLen c) ↪o Fin N =>
    ∏ c : Fin (nu.rowLen 0), minorX R N (nu.colLen c) (I c))

def MinorProdSpanHasCompl : Prop :=
  ∀ (R : Type) [CommRing R] (N : ℕ) (nu : YoungDiagram),
    ∃ Cm : Submodule R (MvPolynomial (ℕ × Fin N) R), IsCompl (nablaSpan R N nu) Cm

structure Loc where

  J : Formalism.BasicNotions.JetLoc

  rank_lt_alt : J.N0 < J.N1

  nu : ZMod J.d → YoungDiagram
  nu_rows : ∀ s, (nu s).colLen 0 ≤ J.N0

  TT : Finset (ZMod J.d)

namespace Loc

variable (L : Loc)

abbrev l : ℕ := L.J.l

abbrev d : ℕ := L.J.d

abbrev N0 : ℕ := L.J.N0

abbrev N1 : ℕ := L.J.N1

abbrev Th : MvPowerSeries (ZMod L.d × Fin L.N0 × Fin L.N1) ℂ_[L.l] := L.J.Th

def A (s : ZMod L.d) : ℕ := (L.nu s).rowLen 0

def size (s : ZMod L.d) : ℕ := (L.nu s).cells.card

def cap (s : ZMod L.d) : ℕ := if s ∈ L.TT then (L.nu s).rowLen 1 else (L.nu s).rowLen 0

def Dl (s : ZMod L.d) : ℕ := if s ∈ L.TT then L.size s - L.A s else L.size s

def dTop (s : ZMod L.d) : ℕ∞ := ⨅ (e : ℕ) (_ : Odd e ∧ s + (e : ZMod L.d) ∈ L.TT), (e : ℕ∞)

def Wc (s : ZMod L.d) : ℕ :=
  sSup {c : ℕ | ∃ i : ℕ, Odd i ∧ L.l ^ i ≤ L.size (s - (i : ZMod L.d)) ∧ c = L.cap (s - (i : ZMod L.d))}

def topTerm (s : ZMod L.d) : ℝ :=
  ∑' e : ℕ,
    if Odd e ∧ (e : ℕ∞) < L.dTop s then
      max ((L.A s : ℝ) / (L.l : ℝ) ^ e - (L.cap (s + (e : ZMod L.d)) : ℝ)) 0
    else if Odd e ∧ L.dTop s < (e : ℕ∞) then (L.A s : ℝ) / (L.l : ℝ) ^ e
    else 0

def baseTerm (s : ZMod L.d) : ℝ :=
  ∑' e : ℕ,
    if Odd e ∧ (e : ℕ∞) ≠ L.dTop s then
      max ((((L.nu s).rowLen 0 : ℝ) - ((L.nu s).rowLen 1 : ℝ)) / (L.l : ℝ) ^ e -
        (L.cap (s + (e : ZMod L.d)) : ℝ)) 0
    else 0

def FD : ℝ := lpF L.l L.d (fun s => (L.Dl s : ℝ))

def Tht (ep : ℂ_[L.l]) : MvPowerSeries (ZMod L.d × Fin L.N0 × Fin L.N1) ℂ_[L.l] :=
  MvPowerSeries.subst (fun v : ZMod L.d × Fin L.N0 × Fin L.N1 =>
    MvPowerSeries.C ep * jetLogG L.l L.d v) L.Th

def beSum (be : MvPowerSeries (ZMod L.d) ℂ_[L.l]) :
    MvPowerSeries (ZMod L.d × Fin L.N0 × Fin L.N1) ℂ_[L.l] :=
  ∑ a : Fin L.N0, ∑ b : Fin L.N1,
    MvPowerSeries.subst (fun s : ZMod L.d =>
      (MvPowerSeries.X (s, a, b) : MvPowerSeries (ZMod L.d × Fin L.N0 × Fin L.N1) ℂ_[L.l])) be

def B0 (ep : ℂ_[L.l]) (be : MvPowerSeries (ZMod L.d) ℂ_[L.l]) : Prop :=
  ∃ sg : ℂ_[L.l], (sg = 1 ∨ sg = -1) ∧
    ∃ U : MvPowerSeries (ZMod L.d × Fin L.N0 × Fin L.N1) ℂ_[L.l],
      (∀ m, ‖MvPowerSeries.coeff m U‖ ≤ 1) ∧
      L.Tht ep = U * MvPowerSeries.subst (jetLogG L.l L.d (β := Fin L.N0 × Fin L.N1))
        (expS ℂ_[L.l] (sg • L.beSum be))

def AdmB : Prop :=
  ∃ ep : ℂ_[L.l], ‖ep‖ = 1 ∧ ∃ be : MvPowerSeries (ZMod L.d) ℂ_[L.l],
    L.B0 ep be ∧ B1 L.l L.d be ∧ B2 L.l L.d be ∧ B3 L.l L.d be ∧ B4 L.l L.d be

def HidaSetting (a : ℝ) : Prop :=
  (L.l : ℝ) ≤ a ∧ (∀ s, (L.size s : ℝ) ≤ a) ∧ 2 * Real.logb L.l a + 2 ≤ (L.N0 : ℝ) - 1

def ThmA (C : ℝ) : Prop :=
  ∀ a : ℝ, L.HidaSetting a →
    KvalGe L.N0 L.N1 L.l L.nu L.Th
      ((∑ s ∈ L.TT, (L.topTerm s - gam L.l * (L.Wc s : ℝ))) + L.FD -
        C * ((L.d : ℝ) * L.N0 * L.N1 * (Real.logb L.l a + 1)))

def Cor (C : ℝ) : Prop :=
  ∀ a : ℝ, L.HidaSetting a →
    ∀ (k : ℕ) (w E : ZMod L.d → ℝ), 3 ≤ k → (∀ s, 0 < w s) →
      (∀ s, 0 ≤ E s ∧ E s ≤ 4 * w s) →
      (∀ s, s ∉ L.TT → (L.Dl s : ℝ) = ((k : ℝ) - 1) * w s + E s) →
      (∀ s, s ∈ L.TT → (L.Dl s : ℝ) = ((k : ℝ) - 1) * w s - 2 * w s + E s) →
      KvalGe L.N0 L.N1 L.l L.nu L.Th
        ((∑ s ∈ L.TT, L.baseTerm s) + lpF L.l L.d (fun s => ((k : ℝ) - 1) * w s) -
          C * (∑ s, w s) / (L.l : ℝ) - gam L.l * (∑ s ∈ L.TT, (L.Wc s : ℝ)) -
          C * ((L.d : ℝ) * L.N0 * L.N1 * (Real.logb L.l a + 1)))

end Loc

structure Loc1 where

  J : Formalism.BasicNotions.JetLoc1

  rank_lt_alt : J.N0 < J.N1

  nu : YoungDiagram
  nu_rows : nu.colLen 0 ≤ J.N0

namespace Loc1

variable (L : Loc1)

abbrev l : ℕ := L.J.l

abbrev N0 : ℕ := L.J.N0

abbrev N1 : ℕ := L.J.N1

abbrev Th : MvPowerSeries (ZMod 1 × Fin L.N0 × Fin L.N1) ℂ_[L.l] := L.J.Th

def Tht (ep0 : ℂ_[L.l]) : MvPowerSeries (ZMod 1 × Fin L.N0 × Fin L.N1) ℂ_[L.l] :=
  MvPowerSeries.subst (fun v : ZMod 1 × Fin L.N0 × Fin L.N1 =>
    MvPowerSeries.C ep0 * jetLogG L.l 1 v) L.Th

def B0 (ep0 : ℂ_[L.l]) (be : MvPowerSeries (ZMod 2) ℂ_[L.l]) : Prop :=
  ∃ ep : ℂ_[L.l], ‖ep‖ = 1 ∧ ∃ sg : ℂ_[L.l], (sg = 1 ∨ sg = -1) ∧
    ∃ U : MvPowerSeries (ZMod 1 × Fin L.N0 × Fin L.N1) ℂ_[L.l],
      (∀ m, ‖MvPowerSeries.coeff m U‖ ≤ 1) ∧
      L.Tht ep0 = U * MvPowerSeries.subst (jetLogG L.l 1 (β := Fin L.N0 × Fin L.N1))
        (expS ℂ_[L.l] ((sg / 2) • ∑ a : Fin L.N0, ∑ b : Fin L.N1,
          MvPowerSeries.subst (fun s : ZMod 2 => if s = 0 then
              (MvPowerSeries.X (0, a, b) : MvPowerSeries (ZMod 1 × Fin L.N0 × Fin L.N1) ℂ_[L.l])
            else MvPowerSeries.C ep * MvPowerSeries.X (0, a, b)) be))

def AdmB : Prop :=
  ∃ ep0 : ℂ_[L.l], ‖ep0‖ = 1 ∧ ∃ be : MvPowerSeries (ZMod 2) ℂ_[L.l],
    L.B0 ep0 be ∧ B1 L.l 2 be ∧ B2 L.l 2 be ∧ B3 L.l 2 be ∧ B4 L.l 2 be

def HidaSetting (a : ℝ) : Prop :=
  (L.l : ℝ) ≤ a ∧ (L.nu.cells.card : ℝ) ≤ a

def ThmOne (C : ℝ) : Prop :=
  ∀ a : ℝ, L.HidaSetting a →
    KvalGe L.N0 L.N1 L.l (fun _ : ZMod 1 => L.nu) L.Th
      (rho L.l * (L.nu.cells.card : ℝ) - C * ((L.N0 : ℝ) * L.N1 * (Real.logb L.l a + 1)))

end Loc1

theorem N_pred_lt (R : Formalism.BasicNotions.Ranks) (j : ℕ) (h : 1 ≤ j) : R.N (j - 1) < R.N j := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  simp only [Formalism.BasicNotions.Ranks.N, Nat.add_sub_cancel, Nat.succ_mul]
  omega

end PI.OrbJet.OJ

namespace PI.OrbJet

open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G

instance instFactRes (D : D7) (w : D.what₂.places.Pl) : Fact (D.what₂.places.resChar w).Prime :=
  ⟨D.what₂.places.resChar_prime w⟩

abbrev Pl (D : D7) : Type := Bool × HH D

structure Ent (D : D7) where

  nu : D.what₂.Word → ℕ → Pl D → YoungDiagram

  nu_row : ∀ u i, i < D.R.m → ∀ z r, (((nu u i z).rowLen r : ℕ) : ℝ) =
    if r < D.R.N i then DV.nuRow D u (i + 1) (tauPl D z) r else 0

  nu_rows : ∀ u i z, (nu u i z).colLen 0 ≤ D.R.N i

  Th : ∀ u μ (w : D.what₂.places.Pl) (i : ℕ), (D.chTw u μ).cls i → (D.chTw u μ).cls (i + 1) →
    MvPowerSeries (Pl D × Fin (D.R.N i) × Fin (D.R.N (i + 1))) ℂ_[D.what₂.places.resChar w]

  ep : ∀ w : D.what₂.places.Pl, ℂ_[D.what₂.places.resChar w]

  be : ∀ w : D.what₂.places.Pl, Pl D → MvPowerSeries (ZMod (nP D (D.what₂.places.resChar w))) ℂ_[D.what₂.places.resChar w]

  sg : ∀ w : D.what₂.places.Pl, Pl D → ℂ_[D.what₂.places.resChar w]

variable {D : D7}

def Ent.size (E : Ent D) (u : D.what₂.Word) (i : ℕ) (z : Pl D) : ℝ := ((E.nu u i z).cells.card : ℝ)

def Ent.row (E : Ent D) (u : D.what₂.Word) (i : ℕ) (z : Pl D) (r : ℕ) : ℝ := ((E.nu u i z).rowLen r : ℝ)

def Ent.cap (E : Ent D) (u : D.what₂.Word) (i : ℕ) (z : Pl D) : ℝ := if IsTopPl D z then E.row u i z 1 else E.row u i z 0

def orbMap (D : D7) (p : ℕ) (z : Pl D) (s : ZMod (nP D p)) : Pl D := posPl D p z s.val

def backPl (D : D7) (p : ℕ) (z : Pl D) (e : ℕ) : Pl D := posPl D p z (e * (nP D p - 1))

def IsReps (D : D7) (p : ℕ) (R : Finset (Pl D)) : Prop := ∀ z, ∃! r, r ∈ R ∧ ∃ e : ℕ, posPl D p r e = z

structure OrbOK (D : D7) (p : ℕ) : Prop where
  five : 5 ≤ p
  even : Even (nP D p)
  two : 2 ≤ nP D p

def logPl (D : D7) (p : ℕ) [Fact p.Prime] {β : Type} (v : Pl D × β) : MvPowerSeries (Pl D × β) ℂ_[p] :=
  fun m => ∑ e ∈ Finset.range (JetTdeg m + 1),
    if m = Finsupp.single (backPl D p v.1 (2 * e), v.2) ((p ^ 2) ^ e) then (((p : ℂ_[p]) ^ e)⁻¹) else 0

def restr (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (z : Pl D) (Th : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p]) :
    MvPowerSeries (ZMod (nP D p) × Fin N0 × Fin N1) ℂ_[p] :=
  fun m => MvPowerSeries.coeff (m.mapDomain fun v => (orbMap D p z v.1, v.2)) Th

def restr1 (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (z : Pl D) (Th : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p]) :
    MvPowerSeries (ZMod 1 × Fin N0 × Fin N1) ℂ_[p] :=
  fun m => MvPowerSeries.coeff (m.mapDomain fun v => (z, v.2)) Th

def orbLoc (E : Ent D) (p : ℕ) [Fact p.Prime] (h : OrbOK D p) (u : D.what₂.Word) (i : ℕ) (z : Pl D)
    (Th : MvPowerSeries (ZMod (nP D p) × Fin (D.R.N i) × Fin (D.R.N (i + 1))) ℂ_[p]) : OJ.Loc where
  J := { l := p, five_le_l := h.five, d := nP D p, d_even := h.even, two_le_d := h.two, N0 := D.R.N i, N1 := D.R.N (i + 1),
         Th := Th }
  rank_lt_alt := OJ.N_pred_lt D.R (i + 1) (Nat.le_add_left 1 i)
  nu := fun s => E.nu u i (orbMap D p z s)
  nu_rows := fun s => E.nu_rows u i (orbMap D p z s)
  TT := Finset.univ.filter fun s : ZMod (nP D p) => IsTopPl D (orbMap D p z s)

def oneLoc (E : Ent D) (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p) (u : D.what₂.Word) (i : ℕ) (z : Pl D)
    (Th : MvPowerSeries (ZMod 1 × Fin (D.R.N i) × Fin (D.R.N (i + 1))) ℂ_[p]) : OJ.Loc1 where
  J := { l := p, five_le_l := h5, N0 := D.R.N i, N1 := D.R.N (i + 1), Th := Th }
  rank_lt_alt := OJ.N_pred_lt D.R (i + 1) (Nat.le_add_left 1 i)
  nu := E.nu u i z
  nu_rows := E.nu_rows u i z

def OrbitThetaExpansion (Lc : OJ.Loc) (ep sg : ℂ_[Lc.l]) (be : MvPowerSeries (ZMod Lc.d) ℂ_[Lc.l]) : Prop :=
  ∃ U : MvPowerSeries (ZMod Lc.d × Fin Lc.N0 × Fin Lc.N1) ℂ_[Lc.l], (∀ m, ‖MvPowerSeries.coeff m U‖ ≤ 1) ∧
    Lc.Tht ep = U * MvPowerSeries.subst (jetLogG Lc.l Lc.d (β := Fin Lc.N0 × Fin Lc.N1))
      (OJ.expS ℂ_[Lc.l] (sg • Lc.beSum be))

def OrbGe (E : Ent D) (p : ℕ) [Fact p.Prime] (h : OrbOK D p) (u : D.what₂.Word) (i : ℕ) (z : Pl D) (ep sg : ℂ_[p])
    (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]) (β : ℝ) : Prop :=
  ∀ Th, OrbitThetaExpansion (orbLoc E p h u i z Th) ep sg be →
    OJ.KvalGe (D.R.N i) (D.R.N (i + 1)) p (fun s => E.nu u i (orbMap D p z s)) Th β

def OneGe (E : Ent D) (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p) (u : D.what₂.Word) (i : ℕ) (z : Pl D) (β : ℝ) : Prop :=
  ∀ Th, (oneLoc E p h5 u i z Th).AdmB →
    OJ.KvalGe (D.R.N i) (D.R.N (i + 1)) p (fun _ : ZMod 1 => E.nu u i z) Th β

def beAll (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (R : Finset (Pl D)) (sg : Pl D → ℂ_[p])
    (be : Pl D → MvPowerSeries (ZMod (nP D p)) ℂ_[p]) : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p] :=
  ∑ r ∈ R, sg r • ∑ a : Fin N0, ∑ b : Fin N1,
    MvPowerSeries.subst (fun s : ZMod (nP D p) =>
      (MvPowerSeries.X (orbMap D p r s, a, b) : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p])) (be r)

def BeOK (D : D7) (p : ℕ) [Fact p.Prime] (R : Finset (Pl D)) (ep : ℂ_[p]) (sg : Pl D → ℂ_[p])
    (be : Pl D → MvPowerSeries (ZMod (nP D p)) ℂ_[p]) : Prop :=
  ‖ep‖ = 1 ∧ (∀ r ∈ R, sg r = 1 ∨ sg r = -1) ∧
    ∀ r ∈ R, OJ.B1 p (nP D p) (be r) ∧ OJ.B2 p (nP D p) (be r) ∧ OJ.B3 p (nP D p) (be r) ∧ OJ.B4 p (nP D p) (be r)

def ThetaExpansionAllPlaces (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (R : Finset (Pl D)) (ep : ℂ_[p]) (sg : Pl D → ℂ_[p])
    (be : Pl D → MvPowerSeries (ZMod (nP D p)) ℂ_[p]) (Th : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p]) : Prop :=
  ∃ U : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p], (∀ m, ‖MvPowerSeries.coeff m U‖ ≤ 1) ∧
    MvPowerSeries.subst (fun v : Pl D × Fin N0 × Fin N1 => MvPowerSeries.C ep * logPl D p v) Th =
      U * MvPowerSeries.subst (logPl D p (β := Fin N0 × Fin N1)) (OJ.expS ℂ_[p] (beAll D p R sg be))

def ThetaExpansionRealPlaces (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (Th : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p]) : Prop :=
  ∃ ep0 : ℂ_[p], ‖ep0‖ = 1 ∧ ∃ be : Pl D → MvPowerSeries (ZMod 2) ℂ_[p],
    (∀ z, OJ.B1 p 2 (be z) ∧ OJ.B2 p 2 (be z) ∧ OJ.B3 p 2 (be z) ∧ OJ.B4 p 2 (be z)) ∧
    ∃ ep : Pl D → ℂ_[p], (∀ z, ‖ep z‖ = 1) ∧ ∃ sg : Pl D → ℂ_[p], (∀ z, sg z = 1 ∨ sg z = -1) ∧
    ∃ U : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p], (∀ m, ‖MvPowerSeries.coeff m U‖ ≤ 1) ∧
      MvPowerSeries.subst (fun v : Pl D × Fin N0 × Fin N1 => MvPowerSeries.C ep0 * logPl D p v) Th =
        U * MvPowerSeries.subst (logPl D p (β := Fin N0 × Fin N1))
          (OJ.expS ℂ_[p] (∑ z : Pl D, (sg z / 2) • ∑ a : Fin N0, ∑ b : Fin N1,
            MvPowerSeries.subst (fun s : ZMod 2 => if s = 0 then
                (MvPowerSeries.X (z, a, b) : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p])
              else MvPowerSeries.C (ep z) * MvPowerSeries.X (z, a, b)) (be z)))

end PI.OrbJet

end
