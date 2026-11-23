import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise

namespace GlobalTheory.ChiGrid

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

open GlobalTheory.SignedHC Formalism.L2.Host Formalism.L2.DIV

structure Consts where

  cGap : ℝ

  cDep : ℝ

  b : ℝ

instance : Inhabited Consts := ⟨⟨1, 1800, Real.exp 1⟩⟩

variable {T : Type}

theorem isCartanInv_neg {V : HSp D} {τ : D.what₂.Tau} {s : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (h : IsCartanInv (gramAt D V τ) s) : IsCartanInv (gramAt D (negSp V) τ) (-s) := by
  have e : gramAt D (negSp V) τ = -gramAt D V τ := Matrix.ext fun i j => map_neg (tauE D τ) _
  rw [e]
  refine ⟨by rw [neg_mul_neg, h.1], ?_, by rw [neg_mul_neg]; exact h.2.2⟩
  rw [conjTranspose_neg, neg_mul_neg, mul_neg, h.2.1]

open Classical in

structure Places (L : LevCh D T) where

  v0 : Pl D.host.F

  basePlace_over_qZero : ((q0 D : ℕ) : 𝓞 D.host.F) ∈ v0.asIdeal

  w : Pl D.host.F → Pl D.host.E

  w_over : ∀ v ∈ insert v0 (S1 D), (w v).under (𝓞 D.host.F) = v

  w_split : ∀ v ∈ insert v0 (S1 D), ∃ e : AE D, Formalism.L2.NTheta.IsIdemAt e (w v)

  w_g : ∀ v : Pl D.host.F, ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal → w v ∈ L.Pg

  w_de : ∀ p ∈ ({D.host.pde, D.host.pde'} : Set ℕ), ∃ 𝔭 : HeightOneSpectrum (𝓞 D.host.K),
    ∀ v : Pl D.host.F, ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal → (w v).under (𝓞 D.host.K) = 𝔭

  w_Q : ∀ t, ∀ PP ∈ L.Q t, PP.under (𝓞 D.host.F) ∈ S1 D → PP = w (PP.under (𝓞 D.host.F))

  levelPlace_ne_basePlace : ∀ t, ∀ PP ∈ L.Q t, PP.under (𝓞 D.host.F) ≠ v0

namespace Places

variable {L : LevCh D T} (P : Places L)

open Classical in

def S0 : Finset (Pl D.host.F) := insert P.v0 (S1 D)

open Classical in

def W0 : Finset (Pl D.host.E) := P.S0.image P.w

open Classical in

def depth (sc : Consts) (v : Pl D.host.F) : ℕ := if v = P.v0 then depth0 D sc.cDep sc.b else 2

def modul (sc : Consts) : Ideal (𝓞 D.host.E) := ∏ v ∈ P.S0, (P.w v).asIdeal ^ P.depth sc v

def modulBar (sc : Consts) : Ideal (𝓞 D.host.E) := D.host.conj • P.modul sc

def stA (sc : Consts) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E :=
  D.host.AA * ((P.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹

def stAbar (sc : Consts) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E :=
  D.host.AAbar * ((P.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹

def sigma0 (sc : Consts) : ℝ := ∑ v ∈ P.S0, (P.depth sc v : ℝ) * Real.log (Ideal.absNorm v.asIdeal)

theorem mem_S0_of_sum_eq {v : Pl D.host.F} : v ∈ P.S0 ↔ v = P.v0 ∨ v ∈ S1 D := by simp [S0]

theorem under_w {v : Pl D.host.F} (h : v ∈ P.S0) : (P.w v).under (𝓞 D.host.F) = v := P.w_over v h

theorem card_chosenPlaces_eq : P.W0.card = P.S0.card := by
  classical
  unfold W0
  convert Finset.card_image_of_injOn fun v hv v' hv' h =>
    (P.under_w hv).symm.trans ((congrArg _ h).trans (P.under_w hv'))

theorem depth_pos (sc : Consts) (v : Pl D.host.F) : 0 < P.depth sc v := by
  unfold depth depth0; split_ifs <;> omega

theorem modul_ne_bot (sc : Consts) : P.modul sc ≠ ⊥ :=
  Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (P.w v).ne_bot

theorem stairId_st (sc : Consts) (c : ℕ) (p : Fin c) : stairId (P.stA sc) (P.stAbar sc) c p =
    stairId D.host.AA D.host.AAbar c p *
      ((P.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ (p.1 + 1) *
      (((P.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ (c - p.1))⁻¹ := by
  simp only [stairId, stA, stAbar, mul_pow, inv_pow, mul_inv, inv_inv]
  ring

end Places

structure Chars {L : LevCh D T} (P : Places L) (C : ℝ) where

  chiH : ℕ → HChar D.host.E

  chi : ℕ → ((AE D)ˣ →* Circle)

  chi_eq : ∀ i, 1 ≤ i → i ≤ D.R.m → ChrEq (chi i) (chiH i)

  triv : ∀ i, 1 ≤ i → i ≤ D.R.m → (chiH i).TrivOn D.host.F

  inf : ∀ i, 1 ≤ i → i ≤ D.R.m → (chiH i).HasInf (embTau D) fun τ => 2 * cen D C τ i

  unr : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ PP : Pl D.host.E, PP.under (𝓞 D.host.F) ∉ P.S0 → (chiH i).UnrAt PP

  lev1 : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ PP : Pl D.host.E, PP.under (𝓞 D.host.F) ∈ S1 D →
    (chiH i).LevelLe PP 2 ∧ ¬ (chiH i).LevelLe PP 1

  wild : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ PP : Pl D.host.E,
    ((D.host.pde : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal ∨ ((D.host.pde' : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal →
    ∀ x : (PP.adicCompletion D.host.E)ˣ, x ^ (Nat.card (kP PP) - 1) = 1 → (chiH i).loc PP x = 1

  lev0 : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ PP : Pl D.host.E, PP.under (𝓞 D.host.F) = P.v0 →
    (chiH i).LevelLe PP 1 ∧ ¬ (chiH i).UnrAt PP

theorem Chars.basePlace_not_mem_chiGridBadPlaces {L : LevCh D T} {P : Places L} {C : ℝ} (X : Chars P C) : P.v0 ∉ S1 D := fun h => by
  have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  have e := P.under_w (P.mem_S0_of_sum_eq.2 (Or.inl rfl))
  exact (X.lev1 1 le_rfl hm _ (by rw [e]; exact h)).2 (X.lev0 1 le_rfl hm _ e).1

def columnBlock (L : LevCh D T) : ℕ → LSp D
  | 0 => ⟨Yc D 0, L.ΛY 0⟩
  | j + 1 => if j + 1 < D.R.m then ⟨Yc D (j + 1), L.ΛY (j + 1)⟩ else ⟨D.sp.X', L.ΛX⟩

theorem colY_lt (L : LevCh D T) {j : ℕ} (h : j < D.R.m) : columnBlock L j = ⟨Yc D j, L.ΛY j⟩ := by
  cases j with
  | zero => rfl
  | succ j => exact if_pos h

theorem colY_m (L : LevCh D T) : columnBlock L D.R.m = ⟨D.sp.X', L.ΛX⟩ := by
  obtain ⟨j, hj⟩ : ∃ j, D.R.m = j + 1 := ⟨D.R.m - 1, by have := D.R.two_le_m; omega⟩
  have : columnBlock L (j + 1) = ⟨D.sp.X', L.ΛX⟩ := if_neg (by omega)
  rw [← this, ← hj]

def vtxOf (L : LevCh D T) (W : ℕ → ℕ → LSp D) : ℕ → ℕ → LSp D
  | 0, j => columnBlock L j
  | i + 1, j => W (i + 1) j

def xOf (X₀ : LSp D) (W : ℕ → LSp D) : ℕ → LSp D
  | 0 => X₀
  | j + 1 => W (j + 1)

structure Vertices (L : LevCh D T) (𝔞 𝔞' : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) where

  Vs : ℕ → ℕ → LSp D

  P : ℕ → LSp D

  Xs : ℕ → LSp D

  V_is : ∀ i j, 1 ≤ i → i ≤ D.R.m → j ≤ D.R.m → (Vs i j).IsV (rankV D i j) ((D.R.m - j) / 2)

  P_is : ∀ i, i ≤ D.R.m → (P i).IsV (rankP D i) ((D.R.m - i + 1) / 2)

  X_is : ∀ j, 1 ≤ j → j ≤ D.R.m → (Xs j).IsV (rankX D j) 0

  dec0 : HermitianOrthogonalExtensionData (Yc D 0) (P 0).sp 1 1

  lat0 : (P 0).lat = dec0.lat (L.ΛY 0) fun _ => 1

  colDec : ∀ i, 1 ≤ i → i ≤ D.R.m → HermitianOrthogonalExtensionData (P i).sp (vtxOf L Vs i 0).sp (i - 1) (-1)

  colLat : ∀ i h h', (vtxOf L Vs i 0).lat = (colDec i h h').lat (P i).lat (stairId 𝔞 𝔞' (i - 1))

  rowDecS : ∀ j, j + 1 < D.R.m → HermitianOrthogonalExtensionData (Xs (j + 1)).sp (vtxOf L Vs D.R.m (j + 1)).sp (D.R.m - 1 - (j + 1)) (-1)

  rowLat : ∀ j h, (vtxOf L Vs D.R.m (j + 1)).lat =
    (rowDecS j h).lat (Xs (j + 1)).lat (stairId D.host.AA D.host.AAbar (D.R.m - 1 - (j + 1)))

  topDec : HermitianOrthogonalExtensionData (vtxOf L Vs D.R.m D.R.m).sp (xOf (P D.R.m) Xs D.R.m).sp 1 1

  topLat : (xOf (P D.R.m) Xs D.R.m).lat = topDec.lat (vtxOf L Vs D.R.m D.R.m).lat fun _ => 1

inductive Node

  | grid (i j : ℕ)

  | core (i : ℕ)

  | top (j : ℕ)
  deriving DecidableEq

def Node.InRange (m : ℕ) : Node → Prop
  | .grid i j => i ≤ m ∧ j ≤ m
  | .core i => i ≤ m
  | .top j => j ≤ m

variable (D) in

def Node.rank : Node → ℕ
  | .grid i j => rankV D i j
  | .core i => rankP D i
  | .top j => rankX D j

def Node.neg (m : ℕ) : Node → ℕ
  | .grid _ j => (m - j) / 2
  | .core i => (m - i + 1) / 2
  | .top _ => 0

variable (D) in

def Node.par0 (C : ℝ) : Node → D.what₂.Tau → SPar
  | .grid i j, τ => (num D C τ).parD i j
  | .core i, τ => (num D C τ).parPi i
  | .top j, τ => (num D C τ).parX j

variable (D) in

def Node.par (C : ℝ) : Node → D.what₂.Tau → SPar
  | .grid i j, τ => parV D C i j τ
  | .core i, τ => (num D C τ).parPi i
  | .top j, τ => (num D C τ).parX j

inductive Pair (T : Type)

  | chi (i j : ℕ)

  | mu (t : T) (i j : ℕ)

  | core (i : ℕ)

  | top (t : T) (j : ℕ)

namespace Pair

@[reducible] def small : Pair T → Node
  | .chi i j => .grid i j
  | .mu _ i j => .grid i j
  | .core i => .core i
  | .top _ j => .top j

@[reducible] def big : Pair T → Node
  | .chi i j => .grid (i + 1) j
  | .mu _ i j => .grid i (j + 1)
  | .core i => .core (i + 1)
  | .top _ j => .top (j + 1)

def InRange (m : ℕ) (p : Pair T) : Prop := p.big.InRange m

variable (D) in

def len : Pair T → ℕ
  | .chi _ _ => sLen D
  | .mu _ _ _ => D.R.t
  | .core _ => sLen D - 1
  | .top _ _ => D.R.t + 1

variable (D) in

def centre (C : ℝ) : Pair T → D.what₂.Tau → ℚ
  | .chi i _, τ => (num D C τ).cen (D.R.m - i)
  | .mu _ _ j, τ => -((num D C τ).e (j + 1) : ℚ)
  | .core i, τ => (num D C τ).cen (D.R.m - i)
  | .top _ j, τ => -((num D C τ).e (j + 1) : ℚ)

def ori : Pair T → Orientation
  | .chi _ _ => .neg
  | .mu _ _ _ => .pos
  | .core _ => .neg
  | .top _ _ => .pos

theorem InRange.small {m : ℕ} {p : Pair T} (h : p.InRange m) : p.small.InRange m := by
  cases p <;> simp only [InRange, Node.InRange] at h ⊢ <;> omega

theorem rank_big (p : Pair T) : p.big.rank D = p.small.rank D + p.len D := by
  cases p <;> simp only [Node.rank, len, rankV, rankP, rankX] <;> ring

end Pair

inductive Arrow (T : Type)

  | right (i j : ℕ)

  | down (t : T) (i j : ℕ)

  | coreUp (i : ℕ)

  | coreDown (i : ℕ)

  | col (t : T) (j : ℕ)

namespace Arrow

@[reducible] def pair : Arrow T → Pair T
  | .right i j => .chi i j
  | .down t i j => .mu t i j
  | .coreUp i => .core i
  | .coreDown i => .core i
  | .col t j => .top t j

@[reducible] def src : Arrow T → Node
  | .right i j => .grid i j
  | .down _ i j => .grid i (j + 1)
  | .coreUp i => .core i
  | .coreDown i => .core (i + 1)
  | .col _ j => .top j

@[reducible] def tgt : Arrow T → Node
  | .right i j => .grid (i + 1) j
  | .down _ i j => .grid i j
  | .coreUp i => .core (i + 1)
  | .coreDown i => .core i
  | .col _ j => .top (j + 1)

theorem src_tgt (a : Arrow T) : (a.src = a.pair.small ∧ a.tgt = a.pair.big) ∨ (a.src = a.pair.big ∧ a.tgt = a.pair.small) := by
  cases a <;> simp

end Arrow

structure GridData (L : LevCh D T) (sc : Consts) where

  pl : Places L

  ch : Chars pl sc.cGap

  sp : Vertices L (pl.stA sc) (pl.stAbar sc)

namespace GridData

variable {L : LevCh D T} {sc : Consts} (G : GridData L sc)

@[reducible] def node : Node → LSp D
  | .grid i j => vtxOf L G.sp.Vs i j
  | .core i => G.sp.P i
  | .top j => xOf (G.sp.P D.R.m) G.sp.Xs j

abbrev V (X : Node) : HSp D := (G.node X).sp

abbrev Λ (X : Node) : Submodule (𝓞 D.host.E) (Fin (G.V X).rank → D.host.E) := (G.node X).lat

abbrev modul : Ideal (𝓞 D.host.E) := G.pl.modul sc

theorem node_zero_zero : G.node (.grid 0 0) = ⟨Yc D 0, L.ΛY 0⟩ := rfl

theorem node_top_zero : G.node (.top 0) = G.node (.core D.R.m) := rfl

theorem isV {X : Node} (h : X.InRange D.R.m) (h0 : ∀ j, X ≠ .grid 0 j) : (G.node X).IsV (X.rank D) (X.neg D.R.m) := by
  rcases X with ⟨_ | i, j⟩ | i | _ | j
  · exact absurd rfl (h0 j)
  · exact G.sp.V_is (i + 1) j (by omega) h.1 h.2
  · exact G.sp.P_is i h
  · have := G.sp.P_is D.R.m le_rfl
    rw [Nat.sub_self] at this
    show (G.sp.P D.R.m).IsV (rankP D D.R.m + 0 * (D.R.t + 1)) 0
    rwa [zero_mul, add_zero]
  · exact G.sp.X_is (j + 1) (by omega) h

abbrev colDec (i : ℕ) (h : 1 ≤ i) (h' : i ≤ D.R.m) : HermitianOrthogonalExtensionData (G.V (.core i)) (G.V (.grid i 0)) (i - 1) (-1) :=
  G.sp.colDec i h h'

def rowDec : ∀ j, j < D.R.m → HermitianOrthogonalExtensionData (G.V (.top j)) (G.V (.grid D.R.m j)) (D.R.m - 1 - j) (-1)
  | 0, h => G.sp.colDec D.R.m h le_rfl
  | j + 1, h => G.sp.rowDecS j h

def besTop : BesDat (G.V (.top 0)) (G.V (.grid D.R.m 0)) (G.rowDec 0 (by have := D.R.two_le_m; omega)).ι :=
  (G.rowDec 0 (by have := D.R.two_le_m; omega)).besDat (neg_ne_zero.2 one_ne_zero) ((D.R.m - 2) / 2)
    (by have := D.R.two_le_m; obtain ⟨a, ha⟩ := D.R.m_even; omega)

def IsListed (θ : InfFam D) : ∀ X : Node, (GA D (G.V X) → ℂ) → Prop
  | .grid i j, φ => ∀ τ, IsTypeAt θ _ τ (Node.par D sc.cGap (.grid i j) τ) fun g => star (φ g)
  | .core i, φ => ∀ τ, IsTypeAt θ _ τ (Node.par D sc.cGap (.core i) τ) φ
  | .top j, φ => ∀ τ, IsTypeAt θ _ τ (Node.par D sc.cGap (.top j) τ) φ

def levMax (X : Node) : Subgroup (GL (Fin (G.V X).rank) (Formalism.IndefR.Lev.EAf D)) :=
  congLev D.sp.cm (G.V X).gram (G.Λ X) ⊤

def levCong (X : Node) : Subgroup (GL (Fin (G.V X).rank) (Formalism.IndefR.Lev.EAf D)) :=
  congLev D.sp.cm (G.V X).gram (G.Λ X) G.modul

abbrev Kplus : Subgroup (GL (Fin (G.V (.top 0)).rank) (Formalism.IndefR.Lev.EAf D)) := G.levCong (.top 0)

abbrev ClPlus : Type := Cl D.sp.cm (G.V (.top 0)).gram G.Kplus

theorem levCong_le (X : Node) : G.levCong X ≤ G.levMax X := congLev_mono le_top

@[reducible] def pS : Pair T → HSp D
  | .chi i j => negSp (G.V (.grid (i + 1) j))
  | .mu _ i j => G.V (.grid i j)
  | .core i => negSp (G.V (.core (i + 1)))
  | .top _ j => G.V (.top j)

@[reducible] def pT : Pair T → HSp D
  | .chi i j => G.V (.grid i j)
  | .mu _ i j => G.V (.grid i (j + 1))
  | .core i => G.V (.core i)
  | .top _ j => G.V (.top (j + 1))

@[reducible] def latS : ∀ p : Pair T, Submodule (𝓞 D.host.E) (Fin (G.pS p).rank → D.host.E)
  | .chi i j => G.Λ (.grid (i + 1) j)
  | .mu _ i j => G.Λ (.grid i j)
  | .core i => G.Λ (.core (i + 1))
  | .top _ j => G.Λ (.top j)

@[reducible] def latT : ∀ p : Pair T, Submodule (𝓞 D.host.E) (Fin (G.pT p).rank → D.host.E)
  | .chi i j => G.Λ (.grid i j)
  | .mu _ i j => G.Λ (.grid i (j + 1))
  | .core i => G.Λ (.core i)
  | .top _ j => G.Λ (.top (j + 1))

def toPair : ∀ p : Pair T, GA D (G.V p.small) → GA D (G.V p.big) → GA D (G.pS p) × GA D (G.pT p)
  | .chi _ _, g, h => (negGA _ h, g)
  | .mu _ _ _, g, h => (g, h)
  | .core _, g, h => (negGA _ h, g)
  | .top _ _, g, h => (g, h)

def chr : Pair T → ((AE D)ˣ →* Circle)
  | .chi i _ => G.ch.chi (D.R.m - i)
  | .mu t _ j => L.mu t (j + 1)
  | .core i => G.ch.chi (D.R.m - i)
  | .top t j => L.mu t (j + 1)

def chrS (p : Pair T) : (AE D)ˣ →* Circle := Formalism.IndefR.Lift.attChr (G.chr p) L.eta (G.pS p).rank

def chrT (p : Pair T) : (AE D)ˣ →* Circle := Formalism.IndefR.Lift.attChr (G.chr p) L.eta (G.pT p).rank

def nu (t : T) (i j : ℕ) : (AE D)ˣ →* Circle := L.mu t j / G.ch.chi (D.R.m - i)

theorem chr_core {i : ℕ} (h : i + 1 ≤ D.R.m) :
    G.chrS (.core i) = G.ch.chi (D.R.m - i) ∧ G.chrT (.core i) = G.ch.chi (D.R.m - i) := by
  have h1 : (G.pS (.core i)).rank = rankP D (i + 1) := (G.sp.P_is _ h).rank
  have h2 : (G.pT (.core i)).rank = rankP D i := (G.sp.P_is _ (by omega)).rank
  rw [chrS, chrT, h1, h2]
  simp [Formalism.IndefR.Lift.attChr, chr, Nat.not_odd_iff_even.2 (even_rankP D _)]

theorem chr_mu_zero (t : T) {j : ℕ} (h : j + 1 ≤ D.R.m) :
    (G.chrS (.mu t 0 j), G.chrT (.mu t 0 j)) = Formalism.IndefR.Lift.chrStep (L.mu t) L.eta (j + 1) := by
  have key : ∀ k, k ≤ D.R.m → (columnBlock L k).sp.rank = D.R.r + k * D.R.t := fun k hk => by
    rcases hk.eq_or_lt with rfl | hk
    · rw [colY_m]; exact D.sp.X'_rank
    · rw [colY_lt L hk]
      exact (D.sp.Y_rank _ (min_le_right _ _)).trans (by rw [min_eq_left hk.le]; rfl)
  rw [Formalism.IndefR.Lift.chrStep_eq_att _ _ (odd_r D) D.R.t_odd (by omega), Nat.add_sub_cancel, ← key j (by omega),
    ← key (j + 1) h]
  rfl

abbrev CosAt (i : ℕ) : Type := Cos (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0)) G.modul

abbrev Datum : Type := ∀ i : Fin D.R.m, G.CosAt i

theorem finite_datum (h : (L.ΛY 0).FG) : Finite G.Datum := by
  have : ∀ i : Fin D.R.m, Finite (G.CosAt i) := fun ⟨i, hi⟩ => by
    refine finite_cos (G.sp.V_is (i + 1) 0 (by omega) hi (by omega)).sd.1 ?_ (G.pl.modul_ne_bot sc)
    cases i with
    | zero => exact h
    | succ i => exact (G.sp.V_is (i + 1) 0 (by omega) (by omega) (by omega)).sd.1.fg
  infer_instance

abbrev RealVec : Type := ∀ i : Fin D.R.m, PolF D (G.V (.grid i 0)).rank (G.V (.grid (i + 1) 0)).rank

@[reducible] def cartS (s : ∀ X : Node, D.what₂.Tau → Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ) :
    ∀ p : Pair T, D.what₂.Tau → Matrix (Fin (G.pS p).rank) (Fin (G.pS p).rank) ℂ
  | .chi i j => fun τ => -s (.grid (i + 1) j) τ
  | .mu _ i j => s (.grid i j)
  | .core i => fun τ => -s (.core (i + 1)) τ
  | .top _ j => s (.top j)

@[reducible] def onS (s : ∀ X : Node, D.what₂.Tau → Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ) :
    ∀ p : Pair T, D.what₂.Tau → Matrix (Fin (G.pS p).rank) (Fin (G.pS p).rank) ℂ
  | .chi i j => s (.grid (i + 1) j)
  | .mu _ i j => s (.grid i j)
  | .core i => s (.core (i + 1))
  | .top _ j => s (.top j)

@[reducible] def onT (s : ∀ X : Node, D.what₂.Tau → Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ) :
    ∀ p : Pair T, D.what₂.Tau → Matrix (Fin (G.pT p).rank) (Fin (G.pT p).rank) ℂ
  | .chi i j => s (.grid i j)
  | .mu _ i j => s (.grid i (j + 1))
  | .core i => s (.core i)
  | .top _ j => s (.top (j + 1))

structure Weil where

  ψ : AddChar (AF D.host.F) ℂ

  ψ_std : IsStdChar D ψ (-1)

  θ : InfFam D

  θ_is : IsInfFam θ

  cart : ∀ X : Node, D.what₂.Tau → Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ

  cart_is : ∀ X : Node, X.InRange D.R.m → ∀ τ, IsCartanInv (gramAt D (G.V X) τ) (cart X τ)

  onb : ∀ X : Node, D.what₂.Tau → Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ

  onb_is : ∀ X : Node, X.InRange D.R.m → ∀ τ, ∃ ε : Fin (G.V X).rank → Bool,
    (onb X τ)ᴴ * gramAt D (G.V X) τ * onb X τ = Formalism.REAL.Jm ε ∧ cart X τ * onb X τ = onb X τ * Formalism.REAL.Jm ε

  om : ∀ p : Pair T, GA D (G.pS p) × GA D (G.pT p) →* Module.End ℂ (WO (G.pS p) (G.pT p) → ℂ)

  om_is : ∀ p : Pair T, p.InRange D.R.m → IsWeilDatumO ψ (G.pS p) (G.pT p) (G.chrS p) (G.chrT p) (om p)

  vac : ∀ i, WO (G.pS (.chi i 0)) (G.pT (.chi i 0)) → ℂ

  vac_is : ∀ i, i < D.R.m → IsVacO ψ θ _ _ (G.cartS cart (.chi i 0)) (G.onT cart (.chi i 0))
    (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _) (vac i)

  cosVec : ∀ i, G.CosAt i → WO (G.pS (.chi i 0)) (G.pT (.chi i 0)) → ℂ

  cosVec_is : ∃ e : AE D, IsIdemSum e G.pl.W0 ∧ ∀ i, i < D.R.m → ∀ κ : G.CosAt i,
    IsThetaAt ψ (symplO _ _) (heisO ψ _ _) e
      (latO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _) fun _ => True) 1
      (vac i) (cosInd e κ) (cosVec i κ)

namespace Weil

variable {G} (W : G.Weil)

def ker (p : Pair T) (f : WO (G.pS p) (G.pT p) → ℂ) (g : GA D (G.V p.small)) (h : GA D (G.V p.big)) : ℂ :=
  thetaKO (W.om p) (G.toPair p g h).1 (G.toPair p g h).2 f

def kerA : ∀ a : Arrow T, (WO (G.pS a.pair) (G.pT a.pair) → ℂ) → GA D (G.V a.src) → GA D (G.V a.tgt) → ℂ
  | .right i j, f, g, h => W.ker (.chi i j) f g h
  | .down t i j, f, g, h => W.ker (.mu t i j) f h g
  | .coreUp i, f, g, h => star (W.ker (.core i) f g h)
  | .coreDown i, f, g, h => W.ker (.core i) f h g
  | .col t j, f, g, h => W.ker (.top t j) f g h

theorem kerA_coreUp (i : ℕ) (f : WO (G.pS (.core i)) (G.pT (.core i)) → ℂ) (g : GA D (G.V (.core i)))
    (h : GA D (G.V (.core (i + 1)))) : W.kerA (.coreUp i) f g h = star (W.kerA (.coreDown i) f h g) := rfl

def IsVac (p : Pair T) (f : WO (G.pS p) (G.pT p) → ℂ) : Prop :=
  IsVacO W.ψ W.θ _ _ (G.cartS W.cart p) (G.onT W.cart p) (G.latS p : Set _) (G.latT p : Set _) f

def fock (p : Pair T) (f : WO (G.pS p) (G.pT p) → ℂ) :
    PolF D (G.pT p).rank (G.pS p).rank →ₗ[ℂ] (WO (G.pS p) (G.pT p) → ℂ) :=
  pureTensorO W.ψ W.θ _ _ (G.cartS W.cart p) (G.onT W.cart p) (G.onS W.onb p) (G.onT W.onb p) f

def datum (ρ : G.RealVec) (Φ : G.Datum) (i : Fin D.R.m) : WO (G.pS (.chi i 0)) (G.pT (.chi i 0)) → ℂ :=
  W.fock (.chi i 0) (W.cosVec i (Φ i)) (ρ i)

end Weil

end GridData

structure GridData.Weil.Over {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) {sc : Consts}
    {G : GridData R.toLevCh sc} (W : G.Weil) : Prop where

  ψ : W.ψ = R.ψ

  θ : W.θ = R.θ

  cartY : ∀ j, j < D.R.m → HEq (W.cart (.grid 0 j)) (Formalism.IndefR.Links.cart (R.MY j))

  cartX : HEq (W.cart (.grid 0 D.R.m)) (Formalism.IndefR.Links.cart R.MX)

  onbY : ∀ j, j < D.R.m → HEq (W.onb (.grid 0 j)) (Formalism.IndefR.Links.onb (R.MY j))

  onbX : HEq (W.onb (.grid 0 D.R.m)) (Formalism.IndefR.Links.onb R.MX)

  omY : ∀ t k, k + 1 < D.R.m → HEq (W.om (.mu t 0 k)) (R.ωY t k)

  omX : ∀ t k, k + 1 = D.R.m → HEq (W.om (.mu t 0 k)) (R.ωX t)

example : ((List.range 5).map fun i => (Node.core i).neg 4) = [2, 2, 1, 1, 0] ∧
    ((List.range 5).map fun j => (Node.grid 3 j).neg 4) = [2, 1, 1, 0, 0] := by decide

example (t : T) (i j : ℕ) : (Arrow.down t i j).src = (Arrow.right i (j + 1) : Arrow T).src ∧
    (Arrow.right i j : Arrow T).tgt = (Arrow.down t (i + 1) j).tgt ∧
    (Arrow.down t i j).tgt = (Arrow.right i j : Arrow T).src ∧
    (Arrow.right i (j + 1) : Arrow T).tgt = (Arrow.down t (i + 1) j).src := ⟨rfl, rfl, rfl, rfl⟩

end GlobalTheory.ChiGrid

end
