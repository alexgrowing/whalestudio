import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Grid

open GlobalTheory.SignedHC

variable {D : D7}

section Numbers

variable (D)

def sLen : ℕ := D.R.r + 6

abbrev gridOf (γ : ℕ) (c : ℕ → ℤ) (τ : D.what₂.Tau) : GridData := GridData.ofHCParam (D.hc τ) (sLen D) γ c

def bigN : ℕ := D.R.k + D.R.m * (D.R.t + sLen D + 1)

def GapCond (γ : ℕ) : Prop :=
  (∀ τ : D.what₂.Tau, (bigN D : ℝ) ^ 3 + ((D.R.r : ℝ) + 1) ^ 7 + ((D.R.r : ℝ) + 1) ^ 3 *
      Real.sqrt (((gridOf D 0 0 τ).v 2 - (gridOf D 0 0 τ).v D.R.k : ℤ) : ℝ) ≤ γ) ∧
    2 * bigN D ^ 3 + 2 * sLen D + 2 < γ ∧ 48 * ((D.R.r : ℝ) + 1) ^ 2 * Real.sqrt D.R.m ≤ γ

def gap : ℕ := sInf {γ | GapCond D γ}

theorem exists_gapCond : ∃ γ, GapCond D γ := by
  obtain ⟨B, hB⟩ := (Set.finite_range fun τ : D.what₂.Tau => (bigN D : ℝ) ^ 3 + ((D.R.r : ℝ) + 1) ^ 7 + ((D.R.r : ℝ) + 1) ^ 3 *
    Real.sqrt (((gridOf D 0 0 τ).v 2 - (gridOf D 0 0 τ).v D.R.k : ℤ) : ℝ)).bddAbove
  refine ⟨⌈B⌉₊ + (2 * bigN D ^ 3 + 2 * sLen D + 3) + ⌈48 * ((D.R.r : ℝ) + 1) ^ 2 * Real.sqrt D.R.m⌉₊, fun τ => ?_, by omega, ?_⟩
  · refine ((hB ⟨τ, rfl⟩).trans (Nat.le_ceil B)).trans ?_
    exact_mod_cast (by omega)
  · refine (Nat.le_ceil _).trans ?_
    exact_mod_cast (by omega)

theorem isLeast_gap : IsLeast {γ | GapCond D γ} (gap D) :=
  ⟨Nat.sInf_mem (exists_gapCond D), fun _ h => Nat.sInf_le h⟩

def cen (τ : D.what₂.Tau) (i : ℕ) : ℤ := ⌊(gridOf D (gap D) 0 τ).mid i⌋

def grid (τ : D.what₂.Tau) : GridData := gridOf D (gap D) (cen D τ) τ

theorem grid_nearMid (τ : D.what₂.Tau) : (grid D τ).NearMid := (grid D τ).nearMid_of_floor fun _ _ => rfl

def rkV (i j : ℕ) : ℕ := D.R.r + j * D.R.t + i * sLen D

def rkP (i : ℕ) : ℕ := D.R.r + 1 + i * (sLen D - 1)

def rkX (j : ℕ) : ℕ := rkP D D.R.m + j * (D.R.t + 1)

theorem rk_eq (τ : D.what₂.Tau) (i j : ℕ) :
    rkV D i j = (grid D τ).rankD i j ∧ rkP D i = (grid D τ).rankP i ∧ rkX D j = (grid D τ).rankX j := ⟨rfl, rfl, rfl⟩

def parV (i j : ℕ) (τ : D.what₂.Tau) : SPar :=
  dualPar (shift (if Odd (i + j) then -(1 / 2) else 0) ((grid D τ).parD i j))

def parP (i : ℕ) (τ : D.what₂.Tau) : SPar := (grid D τ).parPi i

def parXp (j : ℕ) (τ : D.what₂.Tau) : SPar := (grid D τ).parX j

theorem parV_zero {j : ℕ} (hj : j ≤ D.R.m) : parV D 0 j = parB (Ptw D) j := by
  funext τ
  obtain ⟨h1, h2, h3⟩ := GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D) (cen D τ)
  have := (grid D τ).dpar_eq (Ptw D) τ rfl rfl rfl h1 h2 h3 hj
  rw [parV, parB, this, zero_add]
  rfl

theorem parP_m : parP D D.R.m = parXp D 0 := funext fun τ => (grid D τ).parPi_m

end Numbers

variable (D) in

structure PlaceDat where

  q0 : ℕ

  w0 : Pl D.host.E

  e0 : ℕ

  Wd : Finset (Pl D.host.E)

namespace PlaceDat

variable (Z : PlaceDat D) (Pg : Finset (Pl D.host.E))

open Classical in

def W : Finset (Pl D.host.E) := Pg ∪ Z.Wd ∪ {Z.w0}

open Classical in

def depth (w : Pl D.host.E) : ℕ := if w = Z.w0 then Z.e0 else 2

def ideal : Ideal (𝓞 D.host.E) := ∏ w ∈ Z.W Pg, w.asIdeal ^ Z.depth w

def S0 : Finset (HeightOneSpectrum (𝓞 D.host.F)) := by
  classical exact (Z.W Pg).image fun w => w.under (𝓞 D.host.F)

theorem ideal_ne_bot : Z.ideal Pg ≠ ⊥ :=
  Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ w.ne_bot

structure Is {T : Type} (Q : T → Finset (Pl D.host.E)) (e : AE D) : Prop where

  prime : Z.q0.Prime

  five_le : 5 ≤ Z.q0

  referencePlaceOverPrime : Formalism.L2.Host.OverP D.host Z.q0 Z.w0

  split : Formalism.L2.Host.SplitsCompletely {Z.w0}

  ne_g : ∀ k, Z.q0 ≠ D.host.g k

  ne_pde : Z.q0 ≠ D.host.pde ∧ Z.q0 ≠ D.host.pde'

  referencePrimeNeTwist : Z.q0 ≠ D.sp.T ∧ ∀ u : D.what₂.Word, Z.q0 ≠ (D.mem u).A.T

  coprime : Nat.Coprime (Ideal.absNorm D.host.ccK) Z.q0

  offQ : ∀ t, ∀ w ∈ Q t, w.under (𝓞 D.host.F) ≠ Z.w0.under (𝓞 D.host.F)

  depth_pos : 1 ≤ Z.e0

  Wd_over : ∀ w ∈ Z.Wd, Formalism.L2.Host.OverP D.host D.host.pde w ∨ Formalism.L2.Host.OverP D.host D.host.pde' w

  Wd_all : ∀ p ∈ ({D.host.pde, D.host.pde'} : Set ℕ),
    (∀ w, Formalism.L2.Host.OverP D.host p w → ∃ w' ∈ Z.Wd, w'.under (𝓞 D.host.F) = w.under (𝓞 D.host.F)) ∧
    (∃ 𝔭 : HeightOneSpectrum (𝓞 D.host.K), ∀ w ∈ Z.Wd, Formalism.L2.Host.OverP D.host p w → w.under (𝓞 D.host.K) = 𝔭) ∧
    ∀ t, ∀ w ∈ Q t, Formalism.L2.Host.OverP D.host p w → w ∈ Z.Wd

  idem : IsIdemSum e (Z.W Pg)

structure IsGridPlaceAuxiliaryHeckeCharacter (c : D.what₂.Tau → ℤ) (χ : Formalism.L2.Host.HChar D.host.E) : Prop where

  unitary : χ.IsUnitary

  triv : χ.TrivOn D.host.F

  inf : χ.HasInfQ (tauE D) fun τ => (c τ : ℚ)

  unr : ∀ w : Pl D.host.E, w.under (𝓞 D.host.F) ∉ Z.S0 Pg → χ.UnrAt w

  two : ∀ w, w ∈ Pg ∨ w ∈ Z.Wd → χ.LevelLe w 2 ∧ ¬ χ.LevelLe w 1

  teich : ∀ w ∈ Z.Wd, ∀ x, x ^ (Nat.card (kP w) - 1) = 1 → χ.loc w x = 1

  tame : χ.TameAt Z.w0 ∧ ¬ χ.UnrAt Z.w0

end PlaceDat

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

@[reducible] def nodeY (j : ℕ) : Node D := ⟨Yc D j, _, R.MY j, R.ΛY j, R.βY j⟩

@[reducible] def nodeX : Node D := ⟨D.sp.X', _, R.MX, R.ΛX, R.βX⟩

def row0 : ℕ → Node D
  | 0 => nodeY R 0
  | j + 1 => if j + 1 < D.R.m then nodeY R (j + 1) else nodeX R

theorem nodeY_eq_chainVertexAtRowZero_of_lt {j : ℕ} (h : j < D.R.m) : nodeY R j = row0 R j := by
  cases j with
  | zero => rfl
  | succ j => simp only [row0, if_pos h]

theorem nodeX_eq_chainVertexAtRowZero_of_ge {j : ℕ} (h : ¬ j + 1 < D.R.m) : nodeX R = row0 R (j + 1) := by simp only [row0, if_neg h]

theorem nodeX_eq_chainVertexAtRowZero_top : nodeX R = row0 R D.R.m := by
  have h := D.R.two_le_m
  have e : D.R.m - 1 + 1 = D.R.m := by omega
  rw [← e]; exact nodeX_eq_chainVertexAtRowZero_of_ge R (by omega)

def stepY (t : T) (k : ℕ) : ArrS (nodeY R k) (nodeY R (k + 1)) := ⟨R.ωY t k, R.vac k, R.ItY k⟩

def stepX (t : T) : ArrS (nodeY R (D.R.m - 1)) (nodeX R) := ⟨R.ωX t, R.vacX, R.ItX⟩

theorem nodeY_pred_eq_chainVertexAtRowZero_last {j : ℕ} (h : j + 1 = D.R.m) : nodeY R (D.R.m - 1) = row0 R j := by
  rw [show D.R.m - 1 = j by omega]; exact nodeY_eq_chainVertexAtRowZero_of_lt R (by omega)

def th0 (t : T) (j : ℕ) : ArrS (row0 R j) (row0 R (j + 1)) :=
  if h : j + 1 < D.R.m then (stepY R t j).cast (nodeY_eq_chainVertexAtRowZero_of_lt R (by omega)) (nodeY_eq_chainVertexAtRowZero_of_lt R h)
  else if h' : j + 1 = D.R.m then (stepX R t).cast (nodeY_pred_eq_chainVertexAtRowZero_last R h') (nodeX_eq_chainVertexAtRowZero_of_ge R h) else ⟨1, 0, 0⟩

def meas0 (t : T) (j : ℕ) : (row0 R (j + 1)).MeasDat :=
  if h : j + 1 < D.R.m then Node.MeasDat.cast (nodeY_eq_chainVertexAtRowZero_of_lt R h) ⟨R.νY t (j + 1), R.fdY t (j + 1)⟩
  else Node.MeasDat.cast (nodeX_eq_chainVertexAtRowZero_of_ge R h) ⟨R.νX t, R.fdX t⟩

def datum0 (t : T) (j : ℕ) : WO (row0 R j).V (row0 R (j + 1)).V → ℂ :=
  if h : j + 1 < D.R.m then castFun (nodeY_eq_chainVertexAtRowZero_of_lt R (by omega)) (nodeY_eq_chainVertexAtRowZero_of_lt R h) (R.vY t j)
  else if h' : j + 1 = D.R.m then castFun (nodeY_pred_eq_chainVertexAtRowZero_last R h') (nodeX_eq_chainVertexAtRowZero_of_ge R h) (R.vX t) else 0

variable (D) in

structure GridSp extends PlaceDat D where

  nV : ℕ → ℕ → Node D

  P : ℕ → Node D

  nX : ℕ → Node D

namespace GridSp

variable (G : GridSp D)

@[reducible] def vert : ℕ → ℕ → Node D
  | 0, j => row0 R j
  | i + 1, j => G.nV i j

@[reducible] def Xp : ℕ → Node D
  | 0 => G.P D.R.m
  | j + 1 => G.nX j

abbrev lvl : Ideal (𝓞 D.host.E) := G.toPlaceDat.ideal R.Pg

abbrev Cos (i : ℕ) : Type := Coset (G.vert R (i + 1) 0) (G.vert R i 0) (G.lvl R)

def Data : Type := ∀ i : Fin D.R.m, G.Cos R i

instance : Finite (G.Data R) :=
  have : ∀ i : Fin D.R.m, Finite (G.Cos R i) := fun _ => finite_coset (G.toPlaceDat.ideal_ne_bot _)
  Pi.finite

instance : Nonempty (G.Data R) := ⟨fun _ => 0⟩

end GridSp

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure GridPre extends GridSp D where

  idem : AE D

  chiH : ℕ → Formalism.L2.Host.HChar D.host.E

  chi : ℕ → ((AE D)ˣ →* Circle)

  decP : HermitianOrthogonalExtensionData (toGridSp.vert R 0 0) (P 0) 1

  decV : ∀ i, HermitianOrthogonalExtensionData (P i) (toGridSp.vert R i 0) (i - 1)

  decX : ∀ j, HermitianOrthogonalExtensionData (nX j) (toGridSp.vert R D.R.m (j + 1)) (D.R.m - 1 - (j + 1))

  decZ : HermitianOrthogonalExtensionData (toGridSp.vert R D.R.m D.R.m) (toGridSp.Xp D.R.m) 1

  X : ∀ i j, ArrS (toGridSp.vert R (i + 1) j) (toGridSp.vert R i j)

  ωT : T → ∀ i j, WRep (nV i j).V (nV i (j + 1)).V

  vacT : ∀ i j, WO (nV i j).V (nV i (j + 1)).V → ℂ

  ItT : ∀ i j, Pol (nV i j) (nV i (j + 1)) →ₗ[ℂ] SmT (nV i (j + 1)).M →ₗ[ℂ] SmT (nV i j).M

  ωC : T → ∀ j, WRep (toGridSp.Xp j).V (nX j).V

  vacC : ∀ j, WO (toGridSp.Xp j).V (nX j).V → ℂ

  ItC : ∀ j, Pol (toGridSp.Xp j) (nX j) →ₗ[ℂ] SmT (toGridSp.Xp j).M →ₗ[ℂ] SmT (nX j).M

  dn : ∀ i, ArrT (P (i + 1)) (P i)

  ItU : ∀ i, Pol (P (i + 1)) (P i) →ₗ⋆[ℂ] SmT (P i).M →ₗ[ℂ] SmT (P (i + 1)).M

  m00 : (toGridSp.vert R 0 0).MeasDat

  mV : ∀ i j, (nV i j).MeasDat

  mP : ∀ i, (P i).MeasDat

  mX : ∀ j, (nX j).MeasDat

  vC : ∀ i, toGridSp.Cos R i → (WO (toGridSp.vert R (i + 1) 0).V (toGridSp.vert R i 0).V → ℂ)

namespace GridPre

variable {R} (G : GridPre R)

abbrev V (i j : ℕ) : Node D := G.toGridSp.vert R i j

def th (t : T) : ∀ i j, ArrS (G.V i j) (G.V i (j + 1))
  | 0, j => th0 R t j
  | i + 1, j => ⟨G.ωT t i j, G.vacT i j, G.ItT i j⟩

def col (t : T) (j : ℕ) : ArrT (G.Xp j) (G.Xp (j + 1)) := ⟨G.ωC t j, G.vacC j, G.ItC j⟩

def measCol : ∀ i, (G.V i 0).MeasDat
  | 0 => G.m00
  | i + 1 => G.mV i 0

def meas (t : T) : ∀ i j, (G.V i j).MeasDat
  | 0, 0 => G.m00
  | 0, j + 1 => meas0 R t j
  | i + 1, j => G.mV i j

theorem meas_zero (t : T) (i : ℕ) : G.meas t i 0 = G.measCol i := by cases i <;> rfl

def measX : ∀ j, (G.Xp j).MeasDat
  | 0 => G.mP D.R.m
  | j + 1 => G.mX j

def decRow : ∀ j, HermitianOrthogonalExtensionData (G.Xp j) (G.V D.R.m j) (D.R.m - 1 - j)
  | 0 => G.decV D.R.m
  | j + 1 => G.decX j

theorem th_It (t t' : T) (i j : ℕ) : (G.th t i j).It = (G.th t' i j).It := by
  cases i with
  | succ i => rfl
  | zero =>
    show (th0 R t j).It = (th0 R t' j).It
    unfold th0
    split_ifs
    exacts [ArrS.cast_It_congr _ _ rfl, ArrS.cast_It_congr _ _ rfl, rfl]

abbrev muAt (R : RealDat D A Ks) (t : T) (j n : ℕ) : (AE D)ˣ →* Circle := Lift.attChr (R.toLevCh.mu t j) R.eta n

abbrev chiAt (i n : ℕ) : (AE D)ˣ →* Circle := Lift.attChr (G.chi i) R.eta n

structure IsSpaces : Prop where

  vert : ∀ i j, i + 1 ≤ D.R.m → j ≤ D.R.m → (G.nV i j).Is (rkV D (i + 1) j) ((D.R.m - j) / 2) (parV D (i + 1) j)

  P : ∀ i, i ≤ D.R.m → (G.P i).Is (rkP D i) ((D.R.m - i + 1) / 2) (parP D i)

  X : ∀ j, j + 1 ≤ D.R.m → (G.nX j).Is (rkX D (j + 1)) 0 (parXp D (j + 1))

  decP : G.decP.Is (fun _ _ => 1) fun _ => 1

  decV : ∀ i, 1 ≤ i → i ≤ D.R.m → (G.decV i).Is (antiDiagonalSignGramMatrix _ _) (staircaseExtensionIdeal (G.lvl R) _)

  decX : ∀ j, j + 1 < D.R.m → (G.decX j).Is (antiDiagonalSignGramMatrix _ _) (staircaseExtensionIdeal ⊤ _)

  decZ : G.decZ.Is (fun _ _ => 1) fun _ => 1

structure IsChars : Prop where

  places : G.toPlaceDat.Is R.Pg R.Q G.idem

  aux : ∀ i, 1 ≤ i → i ≤ D.R.m → G.toPlaceDat.IsGridPlaceAuxiliaryHeckeCharacter R.Pg (fun τ => cen D τ i) (G.chiH i)

  tie : ∀ i, 1 ≤ i → i ≤ D.R.m → ChrEq (G.chi i) (G.chiH i)

structure IsArrows : Prop where

  X : ∀ i j, i < D.R.m → j ≤ D.R.m →
    (G.X i j).Is R.ψ R.θ true (G.chiAt (D.R.m - i) (rkV D (i + 1) j)) (G.chiAt (D.R.m - i) (rkV D i j))

  th : ∀ t i j, i ≤ D.R.m → j < D.R.m →
    (G.th t i j).Is R.ψ R.θ false (muAt R t (j + 1) (rkV D i j)) (muAt R t (j + 1) (rkV D i (j + 1)))

  col : ∀ t j, j < D.R.m → (G.col t j).Is R.ψ R.θ false (R.toLevCh.mu t (j + 1)) (R.toLevCh.mu t (j + 1))

  dn : ∀ i, i < D.R.m → (G.dn i).Is R.ψ R.θ true (G.chi (D.R.m - i)) (G.chi (D.R.m - i))

  up : ∀ i, i < D.R.m → (G.dn i).IsAdj (G.ItU i)

structure IsMeas : Prop where

  col : ∀ i, i ≤ D.R.m → (G.measCol i).Is False ((G.V i 0).princ (G.lvl R))

  vert : ∀ i j, i + 1 ≤ D.R.m → j + 1 ≤ D.R.m → (G.mV i (j + 1)).Is (D.R.m - 1 ≤ j + 1) ((G.nV i (j + 1)).princ ⊤)

  P : ∀ i, i ≤ D.R.m → (G.mP i).Is (i = D.R.m) ((G.P i).princ (G.lvl R))

  X : ∀ j, j + 1 ≤ D.R.m → (G.mX j).Is True ((G.nX j).princ ⊤)

def IsData : Prop :=
  ∀ i, i < D.R.m → ∀ c, IsCosetVec R.ψ true (G.V (i + 1) 0) (G.V i 0) G.idem (G.lvl R) c (G.X i 0).vac (G.vC i c)

structure Is : Prop where

  spaces : G.IsSpaces

  chars : G.IsChars

  arrows : G.IsArrows

  meas : G.IsMeas

  data : G.IsData

def ValuesInField : Prop :=
  (∀ i, 1 ≤ i → i ≤ D.R.m → (G.chiH i).ValuesIn 0 D.what₂.embLL) ∧
    ∀ w ∈ G.toPlaceDat.W R.Pg, ∃ z : D.what₂.LL, IsPrimitiveRoot z (Nat.card (kP w) ^ G.toPlaceDat.depth w)

def datum (Φ : G.Data R) (i : ℕ) : WO (G.V (i + 1) 0).V (G.V i 0).V → ℂ :=
  if h : i < D.R.m then G.vC i (Φ ⟨i, h⟩) else 0

abbrev CV (i j : ℕ) : Submodule ℂ (G.V i j).Maps := (G.V i j).Cusp R.θ

structure HasLifts : Prop where

  X : ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ f, IsFinVec R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f →
    ∃ io, (G.X i j).IsLift R.ψ R.θ true (G.meas t i j) f io

  th : ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ f, IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) f →
    ∃ io, (G.th t i j).IsLift R.ψ R.θ false (G.meas t i (j + 1)) f io

  col : ∀ t j, j < D.R.m → ∀ f, IsFinVec R.ψ R.θ false (G.Xp j) (G.Xp (j + 1)) f →
    ∃ io, (G.col t j).IsLift R.ψ R.θ false (G.measX j) f io

  dn : ∀ i, i < D.R.m → ∀ f, IsFinVec R.ψ R.θ true (G.P (i + 1)) (G.P i) f →
    ∃ io, (G.dn i).IsLift R.ψ R.θ true (G.mP (i + 1)) f io

  up : ∀ i, i < D.R.m → ∀ f, IsFinVec R.ψ R.θ true (G.P (i + 1)) (G.P i) f →
    ∃ io, (G.dn i).IsLiftConj R.ψ R.θ true (G.ItU i) (G.mP i) f io

structure RealVec where

  pol : ∀ i, Pol (G.V (i + 1) 0) (G.V i 0)

  w : (R.MY 0).Vec

def RealVec.vec {G : GridPre R} (r : G.RealVec) (i : ℕ) : SmT (G.V i 0).M :=
  Nat.rec (motive := fun i => SmT (G.V i 0).M) (PiTensorProduct.tprod ℂ r.w) (fun i v => (G.X i 0).It (r.pol i) v) i

theorem RealVec.vec_zero {G : GridPre R} (r : G.RealVec) : r.vec 0 = PiTensorProduct.tprod ℂ r.w := rfl

theorem RealVec.vec_succ {G : GridPre R} (r : G.RealVec) (i : ℕ) : r.vec (i + 1) = (G.X i 0).It (r.pol i) (r.vec i) := rfl

end GridPre

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure GridDat extends GridPre R where

  gridInclusionColumnZero : ∀ i, (WO (toGridPre.V (i + 1) 0).V (toGridPre.V i 0).V → ℂ) → toGridPre.CV i 0 →ₗ[ℂ] toGridPre.CV (i + 1) 0

  gridInclusionColumnSucc : T → ∀ i j, (WO (toGridPre.V (i + 1) (j + 1)).V (toGridPre.V i (j + 1)).V → ℂ) →
    toGridPre.CV i (j + 1) →ₗ[ℂ] toGridPre.CV (i + 1) (j + 1)

  ioT : T → ∀ i j, (WO (toGridPre.V i j).V (toGridPre.V i (j + 1)).V → ℂ) → toGridPre.CV i (j + 1) →ₗ[ℂ] toGridPre.CV i j

  ioC : T → ∀ j, (WO (toGridPre.Xp j).V (toGridPre.Xp (j + 1)).V → ℂ) →
    (toGridPre.Xp j).Cusp R.θ →ₗ[ℂ] (toGridPre.Xp (j + 1)).Cusp R.θ

  ioD : ∀ i, (WO (P (i + 1)).V (P i).V → ℂ) → (P (i + 1)).Cusp R.θ →ₗ[ℂ] (P i).Cusp R.θ

  ioU : ∀ i, (WO (P (i + 1)).V (P i).V → ℂ) → (P i).Cusp R.θ →ₗ[ℂ] (P (i + 1)).Cusp R.θ

namespace GridDat

variable {R} (G : GridDat R)

def ioX (t : T) (i : ℕ) : ∀ j, (WO (G.V (i + 1) j).V (G.V i j).V → ℂ) → G.CV i j →ₗ[ℂ] G.CV (i + 1) j
  | 0 => G.gridInclusionColumnZero i
  | j + 1 => G.gridInclusionColumnSucc t i j

structure IsLifts : Prop where

  X : ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ f, IsFinVec R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f →
    (G.X i j).IsLift R.ψ R.θ true (G.meas t i j) f (G.ioX t i j f)

  th : ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ f, IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) f →
    (G.th t i j).IsLift R.ψ R.θ false (G.meas t i (j + 1)) f (G.ioT t i j f)

  col : ∀ t j, j < D.R.m → ∀ f, IsFinVec R.ψ R.θ false (G.Xp j) (G.Xp (j + 1)) f →
    (G.col t j).IsLift R.ψ R.θ false (G.measX j) f (G.ioC t j f)

  dn : ∀ i, i < D.R.m → ∀ f, IsFinVec R.ψ R.θ true (G.P (i + 1)) (G.P i) f →
    (G.dn i).IsLift R.ψ R.θ true (G.mP (i + 1)) f (G.ioD i f)

  up : ∀ i, i < D.R.m → ∀ f, IsFinVec R.ψ R.θ true (G.P (i + 1)) (G.P i) f →
    (G.dn i).IsLiftConj R.ψ R.θ true (G.ItU i) (G.mP i) f (G.ioU i f)

structure Is : Prop where

  pre : G.toGridPre.Is

  lifts : G.IsLifts

def colLift (t : T) (j : ℕ) (f : ∀ i, WO (G.V (i + 1) j).V (G.V i j).V → ℂ) (n : ℕ) : G.CV 0 j →ₗ[ℂ] G.CV n j :=
  Nat.rec (motive := fun n => G.CV 0 j →ₗ[ℂ] G.CV n j) LinearMap.id (fun n L => G.ioX t n j (f n) ∘ₗ L) n

theorem colLift_zero (t : T) (j : ℕ) (f : ∀ i, WO (G.V (i + 1) j).V (G.V i j).V → ℂ) : G.colLift t j f 0 = LinearMap.id := rfl

theorem colLift_succ (t : T) (j : ℕ) (f : ∀ i, WO (G.V (i + 1) j).V (G.V i j).V → ℂ) (n : ℕ) :
    G.colLift t j f (n + 1) = G.ioX t n j (f n) ∘ₗ G.colLift t j f n := rfl

def rowLift (t : T) (i : ℕ) (f : ∀ j, WO (G.V i j).V (G.V i (j + 1)).V → ℂ) (n : ℕ) : G.CV i n →ₗ[ℂ] G.CV i 0 :=
  Nat.rec (motive := fun n => G.CV i n →ₗ[ℂ] G.CV i 0) LinearMap.id (fun n L => L ∘ₗ G.ioT t i n (f n)) n

theorem rowLift_zero (t : T) (i : ℕ) (f : ∀ j, WO (G.V i j).V (G.V i (j + 1)).V → ℂ) : G.rowLift t i f 0 = LinearMap.id := rfl

theorem rowLift_succ (t : T) (i : ℕ) (f : ∀ j, WO (G.V i j).V (G.V i (j + 1)).V → ℂ) (n : ℕ) :
    G.rowLift t i f (n + 1) = G.rowLift t i f n ∘ₗ G.ioT t i n (f n) := rfl

def chiLift (Φ : G.Data R) (n : ℕ) : G.CV 0 0 →ₗ[ℂ] G.CV n 0 :=
  Nat.rec (motive := fun n => G.CV 0 0 →ₗ[ℂ] G.CV n 0) LinearMap.id (fun n L => G.gridInclusionColumnZero n (G.datum Φ n) ∘ₗ L) n

theorem chiLift_zero (Φ : G.Data R) : G.chiLift Φ 0 = LinearMap.id := rfl

theorem chiLift_succ (Φ : G.Data R) (n : ℕ) : G.chiLift Φ (n + 1) = G.gridInclusionColumnZero n (G.datum Φ n) ∘ₗ G.chiLift Φ n := rfl

theorem chiLift_eq (t : T) (Φ : G.Data R) (n : ℕ) : G.chiLift Φ n = G.colLift t 0 (G.datum Φ) n := rfl

theorem IsLifts.hasLifts {G : GridDat R} (h : G.IsLifts) : G.toGridPre.HasLifts :=
  ⟨fun t i j a b f c => ⟨_, h.X t i j a b f c⟩, fun t i j a b f c => ⟨_, h.th t i j a b f c⟩,
    fun t j a f c => ⟨_, h.col t j a f c⟩, fun i a f c => ⟨_, h.dn i a f c⟩, fun i a f c => ⟨_, h.up i a f c⟩⟩

end GridDat

theorem GridPre.exists_gridDat {R : RealDat D A Ks} (G : GridPre R) (hG : G.Is) (h : G.HasLifts) :
    ∃ G' : GridDat R, G'.toGridPre = G ∧ G'.Is := by
  have ex : ∀ {α : Type} [Zero α] {p : Prop} {q : α → Prop}, (p → ∃ a, q a) → ∃ a, p → q a := fun {α} _ {p} {q} H => by
    by_cases hp : p
    · exact (H hp).imp fun _ ha _ => ha
    · exact ⟨0, fun h => absurd h hp⟩
  choose x0 hx0 using fun i f => ex fun c : i < D.R.m ∧ IsFinVec R.ψ R.θ true (G.V (i + 1) 0) (G.V i 0) f =>
    h.X A.μ0 i 0 c.1 (Nat.zero_le _) f c.2
  choose x1 hx1 using fun t i j f =>
    ex fun c : i < D.R.m ∧ j + 1 ≤ D.R.m ∧ IsFinVec R.ψ R.θ true (G.V (i + 1) (j + 1)) (G.V i (j + 1)) f =>
      h.X t i (j + 1) c.1 c.2.1 f c.2.2
  choose th hth using fun t i j f =>
    ex fun c : i ≤ D.R.m ∧ j < D.R.m ∧ IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) f => h.th t i j c.1 c.2.1 f c.2.2
  choose cl hcl using fun t j f =>
    ex fun c : j < D.R.m ∧ IsFinVec R.ψ R.θ false (G.Xp j) (G.Xp (j + 1)) f => h.col t j c.1 f c.2
  choose dn hdn using fun i f => ex fun c : i < D.R.m ∧ IsFinVec R.ψ R.θ true (G.P (i + 1)) (G.P i) f => h.dn i c.1 f c.2
  choose up hup using fun i f => ex fun c : i < D.R.m ∧ IsFinVec R.ψ R.θ true (G.P (i + 1)) (G.P i) f => h.up i c.1 f c.2
  refine ⟨⟨G, x0, x1, th, cl, dn, up⟩, rfl, hG, fun t i j a b f c => ?_, fun t i j a b f c => hth t i j f ⟨a, b, c⟩,
    fun t j a f c => hcl t j f ⟨a, c⟩, fun i a f c => hdn i f ⟨a, c⟩, fun i a f c => hup i f ⟨a, c⟩⟩
  cases j with
  | zero =>
    have := hx0 i f ⟨a, c⟩
    rw [G.meas_zero] at this
    show (G.X i 0).IsLift R.ψ R.θ true (G.meas t i 0) f (x0 i f)
    rwa [G.meas_zero]
  | succ j => exact hx1 t i j f ⟨a, b, c⟩

example (G : GridPre R) : (G.V 0 0).V = Yc D 0 ∧ (G.V 0 0).M = R.MY 0 := ⟨rfl, rfl⟩

example (t : T) (j : ℕ) : (GridPre.muAt R t (j + 1) (rkV D 0 j), GridPre.muAt R t (j + 1) (rkV D 0 (j + 1))) =
    Lift.chrStep (R.toLevCh.mu t) R.eta (j + 1) := by
  have hr : Odd D.R.r := by
    have h1 := D.R.k_even; have h2 := D.R.m_even; have h3 := D.R.two_le_m
    unfold Ranks.r; grind
  rw [Lift.chrStep_eq_att _ _ hr D.R.t_odd (Nat.le_add_left 1 j)]
  simp [rkV]

example (i : ℕ) : rkP D (i + 1) + i = rkV D (i + 1) 0 ∧ rkV D D.R.m D.R.m + 1 = rkX D D.R.m := by
  have e : sLen D - 1 = D.R.r + 5 := rfl
  refine ⟨?_, ?_⟩ <;> simp only [rkP, rkV, rkX, e] <;> simp only [sLen] <;> ring

example (t : T) (P : PolF D (Yc D 1).rank (Yc D 0).rank) :
    fock R.ψ R.θ false (nodeY R 0) (nodeY R 1) (R.vY t 0) P = R.ptY t 0 P := rfl

end GlobalTheory.Grid

end
