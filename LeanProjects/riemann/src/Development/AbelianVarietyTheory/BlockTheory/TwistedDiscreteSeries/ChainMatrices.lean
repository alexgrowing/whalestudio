import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev Ef (D : D7) : Type := Formalism.IndefR.Lev.EAf D

variable {D : D7}

def ratM {a b : ℕ} (M : Matrix (Fin a) (Fin b) D.host.E) : Matrix (Fin a) (Fin b) (Ef D) :=
  M.map (Formalism.IndefR.Datum.eToEAf D)

def adjM {a b : ℕ} (M : Matrix (Fin a) (Fin b) (Ef D)) : Matrix (Fin b) (Fin a) (Ef D) :=
  Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) M

def mulM {a b c : ℕ} (M : Matrix (Fin a) (Fin b) (Ef D)) (N : Matrix (Fin b) (Fin c) (Ef D)) : Matrix (Fin a) (Fin c) (Ef D) :=
  HMul.hMul M N

def AgreeAt (PP : Pl D.host.E) {a b : ℕ} (M M' : Matrix (Fin a) (Fin b) (Ef D)) : Prop :=
  ∃ e : AE D, Formalism.L2.NTheta.IsIdemAt e PP ∧
    ∀ i j, Formalism.IndefR.Datum.toEAf D e * M i j = Formalism.IndefR.Datum.toEAf D e * M' i j

variable (D) in

def nAux (j : ℕ) : ℕ := D.R.m - 1 - j

variable (D) in

def IsAuxiliaryHeckeCharacter (j : ℕ) (E Ev : ℕ → (D.sp.Y j).V) (z : (D.sp.Y j).V) : Prop :=
  (∀ i < nAux D j / 2, ∀ l < nAux D j / 2,
    (D.sp.Y j).hD (E i) (E l) = 0 ∧ (D.sp.Y j).hD (Ev i) (Ev l) = 0 ∧
      (D.sp.Y j).hD (E i) (Ev l) = if i = l then 1 else 0) ∧
  (∀ i < nAux D j / 2, ∀ x,
    (D.sp.Y j).hD (E i) (D.sp.iXY j x) = 0 ∧ (D.sp.Y j).hD (Ev i) (D.sp.iXY j x) = 0) ∧
  (Even j → (D.sp.Y j).hD z z = -(D.sp.T : D.host.E) ∧ (∀ x, (D.sp.Y j).hD z (D.sp.iXY j x) = 0) ∧
    ∀ i < nAux D j / 2, (D.sp.Y j).hD (E i) z = 0 ∧ (D.sp.Y j).hD (Ev i) z = 0)

variable (D) in

def normalFr (j : ℕ) (E Ev : ℕ → (D.sp.Y j).V) (z : (D.sp.Y j).V) (n : ℕ) : (D.sp.Y j).V :=
  if n < nAux D j / 2 then E n
  else if Even j ∧ n = nAux D j / 2 then z
  else (if Even j then -(D.sp.T : D.host.E) else (D.sp.T : D.host.E)) • Ev (nAux D j - 1 - n)

variable (D) in

def colX (j : ℕ) (γ : GL (Fin (D.sp.X j).rank) (Ef D)) (n : ℕ) (i : Fin (D.sp.Y j).rank) : Ef D :=
  if h : n < (D.sp.X j).rank then mulM (ratM (frameMat (D.sp.Y j) (D.sp.X j) (D.sp.iXY j))) γ.val i ⟨n, h⟩ else 0

variable (D) in

def chainMat (j : ℕ) (γ : GL (Fin (D.sp.X j).rank) (Ef D)) (E Ev : ℕ → (D.sp.Y j).V) (z : (D.sp.Y j).V) (s : ℕ) :
    Matrix (Fin (D.sp.Y j).rank) (Fin (D.sp.Y j).rank) (Ef D) :=
  fun i a =>
    if (a : ℕ) < D.R.k then colX D j γ a i
    else if (a : ℕ) < D.R.k + nAux D j then
      Formalism.IndefR.Datum.eToEAf D
        ((s : D.host.E) ^ ((a : ℕ) - D.R.k + 1) * (D.sp.Y j).frame.repr (normalFr D j E Ev z ((a : ℕ) - D.R.k)) i)
    else colX D j γ ((a : ℕ) - nAux D j) i

def SpansAt (PP : Pl D.host.E) (V : HSp D) (M : Matrix (Fin V.rank) (Fin V.rank) (Ef D)) : Prop :=
  ∃ e : AE D, Formalism.L2.NTheta.IsIdemAt e PP ∧ ∀ x : Fin V.rank → Ef D,
    (fun i => Formalism.IndefR.Datum.toEAf D e * x i) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Herm.crdLat V V.L0) ↔
      ∃ c : Fin V.rank → Ef D, (∀ a, c a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) ∧
        ∀ i, Formalism.IndefR.Datum.toEAf D e * x i = Formalism.IndefR.Datum.toEAf D e * (M *ᵥ c) i

def ShapeY {T : Type} (L : LevCh D T) (j : ℕ) (γ : GL (Fin (D.sp.X j).rank) (Ef D)) (E Ev : ℕ → (D.sp.Y j).V) (z : (D.sp.Y j).V)
    (β : GL (Fin (D.sp.Y j).rank) (Ef D)) : Prop :=
  (∀ (l : Fin 2) (PP : Pl D.host.E), L.C.P.Div l PP → AgreeAt PP β.val (chainMat D j γ E Ev z (D.host.g l))) ∧
  ∀ t, ∀ PP ∈ L.Q t, SpansAt PP (D.sp.Y j) (chainMat D j γ E Ev z 1) → AgreeAt PP β.val (chainMat D j γ E Ev z 1)

def TopTie (j : ℕ) (β : GL (Fin (D.sp.Y j).rank) (Ef D)) (Λ : Submodule (𝓞 D.host.E) (Fin (D.sp.Y j).rank → D.host.E))
    (βX : GL (Fin D.sp.X'.rank) (Ef D)) : Prop :=
  IsFrame β Λ ∧ ∃ ι : D.sp.X'.V →ₗ[D.host.E] (D.sp.Y j).V, HEq ι D.sp.eYm.toLinearMap ∧
    ∀ (a : Fin (D.sp.Y j).rank) (b : Fin D.sp.X'.rank), (a : ℕ) = b →
      ∀ i, β.val i a = mulM (ratM (frameMat (D.sp.Y j) D.sp.X' ι)) βX.val i b

def IsStdSpace (V : HSp D) : Prop :=
  V.gram = 1 ∧ ∀ x : Fin V.rank → D.host.E, x ∈ L0c D V ↔ ∀ i, x i ∈ (algebraMap (𝓞 D.host.E) D.host.E).range

def OrthoFrame (i : Fin D.R.m) (β : GL (Fin (Vc D i).rank) (Ef D)) : Prop :=
  ∃ B : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) D.host.E, β.val = ratM B ∧
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B * (Vc D i).gram * B =
      if D.sp.Vneg ((i : ℕ) + 1) then -1 else 1

def Transport (Pg : Finset (Pl D.host.E)) (W Y : HSp D) (βW : GL (Fin W.rank) (Ef D)) (βY : GL (Fin Y.rank) (Ef D)) : Prop :=
  ∃ (x y : Matrix (Fin Y.rank) (Fin W.rank) (Ef D)) (y' : Matrix (Fin W.rank) (Fin Y.rank) (Ef D)),
    mulM (mulM (adjM x) (ratM Y.gram)) x = ratM W.gram ∧ mulM x βW.val = mulM βY.val y ∧
    Formalism.IndefR.Datum.IsIntM y ∧ Formalism.IndefR.Datum.IsIntM y' ∧ mulM y y' = 1 ∧ mulM y' y = 1 ∧
    ∀ PP ∈ Pg, AgreeAt PP y (Matrix.of fun a b => if (a : ℕ) = b then 1 else 0)

def FrameClauses {T : Type} (L : LevCh D T) : Prop :=
  (∀ j, j < D.R.m → IsSDFrame (Yc D j) (L.βY j) (L.ΛY j) (D.host.g 0 * D.host.g 1)) ∧
  IsSDFrame D.sp.X' L.βX L.ΛX 1 ∧
  (∀ i, IsSDFrame (Vc D i) (L.βV i) (L.ΛV i) 1) ∧
  ∀ i, IsSDFrame (Wc D i) (L.βW i) (L.ΛW i) 1

def StdShape {T : Type} (L : LevCh D T) (γ : ∀ j, GL (Fin (D.sp.X j).rank) (Ef D))
    (E Ev : ∀ j, ℕ → (D.sp.Y j).V) (z : ∀ j, (D.sp.Y j).V) : Prop :=
  (∀ j, j < D.R.m → IsAuxiliaryHeckeCharacter D (min j D.R.m) (E _) (Ev _) (z _) →
    ShapeY L (min j D.R.m) (γ _) (E _) (Ev _) (z _) (L.βY j)) ∧
  (∀ j, D.R.m ≤ j → TopTie (min j D.R.m) (L.βY j) (L.ΛY j) L.βX) ∧
  (IsStdSpace D.sp.X' → L.βX = 1) ∧
  (∀ i, OrthoFrame i (L.βV i) ∧ (IsStdSpace (Vc D i) → L.βV i = 1)) ∧
  ∀ i, Transport L.Pg (Wc D i) (Yc D 0) (L.βW i) (L.βY 0)

def SameChars {T : Type} (L L' : LevCh D T) : Prop :=
  L'.C = L.C ∧ L'.xiH = L.xiH ∧ L'.mu0 = L.mu0 ∧ L'.eta = L.eta ∧ L'.xi = L.xi ∧ L'.Pg = L.Pg ∧ L'.Q = L.Q ∧
    L'.chi = L.chi ∧ L'.xiR = L.xiR

def FramesStdExist : Prop :=
  ∀ (D : D7) (T : Type) (L : LevCh D T),
    (∀ PP, PP ∈ L.Pg ↔ ∃ l, L.C.P.Div l PP) → (∀ t, Formalism.IndefR.Lev.IsTwistPlaces D.host.g (L.Q t)) →
    ∀ (γ : ∀ j, GL (Fin (D.sp.X j).rank) (Ef D)) (E Ev : ∀ j, ℕ → (D.sp.Y j).V) (z : ∀ j, (D.sp.Y j).V),
      (∀ j, j < D.R.m → IsFrame (γ j) (Formalism.L2.Herm.crdLat (D.sp.X j) (D.sp.X j).L0)) →
      ∃ L' : LevCh D T, SameChars L L' ∧ FrameClauses L' ∧ StdShape L' γ E Ev z

theorem idx_lt {j : ℕ} (hj : j < D.R.m) (a : Fin (D.sp.Y j).rank) :
    ((a : ℕ) < D.R.k → (a : ℕ) < (D.sp.X j).rank) ∧
      (¬ (a : ℕ) < D.R.k + nAux D j → (a : ℕ) - nAux D j < (D.sp.X j).rank) := by
  have h1 := D.sp.X_rank j hj.le
  have h2 := D.sp.Y_rank j hj.le
  have h3 := a.2
  have h4 : j * (D.R.t + 1) = j * D.R.t + j := by ring
  simp only [Ranks.N, Ranks.rankY, Ranks.r] at h1 h2
  unfold nAux
  generalize j * D.R.t = u at *
  constructor <;> intro h <;> omega

theorem isAuxiliaryHyperbolicPart_initialChainSpace : IsAuxiliaryHeckeCharacter D 0 (fun i => if h : i < D.R.rS then D.sp.hypE ⟨i, h⟩ else 0)
    (fun i => if h : i < D.R.rS then D.sp.hypF ⟨i, h⟩ else 0) D.sp.zm := by
  have hρ : nAux D 0 / 2 = D.R.rS := by
    obtain ⟨a, ha⟩ := D.R.m_even
    unfold nAux Ranks.rS
    omega
  have sym : ∀ x y, (D.sp.Y 0).hT x y = 0 → (D.sp.Y 0).hT y x = 0 := fun x y h => by
    rw [← (D.sp.Y 0).herm.eq x y, h, map_zero]
  unfold IsAuxiliaryHeckeCharacter HSpace.hD
  rw [hρ]
  refine ⟨fun i hi l hl => ?_, fun i hi x => ?_, fun _ => ⟨D.sp.zm_norm, D.sp.zm_orth, fun i hi => ?_⟩⟩
  · simp only [dif_pos hi, dif_pos hl]
    refine ⟨D.sp.hyp_ee _ _, D.sp.hyp_ff _ _, ?_⟩
    rw [← (D.sp.Y 0).herm.eq, D.sp.hyp_ef]
    by_cases h : i = l <;> simp [h]
  · simp only [dif_pos hi]
    exact D.sp.hyp_orthX _ x
  · simp only [dif_pos hi]
    exact D.sp.hyp_orthz _

def CharClauses {T : Type} (L : LevCh D T) (μ0 : T) : Prop :=
  ∀ L' : LevCh D T, SameChars L L' → FrameClauses L' → L'.Is μ0

end GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices

end
