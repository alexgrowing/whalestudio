import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RegConst
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.TopFlip

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc}

variable (G) in

abbrev spX (i j : ℕ) : HSp D := GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)

variable (G) in

def latX (i j : ℕ) : Submodule (𝓞 D.host.E) (Fin (spX G i j).rank → D.host.E) :=
  GlobalTheory.Doubling.sumLat finSumFinEquiv (G.Λ (.grid i (j + 1))) (G.Λ (.grid (i + 1) j))

variable (G) in

def homLatA (i j : ℕ) : AddSubgroup (WO (spW G i j) (spX G i j)) :=
  latO (GlobalTheory.Grid.neg (spW G i j)) (spX G i j) (G.Λ (.grid (i + 1) (j + 1))) (latX G i j) fun _ => True

variable (G) in

def homLatB (i j : ℕ) : AddSubgroup (WO (spW₁ G i j) (spX G i j)) :=
  latO (spW₁ G i j) (spX G i j) (G.Λ (.grid i j)) (latX G i j) fun _ => True

variable (G) in

def orderingsOnSpW (i j : ℕ) : Set (WO (spW G i j) (spX G i j)) :=
  {x | GlobalTheory.RouteSeesaw.topR (A := spV G i j) (B := spV₁ G i j) x ∈
      latO (negSp (spW G i j)) (spV G i j) (G.Λ (.grid (i + 1) (j + 1))) (G.Λ (.grid i (j + 1))) (fun _ => True) ∧
    GlobalTheory.RouteSeesaw.adjM (spW G i j) (spV₁ G i j) (GlobalTheory.RouteSeesaw.botR (A := spV G i j) (B := spV₁ G i j) x) ∈
      latO (spV₁ G i j) (spW G i j) (G.Λ (.grid (i + 1) j)) (G.Λ (.grid (i + 1) (j + 1))) fun _ => True}

variable (G) in

def orderingsOnSpWOne (i j : ℕ) : Set (WO (spW₁ G i j) (spX G i j)) :=
  {y | GlobalTheory.RouteSeesaw.topR (A := spV G i j) (B := spV₁ G i j) y ∈
      latO (spW₁ G i j) (spV G i j) (G.Λ (.grid i j)) (G.Λ (.grid i (j + 1))) (fun _ => True) ∧
    GlobalTheory.RouteSeesaw.adjM (spW₁ G i j) (negSp (spV₁ G i j)) (GlobalTheory.RouteSeesaw.botR (A := spV G i j) (B := spV₁ G i j) y) ∈
      latO (negSp (spV₁ G i j)) (spW₁ G i j) (G.Λ (.grid (i + 1) j)) (G.Λ (.grid i j)) fun _ => True}

section Vac

variable {W : G.Weil} (ρ : RealMatch W) (i j : ℕ)

def vacA : WO (spW G i j) (spX G i j) → ℂ :=
  GlobalTheory.RouteSeesaw.box2 (S := negSp (spW G i j)) (A := spV G i j) (B := spV₁ G i j) (ρ.vX i (j + 1))
    fun y => ρ.vT (i + 1) j (GlobalTheory.RouteSeesaw.adjM (spW G i j) (spV₁ G i j) y)

def vacB : WO (spW₁ G i j) (spX G i j) → ℂ :=
  GlobalTheory.RouteSeesaw.box2 (S := spW₁ G i j) (A := spV G i j) (B := spV₁ G i j) (ρ.vT i j)
    fun y => ρ.vX i j (GlobalTheory.RouteSeesaw.adjM (spW₁ G i j) (negSp (spV₁ G i j)) y)

theorem datumA_vac (t : T) : datumA W (t := t) (i := i) (j := j) (Finsupp.single (((), ρ.vX i (j + 1)), ρ.vT (i + 1) j) 1) = vacA ρ i j := by
  unfold datumA
  erw [Finsupp.sum_single_index (by exact zero_smul ℂ _), one_smul]
  rfl

theorem datumB_vac (t : T) : datumB W (t := t) (i := i) (j := j) (Finsupp.single (((), ρ.vT i j), ρ.vX i j) 1) = vacB ρ i j := by
  unfold datumB
  erw [Finsupp.sum_single_index (by exact zero_smul ℂ _), one_smul]
  rfl

end Vac

section Coord

variable (B : Frames G) (t : T) (i j : Fin D.R.m)

def frX : GL (Fin (spX G i j).rank) (EAf D) := GlobalTheory.Doubling.blkGL finSumFinEquiv (B.β i (j + 1), -B.β (i + 1) j)

variable (G) in

def colX (w : Pl D.host.E) : Fin (spX G i j).rank ≃ (locGrid G t w).Cols i j :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr (finCongr (rank_vertex G t w (X := (i, j + 1)) ⟨i.2.le, j.2⟩).symm)
    (finCongr (rank_vertex G t w (X := (i + 1, j)) ⟨i.2, j.2.le⟩).symm))

variable (G) in

def ordX (w : Pl D.host.E) :
    (locGrid G t w).Cols i j ≃ Fin ((locGrid G t w).rank (i + 1, j + 1) + (locGrid G t w).rank (i, j)) :=
  (stdSplit ((locGrid G t w).rank_square i j)).symm.trans finSumFinEquiv

variable (G) in

abbrev MatA (w : Pl D.host.E) : Type :=
  Matrix (Fin ((locGrid G t w).rank (i + 1, j + 1))) ((locGrid G t w).Cols i j) (Kw w)

variable (G) in

abbrev MatB (w : Pl D.host.E) : Type := Matrix (Fin ((locGrid G t w).rank (i, j))) ((locGrid G t w).Cols i j) (Kw w)

def linA (w : Pl D.host.E) (x : WO (spW G i j) (spX G i j)) : MatA G t i j w :=
  reindex (finCongr (rankW G t i j w)) (colX G t i j w)
    ((frMapO (spW G i j) (spX G i j) (B.β (i + 1) (j + 1)) (frX B i j) x).map (cpt w))ᵀ

def linB (w : Pl D.host.E) (y : WO (spW₁ G i j) (spX G i j)) : MatB G t i j w :=
  reindex (finCongr (rankW₁ G t i j w)) (colX G t i j w)
    ((frMapAdj (spW₁ G i j) (spX G i j) (B.β i j) (frX B i j) y).map (cpt w))

open Classical in

def prodA (ε : AE D) (Ξ : ∀ w, MatA G t i j w → ℂ) (x : WO (spW G i j) (spX G i j)) : ℂ :=
  if IsHalf ε x then ∏ w ∈ locPl G t, Ξ w (linA B t i j w x) else 0

open Classical in

def prodB (ε : AE D) (Ψ : ∀ w, MatB G t i j w → ℂ) (y : WO (spW₁ G i j) (spX G i j)) : ℂ :=
  if IsHalf (cA D ε) y then ∏ w ∈ locPl G t, Ψ w (linB B t i j w y) else 0

variable {W : G.Weil} (ρ : RealMatch W)

def IsLinA (ε : AE D) (Ξ : ∀ w, MatA G t i j w → ℂ) (F : WO (spW G i j) (spX G i j) → ℂ) : Prop :=
  IsThetaAt W.ψ (symplO (GlobalTheory.Grid.neg (spW G i j)) (spX G i j)) (heisO W.ψ (GlobalTheory.Grid.neg (spW G i j)) (spX G i j)) ε
    (homLatA G i j) 1 (vacA ρ i j) (prodA B t i j ε Ξ) F

def IsLinB (ε : AE D) (Ψ : ∀ w, MatB G t i j w → ℂ) (F : WO (spW₁ G i j) (spX G i j) → ℂ) : Prop :=
  IsThetaAt W.ψ (symplO (spW₁ G i j) (spX G i j)) (heisO W.ψ (spW₁ G i j) (spX G i j)) (cA D ε)
    (homLatB G i j) 1 (vacB ρ i j) (prodB B t i j ε Ψ) F

end Coord

section Model

variable {i j : ℕ} (e : Num G i j)

def ptA (u : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) : WO (spW G i j) (spX G i j) :=
  (HMul.hMul (uᵀ.submatrix (e.symm.trans finSumFinEquiv).symm id) (incM (GlobalTheory.Grid.sgn true (spW G i j)).gram) :
    Matrix (Fin (_ + _)) (Fin _) (AE D))

def ptB (u : Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) : WO (spW₁ G i j) (spX G i j) :=
  (HMul.hMul (uᵀ.submatrix (e.symm.trans finSumFinEquiv).symm id) (incM (spW₁ G i j).gram) :
    Matrix (Fin (_ + _)) (Fin _) (AE D))

end Model

section Charts

variable (W : G.Weil) (B : Frames G) (t : T) {i j : Fin D.R.m} (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (w : Pl D.host.E)

variable (G i j) in

abbrev ToA : Type :=
  ((Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank) → Fv D.host.F (w.under (𝓞 D.host.F))) → ℂ) →ₗ[ℂ]
    (MatA G t i j w → ℂ)

variable (G i j) in

abbrev ToB : Type :=
  ((Fin (spW₁ G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank) → Fv D.host.F (w.under (𝓞 D.host.F))) → ℂ) →ₗ[ℂ]
    (MatB G t i j w → ℂ)

def IsLinModelA (ι : ToA G t i j w) : Prop :=
  IsLagrModel Γ.M W.ψ (w.under (𝓞 D.host.F)) {u | IsHalf (atPl w 1) (ptA e u)} {u | IsHalf (cA D (atPl w 1)) (ptA e u)}
    (fun u => linA B t i j w (ptA e u)) ι

def IsLinModelB (ι : ToB G t i j w) : Prop :=
  IsLagrModel Γ.M' W.ψ (w.under (𝓞 D.host.F)) {u | IsHalf (cA D (atPl w 1)) (ptB e u)} {u | IsHalf (atPl w 1) (ptB e u)}
    (fun u => linB B t i j w (ptB e u)) ι

def IsMixModelA (ι : ToA G t i j w) : Prop :=
  IsLagrModel Γ.M W.ψ (w.under (𝓞 D.host.F)) (mixHalf e (atPl w 1)) (mixHalf e (cA D (atPl w 1))) (mixCo B t e w) ι

def IsMixModelB (ι : ToB G t i j w) : Prop :=
  IsLagrModel Γ.M' W.ψ (w.under (𝓞 D.host.F)) (mixHalfS e (atPl w 1)) (mixHalfS e (cA D (atPl w 1))) (mixCoS B t e w) ι

end Charts

section ZetaNonvanishing₂

variable (G) (t : T) (i j : Fin D.R.m) (w : Pl D.host.E)

def zetaA (Ξ : MatA G t i j w → ℂ) : GL ((locGrid G t w).Cols i j) (Kw w) → ℂ :=
  bigP (haarVol (KO (Kw w) _)) (unifAt w) (stdSplit ((locGrid G t w).rank_square i j)) ((locGrid G t w).nu i j) 1 Ξ

def zetaB (Ψ : MatB G t i j w → ℂ) : GL ((locGrid G t w).Cols i j) (Kw w) → ℂ :=
  smallP (haarVol (KO (Kw w) _)) (stdSplit ((locGrid G t w).rank_square i j)) ((locGrid G t w).nu i j)
    ((locGrid G t w).nu i j * 1) Ψ

def levVol : ℝ :=
  (haarVol (KO (Kw w) (Fin ((locGrid G t w).rank (i, j))))).real ((givenLevel G t w (i, j)).map invT : Subgroup _)

end ZetaNonvanishing₂

section Std

variable (B : Frames G) (t : T) {i j : Fin D.R.m} (X : TriG G i j) (w : Pl D.host.E)

def chA : GL (Fin ((locGrid G t w).rank (i + 1, j + 1))) (Kw w) :=
  GlobalTheory.StepData.reGL (finCongr (rankW G t i j w)) (invT ((loc w X.rA.β)⁻¹ * loc w (B.β (i + 1) (j + 1))))

def chB : GL (Fin ((locGrid G t w).rank (i, j))) (Kw w) :=
  GlobalTheory.StepData.reGL (finCongr (rankW₁ G t i j w))
    (Units.map (Matrix.scalar (Fin (spW₁ G i j).rank)).toMonoidHom
        (Units.mk0 (xiAt w) ((_root_.map_ne_zero _).2 GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero)) *
      ((loc w X.rA'.β)⁻¹ * loc w (B.β i j)))

def chX : GL ((locGrid G t w).Cols i j) (Kw w) :=
  GlobalTheory.StepData.reGL (colX G t i j w) ((loc w (frX B i j))⁻¹ * loc w X.rW.β)

def locFst (Z : MatA G t i j w) : ℂ :=
  GlobalTheory.StdPairCone.stdA ((locGrid G t w).nu i j) (unifAt w) (X.c t w) _ _
    (reindex (Equiv.refl _) (ordX G t i j w) ((chA B t X w).val * Z * (invT (chX B t X w)).val))

def locSnd (Y : MatB G t i j w) : ℂ :=
  GlobalTheory.StdPairCone.stdB ((locGrid G t w).nu i j) (unifAt w) (X.c t w) _ _
    (reindex (Equiv.refl _) (ordX G t i j w) ((chB B t X w).val * Y * (chX B t X w).val))

end Std

end GlobalTheory.TopFlip

end
