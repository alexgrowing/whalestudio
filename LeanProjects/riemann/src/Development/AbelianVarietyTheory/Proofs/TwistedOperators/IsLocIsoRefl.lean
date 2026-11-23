import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FlipMatch

section Generic

def pairM {k A C : Type} [CommRing k] [Fintype A] [Fintype C] (X Y : Matrix A C k) : k := ∑ i, ∑ j, X i j * Y i j

def chart {k k' A C A' C' : Type} [Field k] [Field k'] [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]
    (j : k ≃+* k') (eA : A ≃ A') (eC : C ≃ C') (g : GL A k') (h : GL C k') (X : Matrix A C k) : Matrix A' C' k' :=
  reindex eA eC (g.val * X.map j * h.val)

def IsLocIso {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [Field k'] [ValuativeRel k'] [TopologicalSpace k']
    (j : k ≃+* k') : Prop :=
  Continuous j ∧ Continuous j.symm ∧ ∀ x, j x ∈ (ValuativeRel.valuation k').integer ↔ x ∈ (ValuativeRel.valuation k).integer

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def coX {n d : ℕ} {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
    (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) : Matrix (Fin n) (Fin d) (Fv F v) :=
  (b⁻¹).1 * u.map (piW t) * (c⁻¹).1ᵀ

def coY (σ : E →ₐ[F] E) {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (t : E →ₐ[F] Fv F v)
    (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)) (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) :
    Matrix (Fin n) (Fin d) (Fv F v) :=
  -(b.1ᵀ * X.J.map t * u.map (piW (t.comp σ)) * (Y.J.map t)ᵀ * c.1)

def IsMixChart {n d : ℕ} (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (A A' : Set (Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)))
    {k R C : Type} [Add k] [Zero k] (co tr mu : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) → Matrix R C k) (P : Finset C) : Prop :=
  (∀ u ∈ A, At (evFin F v) u ∧ (∀ r, ∀ s ∈ P, tr u r s = 0) ∧ (∀ r, ∀ s ∉ P, mu u r s = 0) ∧ co u = tr u + mu u) ∧
    ∀ u ∈ A', At (evFin F v) u ∧ (∀ r, ∀ s ∉ P, tr u r s = 0) ∧ ∀ r, ∀ s ∈ P, mu u r s = 0

end Generic

section Grid

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def mixHalfS {i j : ℕ} (e : Num G i j) (ε : AE D) :
    Set (Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :=
  {u | IsHalf ε (mulG (spW₁ G i j) (colV e u)ᵀ) ∧ IsHalf ε (adjV₁ e u)}

def mixCoS (B : Frames G) (t : T) {i j : Fin D.R.m} (e : Num G i j) (w : Pl D.host.E)
    (u : Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :
    Matrix (Fin ((locGrid G t w).rank (i, j))) ((locGrid G t w).Cols i j) (Kw w) :=
  fromCols (B.coord t w (X := (i, j + 1)) (Y := (i, j)) ⟨i.2.le, j.2⟩ ⟨i.2.le, j.2.le⟩
      ((mulG (spW₁ G i j) (colV e u)ᵀ).map fun a => cpt w (toEAf D a)))
    (B.coord t w (X := (i, j)) (Y := (i + 1, j)) ⟨i.2.le, j.2.le⟩ ⟨i.2, j.2.le⟩ ((adjV₁ e u).map fun a => cpt w (toEAf D a)))ᵀ

def colsEq (t : T) {i j : Fin D.R.m} (e : Num G i j) (w : Pl D.host.E) :
    Fin ((spW G i j).rank + (spW₁ G i j).rank) ≃ (locGrid G t w).Cols i j :=
  e.symm.trans (Equiv.sumCongr (finCongr (rank_vertex G t w (X := (i, j + 1)) ⟨i.2.le, j.2⟩).symm)
    (finCongr (rank_vertex G t w (X := (i + 1, j)) ⟨i.2, j.2.le⟩).symm))

variable (G) in

theorem rankW (t : T) (i j : Fin D.R.m) (w : Pl D.host.E) : (spW G i j).rank = (locGrid G t w).rank (i + 1, j + 1) := by
  rw [rank_vertex G t w (X := ((i : ℕ) + 1, (j : ℕ) + 1)) ⟨Nat.succ_le_of_lt i.2, Nat.succ_le_of_lt j.2⟩]

variable (G) in

theorem rankW₁ (t : T) (i j : Fin D.R.m) (w : Pl D.host.E) : (spW₁ G i j).rank = (locGrid G t w).rank (i, j) := by
  rw [rank_vertex G t w (X := ((i : ℕ), (j : ℕ))) ⟨le_of_lt i.2, le_of_lt j.2⟩]

def IsPlaceIso {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (w : Pl D.host.E) (j : Fv D.host.F v ≃+* Kw w) : Prop :=
  ∀ a : AE D, j (piW τ a) = cpt w (toEAf D a)

def xiAt (w : Pl D.host.E) : Kw w := algebraMap D.host.E (Kw w) D.host.xi0

def basCols (B : Frames G) {i j : ℕ} (e : Num G i j) (w : Pl D.host.E) :
    Matrix (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Kw w) :=
  GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e (loc w (B.β i (j + 1))).val (-(loc w (B.β (i + 1) j)).val)

def IsDoublyCompatible (t : T) (i j : ℕ) (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : Chars D.host.F D.host.E) : Prop :=
  IsTied t i j e Bs Γ X ∧ Γ.V'.L = GlobalTheory.TripleSpaceW.conjSub (G.Λ (.grid i j))

end Grid

end GlobalTheory.FlipMatch

end
