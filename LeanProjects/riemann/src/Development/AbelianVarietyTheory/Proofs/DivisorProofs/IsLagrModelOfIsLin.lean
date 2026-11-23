import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianLatticeLocalBases
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPairLat

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.BigNZ

open GlobalTheory.WeilM GlobalTheory.AdelicU

section Generic

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {Y : Spc F E d}

def IsFinPart (M : Model σ X Y) (T : Finset (Pl F)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) : Prop :=
  (∀ v, φ v ∈ SB (Fin n × Fin d → Fv F v)) ∧ ∀ v, v ∉ T → φ v = M.vac v

def IsLagrModel (M : Model σ X Y) (ψ : AddChar (AF F) ℂ) (v : Pl F) (A A' : Set (Matrix (Fin n) (Fin d) (AE F E)))
    {Z : Type} [TopologicalSpace Z] [Add Z] (co : Matrix (Fin n) (Fin d) (AE F E) → Z)
    (ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Z → ℂ)) : Prop :=
  Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (SB Z : Set _) ∧
  (∀ u ∈ A, ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _, Acts (evFin F v) (M.co.rho ψ u) φ φ₁ → ∀ z, ι φ₁ z = ι φ (z + co u)) ∧
  ∀ u ∈ A', ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _, Acts (evFin F v) (M.co.rho ψ u) φ φ₁ → ∀ x ∈ A,
    ι φ₁ (co x) = ψ (symp (cA σ) (-1) (incM F X.J) (incM F Y.J) x u) * ι φ (co x)

theorem isFinPart_vac {M : Model σ X Y} {ψ : AddChar (AF F) ℂ} (h : M.IsGood ψ) (T : Finset (Pl F)) : IsFinPart M T M.vac :=
  ⟨fun v => (h.vac v).1, fun _ _ => rfl⟩

theorem isLagrModel_of_isLin {M : Model σ X Y} {ψ : AddChar (AF F) ℂ} {v : Pl F} {π₁ π₀ : AE F E →+* Fv F v} {co ι}
    (h : M.IsLin ψ π₁ π₀ co ι) :
    IsLagrModel M ψ v {u | At (evFin F v) u ∧ u.map π₀ = 0} {u | At (evFin F v) u ∧ u.map π₁ = 0} co ι :=
  ⟨h.bij, fun u hu => h.trans u hu.1 hu.2, fun u hu φ hφ φ₁ hφ₁ a x hx => h.mult u hu.1 hu.2 φ hφ φ₁ hφ₁ a x hx.1 hx.2⟩

end Generic

section Grid

open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num Geo IsTripleOf mulG colV adjV₁)
open GlobalTheory.TripleSpaceW (conjSub)
open GlobalTheory.SkewLat (scLat pairLat)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def IsTied (t : T) (i j : ℕ) (e : Num G i j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : Geo G i j)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) : Prop :=
  Γ.V.L = conjSub (G.Λ (.grid (i + 1) (j + 1))) ∧
  Γ.W.L = pairLat (scLat D.host.AA (G.Λ (.grid i (j + 1)))) (conjSub (scLat D.host.AA (conjSub (G.Λ (.grid (i + 1) j))))) e ∧
  (∀ v, v ∈ X.T ↔ ∃ w ∈ locPl G t, w.under (𝓞 D.host.F) = v) ∧
  ∀ v : Bs.P, ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) = v.1 → splitPrime (Bs.τ v) = w

variable {i j : ℕ}

def mixHalf (e : Num G i j) (ε : AE D) :
    Set (Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :=
  {u | IsHalf ε (mulG (negSp (spW G i j)) (colV e u)ᵀ) ∧ IsHalf ε (adjV₁ e u)}

def mixCo (B : Frames G) (t : T) {i j : Fin D.R.m} (e : Num G i j) (w : Pl D.host.E)
    (u : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :
    Matrix (Fin ((locGrid G t w).rank (i + 1, j + 1))) ((locGrid G t w).Cols i j) (Kw w) :=
  fromCols (B.coord t w (X := (i, j + 1)) (Y := (i + 1, j + 1)) ⟨i.2.le, j.2⟩ ⟨i.2, j.2⟩
      ((mulG (negSp (spW G i j)) (colV e u)ᵀ).map fun a => cpt w (toEAf D a)))
    (B.coord t w (X := (i + 1, j + 1)) (Y := (i + 1, j)) ⟨i.2, j.2⟩ ⟨i.2, j.2.le⟩ ((adjV₁ e u).map fun a => cpt w (toEAf D a)))ᵀ

def IsLocFn (W : G.Weil) (B : Frames G) (t : T) {i j : Fin D.R.m} (e : Num G i j) (Γ : Geo G i j) (w : Pl D.host.E)
    (v : Pl D.host.F) (Ψ : Matrix (Fin ((locGrid G t w).rank (i + 1, j + 1))) ((locGrid G t w).Cols i j) (Kw w) → ℂ)
    (φ : (Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank) → Fv D.host.F v) → ℂ) : Prop :=
  φ ∈ SB _ ∧ ∃ ι, IsLagrModel Γ.M W.ψ v (mixHalf e (atPl w 1)) (mixHalf e (cA D (atPl w 1))) (mixCo B t e w) ι ∧ ι φ = Ψ

end Grid

end GlobalTheory.BigNZ

end
