import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerProductFormula

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealEquiv

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {θ : Datum.InfFam D} {M : DSModel V S}
  {J : Set (GA D V)} {χ : GA D V → ℂ}

open Classical in

theorem list_equiv {U : MMap M} (hU : IsMultMap θ M J χ U)
    (g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : ∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ))
    (v w : M.Vec) (h : ∀ ρ, (w ρ : M.H ρ) = M.rep ρ (g ρ) (v ρ : M.H ρ)) (l : List D.what₂.Tau) (hl : l.Nodup) :
    U (fun ρ => if ρ ∈ l then w ρ else v ρ) = rTr V (l.map fun ρ => atTau θ V ρ (g ρ)).prod (U v) := by
  induction l with
  | nil =>
    funext x
    simp [rTr]
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    have e := hU.equiv a (g a) (hg a) (fun ρ => if ρ ∈ l then w ρ else v ρ) (w a) (by
      simp only [if_neg hl.1]; exact h a)
    rw [ih hl.2] at e
    have e2 : rTr V ((a :: l).map fun ρ => atTau θ V ρ (g ρ)).prod (U v) =
        rTr V (atTau θ V a (g a)) (rTr V (l.map fun ρ => atTau θ V ρ (g ρ)).prod (U v)) := by
      funext x
      simp only [rTr, List.map_cons, List.prod_cons, mul_assoc]
    rw [e2, ← e]
    congr 1
    funext ρ
    by_cases hρ : ρ = a
    · subst hρ
      simp
    · rw [Function.update_of_ne hρ]
      simp [hρ]

theorem mult_realElt : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (θ : Datum.InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ U ∈ Mult θ M J χ, ∀ g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ)) → ∀ v w : M.Vec, (∀ ρ, (w ρ : M.H ρ) = M.rep ρ (g ρ) (v ρ : M.H ρ)) → U w = rTr V (realElt θ V g) (U v) := by
  intro D V S θ M J χ U hU g hg v w h
  classical
  induction hU using Submodule.span_induction with
  | mem U hU =>
    have e := list_equiv hU g hg v w h (Finset.univ : Finset D.what₂.Tau).toList (Finset.nodup_toList _)
    rw [realElt, ← e]
    congr 1
    funext ρ
    simp
  | zero => funext x; simp [rTr]
  | add U U' _ _ h1 h2 =>
    funext x
    have a := congrFun h1 x
    have b := congrFun h2 x
    simp only [rTr, MultilinearMap.add_apply, Pi.add_apply] at a b ⊢
    rw [a, b]
  | smul c U _ h1 =>
    funext x
    have a := congrFun h1 x
    simp only [rTr, MultilinearMap.smul_apply, Pi.smul_apply] at a ⊢
    rw [a]

end GlobalTheory.RealEquiv
