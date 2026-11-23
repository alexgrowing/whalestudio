import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE
import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldC
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.CompanionTheory.GodementH

section Defs

variable (F : Type) [Field F] [NumberField F] (E : Type) [Field E] [NumberField E] [Algebra F E]

def embBar (v : Pl F) : E →ₐ[F] FvBar F v := IsAlgClosed.lift

variable {F E} {J : Type} [Fintype J]

def supBar (v : Pl F) (τ : E →ₐ[F] FvBar F v) (u : J → E) : ℝ≥0 :=
  Finset.univ.sup fun f => absBar F v (τ (u f))

def locFin (σ : E →ₐ[F] E) (v : Pl F) (u : J → E) : ℝ≥0 :=
  supBar v (embBar F E v) u * supBar v ((embBar F E v).comp σ) u

open Classical in

def locInf (w : InfinitePlace F) (u : J → E) : ℝ≥0 :=
  (Finset.univ.sup fun p : EmbOver E w × J => ‖p.1.1 (u p.2)‖₊) ^ 2

def vecHt (σ : E →ₐ[F] E) (u : J → E) : ℝ≥0 := (∏ w : InfinitePlace F, locInf w u) * ∏ᶠ v, locFin σ v u

end Defs

section Minors

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}

def mnr (M : Matrix ι (Fin n) R) (f : Fin n → ι) : R := (M.submatrix f id).det

end Minors

end GlobalTheory.CompanionTheory.GodementH

end
