import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFrameRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverRefinementExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.ConstLat GlobalTheory.WholeFlag.Glue
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConstLat.CramerFrame

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

def fnEquiv (V : Cover Y) : V.X.functionField ≃+* V.G.functionField :=
  haveI := GlobalTheory.HtGen.SplitCover.isPreimmersion_j V
  RingEquiv.ofBijective (SmallSec.fnMap V.j (GlobalTheory.HtGen.SplitCover.j_gen_specializes V))
    ⟨(SmallSec.fnMap V.j (GlobalTheory.HtGen.SplitCover.j_gen_specializes V)).injective,
      SmallSec.fnMap_surjective V.j (GlobalTheory.HtGen.SplitCover.j_gen_specializes V)⟩

theorem fnEquiv_apply (V : Cover Y) (f : V.X.functionField) :
    fnEquiv V f = SmallSec.fnMap V.j (GlobalTheory.HtGen.SplitCover.j_gen_specializes V) f := rfl

def frameC {K : Type} [Field K] {g : ℕ} (H : Matrix (Fin (g + g)) (Fin g) K) (σ : ∀ k : ℕ, Fin k → Fin (g + g))
    (k : Fin g) : Kˣ :=
  if h : minorAt H ((k : ℕ) + 1) k.2 (σ ((k : ℕ) + 1)) / minorAt H k k.2.le (σ k) ≠ 0 then
    Units.mk0 _ h else 1

def frameUm (V : Cover Y) {g : ℕ} (H : Matrix (Fin (g + g)) (Fin g) V.G.functionField)
    (σ : ∀ k : ℕ, Fin k → Fin (g + g)) : Matrix (Fin (g + g)) (Fin g) V.X.functionField :=
  (cramerCol H σ).map (fnEquiv V).symm

def frameLf (V : Cover Y) {g : ℕ} (H : Matrix (Fin (g + g)) (Fin g) V.G.functionField)
    (σ : ∀ k : ℕ, Fin k → Fin (g + g)) : Matrix (Fin g) (Fin (g + g)) V.X.functionField :=
  leftInv (frameUm V H σ) (σ g)

theorem frameC_val {K : Type} [Field K] {g : ℕ} (H : Matrix (Fin (g + g)) (Fin g) K) (σ : ∀ k : ℕ, Fin k → Fin (g + g))
    (k : Fin g) (h : minorAt H ((k : ℕ) + 1) k.2 (σ ((k : ℕ) + 1)) ≠ 0) (h' : minorAt H k k.2.le (σ k) ≠ 0) :
    (frameC H σ k : K) = minorAt H ((k : ℕ) + 1) k.2 (σ ((k : ℕ) + 1)) / minorAt H k k.2.le (σ k) := by
  unfold frameC
  rw [dif_pos (div_ne_zero h h')]
  rfl

end GlobalTheory.ConstLat.CramerFrame

end
