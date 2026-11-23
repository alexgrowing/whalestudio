import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocPt

noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.VacLine

variable {F : Type} [Field F] [NumberField F]

def mkPt {κ : Type} (x : κ → mixedEmbedding.mixedSpace F) (y : κ → Af F) : κ → AF F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), y i)

def slice {κ : Type} (Φ : (κ → AF F) → ℂ) (x : κ → mixedEmbedding.mixedSpace F) : (κ → Af F) → ℂ :=
  fun y => Φ (mkPt x y)

def finOp (ψ : AddChar (AF F) ℂ) (v : Pl F) {κ : Type} [Fintype κ] (p : (κ → Fv F v) × (κ → Fv F v))
    (g : (κ → Af F) → ℂ) : (κ → Af F) → ℂ :=
  fun y => psiLoc ψ v ((fun i => evalV F v (y i)) ⬝ᵥ p.2 + p.1 ⬝ᵥ p.2 / 2) * g (y + fun i => singleFin v (p.1 i))

def vacProd {κ : Type} (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) : (κ → Af F) → ℂ :=
  fun y => ∏ᶠ v, φ v fun i => evalV F v (y i)

theorem evI_mkPt {κ : Type} (x : κ → mixedEmbedding.mixedSpace F) (y : κ → Af F) (i : κ) :
    evI F (mkPt x y i) = x i := by
  simp [mkPt, evI]

theorem evFin_mkPt {κ : Type} (x : κ → mixedEmbedding.mixedSpace F) (y : κ → Af F) (i : κ) (v : Pl F) :
    evFin F v (mkPt x y i) = evalV F v (y i) := rfl

theorem mkPt_eq {κ : Type} (z : κ → AF F) : mkPt (fun i => evI F (z i)) (fun i => (z i).2) = z := by
  funext i
  show ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1), (z i).2) = z i
  rw [RingEquiv.symm_apply_apply]
  rfl

theorem pure_mkPt {κ : Type} [Fintype κ] (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ)
    (x : κ → mixedEmbedding.mixedSpace F) (y : κ → Af F) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ (mkPt x y) = f x * vacProd φ y := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure vacProd
  simp only [evI_mkPt, evFin_mkPt]

theorem at_latAtV {E : Type} [Field E] [NumberField E] [Algebra F E] {n d : ℕ} {X : Spc F E n}
    {W : Spc F E d} {v : Pl F} {γ : Matrix (Fin n) (Fin d) (AE F E)} (hγ : γ ∈ latAtV X W v) :
    At (evFin F v) γ := by
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, -, x, -, y, -, rfl⟩ := hz
    intro u hu
    rw [← smul_assoc, ha u hu, zero_smul]
  | zero => intro u _; exact smul_zero u
  | add z z' _ _ hz hz' => intro u hu; rw [smul_add, hz u hu, hz' u hu, add_zero]
  | neg z _ hz => intro u hu; rw [smul_neg, hz u hu, neg_zero]

end GlobalTheory.VacLine
