import Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorIsomorphismLevels
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFCstmt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftClosedUnderOperations

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBFV

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

section Supp

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem uInv_zero_at (s : ℂ) (g : B.Mat k r) :
    ∀ (w : List C.Letter) (x : Wd.Ix (Fin w.length) → B.Mat k r → (Wq →L[ℂ] Wp)),
      (∀ e', x e' g = 0) → ∀ e, KB.uInv s w x e g = 0
  | [], x, hx, e => hx e
  | l :: w, x, hx, e => by
    have h0 := uInv_zero_at s g w (fun e' => x (Fin.cons (0 : Fin 2) e')) (fun e' => hx _)
    have h1 := uInv_zero_at s g w (fun e' => x (Fin.cons (1 : Fin 2) e')) (fun e' => hx _)
    show (if e (0 : Fin (w.length + 1)) = 0 then KB.uInv s w (fun e' => x (Fin.cons (0 : Fin 2) e')) (fun a => e a.succ)
      else KB.uInv s w (fun e' => x (Fin.cons (1 : Fin 2) e')) (fun a => e a.succ) +
        (if l.1 then s else (starRingEnd ℂ) s) • KB.uInv s w (fun e' => x (Fin.cons (0 : Fin 2) e')) fun a => e a.succ) g = 0
    split_ifs <;> simp only [Pi.add_apply, Pi.smul_apply, h0, h1, smul_zero, add_zero]

theorem waveG_bs (Bs : B.RealPlaceData k r Wp Wq) (s : ℂ) (w : List C.Letter)
    (x : Wd.Ix (Fin w.length) → B.Mat k r → (Wq →L[ℂ] Wp)) (R : ℝ)
    (hx : ∀ e, ∀ g ∈ B.GV k r, x e g ≠ 0 → B.gN g ≤ R) :
    ∀ e, ∀ g ∈ B.GV k r, KB.waveG Bs s w x e g ≠ 0 → B.gN g ≤ R := by
  intro e g hg hne
  by_contra hR
  apply hne
  have hz : ∀ e', x e' g = 0 := fun e' => by
    by_contra h
    exact hR (hx e' g hg h)
  show P5.fsv s _ • KB.uInv s w x e g = 0
  rw [uInv_zero_at s g w x hz e, smul_zero]

theorem nice_mono {Bs : B.RealPlaceData k r Wp Wq} {F : B.Mat k r → (Wq →L[ℂ] Wp)} {ε ε' : ℝ} (h : ε' ≤ ε)
    (hF : JC.NiceCoef Bs ε F) : JC.NiceCoef Bs ε' F :=
  ⟨hF.1, hF.2.1, fun g hg hne => h.trans (hF.2.2 g hg hne)⟩

theorem common_R {ι : Type*} [Fintype ι] (F : ι → B.Mat k r → (Wq →L[ℂ] Wp))
    (h : ∀ i, ∃ R : ℝ, ∀ g ∈ B.GV k r, F i g ≠ 0 → B.gN g ≤ R) :
    ∃ R : ℝ, ∀ i, ∀ g ∈ B.GV k r, F i g ≠ 0 → B.gN g ≤ R := by
  classical
  choose R hR using h
  refine ⟨∑ i, |R i|, fun i g hg hne => (hR i g hg hne).trans ?_⟩
  exact (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |R i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i))

end Supp

end Formalism.FourierDecayAlt.P.PBFV
