import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TrueWtAddSSNonneg
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMulOfApprox

noncomputable section

namespace GlobalTheory.GO

open NumberField Formalism.L2.Col Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Forms

section Exp

open MvPolynomial Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint

variable {ι : Type} [Fintype ι] {a b : ℕ}

def expFn (r : ℂ) (ap : ι → Matrix (Fin a) (Fin b) ℂ) (z : VCx ι a b) : ℂ :=
  r * Complex.exp (∑ k : DVar ι a b, ap k.1 k.2.2 k.2.1 * z k.1 k.2.1 k.2.2)

def inclMat (K : Type) [Field K] (ι : Type) (a b : ℕ) : ι → Matrix (Fin a) (Fin b) K := fun _ α β => if (α : ℕ) = β then 1 else 0

end Exp

namespace ChSrc

open Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint

variable {X : Fields} {R : Ranks} (σ : X.K →+* ℂ)

theorem jetInVV_trueWt (hc : X.Tau → HCParam R) {i : ℕ} (hi : i < R.m) : JetInVV X.K (trueWt hc i) (trueWt hc (i + 1)) (nuEnd hc i) := by
  have hab : R.N i < R.N (i + 1) := by
    simp only [Ranks.N]
    nlinarith
  have hW : WtCompat hab (trueWt hc i) (trueWt hc (i + 1)) (sD hc i) (sS hc i) (nuEnd hc i) := by
    refine ⟨fun τ a => ?_, fun τ j hj => trueWt_new hc hi τ j (by omega), fun τ => nuEnd_cast hc hi τ⟩
    have h1 := trueWt_old hc hi τ (Fin.castLE hab.le a) (by simp)
    simp only [Fin.coe_castLE] at h1
    rw [h1]
    ring
  haveI : Infinite X.K := Infinite.of_injective (Nat.cast : ℕ → X.K) Nat.cast_injective
  intro J P hP
  exact GlobalTheory.JetPoint.jetMap_mem hab.le (nuEnd hc i) P _
    (fun ap => GlobalTheory.SubstMem.substAdj_sharp_mem X.K X.Tau _ _ hab _ _ _ _ _ hW ap P hP) J

def exampleJetChain (hc : X.Tau → HCParam R) : ChSrc X R :=
  { toyExample hc with
    kk := fun i _ _ =>
      { k := fun _ _ => jetOp (trueWt hc i) (trueWt hc (i + 1)) (ptTable (inclMat X.K X.Tau _ _)) (nuEnd hc i)
        equiv := fun _ _ _ _ => rfl } }

def toyExpThetaFamily (hc : X.Tau → HCParam R) : (exampleJetChain hc).ThFam := fun _ _ _ => expFn Complex.I (inclMat ℂ X.Tau _ _)

end ChSrc

end GlobalTheory.GO
