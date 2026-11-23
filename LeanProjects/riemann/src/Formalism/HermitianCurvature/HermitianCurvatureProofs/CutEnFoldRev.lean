import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnCVLocal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OperatorPreservesFusionForms
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtFsvOther
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralIdentities

open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.En

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem cV_smul {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (Y α : ℂ) (f : B.Mat k r → E) :
    Q.CV k r Y (α • f) = α • Q.CV k r Y f :=
  Formalism.FourierDecayAlt.P5.qminorOp_smulC (Formalism.FourierDecayAlt.P5.eH_smulC (k := k) (r := r)) _ _ _ α f

section fold

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Q.Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} {Dm : Set (Q.Mx k r)}

theorem ckOn_of_ffl {J : Q.Mx k r → (Wq →L[ℂ] Wp)} (hJ : J ∈ Q.FFl k r z z' π π' 0 Dm) :
    B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (Dm ∩ B.GV k r) J := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hc, he⟩ := hJ.1 g₀ ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hg₀.2, hg₀.1⟩
  exact ⟨U, F, hU, hgU, hc.of_le (by exact_mod_cast le_top), fun g hg hgG => he g hg (Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hgG)⟩

theorem letter_congr (hCL : CVLocal) (hDm : IsOpen Dm) {J₁ J₂ : Q.Mx k r → (Wq →L[ℂ] Wp)}
    (h₁ : J₁ ∈ Q.FFl k r z z' π π' 0 Dm) (h₂ : J₂ ∈ Q.FFl k r z z' π π' 0 Dm)
    (he : ∀ g ∈ Q.Glev k r 0 ∩ Dm, J₁ g = J₂ g) (Y : ℝ) (s : ℂ) :
    ∀ g ∈ Q.Glev k r 0 ∩ Dm, (s • Q.CV k r (Y : ℂ) J₁) g = (s • Q.CV k r (Y : ℂ) J₂) g := by
  intro g hg
  have := hCL k r _ Dm J₁ J₂ (Y : ℂ) hDm (ckOn_of_ffl h₁) (ckOn_of_ffl h₂)
    (fun x hx => he x ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hx.2, hx.1⟩) g ⟨hg.2, hg.1.1⟩
  simp only [Pi.smul_apply, this]

theorem letter_swap (hDm : IsOpen Dm) {J : Q.Mx k r → (Wq →L[ℂ] Wp)} (hJ : J ∈ Q.FFl k r z z' π π' 0 Dm)
    (x y : ℝ) (s : ℂ) : ∀ g ∈ Q.Glev k r 0 ∩ Dm,
      (s • Q.CV k r (x : ℂ) (s • Q.CV k r (y : ℂ) J)) g = (s • Q.CV k r (y : ℂ) (s • Q.CV k r (x : ℂ) J)) g := by
  intro g hg
  simp only [cV_smul, Pi.smul_apply]
  unfold Q.CV
  rw [Formalism.FourierDecayAlt.P.capelli_commutation _ k r 0 Dm J hDm hJ.1 g hg]

theorem foldCV_append (s : ℂ) (l₁ l₂ : List C.Letter) (J : Q.Mx k r → (Wq →L[ℂ] Wp)) :
    foldCV k r s (l₁ ++ l₂) J = foldCV k r s l₁ (foldCV k r s l₂ J) := by
  unfold foldCV; rw [List.foldr_append]

end fold

theorem foldRev_of (hCL : CVLocal) : FoldRev := by
  intro k r Wp Wq _ _ _ _ z z' π π' Dm hDm hcl J hJ s a
  have hcomm : ∀ (b : List C.Letter) (J : Q.Mx k r → (Wq →L[ℂ] Wp)), J ∈ Q.FFl k r z z' π π' 0 Dm →
      ∀ x : C.Letter, ∀ g ∈ Q.Glev k r 0 ∩ Dm,
        foldCV k r s b (s • Q.CV k r (x.2 : ℂ) J) g = (s • Q.CV k r (x.2 : ℂ) (foldCV k r s b J)) g := by
    intro b
    induction b with
    | nil => intro J _ x g _; rfl
    | cons y b ih =>
      intro J hJ x g hg
      have h1 := letter_congr hCL hDm (foldCV_mem hcl (hcl J hJ x.2 s) s b)
        (hcl _ (foldCV_mem hcl hJ s b) x.2 s) (ih J hJ x) y.2 s g hg
      have h2 := letter_swap hDm (foldCV_mem hcl hJ s b) y.2 x.2 s g hg
      rw [foldCV_cons, h1, h2]
      rfl
  induction a generalizing J with
  | nil => intro g _; rfl
  | cons x a ih =>
    intro g hg
    rw [List.reverse_cons, foldCV_append]
    rw [ih (foldCV k r s [x] J) (hcl J hJ x.2 s) g hg]
    exact hcomm a J hJ x g hg

theorem folding_reversal_holds : FoldRev := foldRev_of coefficient_vector_locality

end Formalism.FourierDecayAlt.P.CutMP.En
