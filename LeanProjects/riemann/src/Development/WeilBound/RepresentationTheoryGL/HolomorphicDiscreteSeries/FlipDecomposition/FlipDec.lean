import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.FlipDecomposition.FlipDecAlt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlipUSymmCont

noncomputable section

open Matrix Finset
open scoped InnerProductSpace

namespace PositivityTheory.RgHe.Dec

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition

section Flip

variable {m : ℕ}

theorem flip_he (ε : Fin m → Bool) : ∀ a, (fun a => !ε a) a = !ε a := fun _ => rfl

theorem smoothOnH_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (J : Matrix (Fin m) (Fin m) ℂ)
    (f : Matrix (Fin m) (Fin m) ℂ → E) : PI.PhMeasCore.SmoothOnH (-J) f ↔ PI.PhMeasCore.SmoothOnH J f := by
  have key : ∀ g : Matrix (Fin m) (Fin m) ℂ, gᴴ * -J * g = -J ↔ gᴴ * J * g = J := by
    intro g
    rw [Matrix.mul_neg, Matrix.neg_mul, neg_inj]
  unfold PI.PhMeasCore.SmoothOnH PI.PhMeasCore.UH
  simp only [Set.mem_setOf_eq, key]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem mem_smoothVecs_flip (ε : Fin m → Bool) (π : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)) (v : H) :
    v ∈ PI.PhMeasCore.smoothVecs (Jm (fun a => !ε a)) π ↔ v ∈ PI.PhMeasCore.smoothVecs (Jm ε) π := by
  simp only [PI.PhMeasCore.smoothVecs, Set.mem_setOf_eq]
  rw [GlobalTheory.CompanionTheory.NegDS.Jm_flip (ε := ε) (ε' := fun a => !ε a) (fun a => rfl)]
  exact smoothOnH_neg _ _

theorem mem_SmT_flip (ε : Fin m → Bool) (π : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)) (x : Fin m → H) :
    x ∈ SmT (fun a => !ε a) π ↔ x ∈ SmT ε π := by
  simp only [SmT, Set.mem_setOf_eq, mem_smoothVecs_flip]

theorem thetaJ_flip (ε : Fin m → Bool) (Y : Matrix (Fin m) (Fin m) ℂ) :
    PI.DSInfCharCap.thetaJ (fun a => !ε a) Y = PI.DSInfCharCap.thetaJ ε Y := by
  unfold PI.DSInfCharCap.thetaJ
  rw [GlobalTheory.CompanionTheory.NegDS.Jm_flip (ε := ε) (ε' := fun a => !ε a) (fun a => rfl)]
  simp [Matrix.mul_neg, Matrix.neg_mul]

theorem dsigC_flip (ε : Fin m → Bool) (σ : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)) (Y : Matrix (Fin m) (Fin m) ℂ) (v : H) :
    PI.DSInfCharCap.dsigC (fun a => !ε a) σ Y v = PI.DSInfCharCap.dsigC ε σ Y v := by
  simp only [PI.DSInfCharCap.dsigC, thetaJ_flip]

theorem casT_flip (ε : Fin m → Bool) (π : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)) (x : Fin m → H) :
    casT (fun a => !ε a) π x = casT ε π x := by
  funext c
  simp only [casT, dsigC_flip]

theorem formT_flip (ε : Fin m → Bool) (y x : Fin m → H) : formT (fun a => !ε a) y x = -formT ε y x := by
  unfold formT
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro l _
  by_cases h : ε l = true <;> simp [h]

theorem isDS_of_flip {ε : Fin m → Bool} {lam : Fin m → ℝ} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    {σ : Matrix (Fin m) (Fin m) ℂ → (K →L[ℂ] K)} (h : IsDS (fun a => !ε a) lam σ) : IsDS ε lam σ := by
  have h2 := GlobalTheory.CompanionTheory.NegDS.isDS_flip m K (fun a => !ε a) lam σ h
  simp only [Bool.not_not] at h2
  exact h2

end Flip

theorem flip_decomposition_holds : FlipDec := by
  intro m ε lam H _ _ π X hF
  let Y : Dec ε lam π :=
    { S := X.S
      Hs := X.Hs
      nH := X.nH
      iH := X.iH
      cH := X.cH
      πs := X.πs
      ds := fun s hs => ⟨(X.ds s hs).1, isDS_of_flip (X.ds s hs).2⟩
      p := X.p
      pr := X.pr
      c := fun s => -X.c s
      κ := X.κ
      p_sm := fun s hs x hx => (mem_SmT_flip ε π _).1 (X.p_sm s hs x ((mem_SmT_flip ε π x).2 hx))
      sum := fun x hx => X.sum x ((mem_SmT_flip ε π x).2 hx)
      p_act := fun s hs g x hx =>
        X.p_act s hs ((GlobalTheory.CompanionTheory.NegDS.flipU (flip_he ε)).symm g) x ((mem_SmT_flip ε π x).2 hx)
      pr_act := fun s hs g x hx =>
        X.pr_act s hs ((GlobalTheory.CompanionTheory.NegDS.flipU (flip_he ε)).symm g) x ((mem_SmT_flip ε π x).2 hx)
      form := fun s hs x hx y hy => by
        have h := X.form s hs x ((mem_SmT_flip ε π x).2 hx) y ((mem_SmT_flip ε π y).2 hy)
        rw [formT_flip] at h
        rw [neg_mul, ← h, neg_neg]
      cas := fun s hs x hx => by
        have h := X.cas s hs x ((mem_SmT_flip ε π x).2 hx)
        rwa [casT_flip] at h
      κ_inj := X.κ_inj }
  exact ⟨Y, hF⟩

end PositivityTheory.RgHe.Dec
