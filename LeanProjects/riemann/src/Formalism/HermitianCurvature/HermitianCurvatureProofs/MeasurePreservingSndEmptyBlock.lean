import Formalism.HermitianCurvature.HermitianCurvatureProofs.OuterProductMatrix

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

set_option linter.style.haveILetI false

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Dx2.Split Dx2.SplitM

variable {k j ρ : ℕ}

def tauB (a : Fin 1 → Fin j → ℂ) : Fin j → Fin 1 → ℂ := fun i _ => star (a 0 i)

theorem bC_eq (x : U.RC k j (1 + ρ)) : bC x = tauB (aC x) := by
  funext i b
  have hb : b = 0 := Subsingleton.elim _ _
  subst hb
  simp [bC, tauB]

theorem tauB_mp : MeasurePreserving (tauB (j := j)) volume volume := by
  have u1 := measurePreserving_funUnique (volume : Measure (Fin j → ℂ)) (Fin 1)
  have u2 : MeasurePreserving (fun (v : Fin j → ℂ) (i : Fin j) => (MeasurableEquiv.funUnique (Fin 1) ℂ).symm (v i))
      volume volume :=
    measurePreserving_pi (fun _ => (volume : Measure ℂ)) (fun _ => (volume : Measure (Fin 1 → ℂ)))
      (f := fun _ => (MeasurableEquiv.funUnique (Fin 1) ℂ).symm)
      (fun _ => (measurePreserving_funUnique (volume : Measure ℂ) (Fin 1)).symm)
  have h := u2.comp (vconj_mp.comp u1)
  have e : (tauB (j := j)) =
      (fun (v : Fin j → ℂ) (i : Fin j) => (MeasurableEquiv.funUnique (Fin 1) ℂ).symm (v i)) ∘
        (fun v : Fin j → ℂ => star v) ∘ ⇑(MeasurableEquiv.funUnique (Fin 1) (Fin j → ℂ)) := by
    funext a i l
    rfl
  rw [e]; exact h

theorem PsiR_mp : MeasurePreserving (fun z : U.RC k j (1 + ρ) × U.RC k 1 ρ => (XC z.1 z.2, bC z.1)) volume volume := by
  haveI : SigmaFinite (volume : Measure (G.UT (j + 1) → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin (j + 1) → ℝ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin (2 * ρ + k + 1) → Fin (j + 1) → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure ((G.UT (j + 1) → ℂ) × (Fin (j + 1) → ℝ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.RC k (j + 1) ρ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin 1 → Fin j → ℂ)) := inferInstance
  have h := ((MeasurePreserving.id (volume : Measure (U.RC k (j + 1) ρ))).prod tauB_mp).comp PsiL_mp
  have e : (fun z : U.RC k j (1 + ρ) × U.RC k 1 ρ => (XC z.1 z.2, bC z.1)) =
      Prod.map id tauB ∘ (fun z : U.RC k j (1 + ρ) × U.RC k 1 ρ => (XC z.1 z.2, aC z.1)) := by
    funext z; simp [bC_eq]
  rw [e]; exact h

theorem measurePreserving_snd_empty_block (σ : Equiv.Perm (Fin j)) :
    MeasurePreserving (fun η : U.XiH j 0 σ => η.2) volume volume := by
  have h0 : IsProbabilityMeasure (volume : Measure (Fin 0 → ℂ)) := by
    rw [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_of_empty]
    infer_instance
  have h1 : IsProbabilityMeasure (volume : Measure (Fin 0 → Fin j → ℂ)) := by
    rw [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_of_empty]
    infer_instance
  have h2 : IsProbabilityMeasure (volume : Measure (Fin j → Fin 0 → ℂ)) := by
    rw [MeasureTheory.volume_pi]
    infer_instance
  have h3 : IsProbabilityMeasure (volume : Measure ((Fin 0 → Fin j → ℂ) × (Fin j → Fin 0 → ℂ))) := by
    rw [MeasureTheory.Measure.volume_eq_prod]
    infer_instance
  exact MeasureTheory.measurePreserving_snd

end Formalism.FourierDecayAlt.P.PBH

namespace Formalism.FourierDecayAlt.P.PBH

open Dx2.Split Dx2.SplitM

variable {k j ρ : ℕ}

def TQ (σ : Equiv.Perm (Fin j)) (p : (U.RC k 1 ρ × U.RC k 1 ρ) × U.Xi k j 0 (1 + ρ) σ) : U.Xi k j 1 ρ σ :=
  ((XC p.2.1.1 p.1.1, XC p.2.1.2 p.1.2), ((aC p.2.1.1, bC p.2.1.2), p.2.2.2))

theorem TQ_mp (σ : Equiv.Perm (Fin j)) :
    MeasurePreserving (TQ (k := k) (ρ := ρ) σ) (((U.muRC k 1 ρ).prod (U.muRC k 1 ρ)).prod (U.muXi k j 0 (1 + ρ) σ))
      (U.muXi k j 1 ρ σ) := by
  haveI : SigmaFinite (volume : Measure (G.UT (j + 1) → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin (j + 1) → ℝ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin (2 * ρ + k + 1) → Fin (j + 1) → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure ((G.UT (j + 1) → ℂ) × (Fin (j + 1) → ℝ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.RC k (j + 1) ρ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (G.UT j → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin j → ℝ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin (2 * (1 + ρ) + k + 1) → Fin j → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure ((G.UT j → ℂ) × (Fin j → ℝ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.RC k j (1 + ρ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (G.UT 1 → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin 1 → ℝ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin (2 * ρ + k + 1) → Fin 1 → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure ((G.UT 1 → ℂ) × (Fin 1 → ℝ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.RC k 1 ρ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin 1 → Fin j → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin j → Fin 1 → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.LW σ → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure ((U.LW σ → ℂ) × (G.UT j → ℂ))) := inferInstance
  haveI : SigmaFinite (volume : Measure ((Fin 0 → Fin j → ℂ) × (Fin j → Fin 0 → ℂ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.XiH j 0 σ)) := inferInstance
  set μX := (volume : Measure (U.RC k j (1 + ρ)))
  set μY := (volume : Measure (U.RC k 1 ρ))
  set μH := (volume : Measure (U.XiH j 0 σ))
  set μXC := (volume : Measure (U.RC k (j + 1) ρ))
  set μA := (volume : Measure (Fin 1 → Fin j → ℂ))
  set μB := (volume : Measure (Fin j → Fin 1 → ℂ))
  set μHr := (volume : Measure ((U.LW σ → ℂ) × (G.UT j → ℂ)))
  have s1 := Measure.measurePreserving_swap (μ := μY.prod μY) (ν := (μX.prod μX).prod μH)
  have s2 := measurePreserving_prodAssoc (μX.prod μX) μH (μY.prod μY)
  have s3 := (MeasurePreserving.id (μX.prod μX)).prod (Measure.measurePreserving_swap (μ := μH) (ν := μY.prod μY))
  have s4 := (measurePreserving_prodAssoc (μX.prod μX) (μY.prod μY) μH).symm
  have s5 := (middle_four_swap_measure_preserving μX μX μY μY).prod (MeasurePreserving.id μH)
  have c1 := ((PsiL_mp (k := k) (j := j) (ρ := ρ)).prod (PsiR_mp (k := k) (j := j) (ρ := ρ))).prod (measurePreserving_snd_empty_block σ)
  have t1 := (middle_four_swap_measure_preserving μXC μA μXC μB).prod (MeasurePreserving.id μHr)
  have t2 := measurePreserving_prodAssoc (μXC.prod μXC) (μA.prod μB) μHr
  have h := t2.comp (t1.comp (c1.comp (s5.comp (s4.comp (s3.comp (s2.comp s1))))))
  exact h

end Formalism.FourierDecayAlt.P.PBH

namespace Formalism.FourierDecayAlt.P.PBH

open Dx2.Split Dx2.SplitM

theorem pointStep : PointStep := by
  intro k j ρ σ d hd c hc zA zA' hzA hzA' E _ _ _ F γ hint
  set Gi : U.Xi k j 1 ρ σ → E := fun ξ => U.psiStar k ρ σ zA zA' ξ • F (U.gaXi k ρ σ d ξ (fun _ _ => c) γ) with hGi
  have hT := TQ_mp (k := k) (ρ := ρ) σ
  haveI : SigmaFinite (volume : Measure (G.UT j → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin j → ℝ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin (2 * (1 + ρ) + k + 1) → Fin j → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure ((G.UT j → ℂ) × (Fin j → ℝ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.RC k j (1 + ρ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (G.UT 1 → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin 1 → ℝ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin (2 * ρ + k + 1) → Fin 1 → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure ((G.UT 1 → ℂ) × (Fin 1 → ℝ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.RC k 1 ρ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.LW σ → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure ((U.LW σ → ℂ) × (G.UT j → ℂ))) := inferInstance
  haveI : SigmaFinite (volume : Measure ((Fin 0 → Fin j → ℂ) × (Fin j → Fin 0 → ℂ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.XiH j 0 σ)) := inferInstance
  haveI : SigmaFinite ((volume : Measure (U.RC k j (1 + ρ))).prod (volume : Measure (U.RC k j (1 + ρ)))) :=
    inferInstance
  haveI : SFinite (U.muXi k j 0 (1 + ρ) σ) := by
    unfold U.muXi U.muRC U.muXiH; infer_instance
  haveI : SFinite ((U.muRC k 1 ρ).prod (U.muRC k 1 ρ)) := by
    unfold U.muRC; infer_instance
  have hpt : ∀ p : (U.RC k 1 ρ × U.RC k 1 ρ) × U.Xi k j 0 (1 + ρ) σ, Gi (TQ σ p) =
      (psi k (1 + ρ) (U.lowV k j (1 + ρ) (D.castV (hsv k j ρ) zA)) cStd (U.Rn k 1 ρ p.1.1) *
        star (psi k (1 + ρ) (U.lowV k j (1 + ρ) (D.castV (hsv k j ρ) zA')) cStd (U.Rn k 1 ρ p.1.2))) •
      (U.psiStar (p := j) (s := 0) k (1 + ρ) σ (D.castV (hsv k j ρ) zA) (D.castV (hsv k j ρ) zA') p.2 •
        D.castF (hs' k j ρ) F (U.gaXi (p := j) (s := 0) k (1 + ρ) σ d p.2 (fun a => a.elim0)
          ((U.Rn k 1 ρ p.1.1)⁻¹ * U.mMap k 1 ρ (Matrix.of fun _ _ => c) γ * U.Rn k 1 ρ p.1.2))) := by
    rintro ⟨⟨y, y'⟩, ⟨⟨x, x'⟩, η⟩⟩
    have hgx : D.castM (hs' k j ρ) (U.gaXi (p := j) (s := 0) k (1 + ρ) σ d ((x, x'), η) (fun a => a.elim0)
        ((U.Rn k 1 ρ y)⁻¹ * U.mMap k 1 ρ (Matrix.of fun _ _ => c) γ * U.Rn k 1 ρ y')) =
        U.gaXi (p := j) (s := 1) k ρ σ d ((XC x y, XC x' y'), ((aC x, bC x'), η.2)) (fun _ _ => c) γ :=
      GX σ d hd c hc x x' η y y' γ
    simp only [hGi, TQ]
    rw [PS σ zA zA' hzA hzA' x x' η y y', ← hgx, mul_smul]
    rfl
  have hint' : Integrable (Gi ∘ TQ σ) (((U.muRC k 1 ρ).prod (U.muRC k 1 ρ)).prod (U.muXi k j 0 (1 + ρ) σ)) :=
    (hT.integrable_comp hint.aestronglyMeasurable).mpr hint
  show ∫ ξ, Gi ξ ∂(U.muXi k j 1 ρ σ) = _
  rw [← hT.map_eq, integral_map hT.measurable.aemeasurable (by rw [hT.map_eq]; exact hint.aestronglyMeasurable)]
  have e2 : (fun p => Gi (TQ σ p)) = fun p : (U.RC k 1 ρ × U.RC k 1 ρ) × U.Xi k j 0 (1 + ρ) σ =>
      (psi k (1 + ρ) (U.lowV k j (1 + ρ) (D.castV (hsv k j ρ) zA)) cStd (U.Rn k 1 ρ p.1.1) *
        star (psi k (1 + ρ) (U.lowV k j (1 + ρ) (D.castV (hsv k j ρ) zA')) cStd (U.Rn k 1 ρ p.1.2))) •
      (U.psiStar (p := j) (s := 0) k (1 + ρ) σ (D.castV (hsv k j ρ) zA) (D.castV (hsv k j ρ) zA') p.2 •
        D.castF (hs' k j ρ) F (U.gaXi (p := j) (s := 0) k (1 + ρ) σ d p.2 (fun a => a.elim0)
          ((U.Rn k 1 ρ p.1.1)⁻¹ * U.mMap k 1 ρ (Matrix.of fun _ _ => c) γ * U.Rn k 1 ρ p.1.2))) := funext hpt
  have hint2 := hint'
  rw [show Gi ∘ TQ σ = fun p => Gi (TQ σ p) from rfl, e2] at hint2
  rw [e2, integral_prod _ hint2]
  congr 1
  funext yy
  dsimp only
  rw [integral_smul]
  rfl

end Formalism.FourierDecayAlt.P.PBH
