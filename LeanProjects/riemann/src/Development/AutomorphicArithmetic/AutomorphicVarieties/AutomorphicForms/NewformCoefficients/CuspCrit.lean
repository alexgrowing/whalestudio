import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.AvgZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.SmCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.AutPer
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinConstantTermUpperBlock

open NumberField MeasureTheory GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Sd UpperTheory.V.Af.Nf
open scoped Matrix MatrixGroups

private theorem two_periods {f : ℝ → ℂ} (hc : Continuous f) {N N' : ℕ} (hN' : 0 < N') (h : Function.Periodic f N)
    (h' : Function.Periodic f N') (h0 : ∫ t in (0 : ℝ)..N', f t = 0) : ∫ t in (0 : ℝ)..N, f t = 0 := by
  have e1 := h.intervalIntegral_add_zsmul_eq (N' : ℤ) 0 fun a b => hc.intervalIntegrable a b
  have e2 := h'.intervalIntegral_add_zsmul_eq (N : ℤ) 0 fun a b => hc.intervalIntegrable a b
  simp only [zero_add, zsmul_eq_mul, Int.cast_natCast] at e1 e2
  rw [h0, mul_zero, mul_comm, e1] at e2
  exact (mul_eq_zero.1 e2).resolve_left (Nat.cast_ne_zero.2 hN'.ne')

private theorem aff_add {R : Type} [CommRing R] (x y : R) : aff 1 (x + y) = aff 1 x * aff 1 y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ, add_comm]

private theorem upR_aff (t : ℝ) : upR (aff 1 t) = aff 1 (TR.sInf ℚ (algebraMap ℝ (TR.Rinf ℚ) t)) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change (1 : Matrix (Fin 2) (Fin 2) (Ad ℚ)) i j - TR.sInf ℚ ((1 : Matrix (Fin 2) (Fin 2) (TR.Rinf ℚ)) i j) +
    TR.sInf ℚ (algebraMap ℝ (TR.Rinf ℚ) ((aff 1 t).val i j)) = (aff 1 _).val i j
  fin_cases i <;> fin_cases j <;> simp [aff]

private theorem ratGL_aff (q : ℚ) : ratGL ℚ 2 (aff 1 q) = aff 1 (algebraMap ℚ (Ad ℚ) q) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change algebraMap ℚ (Ad ℚ) ((aff 1 q).val i j) = (aff 1 _).val i j
  fin_cases i <;> fin_cases j <;> simp [aff]

theorem UpperTheory.V.Af.Nf.cuspCrit :
    UpperTheory.V.Af.Nf.CuspCrit := by
  intro φ hl ho hct r h0 h1 _ _ μ D hμ hD g
  obtain rfl : r = 1 := by omega
  obtain ⟨i1, i2, -, i3, -, hu, hx⟩ := UpperTheory.eisenstein_constantTerm_upperBlock ℚ
  have hφ := smCont ℚ 2 φ ho
  obtain ⟨N, hN, hper⟩ := autPer φ hl ho g
  let e : ℝ → BlockIx 2 1 → Ad ℚ := fun t _ => TR.sInf ℚ (algebraMap ℝ (TR.Rinf ℚ) t)
  have he : Continuous e := continuous_pi fun _ =>
    (((TR.continuous_infEq ℚ).comp (continuous_algebraMap ℝ (TR.Rinf ℚ))).prodMk continuous_const :
      Continuous fun t : ℝ => ((TR.infEq ℚ (algebraMap ℝ (TR.Rinf ℚ) t), 0) :
        InfiniteAdeleRing ℚ × Af ℚ))
  have hadd : ∀ t x, unip (e t + x) = upR (aff 1 t) * unip x := fun t x => by
    rw [hx, hx, upR_aff, ← aff_add]; rfl
  have hψ : Continuous fun x : BlockIx 2 1 → Ad ℚ => φ.1 (unip x * g) := hφ.comp (hu.mul continuous_const)
  refine avgZero _ (ratN ℚ 2 1) μ D hμ hD _ hψ ?_ e he N (Nat.cast_pos.2 hN) fun x => ?_
  · rintro _ ⟨q, rfl⟩ x
    have : ∀ y : BlockIx 2 1 → Ad ℚ, y ⟨(0, 1), by decide⟩ = algebraMap ℚ (Ad ℚ) (q ⟨(0, 1), by decide⟩) →
        unip (y + x) = ratGL ℚ 2 (aff 1 (q ⟨(0, 1), by decide⟩)) * unip x := fun y hy => by
      rw [hx, hx, ratGL_aff, ← aff_add, ← hy]; rfl
    rw [this _ rfl, mul_assoc, hl]
  · obtain ⟨N', hN', hp', hz⟩ := hct (unip x * g)
    have ef : (fun t : ℝ => φ.1 (upR (aff 1 t) * (unip x * g))) = fun t => φ.1 (unip (e t + x) * g) :=
      funext fun t => by rw [hadd, mul_assoc]
    have hp : Function.Periodic (fun t : ℝ => φ.1 (upR (aff 1 t) * (unip x * g))) N := fun t => by
      have := hper (e t + x)
      rw [hadd, mul_assoc] at this
      beta_reduce
      rw [add_comm t, aff_add, map_mul, mul_assoc, this]
    rw [ef] at hp hp' hz
    exact two_periods (hψ.comp (he.add continuous_const)) hN' hp hp' hz
