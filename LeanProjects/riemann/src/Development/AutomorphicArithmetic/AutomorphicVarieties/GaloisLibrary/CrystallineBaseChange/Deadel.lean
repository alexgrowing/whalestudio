import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RnStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.DownLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.DownHol
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.DownChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.DownZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.NslMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.NslMdiffPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeOperatorsCommuteOnAutomorphicForms

noncomputable section

open NumberField Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual
open GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Nf UpperTheory.V.Sd CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped Matrix MatrixGroups ModularForm

namespace UpperTheory.V.Br

private theorem nsl_aff (k : ℕ) (f : ℍ → ℂ) (z : ℍ) :
    nsl k f (aff (Units.mk0 z.im z.im_pos.ne') z.re : GL (Fin 2) ℝ) UpperHalfPlane.I =
      ((z.im ^ ((k : ℝ) / 2) : ℝ) : ℂ) * f z := by
  have hd : (aff (Units.mk0 z.im z.im_pos.ne') z.re : GL (Fin 2) ℝ).val.det = z.im := by simp [aff, Matrix.det_fin_two]
  have hz : (z.im : ℂ) * Complex.I + z.re = z := by
    rw [add_comm]; exact Complex.re_add_im (z : ℂ)
  rw [nsl, hd, abs_of_pos z.im_pos, sign_pos z.im_pos]
  simp [aff, hz]

private theorem isLow_fin {k : ℕ} {φ : TR.Sm ℚ 2} (h : IsLow k φ) (u : GL (Fin 2) (Af ℚ)) : IsLow k (TR.finRep ℚ 2 u φ) := by
  have e : ∀ v i j, TR.Eop v i j (TR.finRep ℚ 2 u φ) = TR.finRep ℚ 2 u (TR.Eop v i j φ) := fun v i j =>
    LinearMap.congr_fun (TR.lie_rt_fin _ u) φ
  refine ⟨fun v => ?_, fun v => ?_, fun v => ?_⟩
  · rw [e, e, ← map_sub, h.wt, map_smul]
  · rw [e, e, e, e, ← map_sub, h.low, map_smul, map_add]
  · rw [e, e, ← map_add, h.one, map_zero]

private theorem cusp_fin {φ : TR.Sm ℚ 2} (h : TR.IsCuspForm φ) (u : GL (Fin 2) (Af ℚ)) : TR.IsCuspForm (TR.finRep ℚ 2 u φ) := by
  refine ⟨(UpperTheory.hecke_operators_commute_on_automorphic_forms ℚ 2).2.1 φ u h.1, fun r h0 h1 _ _ μ 𝓕 hμ hF g => ?_⟩
  have e : ∀ x : BlockIx 2 r → Ad ℚ, (TR.finRep ℚ 2 u φ).1 (unip x * g) = φ.1 (unip x * (g * finGL ℚ 2 u)) := fun x =>
    congrArg φ.1 (mul_assoc _ _ _)
  simp only [e]
  exact h.2 r h0 h1 μ 𝓕 hμ hF _

private theorem down_fin {k N : ℕ} {f : ℍ → ℂ} {φ : TR.Sm ℚ 2} (hl : ∀ γ g, φ.1 (ratGL ℚ 2 γ * g) = φ.1 g)
    (h : Nf.IsLift k N f φ.1) (γ : SL(2, ℤ)) :
    down k (TR.finRep ℚ 2 (toF (Matrix.SpecialLinearGroup.mapGL ℚ γ))⁻¹ φ).1 = f ∣[(k : ℤ)] γ := by
  funext z
  set δ : GL (Fin 2) ℚ := Matrix.SpecialLinearGroup.mapGL ℚ γ with hδ
  set x : GL (Fin 2) ℝ := aff (Units.mk0 z.im z.im_pos.ne') z.re with hx
  have hv : (toR δ).val = γ.1.map (Int.cast : ℤ → ℝ) := by
    ext a b
    change Rat.castHom ℝ (algebraMap ℤ ℚ (γ a b)) = _
    simp
  have hd : 0 < x.val.det := by simp [hx, aff, Matrix.det_fin_two, z.im_pos]
  have e : ratGL ℚ 2 δ * (upR x * finGL ℚ 2 (toF δ)⁻¹) = ratGL ℚ 2 1 * (upR (toR δ * x) * finGL ℚ 2 1) := by
    rw [ratGL_eq, upR_comm x, mul_assoc, ← mul_assoc (finGL ℚ 2 (toF δ)), ← map_mul, mul_inv_cancel]
    simp
  change ((z.im ^ (-((k : ℝ) / 2)) : ℝ) : ℂ) * φ.1 (upR x * finGL ℚ 2 (toF δ)⁻¹) = _
  rw [← hl δ, e, h 1 _ 1 (one_mem _), Units.val_mul, ← (nslMul k f).1 _ _ (toR δ).det_ne_zero hd, hv, (nslSl k f).1, hx, nsl_aff,
    ← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add z.im_pos]
  simp

end UpperTheory.V.Br

open UpperTheory.V.Br in
theorem UpperTheory.V.Br.deadel :
    UpperTheory.V.Br.Deadel := by
  intro k N hN χ ω hω φ hc hlow hK hz
  haveI : NeZero N := ⟨by omega⟩
  have hlift := downLift k N hN φ hc.1.left hlow hK
  have hχ := downChar k N hN χ ω hω _ _ hlift hz
  refine ⟨⟨⟨down k φ.1, ?_⟩, downHol k φ hlow, ?_⟩, hχ, hlift⟩
  · rintro _ ⟨γ, hγ, rfl⟩
    have h1 := (Gamma1_mem N γ).1 hγ
    have h2 := hχ γ (Gamma0_mem.2 h1.2.2)
    rw [h1.2.1, map_one, one_smul] at h2
    exact h2
  · intro c hcu
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hcu
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hcu]
    intro γ _
    have := downZero k _ (cusp_fin hc (toF (Matrix.SpecialLinearGroup.mapGL ℚ γ))⁻¹) (isLow_fin hlow _)
    rw [down_fin hc.1.left hlift] at this
    exact this
