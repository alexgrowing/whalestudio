import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.ClozelCohomologicalOf
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.ArchimedeanWhittakerDerivatives.ExistsUpperUnitary
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.ArchimedeanWhittakerDerivatives.HasDerivAtOfMulHom
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.ArchimedeanWhittakerDerivatives.HasDerivAtOfIntRel
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.ArchimedeanWhittakerDerivatives.ConjSingleApply
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.ArchimedeanWhittakerDerivatives.ContinuousAtEmb
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStandardAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsMirabolicWhittakerStageOfIsCuspForm

noncomputable section

namespace PositivityTheory.Rg.Cz

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric GlobalTheory.CuspRep.Generic GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def dpsi (ψ : AddChar (Ad E) ℂ) (Z : Cinf E) : ℂ := deriv (fun t : ℝ => ψ (sInf E (t • Z))) 0

theorem hasDerivAt_dpsi {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (Z : Cinf E) :
    HasDerivAt (fun t : ℝ => ψ (sInf E (t • Z))) (dpsi ψ Z) 0 := by
  obtain ⟨c, hc⟩ := hasDerivAt_of_mulHom (fun t : ℝ => ψ (sInf E (t • Z)))
    (hψ.cont.comp (continuous_sInf'.comp (continuous_id.smul continuous_const)))
    (by simp only [zero_smul, map_zero, AddChar.map_zero_eq_one])
    (fun s t => by simp only [add_smul, map_add, AddChar.map_add_eq_mul])
  have h := hc 0
  simp only [zero_smul, map_zero, AddChar.map_zero_eq_one, mul_one] at h
  rw [dpsi, h.deriv]
  exact h

theorem dpsi_zero (ψ : AddChar (Ad E) ℂ) : dpsi ψ (0 : Cinf E) = 0 := by
  simp [dpsi]

theorem whit_lie_eq {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (π : CuspSub E a) (b : GL (Fin a) (Cinf E))
    (M : Matrix (Fin a) (Fin a) (Cinf E)) (hM : M * M = 0)
    (hMu : ∀ i j : Fin a, j ≤ i → (b.val * M * (b⁻¹).val) i j = 0) (φ : π.V) :
    whit ψ (a - 1) (lieOp π (toL M) φ).1.1 (infGL E a b) =
      dpsi ψ (sd (b.val * M * (b⁻¹).val)) * whit ψ (a - 1) φ.1.1 (infGL E a b) := by
  have hg : ∀ φ : π.V, Good ψ (a - 1) φ.1.1 := fun φ => GlobalTheory.T.isMirabolicWhittakerStage_of_isCuspForm E a ψ φ.1 (π.cusp _ φ.2)
  have h0 : a - 1 < a ∨ a - 1 = 0 := by omega
  have hrel : IntRel M hM φ.1.1 (lieOp π (toL M) φ).1.1 := intRel_sm M hM φ.1
  have hD := hasDerivAt_of_intRel M hM (whit_good hψ (a - 1) h0 (hg (lieOp π (toL M) φ))).1.cont
    (intRel_whit hψ M hM (a - 1) h0 (hg φ) (hg _) hrel) (infGL E a b)
  have he : (fun t => whit ψ (a - 1) φ.1.1 (infGL E a b * infGL E a (cu M hM t))) =
      fun t : ℝ => ψ (sInf E (t • sd (b.val * M * (b⁻¹).val))) * whit ψ (a - 1) φ.1.1 (infGL E a b) :=
    funext fun t => law_conj ψ _ (whit_good hψ (a - 1) h0 (hg φ)).1.law b M hM hMu t
  rw [he] at hD
  exact hD.unique ((hasDerivAt_dpsi hψ _).mul_const _)

theorem whitLie_holds : WhitLie := by
  intro E _ _ _ a π
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_standardAdelicAddChar E
  have hg : ∀ φ : π.V, Good ψ (a - 1) φ.1.1 := fun φ => GlobalTheory.T.isMirabolicWhittakerStage_of_isCuspForm E a ψ φ.1 (π.cusp _ φ.2)
  have h0 : a - 1 < a ∨ a - 1 = 0 := by omega
  obtain ⟨φ₀, hφ₀⟩ : ∃ φ : π.V, φ ≠ 0 := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot π.ne_bot
    exact ⟨⟨x, hx⟩, fun h => hx0 (congrArg Subtype.val h)⟩
  have hw0 : whit ψ (a - 1) φ₀.1.1 ≠ 0 :=
    (whit_good hψ (a - 1) h0 (hg φ₀)).2 fun h => hφ₀ (Subtype.ext (Subtype.ext h))
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.1 hw0
  obtain ⟨b, k, hb, hyk⟩ := exists_upper_unitary (GeneralLinearGroup.map (pInf E) g₀)
  let ℓ : π.V →ₗ[ℂ] ℂ :=
    { toFun := fun φ => whit ψ (a - 1) φ.1.1 (infGL E a b)
      map_add' := fun φ φ' => congrFun (whit_add hψ (a - 1) h0 (hg φ) (hg φ')) _
      map_smul' := fun c φ => congrFun (whit_smul (a - 1) c φ.1.1) _ }
  have hℓ : ∀ φ, ℓ φ = whit ψ (a - 1) φ.1.1 (infGL E a b) := fun _ => rfl
  refine ⟨ℓ, fun h => ?_, fun τ => ?_⟩
  · apply hg₀
    rw [Pi.zero_apply]
    have e := LinearMap.congr_fun h (π.op (.cpt k) (π.op (.fin (GeneralLinearGroup.map (pFin E) g₀)) φ₀))
    rw [hℓ, LinearMap.zero_apply] at e
    refine Eq.trans ?_ e
    refine Eq.trans ?_ (whit_rt (a - 1) (fun y => φ₀.1.1 (y * finGL E a (GeneralLinearGroup.map (pFin E) g₀)))
      (infGL E a (Unitary.toUnits k)) (infGL E a b)).symm
    refine Eq.trans ?_ (whit_rt (a - 1) φ₀.1.1 (finGL E a (GeneralLinearGroup.map (pFin E) g₀)) _).symm
    rw [← map_mul, ← hyk, infGL_mul_finGL]
  · set β : Fin a → Fin a → ℂ := fun p q => coord τ (b.val p p * (b⁻¹).val q q) with hβ
    refine ⟨fun p q => if (p : ℕ) + 1 = q then
      (1 / 2 : ℂ) * (dpsi ψ (atEmb τ (β p q)) - Complex.I * dpsi ψ (atEmb τ (β p q * Complex.I))) else 0,
      fun p q hpq => ?_, fun p q hpq => ?_, fun p q hpq => ?_⟩
    · beta_reduce
      rw [if_pos hpq]
      refine mul_ne_zero (by norm_num) ?_
      have hu : IsUnit (b.val p p * (b⁻¹).val q q) :=
        (IsUnit.of_mul_eq_one _ (diag_inv b hb p)).mul (IsUnit.of_mul_eq_one_right _ (diag_inv b hb q))
      have hβ0 : β p q ≠ 0 := (hu.map (coord τ)).ne_zero
      exact wirtinger_ne_zero (fun z => ψ (sInf E (atEmb τ z)))
        (hψ.cont.comp (continuous_sInf'.comp (continuous_atEmb τ)))
        (fun z w => by simp only [atEmb_add, map_add, AddChar.map_add_eq_mul]) (fun z => hψ.norm _)
        (psi_nontriv hψ τ) (fun z => dpsi ψ (atEmb τ z))
        (fun z => by simpa only [atEmb_real_mul] using hasDerivAt_dpsi hψ (atEmb τ z)) _ hβ0
    · beta_reduce
      rw [if_neg (by omega)]
    · refine LinearMap.ext fun φ => ?_
      have hpq' : p ≠ q := ne_of_lt hpq
      have key : ∀ w : ℂ, ℓ (lieOp π (toL (Matrix.single p q (atEmb τ w))) φ) =
          dpsi ψ (sd (b.val * Matrix.single p q (atEmb τ w) * (b⁻¹).val)) * ℓ φ := fun w =>
        whit_lie_eq hψ π b _ (single_sq p q hpq' _) (conj_single_upper b hb p q hpq _) φ
      have hz : ∀ w, b.val p p * atEmb τ w * (b⁻¹).val q q = atEmb τ (β p q * w) := fun w => by
        rw [mul_right_comm, mul_embeddingScalar_eq_coord_mul]
      rw [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul]
      change ℓ ((1 / 2 : ℂ) • (lieOp π (toL (Matrix.single p q (atEmb τ 1))) φ -
        Complex.I • lieOp π (toL (Matrix.single p q (atEmb τ Complex.I))) φ)) = _
      rw [map_smul, map_sub, map_smul, key, key, sd_conj_single b hb p q hpq, sd_conj_single b hb p q hpq,
        smul_eq_mul, smul_eq_mul]
      by_cases h1 : (p : ℕ) + 1 = q
      · simp only [h1, ↓reduceIte]
        rw [hz, hz, mul_one]; ring
      · simp only [h1, ↓reduceIte]
        rw [dpsi_zero]; ring

end PositivityTheory.Rg.Cz
