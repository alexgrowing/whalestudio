import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompReixMemAdm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalInvariantFormUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDiagonalCoordsEqPosMulAdeleHaar
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot GlobalTheory.DblBox

theorem GlobalTheory.DblBox.eq_smul_integral_bx : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (n d : ℕ) (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin d) (Fin d) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E)
      (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F J) (incM F J')) (Fin n × Fin d))
      (cb : Darboux (symp (R := AF F) (cA σ) (-1) (incM F J₂) (incM F J')) (Fin (n + n) × Fin d)), IsBoxCo co cb →
    ∀ [MeasurableSpace (Fin n × Fin d → AF F)] [BorelSpace (Fin n × Fin d → AF F)] (m : Measure (Fin n × Fin d → AF F)), m.IsAddHaarMeasure →
    ∀ l ∈ (adeleClass F).adm (Fin (n + n) × Fin d), (∃ φ ∈ schA F (Fin (n + n) × Fin d), l φ ≠ 0) →
    (∀ u : Matrix (Fin (n + n)) (Fin d) (AE F E), (∀ j, uᵀ j ∈ diagSub (AE F E) finSumFinEquiv) →
      ∀ φ ∈ schA F (Fin (n + n) × Fin d), l (cb.rho ψ u φ) = l φ) →
    ∃ c : ℂ, c ≠ 0 ∧ ∀ φ₁ ∈ schA F (Fin n × Fin d), ∀ φ₂ ∈ schA F (Fin n × Fin d), l (bx φ₁ φ₂) = c * ∫ x, φ₁ x * φ₂ x ∂m := by
  intro F E _ _ _ _ _ σ ψ hψ n d J J' J₂ co cb hcb inst _ m hm l hl hne hinv
  set l' := l ∘ₗ (reix (rIdx n d)).toLinearMap with hl'
  have hl'a : l' ∈ (adeleClass F).adm ((Fin n × Fin d) ⊕ (Fin n × Fin d)) := comp_reix_mem_adm _ hl
  have hinv' : ∀ x y : Fin n × Fin d → AF F, ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
      l' (schr ψ (Sum.elim x x, Sum.elim y (-y)) Φ) = l' Φ := by
    intro x y Φ hΦ
    obtain ⟨z, hz⟩ : ∃ z, co.e z = (x, y) := ⟨co.e.symm (x, y), co.e.apply_symm_apply _⟩
    obtain ⟨u, hudef⟩ : ∃ u : Matrix (Fin (n + n)) (Fin d) (AE F E),
        u = fun k => Sum.elim z z (finSumFinEquiv.symm k) := ⟨_, rfl⟩
    have hu1 : upB u = z := by
      funext i; simp only [upB, hudef, Equiv.symm_apply_apply]; rfl
    have hu2 : loB u = z := by
      funext i; simp only [loB, hudef, Equiv.symm_apply_apply]; rfl
    have hdiag : ∀ j, uᵀ j ∈ diagSub (AE F E) finSumFinEquiv := by
      intro j
      show (LinearMap.funLeft _ _ _) _ = (LinearMap.funLeft _ _ _) _
      funext i
      show u (finSumFinEquiv (Sum.inl i)) j = u (finSumFinEquiv (Sum.inr i)) j
      simp only [hudef, Equiv.symm_apply_apply]; rfl
    have h := hinv u hdiag (reix (rIdx n d) Φ) (reix_mem_schA (rIdx n d) hΦ)
    rw [hcb.rho_reix, hu1, hu2, hz] at h
    simpa [hl'] using h
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.DiagUniq.eq_smul_lDiag F ψ hψ (Fin n × Fin d) l' hl'a hinv'
  have hc₁0 : c₁ ≠ 0 := by
    rintro rfl
    obtain ⟨φ, hφ, hlφ⟩ := hne
    have hφ' : (reix (rIdx n d)).symm φ ∈ schA F _ := by
      rw [reix_symm]; exact reix_mem_schA _ hφ
    have := hc₁ _ hφ'
    rw [hl', LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, zero_mul] at this
    exact hlφ this
  obtain ⟨c₀, hc₀, hglue⟩ := GlobalTheory.diagForm_glue_integral F (Fin n × Fin d)
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.measurableSpace_adeleRing F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.borelSpace_adeleRing F
  have hms : (MeasurableSpace.pi : MeasurableSpace (Fin n × Fin d → AF F)) = inst := by
    rw [‹BorelSpace (Fin n × Fin d → AF F)›.measurable_eq]
    exact (Pi.borelSpace (X := fun _ : Fin n × Fin d => AdeleRing (𝓞 F) F)).measurable_eq
  subst hms
  haveI := hm
  have h2 := Measure.isAddLeftInvariant_eq_smul (GroundTheory.Automorphic.GJMatrix.adeleMeasurePi F (ι := Fin n × Fin d)) m
  have hc₂ : 0 < (GroundTheory.Automorphic.GJMatrix.adeleMeasurePi F (ι := Fin n × Fin d)).addHaarScalarFactor m :=
    Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  refine ⟨c₁ * (c₀ * ((GroundTheory.Automorphic.GJMatrix.adeleMeasurePi F (ι := Fin n × Fin d)).addHaarScalarFactor m : ℝ)),
    mul_ne_zero hc₁0 (mul_ne_zero (by exact_mod_cast hc₀.ne') (by exact_mod_cast hc₂.ne')), fun φ₁ h₁ φ₂ h₂ => ?_⟩
  have hb := GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φ₁ h₁ φ₂ h₂
  have e1 : l (bx φ₁ φ₂) = l' (boxFun φ₁ φ₂) := rfl
  rw [e1, hc₁ _ hb, GlobalTheory.DiagForm.lDiag, LinearMap.comp_apply,
    GlobalTheory.DiagForm.Lext_apply _ (GlobalTheory.DiagForm.integrable_resD hb)]
  have e2 : GlobalTheory.DiagForm.resD F (Fin n × Fin d) (boxFun φ₁ φ₂) =
      fun p => (fun t => φ₁ t * φ₂ t) (GlobalTheory.DiagForm.glue p) := rfl
  rw [e2, (hglue _).2]
  conv_lhs => rw [h2]
  rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  push_cast
  ring
