import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RWConstMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NsgDivNorm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnstatedLocalWeilLemma
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilRepresentationHypothesisStatement

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilPiRep

section Red

variable {F : Type} [Field F]

def red (M : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2) (Fin 2) F :=
  !![M 0 0 / M.det, M 0 1; M 1 0 / M.det, M 1 1]

theorem det_red {M : Matrix (Fin 2) (Fin 2) F} (hM : M.det ≠ 0) : (red M).det = 1 := by
  have e : M.det = M 0 0 * M 1 1 - M 0 1 * M 1 0 := Matrix.det_fin_two M
  simp only [red, Matrix.det_fin_two_of]
  field_simp
  rw [e]

theorem det_cjA {A : F} (hA : A ≠ 0) (M : Matrix (Fin 2) (Fin 2) F) : (cjA A M).det = M.det := by
  simp only [cjA, Matrix.det_fin_two_of, Matrix.det_fin_two M]
  field_simp

theorem red_mul {M N : Matrix (Fin 2) (Fin 2) F} (hM : M.det ≠ 0) (hN : N.det ≠ 0) :
    red (M * N) = red M * cjA M.det (red N) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [red, cjA, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_mul] <;> field_simp

end Red

section Dil

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
  {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace E] [BorelSpace E] [Algebra F E]

theorem dil_mem {c : Eˣ →* ℂˣ} {Φ : E → ℂ} (hΦ : Φ ∈ SBc F E c) (t : Eˣ) :
    (fun y => Φ (y * (t : E))) ∈ SBc F E c := by
  refine ⟨hΦ.1.comp_continuous (continuous_mul_const _),
    hΦ.2.1.comp_homeomorph (Homeomorph.mulRight₀ (t : E) t.ne_zero), fun u hu x => ?_⟩
  show Φ (x * (u : E) * (t : E)) = _ * Φ (x * (t : E))
  rw [mul_right_comm, hΦ.2.2 u hu]

theorem const_mul_mem {c : Eˣ →* ℂˣ} {f : E → ℂ} (hf : f ∈ SBc F E c) (k : ℂ) :
    (fun y => k * f y) ∈ SBc F E c := by
  have h1 : IsLocallyConstant f := hf.1
  refine ⟨(IsLocallyConstant.const k).mul h1, hf.2.1.mul_left, fun u hu x => ?_⟩
  show k * f (x * (u : E)) = _ * (k * f x)
  rw [hf.2.2 u hu]
  ring

end Dil

theorem wPiRep : Ad3.K.GL2LocalData.WPiRep := by
  unfold WPiRep ForEF
  intro F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hfr hcont σ hσ η hη c Φ hΦ g h hh
  have wch := GlobalTheory.CompanionTheory.WeilChoice.wchoice F χ hχ hχ1 E hfr hcont σ hσ η hη
  have wdg := GlobalTheory.CompanionTheory.WeilDilation.wDiagT F χ hχ hχ1 E hfr hcont σ hσ η hη
  have wsb := GlobalTheory.CompanionTheory.WeilSB.wsb F χ hχ hχ1 E hfr hcont σ hσ η hη
  have wrp := GlobalTheory.T.weil_representation_hypothesis F χ hχ hχ1 E hfr hcont σ hσ η hη
  beta_reduce at wch wdg wsb wrp
  have hdet : ∀ x : GL (Fin 2) F, (x.val).det ≠ 0 := fun x =>
    ((Matrix.isUnit_iff_isUnit_det _).1 x.isUnit).ne_zero
  obtain ⟨t, hnt, hpi⟩ : ∃ t : Eˣ, Algebra.norm F (t : E) = (h.val).det ∧
      piE E χ σ η c h Φ = fun x => (((c t : ℂˣ) : ℂ) * (((modulus (h.val).det : ℝ) : ℂ) ^ (1 / 2 : ℂ))) *
        rWE E χ σ η (red h.val) (fun y => Φ (y * (t : E))) x := by
    refine ⟨hh.choose, hh.choose_spec, ?_⟩
    funext x
    change piG χ σ (muE E χ) (lamE E χ η) c h Φ x = _
    unfold piG
    rw [dif_pos hh]
    rfl
  set k : ℂ := ((c t : ℂˣ) : ℂ) * (((modulus (h.val).det : ℝ) : ℂ) ^ (1 / 2 : ℂ)) with hk
  set Ψ : E → ℂ := fun y => Φ (y * (t : E)) with hΨdef
  have hΨ : Ψ ∈ SBc F E c := dil_mem hΦ t
  have hΨE : Ψ ∈ SBE E := ⟨hΨ.1, hΨ.2.1⟩
  have hd1 : (red h.val).det = 1 := det_red (hdet h)
  have hmem : piE E χ σ η c h Φ ∈ SBc F E c := by
    rw [hpi]
    exact const_mul_mem ((wsb _ hd1 Ψ hΨE).2 c hΨ) k
  refine ⟨?_, hmem⟩
  by_cases hg : ∃ tg : Eˣ, Algebra.norm F (tg : E) = (g.val).det
  · obtain ⟨tg, htg⟩ := hg
    have hdg := hdet g
    have hgh : Algebra.norm F ((tg * t : Eˣ) : E) = ((g * h).val).det := by
      rw [Units.val_mul, map_mul, htg, hnt, Units.val_mul, Matrix.det_mul]
    rw [wch c Φ hΦ (g * h) (tg * t) hgh, wch c _ hmem g tg htg]
    set f : E → ℂ := fun y => Ψ (y * (tg : E)) with hfdef
    have hfE : f ∈ SBE E := by
      have := dil_mem hΨ tg
      exact ⟨this.1, this.2.1⟩
    have hcj : (cjA (g.val).det (red h.val)).det = 1 := by rw [det_cjA hdg, hd1]
    have hgd : (red g.val).det = 1 := det_red hdg
    have hL : (fun y => Φ (y * ((tg * t : Eˣ) : E))) = f := by
      funext y
      simp only [hfdef, hΨdef, Units.val_mul, mul_assoc]
    have hR : (fun y => piE E χ σ η c h Φ (y * (tg : E))) =
        fun y => k * rWE E χ σ η (cjA (g.val).det (red h.val)) f y := by
      funext y
      have := congrFun (wdg (red h.val) hd1 tg Ψ hΨE) y
      rw [htg] at this
      rw [hpi]
      simp only []
      rw [this]
    have e1 : rW χ σ (muE E χ) (lamE E χ η) (((g * h).val) 0 0 / ((g * h).val).det) (((g * h).val) 0 1)
        (((g * h).val) 1 0 / ((g * h).val).det) (((g * h).val) 1 1) f 1 =
        rWE E χ σ η (red (g * h).val) f 1 := rfl
    have e2 : rW χ σ (muE E χ) (lamE E χ η) ((g.val) 0 0 / (g.val).det) ((g.val) 0 1)
        ((g.val) 1 0 / (g.val).det) ((g.val) 1 1)
        (fun y => k * rWE E χ σ η (cjA (g.val).det (red h.val)) f y) 1 =
        k * rWE E χ σ η (red g.val) (rWE E χ σ η (cjA (g.val).det (red h.val)) f) 1 :=
      GlobalTheory.CompanionTheory.WeilChoice.rW_const_mul _ _ _ _ _ _ _ _ _ _ _
    rw [hL, hR, e1, e2, Units.val_mul, red_mul hdg (hdet h), wrp _ _ hgd hcj f hfE]
    have e3 : (((modulus ((g.val * h.val).det) : ℝ) : ℂ) ^ (1 / 2 : ℂ)) =
        (((modulus (g.val).det : ℝ) : ℂ) ^ (1 / 2 : ℂ)) * (((modulus (h.val).det : ℝ) : ℂ) ^ (1 / 2 : ℂ)) := by
      rw [Matrix.det_mul, modulus_mul, NNReal.coe_mul, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]
    rw [e3, map_mul, Units.val_mul, hk]
    ring
  · have hg' : ¬ ∃ s : Eˣ, Algebra.norm F (s : E) = ((g * h).val).det := by
      rintro ⟨s, hs⟩
      refine hg ⟨s * t⁻¹, ?_⟩
      have hn : Algebra.norm F ((t⁻¹ : Eˣ) : E) * (h.val).det = 1 := by
        rw [← hnt, ← map_mul, Units.inv_mul, map_one]
      rw [Units.val_mul, map_mul, hs, Units.val_mul, Matrix.det_mul, mul_assoc, mul_comm (h.val).det, hn, mul_one]
    change Wc χ σ (muE E χ) (lamE E χ η) c Φ (g * h) = Wc χ σ (muE E χ) (lamE E χ η) c _ g
    unfold Wc
    rw [dif_neg hg', dif_neg hg]

end GlobalTheory.CompanionTheory.WeilPiRep
