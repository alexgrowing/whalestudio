import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerInfMemLocSpan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicGLComplementarySupportsCommuteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormModerateGrowthCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalWhittakerCoefficientLinearArchimedeanKerneStatement

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

namespace GlobalTheory.JSW.MirSemi

open GlobalTheory.JSW

theorem whit_rt_apply {E : Type} [Field E] [NumberField E] {a : ℕ} (F : GA E a → ℂ) (h g : GA E a) :
    whit (fun x => F (x * h)) g = whit F (g * h) := by
  simp only [whit, GroundTheory.Automorphic.FourierWhittaker.whittaker, mul_assoc]

theorem whit_zero_apply {E : Type} [Field E] [NumberField E] {a : ℕ} (g : GA E a) :
    whit (0 : GA E a → ℂ) g = 0 := by
  simp [whit, GroundTheory.Automorphic.FourierWhittaker.whittaker]

theorem mul_mem_supS' {E : Type} [Field E] [NumberField E] {a : ℕ} {S : Finset (HeightOneSpectrum (𝓞 E))}
    {x h : GA E a} (hx : x ∈ supS E a S) (hh : h ∈ supS E a S) : x * h ∈ supS E a S := by
  intro w hw
  rw [map_mul, hx w hw, hh w hw, one_mul]

theorem infGL_mem_supS' {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (S : Finset (HeightOneSpectrum (𝓞 E)))
    (y : GL (Fin a) (Cinf E)) : infGL E a y ∈ supS E a S := by
  intro w _
  have h1 : GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (infGL E a y) =
      GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) (infGL E a y)) := by
    ext i j; rfl
  rw [h1, pFin_infGL, map_one]

theorem whit_rel_locSpan : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E a) (φ : Sm E a), φ ∈ π.V → ∀ (t : GA E a) (c : ℂ), GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → (∀ x ∈ GlobalTheory.JSW.supS E a S, GlobalTheory.JSW.whit φ.1 (x * t) = c * GlobalTheory.JSW.whit φ.1 x) → ∀ F ∈ GlobalTheory.JSW.MirSemi.locSpan S φ.1, ∀ x ∈ GlobalTheory.JSW.supS E a S, GlobalTheory.JSW.whit F (x * t) = c * GlobalTheory.JSW.whit F x := by
  intro E _ _ _ a S π φ hφ t c htInf htS hrel
  have hreg := GlobalTheory.T.cusp_form_moderate_growth_compact E a S π φ hφ
  have hlin : ∀ F ∈ locSpan S φ.1, ∀ G ∈ locSpan S φ.1, ∀ (c' : ℂ) (g : GA E a),
      whit (fun x => F x + c' * G x) g = whit F g + c' * whit G g := fun F hF G hG =>
    (GlobalTheory.T.globalWhittakerCoefficient_linear_archimedeanKernel E a F G (hreg F hF).1 (hreg G hG).1 (hreg F hF).2 (hreg G hG).2).1
  let V : Submodule ℂ (GA E a → ℂ) :=
    { carrier := {F | F ∈ locSpan S φ.1 ∧ ∀ x ∈ supS E a S, whit F (x * t) = c * whit F x}
      add_mem' := by
        rintro F G ⟨hF, hF'⟩ ⟨hG, hG'⟩
        refine ⟨add_mem hF hG, fun x hx => ?_⟩
        have e : (F + G) = fun y => F y + 1 * G y := by funext y; simp
        rw [e, hlin F hF G hG, hlin F hF G hG, hF' x hx, hG' x hx]; ring
      zero_mem' := ⟨zero_mem _, fun x _ => by rw [whit_zero_apply, whit_zero_apply, mul_zero]⟩
      smul_mem' := by
        rintro c' F ⟨hF, hF'⟩
        refine ⟨Submodule.smul_mem _ c' hF, fun x hx => ?_⟩
        have e : (c' • F) = fun y => (0 : GA E a → ℂ) y + c' * F y := by funext y; simp
        rw [e, hlin 0 (zero_mem _) F hF, hlin 0 (zero_mem _) F hF, whit_zero_apply, whit_zero_apply, hF' x hx]
        ring }
  have hV : locSpan S φ.1 ≤ V := by
    refine locSpan_le ⟨self_mem_locSpan, hrel⟩ ?_ ?_
    · rintro F ⟨hF, hF'⟩ h hh
      refine ⟨rt_mem_locSpan hF hh, fun x hx => ?_⟩
      rw [whit_rt_apply, whit_rt_apply, mul_assoc, ← GlobalTheory.T.adelicGL_complementary_supports_commute E a S h t hh htInf htS, ← mul_assoc]
      exact hF' (x * h) (mul_mem_supS' hx hh)
    · rintro F ⟨hF, hF'⟩ X _ ν _ k γ hk
      refine ⟨kerInf_mem_locSpan hF ν hk, fun x hx => ?_⟩
      have hker := (GlobalTheory.T.globalWhittakerCoefficient_linear_archimedeanKernel E a F F (hreg F hF).1 (hreg F hF).1 (hreg F hF).2 (hreg F hF).2).2 X ν k γ hk
      rw [hker, hker, ← integral_const_mul]
      congr 1
      funext y
      have hc := GlobalTheory.T.adelicGL_complementary_supports_commute E a S (infGL E a (γ y)) t (infGL_mem_supS' S (γ y)) htInf htS
      rw [mul_assoc x t, ← hc, ← mul_assoc, hF' _ (mul_mem_supS' hx (infGL_mem_supS' S (γ y)))]
      ring
  intro F hF x hx
  exact (hV hF).2 x hx

end GlobalTheory.JSW.MirSemi
