import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs
import GroundTheory.AutomorphicForms.AdelicGLn
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyPcRatFMem

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.FinLevelTw

open PositivityTheory.Rg.BcB.G8

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

def atHom (a b : ℕ) (w : Pl E) : Gf E a b →* GLw a w × GLw b w :=
  (GeneralLinearGroup.map (pLoc E w)).prodMap (GeneralLinearGroup.map (pLoc E w))

omit [IsCMField E] in
theorem atHom_apply (w : Pl E) (y : Gf E a b) : atHom a b w y = atW w y := rfl

theorem continuous_atHom (w : Pl E) : Continuous (atHom (E := E) a b w) :=
  ((GlobalTheory.EulerTwU.continuous_pc w).comp continuous_fst).prodMk ((GlobalTheory.EulerTwU.continuous_pc w).comp continuous_snd)

theorem isOpen_Kf (n : ℕ) : IsOpen (Kf E n : Set (GL (Fin n) (Af E))) := by
  refine Subgroup.isOpen_mono (H₁ := GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n) ?_
    (GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E n)
  intro g hg
  obtain ⟨h1, h2⟩ := (GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff E n).1 hg
  refine Subgroup.mem_iInf.2 fun w => Subgroup.mem_comap.2 ?_
  refine GlobalTheory.EulerTwU.mem_GLint _ _ (fun i j => ?_) (fun i j => ?_)
  · exact GroundTheory.Global.mem_integralFiniteAdeles.1 (h1 i j) w
  · rw [← map_inv]
    exact GroundTheory.Global.mem_integralFiniteAdeles.1 (h2 i j) w

theorem continuous_thP : Continuous (thP E a b) := by
  have h : ∀ n, Continuous (thF E n) := fun n => GlobalTheory.ThetaPull.continuous_thetaGL _ (continuous_conjFin _)
  exact ((h a).comp continuous_fst).prodMk ((h b).comp continuous_snd)

theorem thP_thP (y : Gf E a b) : thP E a b (thP E a b y) = y :=
  Prod.ext (GlobalTheory.EulerTwU.thF_thF y.1) (GlobalTheory.EulerTwU.thF_thF y.2)

theorem isOpen_family (M : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) (hM : ∀ w, IsOpen (M w : Set (GLw a w × GLw b w)))
    (hK : ∀ᶠ w in cofinite, K2 a b w ≤ M w) :
    IsOpen ((⨅ w, (M w).comap (atHom a b w) : Subgroup (Gf E a b)) : Set (Gf E a b)) := by
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  have hT : {w | ¬ K2 a b w ≤ M w}.Finite := hK
  have h1 : ∀ᶠ u in nhds (1 : Gf E a b), ∀ w ∈ {w | ¬ K2 a b w ≤ M w}, atHom a b w u ∈ M w :=
    (Filter.eventually_all_finite hT).2 fun w _ =>
      (continuous_atHom w).continuousAt.eventually_mem
        ((hM w).mem_nhds (by rw [map_one]; exact one_mem _))
  have h2 : ∀ᶠ u in nhds (1 : Gf E a b), u ∈ ((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) :=
    ((isOpen_Kf a).prod (isOpen_Kf b)).mem_nhds ⟨one_mem _, one_mem _⟩
  filter_upwards [h1, h2] with u hu1 hu2
  refine Subgroup.mem_iInf.2 fun w => Subgroup.mem_comap.2 ?_
  by_cases hw : K2 a b w ≤ M w
  · refine hw ⟨?_, ?_⟩
    · exact Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 hu2.1 w)
    · exact Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 hu2.2 w)
  · exact hu1 w hw

theorem exists_level_of_test {φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ} (h : IsTestP φ) :
    ∃ L : ∀ w : Pl E, Subgroup (GLw a w × GLw b w), (∀ w, IsOpen (L w : Set (GLw a w × GLw b w))) ∧
      (∀ᶠ w in cofinite, L w = K2 a b w) ∧ ∀ w, ∀ k ∈ L w, ∀ x, φ w (k * x) = φ w x ∧ φ w (x * k) = φ w x := by
  obtain ⟨K₁, K₂, h₁, h₂, h₃⟩ := h
  refine ⟨fun w => (K₁ w).prod (K₂ w), fun w => ?_, ?_, fun w => (h₃.1 w).2⟩
  · rw [Subgroup.coe_prod]
    exact (h₁.1 w).1.prod (h₂.1 w).1
  · filter_upwards [h₁.2, h₂.2] with w e₁ e₂
    rw [e₁, e₂]

theorem finLevel : FinLevel := by
  intro E _ _ _ _ a b S φ₁ φ₂ h₁ h₂
  obtain ⟨L₁, o₁, e₁, i₁⟩ := exists_level_of_test h₁
  obtain ⟨L₂, o₂, e₂, i₂⟩ := exists_level_of_test h₂
  let A : Subgroup (Gf E a b) := ⨅ w, (L₁ w ⊓ L₂ w).comap (atHom a b w)
  have hA : IsOpen (A : Set (Gf E a b)) := by
    refine isOpen_family _ (fun w => ?_) ?_
    · rw [Subgroup.coe_inf]
      exact (o₁ w).inter (o₂ w)
    · filter_upwards [e₁, e₂] with w f₁ f₂
      rw [f₁, f₂, inf_idem]
  have mA : ∀ {u}, u ∈ A → ∀ w, atW w u ∈ L₁ w ⊓ L₂ w := fun hu w =>
    Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 hu w)
  refine ⟨A ⊓ A.comap (thP E a b), ?_, fun u hu y => ?_⟩
  · rw [Subgroup.coe_inf]
    exact hA.inter (hA.preimage continuous_thP)
  · have hu₁ := mA hu.1
    have hu₂ := mA (Subgroup.mem_comap.1 hu.2)
    have key : ∀ (w : Pl E) (f : GLw a w × GLw b w → ℂ) (k k' x : GLw a w × GLw b w),
        (∀ c ∈ ({k⁻¹, k'} : Set _), ∀ x, f (c * x) = f x ∧ f (x * c) = f x) → f (k⁻¹ * x * k') = f x := by
      intro w f k k' x h
      rw [(h k' (by simp) _).2, (h k⁻¹ (by simp) _).1]
    unfold finFn
    refine finprod_congr fun w => finprod_congr fun _ => ?_
    have m₁ : atW w (u⁻¹ * y * thP E a b u) = (atW w u)⁻¹ * atW w y * atW w (thP E a b u) := by
      simp only [← atHom_apply, map_mul, map_inv]
    have m₂ : atW w (thP E a b (u⁻¹ * y * thP E a b u)) =
        (atW w (thP E a b u))⁻¹ * atW w (thP E a b y) * atW w u := by
      simp only [← atHom_apply, map_mul, map_inv, thP_thP]
    rw [m₁, m₂, key w (φ₁ w), key w (φ₂ w)]
    · intro c hc x
      rcases hc with rfl | rfl
      · exact i₂ w _ (inv_mem (hu₂ w).2) x
      · exact i₂ w _ (hu₁ w).2 x
    · intro c hc x
      rcases hc with rfl | rfl
      · exact i₁ w _ (inv_mem (hu₁ w).1) x
      · exact i₁ w _ (hu₂ w).1 x

end GlobalTheory.CompanionTheory.FinLevelTw

end
