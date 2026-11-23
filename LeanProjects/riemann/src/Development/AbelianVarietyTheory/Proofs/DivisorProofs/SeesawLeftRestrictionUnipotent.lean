import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDblOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicWeilRepSchrodingerModelUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerRestriction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalInvariantFormUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagFormBoxConjNeZeroStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixXChar GlobalTheory.DblEval
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.DblEvNonvan

theorem doubled_eval_nonvanishing : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ dd omd dd₁ omd₁, IsDblOf B.ψ M χW om dd omd → IsDblOf B.ψ M₁ χW om₁ dd₁ omd₁ →
      ∀ l ∈ (adeleClass F).adm ((Fin n₁ × Fin d) ⊕ (Fin n₁ × Fin d)),
        (∀ z : Matrix (Fin d) (Fin n₁) (AE F E), ∀ φ ∈ schA F ((Fin n₁ × Fin d) ⊕ (Fin n₁ × Fin d)), l (dd₁.rho B.ψ (z * ((diagCols (Fin n₁) : Matrix (Fin n₁ ⊕ Fin n₁) (Fin n₁) (AE F E)))ᵀ) φ) = l φ) →
        (∃ φ ∈ schA F ((Fin n₁ × Fin d) ⊕ (Fin n₁ × Fin d)), l φ ≠ 0) →
        ∃ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), l ((partRₗ (conjLin e) ∘ₗ partLₗ e) Φ) ≠ 0 := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he dd omd dd₁ omd₁ hD hD₁ l hl hinv hl0
  obtain ⟨d₁', -, hdc₁, -, -⟩ := hD₁
  have hinv' : ∀ x y : Fin n₁ × Fin d → AF F, ∀ φ ∈ schA F ((Fin n₁ × Fin d) ⊕ (Fin n₁ × Fin d)),
      l (schr B.ψ (Sum.elim x x, Sum.elim y (-y)) φ) = l φ := by
    intro x y φ hφ
    obtain ⟨z, hz⟩ := d₁'.e.surjective (x, y)
    have h := hinv z φ hφ
    have h2 := congrFun (GlobalTheory.WeilSchUnique.dd_rho_diag hdc₁ B.ψ z) φ
    rw [hz] at h2
    erw [h2] at h
    exact h
  obtain ⟨c, hc⟩ := GlobalTheory.T.diagonal_invariant_form_unique F B.ψ hP.base.std _ l hl hinv'
  have hc0 : c ≠ 0 := by
    rintro rfl
    obtain ⟨φ, hφ, hne⟩ := hl0
    exact hne (by rw [hc φ hφ, zero_mul])
  obtain ⟨φ₀, h₀, hne⟩ := GlobalTheory.EvSchANe.exists_mem_schA_ne_zero F E σ B n d n₁ d X W X₁ W M M₁ H.ι 1 _ e hP.good
    hP₁.good he
  have h₁ : (fun x => starRingEnd ℂ (φ₀ x)) ∈ schA F (Fin n × Fin d) := GlobalTheory.SchAConj.star_mem_schA F _ φ₀ h₀
  have hg : e φ₀ ∈ schA F (Fin n₁ × Fin d) := he.maps φ₀ h₀
  refine ⟨boxFun φ₀ (fun x => starRingEnd ℂ (φ₀ x)), GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φ₀ h₀ _ h₁, ?_⟩
  have het : (partRₗ (conjLin e) ∘ₗ partLₗ e) (boxFun φ₀ (fun x => starRingEnd ℂ (φ₀ x))) =
      boxFun (e φ₀) (fun x => starRingEnd ℂ (e φ₀ x)) := by
    funext y
    simp only [LinearMap.comp_apply, partLₗ_apply, partRₗ_apply, partR, partL, boxFun, Sum.elim_comp_inl,
      Sum.elim_comp_inr]
    have h1 : (fun x => e (fun x' => φ₀ x' * starRingEnd ℂ (φ₀ x)) (y ∘ Sum.inl)) =
        e φ₀ (y ∘ Sum.inl) • (fun x => starRingEnd ℂ (φ₀ x)) := funext fun x => by
      rw [show (fun x' => φ₀ x' * starRingEnd ℂ (φ₀ x)) = starRingEnd ℂ (φ₀ x) • φ₀ from
        funext fun x' => by simp [mul_comm], map_smul]
      simp [mul_comm]
    rw [h1, map_smul]
    simp [conjLin_apply]
  have hb : boxFun (e φ₀) (fun x => starRingEnd ℂ (e φ₀ x)) ∈ schA F ((Fin n₁ × Fin d) ⊕ (Fin n₁ × Fin d)) :=
    GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ _ hg _ (GlobalTheory.SchAConj.star_mem_schA F _ _ hg)
  rw [het, hc _ hb]
  exact mul_ne_zero hc0 (GlobalTheory.T.diag_form_box_conj_ne_zero F _ (e φ₀) hg hne)

end GlobalTheory.DblEvNonvan
