import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ListProdFactor

theorem om_listProd_pure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (l : List (Pl F)), l.Nodup → ∀ h : Pl F → UA σ W.J, (∀ v ∈ l, h v ∈ UAt σ W (evFin F v)) →
    ∀ (f : SInf F (Fin n × Fin d)) (φ φ₁ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) →
      (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
      (∀ v ∈ l, φ₁ v ∈ SB _ ∧ Acts (evFin F v) (om (1, h v)) (φ v) (φ₁ v)) → (∀ v, v ∉ l → φ₁ v = φ v) →
      om (1, (l.map h).prod) (pure f φ) = pure f φ₁ := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP l hl h hh f φ φ₁ hφSB hφstd
  classical
  induction l generalizing φ₁ with
  | nil =>
    intro _ hout
    have e : φ₁ = φ := funext fun v => hout v (List.not_mem_nil)
    subst e
    show om 1 _ = _
    rw [map_one]
    rfl
  | cons a l' ih =>
    intro hin hout
    have ha : a ∉ l' := (List.nodup_cons.1 hl).1
    have hl' : l'.Nodup := (List.nodup_cons.1 hl).2
    let φ₁' : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ := fun v => if v ∈ l' then φ₁ v else φ v
    have hφ₁'a : φ₁' a = φ a := by simp only [φ₁', if_neg ha]
    have hIH : om (1, (l'.map h).prod) (pure f φ) = pure f φ₁' := by
      refine ih hl' (fun v hv => hh v (List.mem_cons_of_mem a hv)) φ₁' ?_ ?_
      · intro v hv
        have := hin v (List.mem_cons_of_mem a hv)
        simp only [φ₁', if_pos hv]
        exact this
      · intro v hv
        simp only [φ₁', if_neg hv]
    have hSB' : ∀ v, φ₁' v ∈ SB _ := by
      intro v
      by_cases hv : v ∈ l'
      · simp only [φ₁', if_pos hv]; exact (hin v (List.mem_cons_of_mem a hv)).1
      · simp only [φ₁', if_neg hv]; exact hφSB v
    have hstd' : ∀ᶠ v in Filter.cofinite,
        φ₁' v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
      have hfin : ∀ᶠ v in Filter.cofinite, v ∉ l' :=
        (l'.finite_toSet).compl_mem_cofinite
      filter_upwards [hφstd, hP.good.std, hfin] with v h1 h2 h3
      simp only [φ₁', if_neg h3]
      rw [h1, h2]
    have hpure := GlobalTheory.TensUniq.pure_mem_schA f φ₁' hSB' hstd'
    have hmul := fun x => GlobalTheory.PureFactor.mulSupport_finite φ₁' hstd' x
    have hacts : Acts (evFin F a) (om (1, h a)) (φ₁' a) (φ₁ a) := by
      rw [hφ₁'a]; exact (hin a List.mem_cons_self).2
    have hstep := GlobalTheory.ThK.LocalOps.acts_pure a (om (1, h a)) f φ₁' (φ₁ a) hpure hmul hacts
    have hupd : Function.update φ₁' a (φ₁ a) = φ₁ := by
      funext v
      by_cases hva : v = a
      · subst hva; simp
      · rw [Function.update_of_ne hva]
        by_cases hv : v ∈ l'
        · simp only [φ₁', if_pos hv]
        · simp only [φ₁', if_neg hv]
          exact (hout v (by simp [hva, hv])).symm
    have hsplit : ((1 : UA σ X.J), ((a :: l').map h).prod) = ((1 : UA σ X.J), h a) * (1, (l'.map h).prod) := by
      rw [List.map_cons, List.prod_cons]
      ext <;> simp
    rw [hsplit, map_mul, Module.End.mul_apply, hIH, hstep, hupd]

end GlobalTheory.ListProdFactor
