import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

namespace GlobalTheory.PureListAct

theorem om_list_prod_pure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd)
    (hv : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Wd.J)
    (φ φ₁ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ),
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) → (∀ v, φ₁ v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) →
    (∀ v, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (1, hv v)) (φ v) (φ₁ v)) →
    (∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∀ l : List (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), l.Nodup → ∀ f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
      om (1, (l.map hv).prod) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (fun v => if v ∈ l then φ₁ v else φ v) := by
  intro F E _ _ _ _ _ σ n d Y Wd om hv φ φ₁ hφ hφ₁ hact hstd l
  induction l with
  | nil =>
    intro _ f
    have h1 : om (1, (([] : List (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)).map hv).prod) = 1 := by
      rw [List.map_nil, List.prod_nil, Prod.mk_one_one, map_one]
    rw [h1, Module.End.one_apply]
    congr 1
  | cons a t ih =>
    intro hl f
    rw [List.nodup_cons] at hl
    have hsplit : om (1, ((a :: t).map hv).prod) = om (1, hv a) * om (1, (t.map hv).prod) := by
      rw [List.map_cons, List.prod_cons, ← map_mul, Prod.mk_mul_mk, one_mul]
    rw [hsplit, Module.End.mul_apply, ih hl.2 f]
    set φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ :=
      fun v => if v ∈ t then φ₁ v else φ v with hφ'

    have hstd' : ∀ᶠ v in Filter.cofinite,
        φ' v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
      filter_upwards [hstd, (List.finite_toSet t).compl_mem_cofinite] with v hv1 hv2
      have hvt : v ∉ t := hv2
      simp only [hφ', if_neg hvt]
      exact hv1
    have hSB' : ∀ v, φ' v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v) := by
      intro v
      by_cases h : v ∈ t
      · simp only [hφ', if_pos h]; exact hφ₁ v
      · simp only [hφ', if_neg h]; exact hφ v
    have hat : φ' a = φ a := by simp only [hφ', if_neg hl.1]

    obtain ⟨r, hr, htens⟩ := GlobalTheory.PureFactor.exists_rest_factor a f φ' hstd'
    have hfac : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ' = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F a) (φ a) r := by
      rw [htens, ← hat, Function.update_eq_self]
    have hrest : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.AdelicU.evFin F a) (φ a) r :=
      ⟨hr, hfac ▸ GlobalTheory.TensUniq.pure_mem_schA f φ' hSB' hstd'⟩
    rw [hfac, hact a r hrest, htens]
    congr 1
    funext v
    by_cases h : v = a
    · subst h
      simp
    · rw [Function.update_of_ne h]
      simp [hφ', h]

end GlobalTheory.PureListAct
