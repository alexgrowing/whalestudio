import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFunctionalPure

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.PureLift

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem exists_sep (vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ)
    (hstd : ∀ᶠ v in Filter.cofinite, vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (lam : SInf F κ →ₗ[ℂ] ℂ) (l : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ)
    (hl : {v | l v (vac v) ≠ 1}.Finite) :
    ∃ Λ : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ, ∀ (f : SInf F κ) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ),
      (∀ᶠ v in Filter.cofinite, φ v = vac v) → Λ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = lam f * ∏ᶠ v, l v (φ v) := by
  first
  | exact @_root_.GlobalTheory.FiniteAdelicPoints.exists_functional_pure
  | exact _root_.GlobalTheory.FiniteAdelicPoints.exists_functional_pure
  | (apply _root_.GlobalTheory.FiniteAdelicPoints.exists_functional_pure <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiniteAdelicPoints.exists_functional_pure <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiniteAdelicPoints.exists_functional_pure <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiniteAdelicPoints.exists_functional_pure ..)

theorem exists_pureLift : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n d : ℕ}
    (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Z) (ψ : AddChar (AF F) ℂ),
    M.IsGood ψ → ∀ (P : Type) [AddCommGroup P] [Module ℂ P] (pr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →ₗ[ℂ] P)
    (N : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F → Type) [∀ v, AddCommGroup (N v)] [∀ v, Module ℂ (N v)]
    (pv : ∀ v, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] N v) (s : ∀ v, N v),
    (∀ᶠ v in Filter.cofinite, pv v (M.vac v) = s v) →
    ∃ q : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] P ⊗[ℂ] GlobalTheory.SmallThetaModules.RTens s,
      ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        q (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = pr f ⊗ₜ GlobalTheory.SmallThetaModules.pureT s (fun v => pv v (φ v)) := by
  intro F E _ _ _ _ _ σ n d Y Z M ψ hM P _ _ pr N _ _ pv s hs
  classical
  let b := Module.Free.chooseBasis ℂ P
  have hsep : ∀ (i : Module.Free.ChooseBasisIndex ℂ P) (l : GlobalTheory.SmallThetaModules.AdmFun s),
      ∃ Λ : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ, ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
        (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ), (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        Λ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = (b.coord i) (pr f) * ∏ᶠ v, l.1 v (pv v (φ v)) := by
    intro i l
    refine exists_sep M.vac hM.std ((b.coord i).comp pr) (fun v => (l.1 v).comp (pv v)) ?_
    refine ((Filter.eventually_cofinite.1 hs).union l.2).subset fun v hv => ?_
    by_cases e : pv v (M.vac v) = s v
    · right
      simp only [Set.mem_setOf_eq, LinearMap.comp_apply, e] at hv ⊢
      exact hv
    · left
      exact e
  choose Λ hΛ using hsep
  let ι' : P ⊗[ℂ] GlobalTheory.SmallThetaModules.RTens s →ₗ[ℂ]
      (Module.Free.ChooseBasisIndex ℂ P → GlobalTheory.SmallThetaModules.AdmFun s → ℂ) :=
    (LinearMap.compLeft (GlobalTheory.SmallThetaModules.RTens s).subtype _) ∘ₗ Finsupp.lcoeFun ∘ₗ
      (TensorProduct.equivFinsuppOfBasisLeft b).toLinearMap
  have hinj : Function.Injective ι' := by
    intro t t' h
    apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
    ext i : 1
    apply Subtype.ext
    exact congrFun h i
  obtain ⟨r, hr⟩ := ι'.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨r ∘ₗ LinearMap.pi (fun i => LinearMap.pi (fun l => Λ i l)), fun f φ _ hφ => ?_⟩
  have hR : Formalism.MainNotions.KudlaSiegelWeil.Restr s (fun v => pv v (φ v)) := by
    refine ((Filter.eventually_cofinite.1 hφ).union (Filter.eventually_cofinite.1 hs)).subset fun v hv => ?_
    by_cases e : φ v = M.vac v
    · right
      simp only [Set.mem_setOf_eq, e] at hv ⊢
      exact hv
    · left
      exact e
  have h1 : LinearMap.pi (fun i => LinearMap.pi (fun l => Λ i l)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) =
      ι' (pr f ⊗ₜ GlobalTheory.SmallThetaModules.pureT s (fun v => pv v (φ v))) := by
    funext i l
    rw [LinearMap.pi_apply, LinearMap.pi_apply, hΛ i l f φ hφ]
    simp only [ι', LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lcoeFun_apply, LinearMap.compLeft_apply,
      Function.comp_apply, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, Submodule.subtype_apply,
      Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, GlobalTheory.SmallThetaModules.coe_pureT hR,
      GlobalTheory.SmallThetaModules.evFam, Module.Basis.coord_apply]
  rw [LinearMap.comp_apply, h1, ← LinearMap.comp_apply, hr, LinearMap.id_apply]

end GlobalTheory.PureLift
