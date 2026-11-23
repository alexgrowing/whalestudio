import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombineApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchPartFinIncl
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Matrix TensorProduct

noncomputable section

namespace GlobalTheory.ArchFinSplit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem infTensor_bijective :
    Function.Bijective (fun (y : InfiniteAdeleRing F ⊗[F] E) (w : InfinitePlace F) =>
      Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E) y) := by
  classical
  let P : InfiniteAdeleRing F ⊗[F] E ≃ₗ[F] (∀ w : InfinitePlace F, w.Completion ⊗[F] E) :=
    TensorProduct.piLeft F E (fun w : InfinitePlace F => w.Completion)
  have key : ∀ y : InfiniteAdeleRing F ⊗[F] E, (fun (w : InfinitePlace F) =>
      Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E) y) = P y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => funext w; simp
    | add x y hx hy =>
      funext w
      rw [P.map_add, Pi.add_apply, ← congrFun hx w, ← congrFun hy w]
      exact map_add _ x y
    | tmul a x => rfl
  have : (fun (y : InfiniteAdeleRing F ⊗[F] E) (w : InfinitePlace F) =>
      Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E) y) = P := funext key
  rw [this]
  exact P.bijective

end GlobalTheory.ArchFinSplit

namespace GlobalTheory.ArchFinSplit

theorem splitHom_bijective : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (τ : ∀ w : InfinitePlace F, EmbOver E w), IsCMExt F E σ →
    Function.Bijective (GlobalTheory.ArchFinSplit.splitHom τ) := by
  intro F E _ _ _ _ _ σ τ h
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  have hg : Function.Bijective (fun (y : InfiniteAdeleRing F ⊗[F] E) (w : InfinitePlace F) =>
      infEmb (τ w) (Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E) y)) := by
    refine ⟨fun a b hab => infTensor_bijective.1 (funext fun w => (infEmb_bijective h (τ w)).1 (congrFun hab w)),
      fun z => ?_⟩
    obtain ⟨y, hy⟩ := infTensor_bijective.2 (fun w => ((infEmb_bijective h (τ w)).2 (z w)).choose)
    exact ⟨y, funext fun w => by
      simp only [congrFun hy w]; exact ((infEmb_bijective h (τ w)).2 (z w)).choose_spec⟩
  have hc := (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).bijective
  have hfac : ⇑(splitHom τ) = Prod.map (fun (y : InfiniteAdeleRing F ⊗[F] E) (w : InfinitePlace F) =>
      infEmb (τ w) (Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E) y))
      (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E) ∘ e := by
    funext z
    refine Prod.ext (funext fun w => ?_) ?_
    · change piInf (τ w) z = infEmb (τ w) (Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E) (e z).1)
      rw [(he z).1]
      change infEmb (τ w) (compInf F E w z) = _
      congr 1
      induction z using TensorProduct.induction_on with
      | zero => rw [map_zero]; erw [map_zero]
      | add x y hx hy => rw [map_add, hx, hy]; erw [map_add, map_add]
      | tmul a x => rfl
    · change finPart F E z = Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E (e z).2
      rw [(he z).2]
      rfl
  rw [hfac]
  exact (hg.prodMap hc).comp e.bijective

end GlobalTheory.ArchFinSplit
