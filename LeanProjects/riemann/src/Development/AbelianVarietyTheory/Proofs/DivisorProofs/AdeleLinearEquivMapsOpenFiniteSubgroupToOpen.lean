import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedSpaceVecPairAsAdeles

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.WeilAdm

theorem fintrans_cont (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (B : ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) ≃ₗ[AdeleRing (𝓞 F) F] ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F))) :
    Continuous B :=
  IsModuleTopology.continuous_of_linearMap B.toLinearMap

def finIdem (F : Type) [Field F] [NumberField F] : AdeleRing (𝓞 F) F := (0, 1)

theorem finIdem_mul (F : Type) [Field F] [NumberField F] (a : AdeleRing (𝓞 F) F) :
    finIdem F * a = (0, a.2) := by
  change ((0 : InfiniteAdeleRing F) * a.1, (1 : FiniteAdeleRing (𝓞 F) F) * a.2) = _
  rw [zero_mul, one_mul]

theorem finiteAdelesVecPairAsAdeles_eq_idempotent_smul (F : Type) [Field F] [NumberField F] (κ : Type)
    (m : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) :
    finE2 F m = finIdem F • finE2 F m := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · change _ = finIdem F * (show AdeleRing (𝓞 F) F from (0, m.1 i)); rw [finIdem_mul]; rfl
  · change _ = finIdem F * (show AdeleRing (𝓞 F) F from (0, m.2 i)); rw [finIdem_mul]; rfl

theorem finiteAdeleIdempotent_smul_eq_finiteAdelesVecPair (F : Type) [Field F] [NumberField F] (κ : Type)
    (w : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) :
    finIdem F • w = finE2 F (fun i => (w.1 i).2, fun i => (w.2 i).2) := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · change finIdem F * w.1 i = _; rw [finIdem_mul]; rfl
  · change finIdem F * w.2 i = _; rw [finIdem_mul]; rfl

theorem finiteAdelesVecPairAsAdeles_add (F : Type) [Field F] [NumberField F] (κ : Type)
    (a b : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) :
    finE2 F (a + b) = finE2 F a + finE2 F b := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · change ((0 : InfiniteAdeleRing F), a.1 i + b.1 i) = ((0 : InfiniteAdeleRing F) + 0, a.1 i + b.1 i)
    rw [add_zero]
  · change ((0 : InfiniteAdeleRing F), a.2 i + b.2 i) = ((0 : InfiniteAdeleRing F) + 0, a.2 i + b.2 i)
    rw [add_zero]

theorem finiteAdelesVecPairAsAdeles_zero (F : Type) [Field F] [NumberField F] (κ : Type) :
    finE2 F (0 : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) = 0 := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> rfl

theorem fintrans : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (B : ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) ≃ₗ[AdeleRing (𝓞 F) F] ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)))
    (M : AddSubgroup ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F))), IsOpen (M : Set ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F))) →
      ∃ M' : AddSubgroup ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)), IsOpen (M' : Set ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F))) ∧
        ∀ m' ∈ M', ∃ m ∈ M, B (GlobalTheory.WeilAdm.finE2 F m) = GlobalTheory.WeilAdm.finE2 F m' := by
  intro F _ _ κ _ B M hM
  let g : ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) →+
      ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) :=
    { toFun := fun m' => (fun i => ((B.symm (finE2 F m')).1 i).2, fun i => ((B.symm (finE2 F m')).2 i).2)
      map_zero' := by
        simp only [finiteAdelesVecPairAsAdeles_zero, map_zero]; rfl
      map_add' := fun a b => by
        simp only [finiteAdelesVecPairAsAdeles_add, map_add]; rfl }
  have hg : ∀ m', finE2 F (g m') = B.symm (finE2 F m') := by
    intro m'
    rw [finiteAdelesVecPairAsAdeles_eq_idempotent_smul F κ m', map_smul, finiteAdeleIdempotent_smul_eq_finiteAdelesVecPair]
    rfl
  have hgc : Continuous g := by
    have h1 : Continuous fun m' : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F) => B.symm (finE2 F m') := by
      refine (fintrans_cont F κ B.symm).comp ?_
      refine Continuous.prodMk (continuous_pi fun i => ?_) (continuous_pi fun i => ?_)
      · exact continuous_const.prodMk ((continuous_apply i).comp continuous_fst)
      · exact continuous_const.prodMk ((continuous_apply i).comp continuous_snd)
    refine Continuous.prodMk (continuous_pi fun i => ?_) (continuous_pi fun i => ?_)
    · exact continuous_snd.comp ((continuous_apply i).comp (continuous_fst.comp h1))
    · exact continuous_snd.comp ((continuous_apply i).comp (continuous_snd.comp h1))
  refine ⟨M.comap g, hM.preimage hgc, fun m' hm' => ⟨g m', hm', ?_⟩⟩
  rw [hg, LinearEquiv.apply_symm_apply]

end GlobalTheory.WeilAdm
