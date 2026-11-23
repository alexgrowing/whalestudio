import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwIwQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHeckePairIwC

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

section Loc
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
  (C : Subgroup 𝓀[k]ˣ)

private theorem iwLev_loc : IsOpen (AlgebraTools.iwC k n C : Set (GL (Fin n) k)) ∧ IsCompact (AlgebraTools.iwC k n C : Set (GL (Fin n) k)) ∧
    AlgebraTools.iwC k n C ≤ AlgebraTools.iwC k n ⊤ := by
  have h1 := (AlgebraTools.memIwC k n C).1
  have h2 := (AlgebraTools.memIwC k n C).2.1
  have hle : AlgebraTools.iwC k n C ≤ AlgebraTools.iwC k n ⊤ := by
    intro g hg
    rw [h2]
    exact ((h1 g).1 hg).1
  have hopen : IsOpen (AlgebraTools.iwC k n C : Set (GL (Fin n) k)) :=
    Subgroup.isOpen_mono (show KOne k (Fin n) ≤ AlgebraTools.iwC k n C from le_sup_left.trans le_sup_left)
      GlobalTheory.StepData.isOpen_KOne
  refine ⟨hopen, ?_, hle⟩
  refine IsCompact.of_isClosed_subset GlobalTheory.SplitFlip.isCompact_KO (Subgroup.isClosed_of_isOpen _ hopen) ?_
  intro g hg
  exact GlobalTheory.SmGL.iwahori_le_KO k (Fin n) ((h1 g).1 hg).1

private theorem iwLev_conj {x g : GL (Fin n) k} (hx : x ∈ AlgebraTools.iwC k n C) (hg : g ∈ AlgebraTools.iwC k n ⊤) :
    g * x * g⁻¹ ∈ AlgebraTools.iwC k n C := by
  have h2 := (AlgebraTools.memIwC k n C).2.1
  have h3 := (AlgebraTools.memIwC k n C).2.2.1
  rw [h2] at hg
  exact h3 g hg x hx

end Loc

theorem UpperTheory.V.Hi.levelUR2IwLev :
    ∀ (l : ℕ) (L : Type) [Field L] [NumberField L] (n q : ℕ) (w : Fin q → Plc L), (∀ j C, IsOpen (AlgebraTools.iwC ((w j).adicCompletion L) n C : Set (GLw n (w j))) ∧ IsCompact (AlgebraTools.iwC ((w j).adicCompletion L) n C : Set (GLw n (w j))) ∧ AlgebraTools.iwC ((w j).adicCompletion L) n C ≤ AlgebraTools.iwC ((w j).adicCompletion L) n ⊤) ∧ ((Pa.UIw1 l n w).subgroupOf (Pa.UIw n w)).Normal := by
  intro l L _ _ n q w
  refine ⟨fun j C => iwLev_loc _ n C, ?_⟩
  have hle : Pa.UIw1 l n w ≤ Pa.UIw n w := by
    intro g hg
    simp only [Pa.UIw, Pa.UIw1, Subgroup.mem_pi] at hg ⊢
    intro j hj
    exact (iwLev_loc _ n _).2.2 (hg j hj)
  rw [Subgroup.normal_subgroupOf_iff hle]
  intro h g hh hg
  simp only [Pa.UIw, Pa.UIw1, Subgroup.mem_pi] at hh hg ⊢
  intro j hj
  exact iwLev_conj _ n _ (hh j hj) (hg j hj)
