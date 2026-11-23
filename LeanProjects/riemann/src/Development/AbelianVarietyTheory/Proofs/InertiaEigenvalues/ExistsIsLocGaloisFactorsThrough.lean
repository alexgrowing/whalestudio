import Mathlib
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.EpsilonConsistencyFiniteOrder

noncomputable section

open NumberField IsDedekindDomain ValuativeRel
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.WeilRestrict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DelEps

variable {Ω : Type} [Field Ω] {A : ValuationSubring Ω}

section Defs

variable {K : Type} [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] {v : HeightOneSpectrum (𝓞 K)}
  {h : IsPlaceOver A v}

def LocExt.fixSub (M : LocExt h) : Subgroup (Weil h) where
  carrier := {σ | ∀ z : M.L, (σ : G K Ω) (algebraMap M.L Ω z) = algebraMap M.L Ω z}
  one_mem' := fun _ => rfl
  mul_mem' := fun {σ τ} hσ hτ z => by
    show (σ : G K Ω) ((τ : G K Ω) _) = _
    rw [hτ z, hσ z]
  inv_mem' := fun {σ} hσ z => by
    show (σ : G K Ω).symm _ = _
    rw [AlgEquiv.symm_apply_eq, hσ z]

theorem LocExt.mem_fixSub (M : LocExt h) (σ : Weil h) :
    σ ∈ M.fixSub ↔ ∀ z : M.L, (σ : G K Ω) (algebraMap M.L Ω z) = algebraMap M.L Ω z := Iff.rfl

theorem LocExt.index_fixSub (M : LocExt h) : M.fixSub.index = Module.finrank K M.L :=
  EpsUnique.index_eq_finrank K M.L Ω A v h M.loc _ M.mem_fixSub

instance LocExt.finiteIndex_fixSub (M : LocExt h) : M.fixSub.FiniteIndex :=
  ⟨by rw [M.index_fixSub]; exact Module.finrank_pos.ne'⟩

def LocExt.IsLocGalois (M : LocExt h) : Prop := M.fixSub.Normal

variable {ψ : AddChar (v.adicCompletion K) Circle}

def BTerm.FactorsThrough (t : BTerm h ψ) (M : LocExt h) : Prop :=
  M.fixSub ≤ t.E.fixSub ∧ ∀ σ : Weil t.E.h', resWeil h t.E.h' σ ∈ M.fixSub → t.χ (t.a σ) = 1

end Defs

def WeilDeligneFactorsFiniteGalois (n : ℕ) : Prop :=
  ∀ (Ω : Type) [Field Ω] (A : ValuationSubring Ω) (K : Type) [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
    (v : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A v) (ψ : AddChar (v.adicCompletion K) Circle), Continuous ψ → ψ ≠ 1 →
    ∀ M : LocExt h, M.IsLocGalois → Module.finrank K M.L ≤ n →
    ∀ l : List (BTerm h ψ), (∀ t ∈ l, t.FactorsThrough M) →
      (∀ σ : Weil h, (l.map fun t => (t.n : ℂ) * (trW t.indChi σ - trW t.indOne σ)).sum = 0) → val l = 1

theorem WeilDeligneFactorsFiniteGalois.mono {m n : ℕ} (hmn : m ≤ n) (H : WeilDeligneFactorsFiniteGalois n) : WeilDeligneFactorsFiniteGalois m :=
  fun Ω _ A K _ _ _ _ v h ψ hc h1 M hM hd => H Ω A K v h ψ hc h1 M hM (hd.trans hmn)

end GlobalTheory.DelEps

end
