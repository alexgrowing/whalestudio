import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.GalUnitaryT
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.ExistsRec

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.Zero.LLC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def LocRelT (l : ℕ) (x δ : kˣ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
    (P T : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ C : Subgroup 𝓀[k]ˣ, ellC l _ ≤ C → ∀ θ, IsTheta π C θ → ∀ χ : (Fin n → kˣ) →* ℂˣ,
    (⨅ t, Module.End.maxGenEigenspace (θ t : Module.End ℂ (fixd π (iwC k n C))) (χ t : ℂ)) ≠ ⊥ →
    ∀ α : Fin n → ℂ, (∀ i, α i = (resCard k : ℂ) ^ (i : ℕ) * χ (Pi.mulSingle i x)) →
    ((IsSpherical π ∨ ∀ i i', i ≠ i' → α i ≠ α i' ∧ α i ≠ (resCard k : ℂ) * α i') →
      P.charpoly = ∏ i, (Polynomial.X - Polynomial.C (α i))) ∧
    ((∀ i i', i ≠ i' → α i ≠ α i' ∧ α i ≠ (resCard k : ℂ) * α i') → ∀ i,
      (List.ofFn fun i' => if i' = i then 1 else P - α i' • (1 : Matrix (Fin n) (Fin n) ℂ)).prod *
        (T - (χ (Pi.mulSingle i δ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) = 0)

example : type_of% @LocRel := @LocRelT

variable {l : ℕ} {x δ : kˣ} {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) k) V}
  {P T : Matrix (Fin n) (Fin n) ℂ}

theorem relT' (h : LocRelT l x δ π P T) : LocRelT l x δ π P T := h

end Loc

def LocDataT : Prop :=
  LocP → ∀ (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (Bq : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (hB : IsPlaceOver Bq w), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ fr τ : G E Ω, fr ∈ Dec (F := E) Bq → IsFrob (F := E) Bq (normV w) fr⁻¹ → GlobalTheory.TameQuot.IsProGen E Bq l τ → resCard (w.adicCompletion E) = normV w ∧ ∃ x δ : (w.adicCompletion E)ˣ, IsUnif x ∧ IsGenMod _ (ellC l _) δ ∧ ∀ (n : ℕ) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin n) (Qbar l)) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))), (∀ rc : IrrGL (w.adicCompletion E) → WD hB, IsRecT hB rc → WDT ι r (rc (algNorm σ))) → LocRelT l x δ σ.ρ ((r fr : Matrix (Fin n) (Fin n) (Qbar l)).map ι) ((r τ : Matrix (Fin n) (Fin n) (Qbar l)).map ι)

def WOT : type_of% @UpperTheory.V.Lev.WO := fun ι r y => WDT ι r y

example : type_of% @UpperTheory.V.Af.LocGlob := @LocGlobT
example : type_of% @UpperTheory.V.Af.Gu.ParAt := @ParAtT

end UpperTheory.V.Z.Win
