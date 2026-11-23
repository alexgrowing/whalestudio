import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HasLevelOffOf
import Development.AbelianVarietyTheory.Definitions.Divisors.GenOf

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong MvPolynomial

namespace GlobalTheory.CongL

def DGen (a : ℕ) : MvPolynomial (Fin a) ℤ :=
  (∏ i : Fin a, ∏ j : Fin a, if i = j then 1 else ∏ c ∈ Finset.range a, (X i ^ (c + 1) - X j ^ (c + 1))) *
  (∏ i : Fin a, ∏ j : Fin a, ∏ k : Fin a, if j = i ∨ j = k then 1 else (X i * X k - X j ^ 2)) *
  (∏ m ∈ (Finset.univ : Finset (Fin a → Fin (a + 1))).filter (fun m => (∑ i, (m i : ℕ)) = a ∧ m ≠ fun _ => 1),
    ((∏ i, X i ^ (m i : ℕ)) - ∏ i, X i))

def GapJ (a : ℕ) (J : Multiset ℤ) : Prop :=
  ∀ i : ℕ, i + 1 < a →
    (J.sort (· ≤ ·)).getD (i + 1) 0 - (J.sort (· ≤ ·)).getD 0 0 > (a : ℤ) * ((J.sort (· ≤ ·)).getD i 0 - (J.sort (· ≤ ·)).getD 0 0)

def WtLac : SeedWtU := fun E _ _ _ l _ a ι w₀ v' U U' =>
  SameWtOff ι w₀ v' U U' ∧ ∃ τ₀ : E →+* ℂ, OverPl ι τ₀ v' ∧ ∀ lam, HasWeightAt U' τ₀ lam → ∀ J : Multiset ℤ,
    J.map (fun n : ℤ => (n : ℂ)) = (infOfWeight lam).map (fun z => ((a : ℂ) - 1) / 2 - z) → GapJ a J

def FinitenessCondition : Prop := UnitaryWeightConditionWithWeights GlobalTheory.CongW.TyEll (GlobalTheory.CongW.GenOf DGen) WtLac

def CongFin : Prop := CongUW3 GlobalTheory.CongW.TyEll (GlobalTheory.CongW.GenOf DGen) WtLac

def LimFin : Prop := LimWU3

def LimWPhi : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ d : ℕ, ImQ E d → SqAt d l →
    ∀ π : CuspSub E a, InScope .csd l π (quadChar E ^ a) →
    ∀ w₀ v' : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → ((l : ℕ) : 𝓞 E) ∈ v'.asIdeal → Apart v' w₀ →
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), Continuous r ∧ IsSSRep r ∧
      (∀ w, UsPl d w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ B, (CG.mk π).HasSat w B →
        UpperTheory.V.Af.FrobEig ι r w (UpperTheory.V.Af.algSat a (normV w) B)) ∧
      (∀ w, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → Apart w w₀ → Apart w v' → (∃ B, (CG.mk π).HasSat w B) →
        ClauseAt .crys π ι r w ∧ ClauseAt .dR π ι r w) ∧
      (∀ w, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → Apart w w₀ → Apart w v' → ∀ B, (CG.mk π).HasSat w B →
        GlobalTheory.RoadU.SphAt .phi π ι r w B)

example : GapJ 1 0 := fun i hi => absurd hi (by omega)

end GlobalTheory.CongL

end
