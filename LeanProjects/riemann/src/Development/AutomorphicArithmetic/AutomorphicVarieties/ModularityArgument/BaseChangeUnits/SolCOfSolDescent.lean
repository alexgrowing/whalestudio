import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.IsAutQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CqStmt

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Bc

def SolC : Prop :=
  ∀ (F₀ F M Ω : Type) [Field F₀] [NumberField F₀] [Field F] [NumberField F] [Field M] [NumberField M] [Field Ω]
    [Algebra F₀ F] [Algebra F M] [Algebra F₀ Ω] [Algebra F Ω] [Algebra M Ω] [IsScalarTower F₀ F Ω] [IsScalarTower F M Ω]
    [IsAlgClosure F₀ Ω] [IsAlgClosure F Ω] [IsAlgClosure M Ω] [IsGalois F M], IsSolvable (M ≃ₐ[F] M) → IsPlusOf F₀ F →
    IsCMField F → IsCMField M → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n →
    ∀ (r : G F Ω →* GL (Fin n) (Qbar l)) (μ : G F₀ Ω →* (Qbar l)ˣ), Continuous r → IsIrr (r.comp (resG F M Ω)) →
      IsAlgChar ι μ → (∀ c c' : G F₀ Ω, IsConjEl c → IsConjEl c' → μ c = μ c') →
      (∃ (c : G F₀ Ω) (P : GL (Fin n) (Qbar l)), IsConjEl c ∧ IsPairing c r (μ.comp (resG F₀ F Ω)) P) →
      (IsAut ι r ↔ IsAut ι (r.comp (resG F M Ω)))

theorem solC_of_solDescent (h : SolDescent) : SolC :=
  fun F₀ F M Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs hp _ hM => h F₀ F M Ω hs hp (Or.inr hM)

def BiQuad : Prop :=
  ∀ (K K' Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field K'] [NumberField K'] [IsCMField K'] [Field Ω] [Algebra ℚ Ω]
    [Algebra K Ω] [Algebra K' Ω] [IsScalarTower ℚ K Ω] [IsScalarTower ℚ K' Ω] [IsAlgClosure ℚ Ω],
    Module.finrank ℚ K = 2 → Module.finrank ℚ K' = 2 →
    ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : IsCMField M) (_ : Algebra K M) (_ : Algebra K' M) (_ : Algebra M Ω)
      (_ : IsScalarTower K M Ω) (_ : IsScalarTower K' M Ω) (_ : IsGalois K M) (_ : IsGalois K' M),
      IsSolvable (M ≃ₐ[K] M) ∧ IsSolvable (M ≃ₐ[K'] M) ∧
      (∀ s : G K Ω, s ∈ (resG K M Ω).range ↔ resG ℚ K Ω s ∈ (resG ℚ K' Ω).range) ∧
      ∀ s : G K' Ω, s ∈ (resG K' M Ω).range ↔ resG ℚ K' Ω s ∈ (resG ℚ K Ω).range

def Third : Prop :=
  ∀ (K K' Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field K'] [NumberField K'] [IsCMField K'] [Field Ω] [Algebra ℚ Ω]
    [Algebra K Ω] [Algebra K' Ω] [IsScalarTower ℚ K Ω] [IsScalarTower ℚ K' Ω] [IsAlgClosure ℚ Ω],
    Module.finrank ℚ K = 2 → Module.finrank ℚ K' = 2 → ∀ (l : ℕ) [Fact l.Prime] (n : ℕ) (r : G ℚ Ω →* GL (Fin n) (Qbar l)),
    IsIrr (r.comp (resG ℚ K Ω)) → IsIrr (r.comp (resG ℚ K' Ω)) →
    ∃ (K'' : Type) (_ : Field K'') (_ : NumberField K'') (_ : IsCMField K'') (_ : Algebra K'' Ω) (_ : IsScalarTower ℚ K'' Ω),
      Module.finrank ℚ K'' = 2 ∧ IsIrr (r.comp ((resG ℚ K Ω).range ⊓ (resG ℚ K'' Ω).range).subtype) ∧
        IsIrr (r.comp ((resG ℚ K' Ω).range ⊓ (resG ℚ K'' Ω).range).subtype)

def Across : Prop :=
  ∀ (K K' Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field K'] [NumberField K'] [IsCMField K'] [Field Ω] [Algebra ℚ Ω]
    [Algebra K Ω] [Algebra K' Ω] [IsScalarTower ℚ K Ω] [IsScalarTower ℚ K' Ω] [IsAlgClosure ℚ Ω],
    Module.finrank ℚ K = 2 → Module.finrank ℚ K' = 2 → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n →
    ∀ (r : G ℚ Ω →* GL (Fin n) (Qbar l)) (θ : G ℚ Ω →* (Qbar l)ˣ), Continuous r → IsAlgChar ι θ → DualTw r θ →
    IsIrr (r.comp ((resG ℚ K Ω).range ⊓ (resG ℚ K' Ω).range).subtype) →
    IsAut ι (r.comp (resG ℚ K Ω)) → IsAut ι (r.comp (resG ℚ K' Ω))

def OfOne : Prop :=
  ∀ (K Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω]
    [IsAlgClosure ℚ Ω], Module.finrank ℚ K = 2 → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n →
    ∀ (r : G ℚ Ω →* GL (Fin n) (Qbar l)) (θ : G ℚ Ω →* (Qbar l)ˣ), IsAlgChar ι θ → DualTw r θ →
    IsIrr (r.comp (resG ℚ K Ω)) → IsAut ι (r.comp (resG ℚ K Ω)) → IsAutQ ι r

def PolK : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], Module.finrank ℚ K = 2 → ∀ (n : ℕ), 1 ≤ n →
    ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω] [IsAlgClosure K Ω]
      (ι : Qbar l ≃+* ℂ) (r : G ℚ Ω →* GL (Fin n) (Qbar l)) (wt : ℤ) (θ : G ℚ Ω →* (Qbar l)ˣ) (P : CuspSub K n),
      IsCycWt l wt θ → DualTw r θ → AttC ι (r.comp (res ℚ Ω K)) P →
      ∃ (χ : HChar (maximalRealSubfield K)) (μ : G (maximalRealSubfield K) Ω →* (Qbar l)ˣ),
        GlobalTheory.ContraPair.PolarizedPair P χ ∧ IsLAdicCharOf ι χ μ ∧
        μ.comp (res (maximalRealSubfield K) Ω K) = θ.comp (res ℚ Ω K) * cycBar K Ω l ^ ((n : ℤ) - 1)

def PstDown : Prop :=
  ∀ (F K Ω : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω]
    [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (O : Type) [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (Bw' : LocBridge l K Ω (Dec (F := K) A) O),
    Bw'.Kw = Bw.Kw → Bw'.j = Bw.j → Bw'.LL = Bw.LL → ∀ (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)),
      IsPstAt (Loc.PP l) Bw' ((r.comp (res F Ω K)).comp (Dec (F := K) A).subtype) →
      IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype)

def LevelPotQ : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (m : Fin n → ℤ) (wt : ℤ), StrictAnti m → ∀ M : ℕ, 1 ≤ M → ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 →
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (r : G ℚ Ω →* GL (Fin n) (Qbar l)),
      IsIrr r → IsAutQ ι r → Level l M m r → (∃ θ, IsCycWt l wt θ ∧ DualTw r θ) → Br.LevelC l M m r

def AutQIso : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ)
    (r r' : G F Ω →* GL (Fin n) (Qbar l)), RepIso r r' → IsAutQ ι r' → IsAutQ ι r

end UpperTheory.V.Z.Bc
