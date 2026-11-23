import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RDual2

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

namespace UpperTheory.V.Af.Sol

def RC (F : Type) [Field F] [NumberField F] : Prop := IsTotallyReal F ∨ IsCMField F

theorem rc_rat : RC ℚ := Or.inl inferInstance

section Defs

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

omit [NumberField F] in

def SameSign (μ : G F Ω →* (Qbar l)ˣ) : Prop := ∀ c c' : G F Ω, IsConjEl c → IsConjEl c' → μ c = μ c'

omit [NumberField F] in
theorem sameSign_one : SameSign (1 : G F Ω →* (Qbar l)ˣ) := fun _ _ _ _ => rfl

omit [NumberField F] in

def Pol (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∃ (F₀ : Type) (_ : Field F₀) (_ : NumberField F₀) (_ : Algebra F₀ F) (_ : Algebra F₀ Ω) (_ : IsScalarTower F₀ F Ω)
    (_ : IsAlgClosure F₀ Ω), IsTotallyReal F₀ ∧ ∃ (μ : G F₀ Ω →* (Qbar l)ˣ) (c : G F₀ Ω) (P : GL (Fin n) (Qbar l)),
      IsAlgChar ι μ ∧ SameSign μ ∧ IsConjEl c ∧ IsPairing c r (μ.comp (resG F₀ F Ω)) P

variable (F Ω) in

def Equi (M : Type) [Field M] [NumberField M] [Algebra F M] [Algebra M Ω] [IsScalarTower F M Ω] : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ r : G F Ω →* GL (Fin n) (Qbar l), Continuous r →
    IsIrr (r.comp (resG F M Ω)) → Pol ι r → (IsAut ι r ↔ IsAut ι (r.comp (resG F M Ω)))

end Defs

def CycConj : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (c : G F Ω), IsConjEl c → cycBar F Ω l c = -1

def ToPolR : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [IsTotallyReal F] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ)
    (r : G F Ω →* GL (Fin n) (Qbar l)), Pol ι r → ∃ (θ : G F Ω →* (Qbar l)ˣ) (χ : HChar F), DualTw r θ ∧
      IsCharOf ι χ (θ * cycBar F Ω l ^ ((n : ℤ) - 1)) ∧ SameSign (θ * cycBar F Ω l ^ ((n : ℤ) - 1))

def ToPolC : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [IsCMField F] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ)
    (r : G F Ω →* GL (Fin n) (Qbar l)), Pol ι r → ∃ (μ : G (maximalRealSubfield F) Ω →* (Qbar l)ˣ) (χ : HChar (maximalRealSubfield F))
      (c : G (maximalRealSubfield F) Ω) (P : GL (Fin n) (Qbar l)), IsLAdicCharOf ι χ μ ∧ SameSign μ ∧ IsConjEl c ∧
        IsPairing c r (cycBar F Ω l ^ (1 - (n : ℤ)) * μ.comp (resG (maximalRealSubfield F) F Ω)) P

def Parallel : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (χ : HChar F) (a : (F →+* ℂ) → ℤ), IsAlgPos χ a → ∀ φ φ', a φ = a φ'

def SignOf : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [IsTotallyReal F] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (χ : HChar F) (μ : G F Ω →* (Qbar l)ˣ), IsCharOf ι χ μ → SameSign μ →
      ∀ v v' : InfinitePlace F, χ.locInf v (-1) = χ.locInf v' (-1)

def CharFrob : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (χ : HChar F) (μ : G F Ω →* (Qbar l)ˣ), IsCharOf ι χ μ → ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      χ.UnrAt v ∧ CharEig ι μ v (χ.val v : ℂˣ)

def EigBasic : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (v : HeightOneSpectrum (𝓞 F)),
    (∀ (δ δ' : G F Ω →* (Qbar l)ˣ) (z z' : ℂˣ), CharEig ι δ v z → CharEig ι δ' v z' → CharEig ι (δ * δ'⁻¹) v ((z * z'⁻¹ : ℂˣ) : ℂ)) ∧
    (∀ (δ : G F Ω →* (Qbar l)ˣ) (z z' : ℂˣ), CharEig ι δ v z → CharEig ι δ v z' → z = z') ∧
    ∀ (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)) (B B' : Multiset ℂˣ),
      FrobEig ι r v (algSat n (normV v) B) → FrobEig ι r v (algSat n (normV v) B') → B = B'

def NormChar : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K M] [Algebra K Ω]
    [Algebra M Ω] [IsScalarTower K M Ω] [IsAlgClosure K Ω] [IsAlgClosure M Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (η : HChar K), (η = 1 ∨ IsNormChar M η) → ∃ δ : G K Ω →* (Qbar l)ˣ, δ.comp (resG K M Ω) = 1 ∧
      ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, CharEig ι δ v (η.val v : ℂˣ)

def FinChar : Prop :=
  (∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (δ : G F Ω →* (Qbar l)ˣ), IsOpen (δ.ker : Set (G F Ω)) → IsAlgChar ι δ) ∧
  ∀ (K M Ω : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K M] [Algebra K Ω]
    [Algebra M Ω] [IsScalarTower K M Ω] [IsAlgClosure K Ω] [IsAlgClosure M Ω] (l : ℕ) [Fact l.Prime]
    (δ : G K Ω →* (Qbar l)ˣ), δ.comp (resG K M Ω) = 1 → IsOpen (δ.ker : Set (G K Ω))

def ConjAgree : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K M] [Algebra K Ω]
    [Algebra M Ω] [IsScalarTower K M Ω] [IsAlgClosure K Ω] [IsAlgClosure M Ω] (l : ℕ) [Fact l.Prime], RC M →
    ∀ δ : G K Ω →* (Qbar l)ˣ, δ.comp (resG K M Ω) = 1 → SameSign δ

def ExtChar : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K M] [Algebra K Ω]
    [Algebra M Ω] [IsScalarTower K M Ω] [IsAlgClosure K Ω] [IsAlgClosure M Ω] [IsCMField K] [IsCMField M] [IsGalois K M]
    (l : ℕ) [Fact l.Prime] (δ : G K Ω →* (Qbar l)ˣ), δ.comp (resG K M Ω) = 1 →
      ∃ δ' : G (maximalRealSubfield K) Ω →* (Qbar l)ˣ, δ'.comp (resG (maximalRealSubfield K) K Ω) = δ ∧
        (∀ c, IsConjEl c → δ' c = 1) ∧ IsOpen (δ'.ker : Set (G (maximalRealSubfield K) Ω))

def PolSatR : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (n : ℕ), 1 ≤ n → ∀ (π : TR.CuspSub F n) (ψ : HChar F),
    (∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ψ.UnrAt v ∧ ∃ B, π.HasSat v B ∧ B.map (·⁻¹) = B.map (· * (ψ.val v)⁻¹)) →
      π.IsSelfDualBy ψ

def FrobDualC : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [IsCMField F] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ)
    (r : G F Ω →* GL (Fin n) (Qbar l)) (θ : G F Ω →* (Qbar l)ˣ) (c : G (maximalRealSubfield F) Ω) (P : GL (Fin n) (Qbar l)),
    IsConjEl c → IsPairing c r (cycBar F Ω l ^ (1 - (n : ℤ)) * θ) P →
    ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ∀ (B B' : Multiset ℂˣ) (z : ℂˣ),
      FrobEig ι r w (algSat n (normV w) B) → FrobEig ι r (cPl w) (algSat n (normV (cPl w)) B') → CharEig ι θ w z →
      B'.map (·⁻¹) = B.map (· * z⁻¹)

def ConjUnder : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsCMField K] [IsCMField M]
    (w : HeightOneSpectrum (𝓞 M)), (cPl w).under (𝓞 K) = cPl (w.under (𝓞 K)) ∧ normV (cPl w) = normV w ∧ cPl (cPl w) = w

def DualBcR : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K M] [Algebra K Ω]
    [Algebra M Ω] [IsScalarTower K M Ω] [IsAlgClosure K Ω] [IsAlgClosure M Ω] [IsTotallyReal K] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (n : ℕ) (r : G K Ω →* GL (Fin n) (Qbar l)) (π : TR.CuspSub K n) (sat' : HeightOneSpectrum (𝓞 M) → Multiset ℂˣ → Prop),
    (∀ w B B', sat' w B → sat' w B' → B = B') → WeakBC π.HasSat sat' → AttachedSys ι (r.comp (resG K M Ω)) sat' →
    ∀ (θ : G K Ω →* (Qbar l)ˣ) (χ : HChar K), DualTw r θ → IsCharOf ι χ (θ * cycBar K Ω l ^ ((n : ℤ) - 1)) →
      WeakBC (π.dual.twist χ).HasSat sat'

def DualBcC : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K M] [Algebra K Ω]
    [Algebra M Ω] [IsScalarTower K M Ω] [IsAlgClosure K Ω] [IsAlgClosure M Ω] [IsCMField K] [IsCMField M] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (n : ℕ) (r : G K Ω →* GL (Fin n) (Qbar l)) (π : CuspSub K n) (sat' : HeightOneSpectrum (𝓞 M) → Multiset ℂˣ → Prop),
    (∀ w B B', sat' w B → sat' w B' → B = B') → WeakBC (CG.mk π).HasSat sat' → AttachedSys ι (r.comp (resG K M Ω)) sat' →
    ∀ (μ : G (maximalRealSubfield K) Ω →* (Qbar l)ˣ) (χ : HChar (maximalRealSubfield K)) (c : G (maximalRealSubfield K) Ω)
      (P : GL (Fin n) (Qbar l)), IsLAdicCharOf ι χ μ → IsConjEl c →
      IsPairing c r (cycBar K Ω l ^ (1 - (n : ℤ)) * μ.comp (resG (maximalRealSubfield K) K Ω)) P →
      WeakBC (CG.mk ((GlobalTheory.ThetaPull.thetaSub π).twist (compNorm K χ))).HasSat sat'

def ExDownR : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K M] [Algebra K Ω]
    [Algebra M Ω] [IsScalarTower K M Ω] [IsAlgClosure K Ω] [IsAlgClosure M Ω] [IsGalois K M] [IsTotallyReal K],
    (Module.finrank K M).Prime → RC M → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n →
    ∀ (r : G K Ω →* GL (Fin n) (Qbar l)) (π : TR.CuspSub K n) sat' inf', Pol ι r → π.IsRegAlg → IsCusp (F := M) n sat' inf' →
      WeakBC π.HasSat sat' → AttachedSys ι (r.comp (resG K M Ω)) sat' →
      ∃ r₁ : G K Ω →* GL (Fin n) (Qbar l), Continuous r₁ ∧ AttR ι r₁ π

def ExDownC : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K M] [Algebra K Ω]
    [Algebra M Ω] [IsScalarTower K M Ω] [IsAlgClosure K Ω] [IsAlgClosure M Ω] [IsGalois K M] [IsCMField K] [IsCMField M],
    (Module.finrank K M).Prime → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n →
    ∀ (r : G K Ω →* GL (Fin n) (Qbar l)) (π : CuspSub K n) sat' inf', Pol ι r → (CG.mk π).IsRegAlg → IsCusp (F := M) n sat' inf' →
      WeakBC (CG.mk π).HasSat sat' → AttachedSys ι (r.comp (resG K M Ω)) sat' →
      ∃ r₁ : G K Ω →* GL (Fin n) (Qbar l), Continuous r₁ ∧ AttC ι r₁ π

def FrobConj : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K M] [Algebra K Ω]
    [Algebra M Ω] [IsScalarTower K M Ω] [IsAlgClosure K Ω] [IsAlgClosure M Ω] [IsGalois K M] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (n : ℕ) (r : G K Ω →* GL (Fin n) (Qbar l)) (w w' : HeightOneSpectrum (𝓞 M)), w'.under (𝓞 K) = w.under (𝓞 K) →
      normV w' = normV w ∧ ∀ B, FrobEig ι (r.comp (resG K M Ω)) w B → FrobEig ι (r.comp (resG K M Ω)) w' B

def InvSat : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K M] [Algebra K Ω]
    [Algebra M Ω] [IsScalarTower K M Ω] [IsAlgClosure K Ω] [IsAlgClosure M Ω] [IsGalois K M] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (n : ℕ) (r : G K Ω →* GL (Fin n) (Qbar l)) (sat' : HeightOneSpectrum (𝓞 M) → Multiset ℂˣ → Prop),
    AttachedSys ι (r.comp (resG K M Ω)) sat' → ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite,
      ∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 K) = w.under (𝓞 K) → ∃ B, sat' w B ∧ sat' w' B

def AttBc : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K M] [Algebra K Ω]
    [Algebra M Ω] [IsScalarTower K M Ω] [IsAlgClosure K Ω] [IsAlgClosure M Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (n : ℕ) (r : G K Ω →* GL (Fin n) (Qbar l)) (sat : HeightOneSpectrum (𝓞 K) → Multiset ℂˣ → Prop)
    (sat' : HeightOneSpectrum (𝓞 M) → Multiset ℂˣ → Prop), (∀ v B B', sat v B → sat v B' → B = B') → WeakBC sat sat' →
    AttachedSys ι r sat → IsSSRep (r.comp (resG K M Ω)) → AttachedSys ι (r.comp (resG K M Ω)) sat'

def SsRes : Prop :=
  ∀ (Γ Γ' k : Type) [Group Γ] [Group Γ'] [Field k] (n : ℕ) (r : Γ →* GL (Fin n) k) (φ : Γ' →* Γ), φ.range.Normal →
    IsSSRep r → IsSSRep (r.comp φ)

def SchurExt : Prop :=
  ∀ (Γ Γ' k : Type) [Group Γ] [Group Γ'] [Field k] [IsAlgClosed k] (n : ℕ) (r r₁ : Γ →* GL (Fin n) k) (φ : Γ' →* Γ), φ.range.Normal →
    IsIrr (r.comp φ) → RepIso (r₁.comp φ) (r.comp φ) → ∃ δ : Γ →* kˣ, δ.comp φ = 1 ∧ RepIso (tw r₁ δ) r

def IrrPrime : Prop :=
  ∀ (Γ Γ' k : Type) [Group Γ] [Group Γ'] [Field k] [IsAlgClosed k] [CharZero k] (n : ℕ) (r : Γ →* GL (Fin n) k) (φ : Γ' →* Γ),
    φ.range.Normal → φ.range.index.Prime → n < φ.range.index → IsIrr r → IsIrr (r.comp φ)

def GalRange : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K M] [Algebra K Ω]
    [Algebra M Ω] [IsScalarTower K M Ω] [IsAlgClosure K Ω] [IsAlgClosure M Ω] [IsGalois K M],
    (resG K M Ω).range.Normal ∧ (resG K M Ω).range.index = Module.finrank K M

def CycQ : Prop :=
  ∀ N : ℕ, ∃ (L : Type) (_ : Field L) (_ : NumberField L), IsGalois ℚ L ∧ IsTotallyReal L ∧ (Module.finrank ℚ L).Prime ∧
    N < Module.finrank ℚ L

def ExistsCompositumWithPrimeDegreeGalois : Prop :=
  ∀ (M Ω : Type) [Field M] [NumberField M] [Field Ω] [Algebra M Ω] [IsAlgClosure M Ω] (L : Type) [Field L] [NumberField L] [IsGalois ℚ L],
    (Module.finrank ℚ L).Prime → Module.finrank ℚ M < Module.finrank ℚ L →
    ∃ (M' : Type) (_ : Field M') (_ : NumberField M') (_ : Algebra M M') (_ : Algebra M' Ω) (_ : IsScalarTower M M' Ω) (f : L →+* M'),
      IsGalois M M' ∧ Module.finrank M M' = Module.finrank ℚ L ∧ Algebra.adjoin M (Set.range f) = ⊤

def RCSup : Prop :=
  ∀ (L M M' : Type) [Field L] [NumberField L] [Field M] [NumberField M] [Field M'] [NumberField M'] [Algebra M M'] (f : L →+* M'),
    IsTotallyReal L → Algebra.adjoin M (Set.range f) = ⊤ → RC M → RC M'

def Tower : Prop :=
  ∀ (F M : Type) [Field F] [NumberField F] [Field M] [NumberField M] [Algebra F M] [IsGalois F M], IsSolvable (M ≃ₐ[F] M) →
    RC F → RC M → Module.finrank F M ≠ 1 → ¬ (Module.finrank F M).Prime →
    ∃ K : IntermediateField F M, K ≠ ⊥ ∧ K ≠ ⊤ ∧ IsGalois F K ∧ RC K

def Step : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K M] [Algebra K Ω]
    [Algebra M Ω] [IsScalarTower K M Ω] [IsAlgClosure K Ω] [IsAlgClosure M Ω] [IsGalois K M],
    (Module.finrank K M).Prime → RC K → RC M → Equi K Ω M

def DegOne : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K M] [Algebra K Ω]
    [Algebra M Ω] [IsScalarTower K M Ω] [IsAlgClosure K Ω] [IsAlgClosure M Ω],
    Module.finrank K M = 1 → RC K → RC M → Equi K Ω M

def PolRes : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K M] [Algebra K Ω]
    [Algebra M Ω] [IsScalarTower K M Ω] [IsAlgClosure K Ω] [IsAlgClosure M Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (n : ℕ) (r : G K Ω →* GL (Fin n) (Qbar l)), Pol ι r → Pol ι (r.comp (resG K M Ω))

def Soluble : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K M] [Algebra K Ω]
    [Algebra M Ω] [IsScalarTower K M Ω] [IsAlgClosure K Ω] [IsAlgClosure M Ω] [IsGalois K M],
    IsSolvable (M ≃ₐ[K] M) → RC K → RC M → Equi K Ω M

end UpperTheory.V.Af.Sol
