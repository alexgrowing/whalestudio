import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.SlopeTestRemainingChoices

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published
open scoped Matrix

namespace UpperTheory.V.Sd

def ToNewform : Prop :=
  ∀ (k N : ℕ) [NeZero N], 2 ≤ k → ∀ χ : DirichletCharacter ℂ N, χ.IsPrimitive → ∀ g : Eigenform k N χ,
    ∃ f : Newform k, f.M = N ∧ (∀ n, f.a n = g.a n) ∧ ∀ n : ℕ, f.χ (n : ZMod f.M) = χ (n : ZMod N)

def EigAut : Prop :=
  ∀ (k N : ℕ) [NeZero N], 2 ≤ k → ∀ χ : DirichletCharacter ℂ N, χ.IsPrimitive → ∀ (g : Eigenform k N χ) (l : ℕ) [Fact l.Prime]
    (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)), Continuous ρ → IsIrr ρ →
    (∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ∀ A : ValuationSubring Ω, IsPlaceOver A w →
      (∀ s ∈ Ine (F := ℚ) A, ρ s = 1) ∧ ∀ σ : G ℚ Ω, IsFrob A (normV w) σ →
        (ρ σ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.map ι.toRingHom =
          X ^ 2 - C (g.a (normV w)) * X + C (χ (normV w : ZMod N) * (normV w : ℂ) ^ (k - 1))) → IsAutR ι ρ

def DirOf : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (N : ℕ), 0 < N →
    ∀ φ : G ℚ Ω →* (Qbar l)ˣ, KillsMu N φ → ∃ (M : ℕ) (_ : NeZero M) (χ : DirichletCharacter ℂ M), M ∣ N ∧ χ.IsPrimitive ∧
      φ = Chr.dirG ℚ Ω (χ.ringHomComp ι.symm.toRingHom)

def PropEG : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (c : G ℚ Ω), IsCC c →
    ∀ (N w : ℕ) (φ θ : G ℚ Ω →* (Qbar l)ˣ), SlopeTestRemainingChoices N w θ → SplitAt N w φ → φ ≠ 1 → ∃ k₀ : ℕ, ∀ k ≥ k₀, φ c = (-1) ^ k →
      ∃ ρ, EisRep ι φ θ k ρ

def SIabs : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Γ : Type) [Group Γ] (ρ : Γ →* GL (Fin 2) (Qbar l)) (Φ : Γ →* (Qbar l)ˣ),
    (∀ s, ‖(Φ s : Qbar l)‖ = 1) → IsIrr ρ → ResSum ρ ![1, Φ] → ∀ H : Subgroup Γ, H.Normal →
    (∃ s ∈ H, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.Separable) → ¬ IsIrr (ρ.comp H.subtype) →
      (∀ s ∈ H, Cong (Φ s) 1) ∧ ∀ s, Cong (Φ s ^ 2) 1

def EisReg : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (φ θ : G ℚ Ω →* (Qbar l)ˣ)
    (k : ℕ), 2 ≤ k → ∀ ρ, EisRep ι φ θ k ρ → ∀ H : Subgroup (G ℚ Ω), IsOpen (H : Set (G ℚ Ω)) →
    ∃ s ∈ H, ∃ a : (Qbar l)ˣ, ¬ IsOfFinOrder a ∧
      (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly = (X - C (a : Qbar l)) * (X - C 1)

def SI : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ)
    (φ θ : G ℚ Ω →* (Qbar l)ˣ) (k : ℕ), 2 ≤ k → IsOfFinOrder φ → ∀ ρ, EisRep ι φ θ k ρ →
    (∀ H : Subgroup (G ℚ Ω), IsOpen (H : Set (G ℚ Ω)) → H.Normal →
      (∃ s ∈ H, ¬ Cong ((cycBar ℚ Ω l ^ (k - 1) * φ) s) 1) → IsIrr (ρ.comp H.subtype)) ∧
    ((∃ s, ¬ Cong ((cycBar ℚ Ω l ^ (k - 1) * φ) s ^ 2) 1) → IrrOpen ρ)

def Ad0Irr : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (ρ : Γ →* GL (Fin 2) (Qbar l)),
    Continuous ρ → IrrOpen ρ → IrrOpen (ad0 ρ)

def Sym3Irr : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (ρ : Γ →* GL (Fin 2) (Qbar l)),
    Continuous ρ → IrrOpen ρ → (∀ H : Subgroup Γ, IsOpen (H : Set Γ) → ∃ s ∈ H, ∃ a b : (Qbar l)ˣ, ¬ IsOfFinOrder (a / b) ∧
      (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly = (X - C (a : Qbar l)) * (X - C (b : Qbar l))) → IrrOpen (sym3 ρ)

def IrrAb : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (n : ℕ) (r : Γ →* GL (Fin n) (Qbar l)),
    Continuous r → IrrOpen r → ∀ H H' : Subgroup Γ, IsOpen (H : Set Γ) → H' ≤ H → (∀ a ∈ H, ∀ b ∈ H, a * b * a⁻¹ * b⁻¹ ∈ H') →
      IsIrr (r.comp H'.subtype)

def Ad0Facts : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ρ : Γ →* GL (Fin 2) (Qbar l)),
    (Continuous ρ → Continuous (ad0 ρ)) ∧
    (∃ P : GL (Fin 3) (Qbar l), (P : Matrix (Fin 3) (Fin 3) (Qbar l))ᵀ = P ∧ ∀ s,
      (ad0 ρ s : Matrix (Fin 3) (Fin 3) (Qbar l))ᵀ * (P : Matrix (Fin 3) (Fin 3) (Qbar l)) * (ad0 ρ s : Matrix (Fin 3) (Fin 3) (Qbar l)) = P) ∧
    (∀ (H : Subgroup Γ) (a b : Γ →* (Qbar l)ˣ), IsDiagOn ρ H ![a, b] → IsDiagOn (ad0 ρ) H ![b / a, 1, a / b]) ∧
    (∀ (H : Subgroup Γ) (κ : Fin 2 → ↥H →* (Qbar l)ˣ), IsFlagOn ρ H κ → IsFlagOn (ad0 ρ) H ![κ 0 / κ 1, 1, κ 1 / κ 0]) ∧
    (∀ s (a b : (Qbar l)ˣ), (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly = (X - C (a : Qbar l)) * (X - C (b : Qbar l)) →
      (ad0 ρ s : Matrix (Fin 3) (Fin 3) (Qbar l)).charpoly =
        (X - C ((a / b : (Qbar l)ˣ) : Qbar l)) * (X - C 1) * (X - C ((b / a : (Qbar l)ˣ) : Qbar l))) ∧
    ∀ a b : Γ →* (Qbar l)ˣ, (∀ s, ‖(a s : Qbar l)‖ = 1 ∧ ‖(b s : Qbar l)‖ = 1) → ResSum ρ ![a, b] → ResSum (ad0 ρ) ![b / a, 1, a / b]

def Sym3Facts : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ρ : Γ →* GL (Fin 2) (Qbar l)),
    (Continuous ρ → Continuous (sym3 ρ)) ∧
    (∀ s, (sym3 ρ s : Matrix (Fin 4) (Fin 4) (Qbar l))ᵀ * !![0, 0, 0, 3; 0, 0, -1, 0; 0, 1, 0, 0; -3, 0, 0, 0] *
      (sym3 ρ s : Matrix (Fin 4) (Fin 4) (Qbar l)) =
        (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).det ^ 3 • !![0, 0, 0, 3; 0, 0, -1, 0; 0, 1, 0, 0; -3, 0, 0, 0]) ∧
    (∀ (H : Subgroup Γ) (a b : Γ →* (Qbar l)ˣ), IsDiagOn ρ H ![a, b] → IsDiagOn (sym3 ρ) H ![a ^ 3, a ^ 2 * b, a * b ^ 2, b ^ 3]) ∧
    (∀ (H : Subgroup Γ) (κ : Fin 2 → ↥H →* (Qbar l)ˣ), IsFlagOn ρ H κ →
      IsFlagOn (sym3 ρ) H ![κ 0 ^ 3, κ 0 ^ 2 * κ 1, κ 0 * κ 1 ^ 2, κ 1 ^ 3]) ∧
    (∀ s (a b : Qbar l), (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly = (X - C a) * (X - C b) →
      (sym3 ρ s : Matrix (Fin 4) (Fin 4) (Qbar l)).charpoly =
        (X - C (a ^ 3)) * (X - C (a ^ 2 * b)) * (X - C (a * b ^ 2)) * (X - C (b ^ 3))) ∧
    ∀ a b : Γ →* (Qbar l)ˣ, (∀ s, ‖(a s : Qbar l)‖ = 1 ∧ ‖(b s : Qbar l)‖ = 1) → ResSum ρ ![a, b] →
      ResSum (sym3 ρ) ![a ^ 3, a ^ 2 * b, a * b ^ 2, b ^ 3]

def ShapeFacts : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (n : ℕ) (r : Γ →* GL (Fin n) (Qbar l)) (δ : Γ →* (Qbar l)ˣ),
    (∀ (H : Subgroup Γ) (χ : Fin n → Γ →* (Qbar l)ˣ), IsDiagOn r H χ → IsDiagOn (tw r δ) H fun i => χ i * δ) ∧
    (∀ (H : Subgroup Γ) (χ χ' : Fin n → Γ →* (Qbar l)ˣ) (e : Equiv.Perm (Fin n)), IsDiagOn r H χ → (∀ i, ∀ s ∈ H, χ' i s = χ (e i) s) →
      IsDiagOn r H χ') ∧
    (∀ (H : Subgroup Γ) (κ : Fin n → ↥H →* (Qbar l)ˣ), IsFlagOn r H κ → IsFlagOn (tw r δ) H fun i => κ i * δ.comp H.subtype) ∧
    (∀ χ : Fin n → Γ →* (Qbar l)ˣ, (∀ s, ‖(δ s : Qbar l)‖ = 1) → ResSum r χ → ResSum (tw r δ) fun i => χ i * δ) ∧
    (∀ (χ χ' : Fin n → Γ →* (Qbar l)ˣ) (e : Equiv.Perm (Fin n)), (∀ i s, ‖(χ i s : Qbar l)‖ = 1) → ResSum r χ →
      (∀ i s, Cong (χ' i s) (χ (e i) s)) → ResSum r χ') ∧
    (IsIrr r → IsIrr (tw r δ))

def ResFacts : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω]
    [IsScalarTower F E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)),
    Continuous (galEmb F E Ω) ∧ IsOpen (galOf F E Ω : Set (G F Ω)) ∧ (cycBar F Ω l).comp (galEmb F E Ω) = cycBar E Ω l ∧
    (IsIrr (r.comp (galOf F E Ω).subtype) ↔ IsIrr (r.comp (galEmb F E Ω))) ∧
    (IrrOpen r → IrrOpen (r.comp (galEmb F E Ω))) ∧
    (∀ τ, TypeAway r τ → TypeAway (r.comp (galEmb F E Ω)) fun i => (τ i).comp (galEmb F E Ω)) ∧
    ∀ m ψ A, OrdAt r m ψ A → OrdAt (r.comp (galEmb F E Ω)) m (fun i => (ψ i).comp (galEmb F E Ω)) A

def SelfTwGal : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ)
    (r : G F Ω →* GL (Fin n) (Qbar l)) (sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop), (∀ v B B', sat v B → sat v B' → B = B') →
    Continuous r → AttachedSys ι r sat → ∀ (η : HChar F) (m : ℕ), 0 < m → η ^ m = 1 → η ≠ 1 → SelfTw sat η →
    ∃ δ : G F Ω →* (Qbar l)ˣ, δ ≠ 1 ∧ IsOpen (δ.ker : Set (G F Ω)) ∧ RepIso r (tw r δ) ∧
      ∀ (E : Type) [Field E] [NumberField E] [Algebra F E] [Algebra E Ω] [IsScalarTower F E Ω], IsNormChar E η →
        δ.comp (galEmb F E Ω) = 1

def AdAut : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (ρ : G F Ω →* GL (Fin 2) (Qbar l)), Continuous ρ → IsAutR ι ρ → IrrOpen ρ →
    IsAutR ι (tw (ad0 ρ) (cycBar F Ω l)⁻¹)

def Sym3Aut : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (ρ : G F Ω →* GL (Fin 2) (Qbar l)), Continuous ρ → IsAutR ι ρ → IrrOpen ρ → IsIrr (sym3 ρ) → IsAutR ι (sym3 ρ)

def UpQuad : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [IsTotallyComplex E] [Field Ω] [Algebra F E]
    [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ),
    Module.finrank F E = 2 → ∀ (n : ℕ) [Fact (n = 2)], 1 ≤ n → ∀ r : G F Ω →* GL (Fin n) (Qbar l), Continuous r → IsAutR ι r →
      IsIrr (r.comp (galEmb F E Ω)) → IsAutC ι (r.comp (galEmb F E Ω))

def UpCyc : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field E] [NumberField E] [IsTotallyComplex E] [Field Ω] [Algebra F E]
    [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω] [IsGalois F E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ),
    (Module.finrank F E).Prime → ∀ (n : ℕ), 1 ≤ n → ∀ r : G F Ω →* GL (Fin n) (Qbar l), Continuous r → IsAutC ι r →
      IsIrr (r.comp (galEmb F E Ω)) → IsAutC ι (r.comp (galEmb F E Ω))

def UpSol : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field E] [NumberField E] [IsTotallyComplex E] [Field Ω] [Algebra F E]
    [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω] [IsGalois F E] [Group.IsSolvable (E ≃ₐ[F] E)] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ r : G F Ω →* GL (Fin n) (Qbar l), Continuous r → IsAutC ι r →
      IsIrr (r.comp (galEmb F E Ω)) → IsAutC ι (r.comp (galEmb F E Ω))

def TwC : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)) (κ : G F Ω →* (Qbar l)ˣ), IsAlgChar ι κ → IsAutC ι r → IsAutC ι (tw r κ)

def TwR : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)) (κ : G F Ω →* (Qbar l)ˣ), IsAlgChar ι κ → IsAutR ι r → IsAutR ι (tw r κ)

def AlgCyc : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ),
    (∀ (j : ℤ) (χ : G F Ω →* (Qbar l)ˣ), IsOpen (χ.ker : Set (G F Ω)) → IsAlgChar ι (cycBar F Ω l ^ j * χ)) ∧
    (∀ κ κ' : G F Ω →* (Qbar l)ˣ, IsAlgChar ι κ → IsAlgChar ι κ' → IsAlgChar ι (κ * κ')) ∧
    ∀ κ : G F Ω →* (Qbar l)ˣ, IsAlgChar ι κ → IsAlgChar ι κ⁻¹

def AlgRes : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω]
    [IsScalarTower F E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (κ : G F Ω →* (Qbar l)ˣ),
    IsAlgChar ι κ → IsAlgChar ι (κ.comp (galEmb F E Ω))

def ToCsd : Prop :=
  ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra L Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (r : G L Ω →* GL (Fin n) (Qbar l)) (c : G ℚ Ω), IsCC c →
    (∃ P, IsPair c r (cycBar L Ω l ^ (1 - (n : ℤ))) P) → IsAutC ι r → IsAutCsd ι r

def Twist : Prop :=
  ∀ (K Ω : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω],
    Module.finrank ℚ K = 2 → ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ (l : ℤ) ∣ discr K → ∀ (ι : Qbar l ≃+* ℂ) (c : G ℚ Ω), IsCC c →
    ∃ κ : G K Ω →* (Qbar l)ˣ, IsTwist ι c κ

def Seed3 : Prop :=
  ∀ (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L] [IsCMField L] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    [Algebra K Ω] [Algebra L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : G ℚ Ω) (N w : ℕ) (χ' η θ : G ℚ Ω →* (Qbar l)ˣ) (j : ℕ),
    FieldPairCharacterTripleConditions K L c N w χ' η θ j → χ' ≠ η → ∀ B : ℕ, ∃ m ≥ B, m ≡ j [MOD l - 1] ∧ ∃ r : G L Ω →* GL (Fin 3) (Qbar l), IrrOpen r ∧
      IsSeed ι c (fun i => (![cycBar ℚ Ω l ^ j * χ', 1, (cycBar ℚ Ω l ^ j * χ')⁻¹] i).comp (galEmb ℚ L Ω))
        (fun i => (![χ', 1, χ'⁻¹] i).comp (galEmb ℚ L Ω)) ![(m : ℤ), 0, -(m : ℤ)] (cycBar L Ω l)⁻¹ r

def Seed2 : Prop :=
  ∀ (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L] [IsCMField L] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    [Algebra K Ω] [Algebra L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : G ℚ Ω) (N w : ℕ) (χ' η θ : G ℚ Ω →* (Qbar l)ˣ) (j : ℕ),
    FieldPairCharacterTripleConditions K L c N w χ' η θ j → ∀ (κ : G K Ω →* (Qbar l)ˣ) (ka : G L Ω →* (Qbar l)ˣ), IsTwist ι c κ →
    (∀ (s : G L Ω) (s' : G K Ω), galEmb ℚ L Ω s = galEmb ℚ K Ω s' → ka s = κ s') →
    ∀ B : ℕ, ∃ m ≥ B, m ≡ j [MOD l - 1] ∧ ∃ σ : G ℚ Ω →* GL (Fin 2) (Qbar l), Continuous σ ∧
      Matrix.GeneralLinearGroup.det.comp σ = η * θ ∧ ResSum σ ![cycBar ℚ Ω l ^ j * χ' * η, (cycBar ℚ Ω l ^ j * χ')⁻¹] ∧
      IsSeed ι c (fun i => (![cycBar ℚ Ω l ^ j * χ', (cycBar ℚ Ω l ^ j * χ')⁻¹] i).comp (galEmb ℚ L Ω))
        (fun i => (![χ', χ'⁻¹] i).comp (galEmb ℚ L Ω)) ![(m : ℤ), -(m : ℤ)] ka (σ.comp (galEmb ℚ L Ω))

def SeedSym : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (c : G ℚ Ω), IsCC c →
    ∀ (N w : ℕ) (ξ θ : G ℚ Ω →* (Qbar l)ˣ), SlopeTestRemainingChoices N w θ → SplitAt N w ξ → ξ c = -1 → (∃ s, ¬ Cong (ξ s ^ 2) 1) →
    ∀ B : ℕ, ∃ k ≥ B, k ≡ 1 [MOD l - 1] ∧ ∃ ρ, EisRep ι ξ θ k ρ ∧ IrrOpen ρ ∧ IrrOpen (sym3 ρ) ∧ IsAutR ι (sym3 ρ)

def RibetLat : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ]
    (ρ : Γ →* GL (Fin 2) (Qbar l)) (a b : Γ →* (Qbar l)ˣ), Continuous ρ → IsIrr ρ → (∀ s, ‖(a s : Qbar l)‖ = 1 ∧ ‖(b s : Qbar l)‖ = 1) →
    ResSum ρ ![a, b] → ∀ g₀ : Γ, ¬ Cong (a g₀) (b g₀) → ∃ ρ' : Γ →* GL (Fin 2) (Qbar l), RepIso ρ ρ' ∧
      ρ' g₀ 0 1 = 0 ∧ ρ' g₀ 1 0 = 0 ∧ (∀ s, ‖ρ' s 0 0 - a s‖ < 1 ∧ ‖ρ' s 1 1 - b s‖ < 1 ∧ ‖ρ' s 1 0‖ < 1 ∧ ‖ρ' s 0 1‖ ≤ 1) ∧
      ∃ s, ‖ρ' s 0 1‖ = 1

end UpperTheory.V.Sd
