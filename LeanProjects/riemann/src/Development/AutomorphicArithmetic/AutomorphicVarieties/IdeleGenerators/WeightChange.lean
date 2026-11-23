import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Hilbert
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix

namespace UpperTheory.V.Sd

structure Hypotheses4 : Prop where
  h : Af.HypothesesH
  hida : Published.HidaGal
  adj : Published.AdjointLift
  cube : Published.SymCube
  ind : Published.QuadInduction
  eis : Published.HilbertEisOne
  one : Published.HilbertOne

def HypothesesOf : Prop := Af.HypothesesH → Published.HidaGal → Published.AdjointLift → Hypotheses₂

abbrev Pl (F : Type) [Field F] : Type := HeightOneSpectrum (𝓞 F)

open Classical in

def levL {F : Type} [Field F] (l : ℕ) (c : Pl F → ℕ) (w : Pl F) : ℕ := if ((l : ℕ) : 𝓞 F) ∈ w.asIdeal then 1 else c w

open Classical in

def eisT {F : Type} [Field F] [NumberField F] (l : ℕ) (ω : HChar F) (c : Pl F → ℕ) (P : Set (Pl F)) (w : Pl F) : ℂ :=
  if ((l : ℕ) : 𝓞 F) ∈ w.asIdeal then (if w ∈ P then ((ω.val w : ℂˣ) : ℂ) else 1) else if c w = 0 then 1 + ((ω.val w : ℂˣ) : ℂ) else 1

def ExpUnique : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (φ : GA F 2 → ℂ) (k : ℕ) c₀ c₀' a a', HasExp φ k c₀ a → HasExp φ k c₀' a' →
    c₀ = c₀' ∧ ∀ 𝔪, 𝔪 ≠ ⊥ → a 𝔪 = a' 𝔪

def StrongApp : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (K : Subgroup (GL (Fin 2) (Af F))), IsOpen (K : Set (GL (Fin 2) (Af F))) →
    ∀ g : GA F 2, ∃ (γ : GL (Fin 2) F) (h : GL (Fin 2) (TR.Rinf F)) (y : (Af F)ˣ) (u : GL (Fin 2) (Af F)), u ∈ K ∧
      (∀ v, 0 < (h : Matrix (Fin 2) (Fin 2) (TR.Rinf F)).det v) ∧ g = ratGL F 2 γ * (TR.infGL F 2 h * finGL F 2 (aff y 0 * u))

def ExpInj : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ), 1 ≤ k → ∀ (c : Pl F → ℕ) (ω : HChar F), IsOfFinOrder ω →
    ∀ φ : TR.Sm F 2, IsHol k c ω φ → ∀ c₀ a, HasExp φ.1 k c₀ a → (∀ 𝔪, 𝔪 ≠ ⊥ → a 𝔪 = 0) → φ = 0

def HolLin : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (c : Pl F → ℕ) (ω : HChar F),
    IsHol k c ω 0 ∧ HasExp (0 : GA F 2 → ℂ) k 0 0 ∧
    (∀ (φ ψ : TR.Sm F 2) (z : ℂ), IsHol k c ω φ → IsHol k c ω ψ → IsHol k c ω (φ + z • ψ)) ∧
    (∀ (φ ψ : GA F 2 → ℂ) (z : ℂ) c₀ a d₀ b, HasExp φ k c₀ a → HasExp ψ k d₀ b → HasExp (φ + z • ψ) k (c₀ + z • d₀) (a + z • b)) ∧
    ∀ (φ : TR.Sm F 2) (c' : Pl F → ℕ), c ≤ c' → IsHol k c ω φ → IsHol k c' ω φ

def HolMul : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (k k' : ℕ) (c : Pl F → ℕ)
    (ω : HChar F), IsOfFinOrder ω → ∀ (φ ψ : TR.Sm F 2) a d₀ b, IsHol k c ω φ → IsHol k' (fun _ => 0) 1 ψ → HasExp φ.1 k 0 a →
    HasExp ψ.1 k' d₀ b → (∀ 𝔪, 𝔪 ≠ ⊥ → ‖ι.symm (a 𝔪)‖ ≤ 1) → (∀ y, ‖ι.symm (d₀ y) - 1‖ < 1) → (∀ 𝔪, 𝔪 ≠ ⊥ → ‖ι.symm (b 𝔪)‖ < 1) →
    ∃ (χ : TR.Sm F 2) (a' : Ideal (𝓞 F) → ℂ), IsHol (k + k') c ω χ ∧ HasExp χ.1 (k + k') 0 a' ∧
      ∀ 𝔪, 𝔪 ≠ ⊥ → ‖ι.symm (a' 𝔪 - a 𝔪)‖ < 1

open Classical in

def HolB : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (c : Pl F → ℕ) (ω : HChar F) (φ : TR.Sm F 2) c₀ a (w : Pl F),
    IsHol k c ω φ → HasExp φ.1 k c₀ a → ∃ (ψ : TR.Sm F 2) (u : (Af F)ˣ), IsHol k (Function.update c w (c w + 1)) ω ψ ∧
      HasExp ψ.1 k (fun y => c₀ (y * u)) (coefDiv a w.asIdeal)

def UopSum : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (w : Pl F) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin 2) (w.adicCompletion F)) V) (c : ℕ) (v : V), v ∈ Hi.fixd ρ (K1 w c) →
    Uop w ρ c v ∈ Hi.fixd ρ (K1 w c) ∧
    ∀ S : Finset (w.adicCompletionIntegers F), Set.BijOn (IsLocalRing.residue _) (S : Set (w.adicCompletionIntegers F)) Set.univ →
      Uop w ρ c v = ∑ u ∈ S, ρ (aff (atFin w (unif w)) (u : w.adicCompletion F)) v +
        if c = 0 then ρ (Matrix.GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w)) * (aff (atFin w (unif w)) 0)⁻¹) v else 0

def HolHk : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ), 1 ≤ k → ∀ (c : Pl F → ℕ) (ω : HChar F), IsOfFinOrder ω →
    ∀ φ : TR.Sm F 2, IsHol k c ω φ → ∀ w : Pl F, IsHol k c ω (hk k w (c w) φ) ∧
      (∀ w' : Pl F, hk k w (c w) (hk k w' (c w') φ) = hk k w' (c w') (hk k w (c w) φ)) ∧
      ∀ c₀ a, HasExp φ.1 k c₀ a → ∃ c₀', HasExp (hk k w (c w) φ).1 k c₀' (hkCoef k c ω w a)

def HolCap : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (c : Pl F → ℕ) (ω : HChar F), IsOfFinOrder ω →
    ∀ φ : TR.Sm F 2, IsHol k c ω φ → TR.lie F 2 (TR.oneL F 2) φ = 0 ∧
      ∀ v (u : ℂ), TR.cap v u φ = ((u + ((k : ℂ) - 1) / 2) * (u - ((k : ℂ) - 1) / 2)) • φ

def HolFin : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (c : Pl F → ℕ), {w | c w ≠ 0}.Finite → ∀ ω : HChar F, IsOfFinOrder ω →
    FiniteDimensional ℂ (Submodule.span ℂ {φ : TR.Sm F 2 | IsHol k c ω φ})

def HolLift : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (k : ℕ), 1 ≤ k →
    ∀ (c : Pl F → ℕ), {w | c w ≠ 0}.Finite → ∀ ω : HChar F, IsOfFinOrder ω → ∀ (φ : TR.Sm F 2) c₀ a (t : Pl F → ℂ), IsHol k c ω φ →
    HasExp φ.1 k c₀ a → (∀ 𝔪, 𝔪 ≠ ⊥ → ‖ι.symm (a 𝔪)‖ ≤ 1) → ‖ι.symm (a ⊤)‖ = 1 → (∀ w, ‖ι.symm (t w)‖ ≤ 1) →
    (∀ w 𝔪, 𝔪 ≠ ⊥ → ‖ι.symm (hkCoef k c ω w a 𝔪 - t w * a 𝔪)‖ < 1) →
    ∃ ψ lam, IsEigHol k c ω ψ lam ∧ ∀ w, ‖ι.symm (lam w - t w)‖ < 1

def Emix : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (ω : HChar F) (c : Pl F → ℕ),
    IsOfFinOrder ω → (∀ v, ω.locInf v (-1) = -1) → (∀ w, IsCondAt w ω (c w)) → (∃ w, c w ≠ 0) →
    (∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → c w = 0) → ∀ P : Set (Pl F), (∃ w ∈ P, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) →
    ∃ (φ : TR.Sm F 2) (a : Ideal (𝓞 F) → ℂ), IsHol 1 (levL l c) ω φ ∧ HasExp φ.1 1 0 a ∧ a ⊤ = 1 ∧
      (∀ 𝔪, 𝔪 ≠ ⊥ → ‖ι.symm (a 𝔪)‖ ≤ 1) ∧ ∀ w 𝔪, 𝔪 ≠ ⊥ → hkCoef 1 (levL l c) ω w a 𝔪 = eisT l ω c P w * a 𝔪

def LocEig : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (w : Pl F) (μ₁ μ₂ : (w.adicCompletion F)ˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (Φ : GL (Fin 2) (w.adicCompletion F) → V), Φ ≠ 0 →
    (∀ (a d : (w.adicCompletion F)ˣ) (x : w.adicCompletion F) g,
      Φ (Matrix.GeneralLinearGroup.scalar (Fin 2) d * aff (a / d) x * g) = ((μ₁ a * μ₂ d : ℂˣ) : ℂ) • Φ g) →
    ∀ (c : ℕ) (lam : ℂ), Φ ∈ Hi.fixd (Hi.rtr ℂ _ V) (K1 w c) → Uop w (Hi.rtr ℂ _ V) c Φ = lam • Φ →
    (c = 0 → (∀ x, IsUnitAt w x → μ₁ x = 1 ∧ μ₂ x = 1) ∧
      lam = (normV w : ℂ) * (μ₁ (atFin w (unif w)) : ℂ) + (μ₂ (atFin w (unif w)) : ℂ)) ∧
    (c ≠ 0 → lam = 0 ∨ ((∀ x, IsUnitAt w x → μ₁ x = 1) ∧ lam = (normV w : ℂ) * (μ₁ (atFin w (unif w)) : ℂ)) ∨
      ((∀ x, IsUnitAt w x → μ₂ x = 1) ∧ lam = (μ₂ (atFin w (unif w)) : ℂ)))

def HolEis : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ), 1 ≤ k → ∀ (c : Pl F → ℕ), {w | c w ≠ 0}.Finite →
    ∀ ω : HChar F, IsOfFinOrder ω → ∀ φ lam, IsEigHol k c ω φ lam → ¬ TR.IsCuspForm φ →
    ∃ η₁ η₂ : HChar F, IsOfFinOrder η₁ ∧ IsOfFinOrder η₂ ∧ η₁ * η₂ = ω ∧
      (∀ w, c w = 0 → η₁.UnrAt w ∧ η₂.UnrAt w ∧ lam w = (η₁.val w : ℂˣ) + (η₂.val w : ℂˣ) * (normV w : ℂ) ^ (k - 1)) ∧
      ∀ w, c w ≠ 0 → lam w = 0 ∨ (η₁.UnrAt w ∧ lam w = (η₁.val w : ℂˣ)) ∨
        (η₂.UnrAt w ∧ lam w = (η₂.val w : ℂˣ) * (normV w : ℂ) ^ (k - 1))

def PropMHol : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ι : Qbar l ≃+* ℂ) (ω : HChar F)
    (c : Pl F → ℕ), IsOfFinOrder ω → (∀ v, ω.locInf v (-1) = -1) → (∀ w, IsCondAt w ω (c w)) → (∃ w, c w ≠ 0) →
    (∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → c w = 0) → ∀ P : Set (Pl F),
    (∃ w ∈ P, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal ∧ ¬ ‖ι.symm (ω.val w : ℂˣ) - 1‖ < 1) →
    (∃ w ∉ P, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal ∧ ¬ ‖ι.symm (ω.val w : ℂˣ) - 1‖ < 1) →
    ∀ B : ℕ, ∃ k ≥ B, l - 1 ∣ k ∧ ∃ φ lam, IsEigHol (k + 1) (levL l c) ω φ lam ∧ TR.IsCuspForm φ ∧
      ∀ w, ‖ι.symm (lam w - eisT l ω c P w)‖ < 1

def HolRep : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ), 2 ≤ k → ∀ (c : Pl F → ℕ) (ω : HChar F), IsOfFinOrder ω →
    ∀ φ lam, IsEigHol k c ω φ lam → TR.IsCuspForm φ → ∃ π : TR.CuspSub F 2, π.IsRegAlg ∧ (∃ χ : HChar F, π.Polarized χ) ∧
      (∀ v, π.HasInfChar v (infOf ![0, 1 - (k : ℤ)])) ∧ (∀ w, HasU w (π.locRep w) (c w) (lam w)) ∧
      ∀ w, c w = 0 → ∃ B, π.HasSat w B ∧ ((algSat 2 (normV w) B).map fun b => X - C b).prod =
        X ^ 2 - C (lam w) * X + C ((ω.val w : ℂˣ) * (normV w : ℂ) ^ (k - 1))

def PropM : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 →
    ∀ (ι : Qbar l ≃+* ℂ) (ξ : G F Ω →* (Qbar l)ˣ), IsOpen (ξ.ker : Set (G F Ω)) → (∀ c, IsConjEl c → ξ c = -1) →
    (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → Ine (F := F) A ≤ ξ.ker) → (∃ A : ValuationSubring Ω, ¬ Ine (F := F) A ≤ ξ.ker) →
    ∀ P : Set (Pl F),
    (∃ w ∈ P, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal ∧ ∃ A, IsPlaceOver A w ∧ ∃ σ ∈ Dec (F := F) A, ¬ Cong (ξ σ) 1) →
    (∃ w ∉ P, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal ∧ ∃ A, IsPlaceOver A w ∧ ∃ σ ∈ Dec (F := F) A, ¬ Cong (ξ σ) 1) →
    ∀ B : ℕ, ∃ k ≥ B, l - 1 ∣ k ∧ ∃ c a π r, OrdForm ι ξ (-(k : ℤ)) c (fun _ => ![0, -(k : ℤ)]) a π r ∧ ResSum r ![1, ξ] ∧
      ∀ (w : Pl F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∀ A, IsPlaceOver A w → ∀ σ : G F Ω, IsFrob A (normV w) σ →
        (w ∈ P → a w = (ξ σ⁻¹ : (Qbar l)ˣ)) ∧ (w ∉ P → a w = 1)

def SplitL (F : Type) [Field F] [NumberField F] (l : ℕ) : Prop :=
  ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → Ideal.absNorm w.asIdeal = l ∧ ((l : ℕ) : 𝓞 F) ∉ w.asIdeal ^ 2

def GlobVec : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (π : TR.CuspSub F 2) (c : Pl F → ℕ), {w | c w ≠ 0}.Finite →
    ∀ lam : Pl F → ℂ, (∀ w, c w = 0 → HasFixed (π.locRep w) (K1 w 0)) → (∀ w, c w ≠ 0 → HasU w (π.locRep w) (c w) (lam w)) →
    ∃ (v : π.V) (mu : Pl F → ℂ), v ≠ 0 ∧ (∀ w, c w ≠ 0 → mu w = lam w) ∧
      ∀ w, v ∈ Hi.fixd (π.locRep w) (K1 w (c w)) ∧ Uop w (π.locRep w) (c w) v = mu w • v

def WeightChange : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 →
    Even (Module.finrank ℚ F) → SplitL F l → ∀ (ι : Qbar l ≃+* ℂ) (ξ : G F Ω →* (Qbar l)ˣ) s c m a π r, OrdForm ι ξ s c m a π r →
    (∃ u, c u ≠ 0 ∧ normV u = 2) → ∀ m' : Pl F → Fin 2 → ℤ,
    (∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → m' w 1 + 2 ≤ m' w 0 ∧ m' w 0 + m' w 1 = s ∧ ((l : ℤ) - 1) ∣ m' w 0 - m w 0) →
    ∃ π' r', OrdForm ι ξ s c m' a π' r' ∧ ∀ g i, ‖(r' g : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.coeff i -
      (r g : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.coeff i‖ < 1

def JacqOfU : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (w : Pl F) (σ : SmIrr (GL (Fin 2) (w.adicCompletion F))) (c : ℕ) (lam : ℂˣ), c ≠ 0 →
    HasU w σ.ρ c lam → ∃ (μ₁ μ₂ : (w.adicCompletion F)ˣ →* ℂˣ) (L : σ.V →ₗ[ℂ] ℂ), L ≠ 0 ∧ (∀ x, IsUnitAt w x → μ₁ x = 1) ∧
      (normV w : ℂ) * (μ₁ (atFin w (unif w)) : ℂ) = lam ∧ ∀ (a d : (w.adicCompletion F)ˣ) (x : w.adicCompletion F) v,
        L (σ.ρ (Matrix.GeneralLinearGroup.scalar (Fin 2) d * aff (a / d) x) v) = ((μ₁ a * μ₂ d : ℂˣ) : ℂ) * L v

def OrdAway : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (ξ : G F Ω →* (Qbar l)ˣ) s c m a π r, OrdForm ι ξ s c m a π r → TypeAway r ![1, ξ]

def OrdAbove : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 →
    SplitL F l → ∀ (ι : Qbar l ≃+* ℂ) (ξ : G F Ω →* (Qbar l)ˣ) s c m a π r, OrdForm ι ξ s c m a π r →
    ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∀ A, IsPlaceOver A w →
      ∃ κ : Fin 2 → ↥(Dec (F := F) A) →* (Qbar l)ˣ, IsFlagOn r (Dec (F := F) A) κ ∧
        (∀ i (g : ↥(Dec (F := F) A)), (g : G F Ω) ∈ Ine (F := F) A → κ i g = cycBar F Ω l g ^ m w i) ∧
        ∀ σ : ↥(Dec (F := F) A), IsFrob A (normV w) (σ : G F Ω) →
          ‖((κ 0 σ⁻¹ * cycBar F Ω l (σ : G F Ω) ^ m w 0 : (Qbar l)ˣ) : Qbar l) - a w‖ < 1

def OrdIrr : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 →
    SplitL F l → ∀ (ι : Qbar l ≃+* ℂ) (ξ : G F Ω →* (Qbar l)ˣ) s c m a π r, OrdForm ι ξ s c m a π r → IsIrr r

def MixSeed : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 →
    Even (Module.finrank ℚ F) → SplitL F l → ∀ (ι : Qbar l ≃+* ℂ) (ξ : G F Ω →* (Qbar l)ˣ), IsOpen (ξ.ker : Set (G F Ω)) →
    (∀ c, IsConjEl c → ξ c = -1) → (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → Ine (F := F) A ≤ ξ.ker) →
    (∃ (u : Pl F) (A : ValuationSubring Ω), normV u = 2 ∧ IsPlaceOver A u ∧ ¬ Ine (F := F) A ≤ ξ.ker) → (∃ g, ¬ Cong (ξ g ^ 2) 1) →
    (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ σ ∈ Dec (F := F) A, ¬ Cong (ξ σ) 1) →
    ∀ P : Set (Pl F), (∃ w ∈ P, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) → (∃ w ∉ P, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) →
    ∃ (k t : ℕ) (π : TR.CuspSub F 2) (r : G F Ω →* GL (Fin 2) (Qbar l)), 2 ≤ k ∧ 2 ≤ t ∧ l - 1 ∣ k ∧ l - 1 ∣ t ∧
      Continuous r ∧ IrrOpen r ∧ AttR ι r π ∧ Matrix.GeneralLinearGroup.det.comp r = cycBar F Ω l ^ k * ξ ∧ ResSum r ![1, ξ] ∧
      TypeAway r ![1, ξ] ∧ ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal →
        (w ∈ P → (∀ A, IsPlaceOver A w → OrdAt r ![(k : ℤ) + t, -(t : ℤ)] ![ξ, 1] A) ∧ ∀ τ : F →+* Qbar l, EmbAt w τ →
          π.HasInfChar (InfinitePlace.mk (ι.toRingHom.comp τ)) (infOf ![(k : ℤ) + t, -(t : ℤ)])) ∧
        (w ∉ P → (∀ A, IsPlaceOver A w → OrdAt r ![(k : ℤ), 0] ![1, ξ] A) ∧ ∀ τ : F →+* Qbar l, EmbAt w τ →
          π.HasInfChar (InfinitePlace.mk (ι.toRingHom.comp τ)) (infOf ![(k : ℤ), 0]))

def IndAut : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsTotallyReal E] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra E Ω],
    Module.finrank ℚ E = 2 → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (π : TR.CuspSub E 2) (r : G E Ω →* GL (Fin 2) (Qbar l))
    (m m' : Fin 2 → ℤ), AttR ι r π → (∃ v v', v ≠ v' ∧ π.HasInfChar v (infOf m) ∧ π.HasInfChar v' (infOf m')) →
    Function.Injective ![m 0, m 1, m' 0, m' 1] → ∀ R : G ℚ Ω →* GL (Fin 4) (Qbar l), IsSSRep R →
    (∀ t : G ℚ Ω, t ∉ galOf ℚ E Ω →
      (∀ g g' : G E Ω, galEmb ℚ E Ω g' = t⁻¹ * galEmb ℚ E Ω g * t →
        (R (galEmb ℚ E Ω g) : Matrix (Fin 4) (Fin 4) (Qbar l)).charpoly =
          (r g : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly * (r g' : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly) ∧
      ∀ g : G E Ω, galEmb ℚ E Ω g = t * t →
        (R t : Matrix (Fin 4) (Fin 4) (Qbar l)).charpoly = (r g : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.comp (X ^ 2)) →
    IsAutR ι R

def FinCoef : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] (n : ℕ)
    (r : Γ →* GL (Fin n) (Qbar l)), Continuous r → ∃ E : IntermediateField ℚ_[l] (Qbar l), FiniteDimensional ℚ_[l] E ∧
      ∀ g i j, r g i j ∈ E

end UpperTheory.V.Sd
