import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf

noncomputable section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4

namespace UpperTheory.V.Z.Kato.Sym.PT

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

attribute [local instance] algMdl

def IsIso (X : Tower Ω ε) (M : ℕ) (e : topBar X M ≃+* Kb X) : Prop :=
  ∀ f : topL X M, e (algebraMap (topL X M) (topBar X M) f) = io X f

def FixF (X : Tower Ω ε) (M : ℕ) (σ : RingAut (Kb X)) : Prop := ∀ f ∈ topF X M, σ (io X f) = io X f

def cj (X : Tower Ω ε) (M : ℕ) (e : topBar X M ≃+* Kb X) (σ : RingAut (Kb X)) : topGal X M :=
  Classical.epsilon fun g : topGal X M => ∀ z, e (g z) = σ (e z)

def topPt (X : Tower Ω ε) (M : ℕ) (e : topBar X M ≃+* Kb X) (l n : ℕ) (u v : X.K) (η : topGal X M → ZMod (l ^ n)) : Pt X (l ^ n) :=
  ⟨e (topRoot X M (l ^ n) u), e (topRoot X M (l ^ n) v), fun σ => η (cj X M e σ)⟩

def IsoEx : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (M : ℕ), ∃ e : topBar X M ≃+* Kb X, IsIso X M e

def LevFin : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (M : ℕ), 0 < M → ∃ S : Finset X.K, (∀ f ∈ S, f ∈ topL X M) ∧
    ∀ f ∈ topL X M, f ∈ Subfield.closure (Set.range (algebraMap Ω X.K) ∪ {X.jK} ∪ (S : Set X.K))

def IntU : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (M : ℕ) (u : X.K), IsU X u → IsIntegral (Algebra.adjoin Ω {X.jK}) u ∧ IsIntegral (Algebra.adjoin Ω {X.jK}) u⁻¹

def EtaEx : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l n M : ℕ), l.Prime → 0 < M → l ^ n ∣ M → ∀ u v : X.K, IsU X u → IsU X v → u ∈ topF X M → v ∈ topF X M →
    ∃ η, IsTopEta X M (topChar X M l n u) (topChar X M l n v) η

def LcGeo : Prop :=
  ∀ (F K E : Type) [Field F] [Field K] [Field E] [Algebra F K] [Algebra F E] [Algebra K E] [IsScalarTower F K E]
    [IsGalois K E] (A : Type) (η : (E ≃ₐ[F] E) → A), IsLocallyConstant (fun g : geo F K E => η g) →
      ∃ B : Finset E, ∀ g ∈ geo F K E, ∀ g' ∈ geo F K E, (∀ b ∈ B, g b = g' b) → η g = η g'

def KumL : Prop :=
  ∀ (F K E : Type) [Field F] [Field K] [Field E] [Algebra F K] [Algebra F E] [Algebra K E] [IsScalarTower F K E]
    [IsGalois K E] (m : ℕ) [NeZero m] (z : K), IsPrimitiveRoot (algebraMap K E z) m → ∀ φ : (E ≃ₐ[F] E) → ZMod m,
      (∀ g ∈ geo F K E, ∀ h ∈ geo F K E, φ (g * h) = φ g + φ h) →
      (∃ B : Finset E, ∀ g ∈ geo F K E, ∀ g' ∈ geo F K E, (∀ b ∈ B, g b = g' b) → φ g = φ g') →
      ∃ (w : K) (θ : E), w ≠ 0 ∧ θ ^ m = algebraMap K E w ∧ ∀ g ∈ geo F K E, GlobalTheory.NeedB.kum (N := m) (algebraMap K E z) θ g = φ g

def EdgeGeo : Prop :=
  ∀ (Γ : Type) [Group Γ] (m : ℕ) (Δ : Subgroup Γ) (x y : Γ →* Multiplicative (ZMod m)) (η : Γ → ZMod m),
    GlobalTheory.KEdge.CobOn Δ x y η → (∀ g ∈ Δ, ∀ h ∈ Δ, GlobalTheory.KEdge.edge x y η g h = 0) ∧
      ∀ σ : Γ, (∀ h ∈ Δ, σ * h * σ⁻¹ ∈ Δ) → ∀ g ∈ Δ, ∀ h ∈ Δ,
        GlobalTheory.KEdge.edge x y η σ (g * h) = GlobalTheory.KEdge.edge x y η σ g + GlobalTheory.KEdge.edge x y η σ h

def TopWEx : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l n M : ℕ), l.Prime → 0 < M → l ^ n ∣ M → ∀ u v : X.K, IsU X u → IsU X v → u ∈ topF X M → v ∈ topF X M →
    ∀ η, IsTopEta X M (topChar X M l n u) (topChar X M l n v) η → ∀ s ∈ fixMu Ω M,
      IsTopW (K := topL X M) (topZeta X M l n) (topChar X M l n u) (topChar X M l n v) η (topLift X M s)⁻¹
        (topW (K := topL X M) (topZeta X M l n) (topChar X M l n u) (topChar X M l n v) η (topLift X M s)⁻¹)

def CjB : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (M : ℕ) (e : topBar X M ≃+* Kb X), IsIso X M e →
    (∀ σ, FixF X M σ → ∀ z, e (cj X M e σ z) = σ (e z)) ∧
    (∀ σ τ, FixF X M σ → FixF X M τ → FixF X M (σ * τ) ∧ FixF X M σ⁻¹ ∧ cj X M e (σ * τ) = cj X M e σ * cj X M e τ ∧
      cj X M e σ⁻¹ = (cj X M e σ)⁻¹) ∧
    (∀ σ : RingAut (Kb X), (∀ f ∈ topL X M, σ (io X f) = io X f) → FixF X M σ ∧ cj X M e σ ∈ geo (topF X M) (topL X M) (topBar X M)) ∧
    (∀ l n : ℕ, e (topZeta X M l n) = zt X (l ^ n)) ∧
    ∀ (l n : ℕ), l ≠ 0 → ∀ σ, FixF X M σ → ∀ a b : topBar X M, b ≠ 0 → ∀ i : ZMod (l ^ n),
      a = topZeta X M l n ^ i.val * b → lg X (l ^ n) (e a) (e b) = i

def ChB : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l n M : ℕ), l.Prime → 0 < M → l ^ n ∣ M → ∀ u : X.K, u ≠ 0 → u ∈ topF X M →
    ∀ e : topBar X M ≃+* Kb X, IsIso X M e → e (topRoot X M (l ^ n) u) ^ l ^ n = io X u ∧
      ∀ σ, FixF X M σ → ka X (l ^ n) (e (topRoot X M (l ^ n) u)) σ = (topChar X M l n u (cj X M e σ)).toAdd

def PtIs : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l n M : ℕ), l.Prime → 0 < M → l ^ n ∣ M → ∀ u v : X.K, IsU X u → IsU X v → u ∈ topF X M → v ∈ topF X M →
    ∀ e : topBar X M ≃+* Kb X, IsIso X M e → ∀ η, IsTopEta X M (topChar X M l n u) (topChar X M l n v) η →
      IsPt X (l ^ n) u v (topPt X M e l n u v η)

def PtGam : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l n M : ℕ), l.Prime → 0 < M → l ^ n ∣ M → ∀ u v : X.K, IsU X u → IsU X v → u ∈ topF X M → v ∈ topF X M →
    ∀ e : topBar X M ≃+* Kb X, IsIso X M e → ∀ η, IsTopEta X M (topChar X M l n u) (topChar X M l n v) η →
      ∀ γ ∈ CongruenceSubgroup.Gamma M,
        Mv X (l ^ n) (slR X (ofSL γ)) 1 (topPt X M e l n u v η) (topPt X M e l n u v η) 1

def PtGal : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l n M : ℕ), l.Prime → 0 < M → l ^ n ∣ M → ∀ u v : X.K, IsU X u → IsU X v → u ∈ topF X M → v ∈ topF X M →
    ∀ e : topBar X M ≃+* Kb X, IsIso X M e → ∀ η, IsTopEta X M (topChar X M l n u) (topChar X M l n v) η →
      ∀ s ∈ fixMu Ω M, ∀ w : topL X M,
        IsTopW (K := topL X M) (topZeta X M l n) (topChar X M l n u) (topChar X M l n v) η (topLift X M s)⁻¹ w →
        ∀ f : X.Kˣ, (f : X.K) = w → Mv X (l ^ n) (X.gal s) s (topPt X M e l n u v η) (topPt X M e l n u v η) f

end UpperTheory.V.Z.Kato.Sym.PT

end
