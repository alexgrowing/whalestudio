import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FrobFactsAlt

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.DZA GlobalTheory.LBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L

def itN {A : Type} [CommRing A] (τ : A ≃+* A) (d : ℕ) (x : A) : A := ∏ i ∈ Finset.range d, τ^[i] x

def IntEl {k : Type} [Field k] [ValuativeRel k] {n : ℕ} (γ : GL (Fin n) k) : Prop :=
  (∀ i, valuation k ((γ : Matrix (Fin n) (Fin n) k).charpoly.coeff i) ≤ 1) ∧ valuation k (γ : Matrix (Fin n) (Fin n) k).det = 1

def FrobeniusTwistedHilbertNinety : Prop :=
  ∀ (F₀ F₁ : Type) [Field F₀] [Fintype F₀] [Field F₁] [Fintype F₁] [Algebra F₀ F₁] (sb : F₁ ≃ₐ[F₀] F₁),
    (∀ z : F₁, sb z = z ^ Fintype.card F₀) → ∀ (A : Type) [CommRing A] [Algebra F₁ A] [Finite A] (τ : A ≃+* A), (∀ z, τ (algebraMap F₁ A z) = algebraMap F₁ A (sb z)) →
      (∀ x, τ^[Module.finrank F₀ F₁] x = x) → ∀ c : A, itN τ (Module.finrank F₀ F₁) c = 1 → ∃ y : Aˣ, c * τ y = y

def NormFin : Prop :=
  ∀ (F₀ F₁ : Type) [Field F₀] [Fintype F₀] [Field F₁] [Fintype F₁] [Algebra F₀ F₁] (sb : F₁ ≃ₐ[F₀] F₁),
    (∀ z : F₁, sb z = z ^ Fintype.card F₀) → ∀ (A : Type) [CommRing A] [Algebra F₁ A] [Finite A] (τ : A ≃+* A), (∀ z, τ (algebraMap F₁ A z) = algebraMap F₁ A (sb z)) →
      (∀ x, τ^[Module.finrank F₀ F₁] x = x) → ∀ x : A, IsUnit x → τ x = x → ∃ y : A, itN τ (Module.finrank F₀ F₁) y = x

def NormAdic : Prop :=
  ∀ (A : Type) [CommRing A] (I : Ideal A) [IsAdicComplete I A] (τ : A ≃+* A) (d : ℕ), (∀ x, τ^[d] x = x) → (∀ x ∈ I, τ x ∈ I) →
    ∀ a : A, ∑ i ∈ Finset.range d, τ^[i] a = 1 → ∀ x y : A, IsUnit x → τ x = x → itN τ d y - x ∈ I → ∃ y', itN τ d y' = x

def NormPoly : Prop :=
  ∀ (k K : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra k K] [ValuativeExtension k K] [FiniteDimensional k K] [IsGalois k K]
    (F₀ F₁ : Type) [Field F₀] [Fintype F₀] [Field F₁] [Fintype F₁] [Algebra F₀ F₁]
    (rk : 𝒪[k] →+* F₀) (rK : 𝒪[K] →+* F₁) (s : K ≃ₐ[k] K) (sb : F₁ ≃ₐ[F₀] F₁), IsRes rk rK s sb →
    ∀ χ : k[X], χ.Monic → (∀ i, valuation k (χ.coeff i) ≤ 1) → valuation k (χ.coeff 0) = 1 →
      ∃ p : K[X], (∀ i, valuation K (p.coeff i) ≤ 1) ∧
        χ.map (algebraMap k K) ∣ ∏ i ∈ Finset.range (Module.finrank k K), p.map ((s ^ i : K ≃ₐ[k] K) : K →+* K) - X

def GoodDelta : Prop :=
  ∀ (k K : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra k K] [ValuativeExtension k K] [FiniteDimensional k K] [IsGalois k K]
    (F₀ F₁ : Type) [Field F₀] [Fintype F₀] [Field F₁] [Fintype F₁] [Algebra F₀ F₁]
    (rk : 𝒪[k] →+* F₀) (rK : 𝒪[K] →+* F₁) (s : K ≃ₐ[k] K) (sb : F₁ ≃ₐ[F₀] F₁), IsRes rk rK s sb →
    ∀ (n : ℕ) (γ : GL (Fin n) k), IntEl γ → ∃ δ : GL (Fin n) K, GlobalTheory.LBC.norm k s δ = incl K n γ ∧
      (∀ x : GL (Fin n) K, Commute x (incl K n γ) → Commute x δ) ∧
      ∀ g : GL (Fin n) K, g⁻¹ * incl K n γ * g ∈ KO K n → g⁻¹ * δ * g ∈ KO K n

def LatDesc : Prop :=
  ∀ (k K : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra k K] [ValuativeExtension k K] [FiniteDimensional k K] [IsGalois k K]
    (F₀ F₁ : Type) [Field F₀] [Fintype F₀] [Field F₁] [Fintype F₁] [Algebra F₀ F₁]
    (rk : 𝒪[k] →+* F₀) (rK : 𝒪[K] →+* F₁) (s : K ≃ₐ[k] K) (sb : F₁ ≃ₐ[F₀] F₁), IsRes rk rK s sb →
    ∀ (n : ℕ) (g : GL (Fin n) K), g⁻¹ * galAct s n g ∈ KO K n → ∃ h : GL (Fin n) k, ∃ κ ∈ KO K n, g = incl K n h * κ

def LiftVal : Prop :=
  ∀ (F₀ F₁ : Type) [Field F₀] [Fintype F₀] [Field F₁] [Fintype F₁] [Algebra F₀ F₁] (sb : F₁ ≃ₐ[F₀] F₁),
    (∀ z : F₁, sb z = z ^ Fintype.card F₀) → ∀ (n : ℕ) (fb : GL (Fin n) F₀ → ℂ), (∀ a b, fb (b⁻¹ * a * b) = fb a) →
      (∀ δ γ, IsFinNorm sb δ γ → normLift sb fb δ = fb γ) ∧
      ∀ δ x : GL (Fin n) F₁, normLift sb fb (x⁻¹ * δ * galAct sb n x) = normLift sb fb δ

def RedNorm : Prop :=
  ∀ (k K : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra k K] [ValuativeExtension k K] [FiniteDimensional k K] [IsGalois k K]
    (F₀ F₁ : Type) [Field F₀] [Fintype F₀] [Field F₁] [Fintype F₁] [Algebra F₀ F₁]
    (rk : 𝒪[k] →+* F₀) (rK : 𝒪[K] →+* F₁) (s : K ≃ₐ[k] K) (sb : F₁ ≃ₐ[F₀] F₁), IsRes rk rK s sb →
    ∀ n : ℕ, (∀ h : GL (Fin n) k, incl K n h ∈ KO K n ↔ h ∈ KO k n) ∧ (∀ β ∈ KO K n, GlobalTheory.LBC.norm k s β ∈ KO K n) ∧
      (∀ β g : GL (Fin n) K, GlobalTheory.LBC.norm k s (g⁻¹ * β * galAct s n g) = g⁻¹ * GlobalTheory.LBC.norm k s β * g) ∧
      (∀ (γ : GL (Fin n) k) (g : GL (Fin n) K), g⁻¹ * incl K n γ * g ∈ KO K n → IntEl γ) ∧
      ∀ fb : GL (Fin n) F₀ → ℂ, (∀ a b, fb (b⁻¹ * a * b) = fb a) →
        (∀ β ∈ KO K n, ∀ γ : GL (Fin n) k, GlobalTheory.LBC.norm k s β = incl K n γ → infl rK (normLift sb fb) β = infl rk fb γ) ∧
        ∀ κ ∈ KO K n, ∀ y, infl rK (normLift sb fb) (κ⁻¹ * y * galAct s n κ) = infl rK (normLift sb fb) y

def OrbTransfer : Prop :=
  ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [T2Space H] (j : H →* G), Topology.IsClosedEmbedding j → ∀ (θ : G →* G) (K : Subgroup G) (K₀ : Subgroup H),
    (∀ h, j h ∈ K ↔ h ∈ K₀) → ∀ (δ : G) (γ : H), GlobalTheory.BCT.twCent θ δ = (GlobalTheory.BCT.twCent (MonoidHom.id H) γ).map j →
    ∀ (φ : G → ℂ) (f : H → ℂ), (∀ κ ∈ K, ∀ y, φ (κ⁻¹ * y * θ κ) = φ y) →
      (∀ x, φ (x⁻¹ * δ * θ x) ≠ 0 → ∃ h, ∃ κ ∈ K, x = j h * κ) → (∀ h, φ ((j h)⁻¹ * δ * θ (j h)) = f (h⁻¹ * γ * h)) →
      (∀ h, θ (j h) = j h) → GlobalTheory.BCT.twOrb θ K δ φ = GlobalTheory.BCT.twOrb (MonoidHom.id H) K₀ γ f

def Derive : Prop :=
  ∀ (k K : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Algebra k K], Continuous (algebraMap k K) →
    ∀ (F₀ F₁ : Type) [Field F₀] [Fintype F₀] [Field F₁] [Fintype F₁] [Algebra F₀ F₁]
      (rk : 𝒪[k] →+* F₀) (rK : 𝒪[K] →+* F₁) (s : K ≃ₐ[k] K) (sb : F₁ ≃ₐ[F₀] F₁), IsRes rk rK s sb →
      ValuativeExtension k K ∧ FiniteDimensional k K ∧ IsGalois k K

end UpperTheory.Gal.InertialTypesAlt.L
