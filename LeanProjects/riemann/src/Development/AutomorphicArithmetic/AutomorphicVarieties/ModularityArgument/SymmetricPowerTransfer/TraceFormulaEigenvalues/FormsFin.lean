import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.IsGenEig

noncomputable section

namespace UpperTheory.V.Z.Sym.Tf

open MulAction

def FormsFin : Prop :=
  ∀ (Γ G V : Type) [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (B : Base Γ G V), B.Fin →
    FiniteDimensional ℂ B.Forms

def RSpec : Prop :=
  ∀ (Γ G V : Type) [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] (B : Base Γ G V) (s : B.Tw) (f : G → ℂ), s.IsTest f →
    ∀ φ : B.Forms, (s.R f φ).1 = s.opF f φ.1

def RLin : Prop :=
  ∀ (Γ G V : Type) [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] (B : Base Γ G V) (s : B.Tw) (I : Type) (S : Finset I)
    (c : I → ℂ) (f : I → G → ℂ), (∀ i ∈ S, s.IsTest (f i)) →
    s.IsTest (fun y => ∑ i ∈ S, c i * f i y) ∧ s.R (fun y => ∑ i ∈ S, c i * f i y) = ∑ i ∈ S, c i • s.R (f i)

def RMul : Prop :=
  ∀ (Γ G V : Type) [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] (B : Base Γ G V) (s₁ s₂ : B.Tw) (f₁ f₂ : G → ℂ),
    s₁.IsTest f₁ → s₂.IsTest f₂ →
    (s₁.mul s₂).IsTest (s₁.conv f₁ f₂) ∧ s₁.R f₁ * s₂.R f₂ = (s₁.mul s₂).R (s₁.conv f₁ f₂)

def Trace : Prop :=
  ∀ (Γ G V : Type) [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (B : Base Γ G V), B.Fin →
    ∀ (s : B.Tw) (f : G → ℂ), s.IsTest f → ∀ (I : Type) (δ : I → Γ), (∀ i j, s.Rel (δ i) (δ j) → i = j) →
    (∀ γ : Γ, (∃ y, s.ker f γ y ≠ 0) → ∃ i, s.Rel (δ i) γ) →
    {i | ∃ y, s.ker f (δ i) y ≠ 0}.Finite ∧ LinearMap.trace ℂ B.Forms (s.R f) = ∑ᶠ i, s.term f (δ i)

def CentFin : Prop :=
  ∀ (Γ G V : Type) [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] (B : Base Γ G V), B.Fin →
    ∀ (s : B.Tw) (f : G → ℂ), s.IsTest f → ∀ δ : Γ, FinOrb (B.ι.comp (s.Cent δ).subtype) s.θ.toMonoidHom B.U f (B.ι δ)

def GqIndex : Prop :=
  ∀ (H' H G : Type) [Group H'] [Group H] [Group G] (φ : H' →* H) (j : H →* G) (H₀ : Subgroup H) (U : Subgroup G) (k : G ⧸ U → ℂ),
    H₀.Normal → (∀ z ∈ H₀, ∀ y : G ⧸ U, j z • y = y) → (φ.range ⊔ H₀).index ≠ 0 → (∀ h y, k (j h • y) = k y) →
    (∃ S : Finset (G ⧸ U), ∀ y, k y ≠ 0 → ∃ h, ∃ x ∈ S, y = j h • x) →
    (∀ y : G ⧸ U, k y ≠ 0 → H₀.relIndex ((stabilizer G y).comap j) ≠ 0) →
    gqOn (j.comp φ) (H₀.comap φ) U k = ((φ.range ⊔ H₀).index : ℂ) * gqOn j H₀ U k

def GqMass : Prop :=
  ∀ (H T G : Type) [Group H] [CommGroup T] [Group G] (φ : H →* T) (ι : T →* G) (H₀ : Subgroup H) (C : Subgroup T) (θ : G →* G)
    (U : Subgroup G) (f : G → ℂ) (δ : G), (∀ u ∈ U, ∀ x, f (u⁻¹ * x * θ u) = f x) → (∀ t, (ι t)⁻¹ * δ * θ (ι t) = δ) →
    FinOrb ι θ U f δ → (∀ z ∈ H₀, ∀ y : G ⧸ U, ι (φ z) • y = y) → (φ.range ⊔ C).index ≠ 0 → H₀.relIndex (C.comap φ) ≠ 0 →
    (∀ y : G ⧸ U, f (y.out⁻¹ * δ * θ y.out) ≠ 0 →
      (stabilizer G y).comap ι ≤ C ∧ ((stabilizer G y).comap ι).relIndex C ≠ 0) → H₀ ≤ C.comap φ →
    gqOn (ι.comp φ) H₀ U (fun y => f (y.out⁻¹ * δ * θ y.out)) = mass φ H₀ C * orb ι C θ U f δ

def OrbProd : Prop :=
  ∀ (I G T : Type) [Group G] [CommGroup T] (Gv Tv : I → Type) [∀ v, Group (Gv v)] [∀ v, CommGroup (Tv v)]
    (K U : ∀ v, Subgroup (Gv v)) (C₀ C : ∀ v, Subgroup (Tv v)) (P : RPG G Gv K) (Q : RPG T Tv C₀)
    (ι : T →* G) (ιv : ∀ v, Tv v →* Gv v) (θ : G →* G) (θv : ∀ v, Gv v →* Gv v) (f : G → ℂ) (fv : ∀ v, Gv v → ℂ) (δ : G),
    (∀ v t, P.p v (ι t) = ιv v (Q.p v t)) → (∀ v g, P.p v (θ g) = θv v (P.p v g)) → (∀ g, f g = ∏ᶠ v, fv v (P.p v g)) →
    (∀ v, ∀ u ∈ U v, ∀ x, fv v (u⁻¹ * x * θv v u) = fv v x) → (∀ v t, (ιv v t)⁻¹ * P.p v δ * θv v (ιv v t) = P.p v δ) →
    ∀ S : Finset I, (∀ v ∈ S, FinOrb (ιv v) (θv v) (U v) (fv v) (P.p v δ)) →
    (∀ v ∉ S, K v ≤ U v ∧ C₀ v ≤ C v ∧ (C v).map (ιv v) ≤ U v ∧ fv v (P.p v δ) = 1 ∧
      ∀ y, fv v (y⁻¹ * P.p v δ * θv v y) ≠ 0 → ∃ t, ∃ u ∈ U v, y = ιv v t * u) →
    FinOrb ι θ (P.box U) f δ ∧
      orb ι (Q.box C) θ (P.box U) f δ = ∏ v ∈ S, orb (ιv v) (C v) (θv v) (U v) (fv v) (P.p v δ)

def OrbOne : Prop :=
  ∀ (T G : Type) [CommGroup T] [Group G] (ι : T →* G) (C : Subgroup T) (θ : G →* G) (U : Subgroup G) (f : G → ℂ) (δ : G),
    (∀ u ∈ U, ∀ x, f (u⁻¹ * x * θ u) = f x) → (∀ t, (ι t)⁻¹ * δ * θ (ι t) = δ) → C.map ι ≤ U →
    (∀ y, f (y⁻¹ * δ * θ y) ≠ 0 → ∃ t, ∃ u ∈ U, y = ι t * u) → orb ι C θ U f δ = f δ

def OrbReps : Prop :=
  ∀ (T G : Type) [CommGroup T] [Group G] (ι : T →* G) (C : Subgroup T) (θ : G →* G) (U : Subgroup G) (f : G → ℂ) (δ : G),
    (∀ u ∈ U, ∀ x, f (u⁻¹ * x * θ u) = f x) → (∀ t, (ι t)⁻¹ * δ * θ (ι t) = δ) → ∀ (J : Type) (S : Finset J) (x : J → G),
    (∀ i ∈ S, ∀ j ∈ S, ∀ t, ∀ u ∈ U, x j = ι t * x i * u → i = j) →
    (∀ y, f (y⁻¹ * δ * θ y) ≠ 0 → ∃ t, ∃ i ∈ S, ∃ u ∈ U, y = ι t * x i * u) →
    orb ι C θ U f δ = ∑ i ∈ S, (((stabilizer G (x i : G ⧸ U)).comap ι).relIndex C : ℂ) * f ((x i)⁻¹ * δ * θ (x i))

def OrbConj : Prop :=
  ∀ (T G : Type) [Group T] [Group G] (ι : T →* G) (C : Subgroup T) (θ : G →* G) (U : Subgroup G) (f : G → ℂ) (δ x : G),
    (∀ u ∈ U, ∀ y, f (u⁻¹ * y * θ u) = f y) → (∀ t, (ι t)⁻¹ * δ * θ (ι t) = δ) → C.Normal →
    orb ((MulAut.conj x⁻¹).toMonoidHom.comp ι) C θ U f (x⁻¹ * δ * θ x) = orb ι C θ U f δ

def TrTheta : Prop :=
  ∀ (Λ M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (u : Λ → Module.End ℂ M) (Θ : Module.End ℂ M) (σ : Λ ≃ Λ),
    (∀ a b, Commute (u a) (u b)) → (∀ a, Θ * u a = u (σ a) * Θ) →
    ∃ (X : Finset (Λ → ℂ)) (c : (Λ → ℂ) → ℂ), (∀ χ ∈ X, IsGenEig u χ ∧ ∀ a, χ (σ a) = χ a) ∧
      ∀ a, LinearMap.trace ℂ M (u a * Θ) = ∑ χ ∈ X, c χ * χ a

def TrPos : Prop :=
  ∀ (Λ M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (u : Λ → Module.End ℂ M), (∀ a b, Commute (u a) (u b)) →
    ∃ (X : Finset (Λ → ℂ)) (d : (Λ → ℂ) → ℕ), (∀ χ, χ ∈ X ↔ IsGenEig u χ) ∧ (∀ χ ∈ X, 0 < d χ) ∧
      ∀ a, LinearMap.trace ℂ M (u a) = ∑ χ ∈ X, (d χ : ℂ) * χ a

def EigVec : Prop :=
  ∀ (Λ M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (u : Λ → Module.End ℂ M), (∀ a b, Commute (u a) (u b)) →
    ∀ χ, IsGenEig u χ ↔ ∃ v : M, v ≠ 0 ∧ ∀ a, u a v = χ a • v

def Extract : Prop :=
  ∀ (P I J : Type) [Mul P] (S : Finset I) (S' : Finset J) (a : I → ℂ) (b : J → ℂ) (α : I → P → ℂ) (β : J → P → ℂ),
    (∀ i ∈ S, ∀ p q, α i (p * q) = α i p * α i q) → (∀ j ∈ S', ∀ p q, β j (p * q) = β j p * β j q) →
    (∀ p, ∑ i ∈ S, a i * α i p = ∑ j ∈ S', b j * β j p) → ∀ χ : P → ℂ, χ ≠ 0 →
    (open Classical in ∑ j ∈ S'.filter (fun j => β j = χ), b j ≠ 0) → ∃ i ∈ S, a i ≠ 0 ∧ α i = χ

def Pigeon : Prop :=
  ∀ (X I : Type) (A : Set X), A.Finite → ∀ P : X → I → Prop, (∀ S : Finset I, ∃ x ∈ A, ∀ i ∈ S, P x i) → ∃ x ∈ A, ∀ i, P x i

end UpperTheory.V.Z.Sym.Tf
