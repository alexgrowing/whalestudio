import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin

noncomputable section

namespace UpperTheory.V.Z.Sym.Glob.Fib

open MulAction

def Decomp : Prop :=
  ∀ (H X I : Type) [Group H] [MulAction H X] (H₀ : Subgroup H) (k : X → ℂ) (Hi Yi : I → Type) [∀ i, Group (Hi i)]
    [∀ i, MulAction (Hi i) (Yi i)] (φ : ∀ i, Hi i →* H) (e : ∀ i, Yi i → X) (ki : ∀ i, Yi i → ℂ),
    H₀.Normal → (∀ (h : H) x, k (h • x) = k x) → (∃ T : Finset X, ∀ x, k x ≠ 0 → ∃ h : H, ∃ s ∈ T, x = h • s) →
    (∀ i (h : Hi i) y, e i (h • y) = φ i h • e i y) → (∀ i, Function.Injective (e i)) →
    (∀ i (h : Hi i) y, ki i (h • y) = ki i y) → (∀ i y, ki i y ≠ 0 → k (e i y) = ki i y) →
    (∀ x, k x ≠ 0 → ∃ i y, ∃ h : H, ki i y ≠ 0 ∧ x = h • e i y) →
    (∀ i j y y' (h : H), ki i y ≠ 0 → ki j y' ≠ 0 → h • e i y = e j y' → i = j ∧ h ∈ (φ i).range) →
    gq H₀ k = ∑ᶠ i, gq (H₀.comap (φ i)) (ki i)

def PushZero : Prop :=
  ∀ (H Y : Type) [Group H] [MulAction H Y] (H₀ : Subgroup H) (k : Y → ℂ), H₀.index ≠ 0 → (∀ z ∈ H₀, ∀ y : Y, z • y = y) →
    (∀ (h : H) y, k (h • y) = k y) → (Function.support k).Finite → gq H₀ k = (∑ᶠ y, k y) / (H₀.index : ℂ)

def Push : Prop :=
  ∀ (H X' X : Type) [Group H] [MulAction H X'] [MulAction H X] (H₀ : Subgroup H) (q : X' → X) (k : X' → ℂ), H₀.Normal →
    (∀ (h : H) y, q (h • y) = h • q y) → (∀ z ∈ H₀, ∀ y : X', z • y = y) → (∀ (h : H) y, k (h • y) = k y) →
    (∃ T : Finset X', ∀ y, k y ≠ 0 → ∃ h : H, ∃ s ∈ T, y = h • s) → (∀ x, {y | q y = x ∧ k y ≠ 0}.Finite) →
    (∀ y, k y ≠ 0 → H₀.relIndex (stabilizer H (q y)) ≠ 0) →
    gq H₀ k = gq H₀ fun x => ∑ᶠ (y : X') (_ : q y = x), k y

def Bot : Prop :=
  ∀ (H Y : Type) [Group H] [MulAction H Y] (H₀ : Subgroup H) (k : Y → ℂ), (∀ a : ℂ, gq H₀ (fun y => a * k y) = a * gq H₀ k) ∧
    (Nat.card H₀ ≠ 0 → (∀ z ∈ H₀, ∀ y : Y, z • y = y) → gq H₀ k = (Nat.card H₀ : ℂ) * gq (⊥ : Subgroup H) k)

def Pair : Prop :=
  ∀ (H G I : Type) [Group H] [Group G] (j : H →* G) (H₀ : Subgroup H) (U : Subgroup G) (c : H → ℂ) (f : G → ℂ)
    (δ : I → H) (Hi : I → Type) [∀ i, Group (Hi i)] (φ : ∀ i, Hi i →* H),
    H₀ ≤ Subgroup.center H → (∀ z ∈ H₀, ∀ y : G ⧸ U, j z • y = y) → (∀ h γ, c (h * γ * h⁻¹) = c γ) →
    (∀ u ∈ U, ∀ g, f (u⁻¹ * g * u) = f g) → (∀ g, {γ | c γ * f (g⁻¹ * j γ * g) ≠ 0}.Finite) →
    (∃ T : Finset G, ∀ g, ∃ γ, ∃ s ∈ T, ∃ u ∈ U, g = j γ * s * u) →
    (∀ y : G ⧸ U, H₀.relIndex ((stabilizer G y).comap j) ≠ 0) →
    (∀ i x, x ∈ (φ i).range ↔ x * δ i = δ i * x) → (∀ i i' h, δ i' = h * δ i * h⁻¹ → i = i') →
    (∀ γ g, c γ * f (g⁻¹ * j γ * g) ≠ 0 → ∃ i h, γ = h * δ i * h⁻¹) →
    gqOn j H₀ U (fun y => ∑ᶠ γ, c γ * f (y.out⁻¹ * j γ * y.out)) =
      ∑ᶠ i, c (δ i) * gqOn (j.comp (φ i)) (H₀.comap (φ i)) U fun y => f (y.out⁻¹ * j (δ i) * y.out)

def SuppFin : Prop :=
  ∀ (Γ G V : Type) [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] (B : Base Γ G V), B.Fin → B.Γ₀ = ⊥ →
    ∀ f : G → ℂ, (Base.Tw.one B).IsTest f → ∀ g, {γ | f (g⁻¹ * B.ι γ * g) ≠ 0}.Finite

def TrKer : Prop :=
  ∀ (Γ G V : Type) [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (B : Base Γ G V), B.Fin →
    B.ω = 1 → B.Γ₀ = ⊥ → ∀ f : G → ℂ, (Base.Tw.one B).IsTest f →
    LinearMap.trace ℂ B.Forms ((Base.Tw.one B).R f) =
      gqOn B.ι ⊥ B.U fun y => ∑ᶠ γ, LinearMap.trace ℂ V (B.W γ) * f (y.out⁻¹ * B.ι γ * y.out)

def CardFib : Prop :=
  ∀ (G : Type) [Group G] (S U U' : Subgroup G) (x : G) (Ux : Subgroup S) (s₀ : S), S.Normal → U ≤ U' →
    (∀ s : S, s ∈ Ux ↔ x⁻¹ * s * x ∈ U) →
    {s : S ⧸ Ux | (((s.out : G) * x : G) : G ⧸ U') = (((s₀ : G) * x : G) : G ⧸ U')}.ncard = U.relIndex (U' ⊓ S)

def Cover : Prop :=
  ∀ (H G : Type) [Group H] [Group G] (S U U' : Subgroup G) (x : G) (Ux : Subgroup S) (ι : H →* S) (Φ : G → ℂ), S.Normal → U ≤ U' →
    (∀ s : S, s ∈ Ux ↔ x⁻¹ * s * x ∈ U) → U.relIndex (U' ⊓ S) ≠ 0 → (∀ h g, Φ (ι h * g) = Φ g) → (∀ u ∈ U', ∀ g, Φ (g * u) = Φ g) →
    (∃ T : Finset S, ∀ s, ∃ h, ∃ t ∈ T, ∃ u ∈ Ux, s = ι h * t * u) → (∀ g : G, {h | g⁻¹ * ι h * g ∈ U'}.Finite) →
    gqOn ι ⊥ Ux (fun s => Φ (s.out * x)) =
      (U.relIndex (U' ⊓ S) : ℂ) * gqOn (S.subtype.comp ι) ⊥ U' ((orbit S (x : G ⧸ U')).indicator fun y => Φ y.out)

def SumFib : Prop :=
  ∀ (Γ G I : Type) [Group Γ] [Group G] [Fintype I] (ι : Γ →* G) (S U' : Subgroup G) (Γ₀ : Subgroup Γ) (x : I → G) (Φ : G → ℂ),
    (∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ S) → Γ₀.Normal → (∀ h g, Φ (ι h * g) = Φ g) → (∀ u ∈ U', ∀ g, Φ (g * u) = Φ g) →
    (∃ T : Finset G, ∀ g, ∃ γ, ∃ s ∈ T, ∃ u ∈ U', g = ι γ * s * u) →
    (∀ i j γ, ∀ s ∈ S, ∀ u ∈ U', x j = ι γ * s * x i * u → i = j) → (∀ g, ∃ i γ, ∃ s ∈ S, ∃ u ∈ U', g = ι γ * s * x i * u) →
    gqOn ι Γ₀ U' (fun y => Φ y.out) =
      ∑ i, gqOn (ι.comp ((S ⊔ U').comap ι).subtype) (Γ₀.subgroupOf ((S ⊔ U').comap ι)) U'
        ((orbit S (x i : G ⧸ U')).indicator fun y => Φ y.out)

def IndexFin : Prop :=
  ∀ (Γ G : Type) [Group Γ] [Group G] (ι : Γ →* G) (S U' : Subgroup G) (Γ₁ Γ₀ : Subgroup Γ), S.Normal → Γ₁.Normal →
    (∃ T : Finset G, ∀ s ∈ S, ∃ h ∈ Γ₁, ∃ t ∈ T, ∃ u ∈ U', s = ι h * t * u) → Γ₀.relIndex (U'.comap ι) ≠ 0 →
    (Γ₁ ⊔ Γ₀).relIndex ((S ⊔ U').comap ι) ≠ 0

def StabFin : Prop :=
  ∀ (H G : Type) [Group H] [Group G] (S U U' : Subgroup G) (ι : H →* S) (x : G), S.Normal → U.relIndex (U' ⊓ S) ≠ 0 →
    {h | x⁻¹ * ι h * x ∈ U}.Finite → {h | x⁻¹ * ι h * x ∈ U'}.Finite

def Reps : Prop :=
  ∀ (Γ G : Type) [Group Γ] [Group G] (ι : Γ →* G) (S U' : Subgroup G) (Y : Finset G) (x₀ : G), S.Normal →
    (∀ g, ∃ γ, ∃ s ∈ S, ∃ y ∈ Y, ∃ u ∈ U', g = ι γ * s * y * u) →
    ∃ (n : ℕ) (x : Fin (n + 1) → G), x 0 = x₀ ∧ (∀ i, x i = x₀ ∨ x i ∈ Y) ∧
      (∀ i j γ, ∀ s ∈ S, ∀ u ∈ U', x j = ι γ * s * x i * u → i = j) ∧ ∀ g, ∃ i γ, ∃ s ∈ S, ∃ u ∈ U', g = ι γ * s * x i * u

def OneFib : Prop :=
  ∀ (Γ G : Type) [Group Γ] [Group G] (ι : Γ →* G) (S U' : Subgroup G) (Γ₁ Γ₀ : Subgroup Γ) (x : G) (Φ : G → ℂ),
    (∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ S) → Γ₁ ≤ S.comap ι → Γ₀.Normal → (∀ z ∈ Γ₀, ∀ y : G ⧸ U', ι z • y = y) →
    (∀ h g, Φ (ι h * g) = Φ g) → (∀ u ∈ U', ∀ g, Φ (g * u) = Φ g) →
    (∃ T : Finset G, ∀ s ∈ S, ∃ h ∈ Γ₁, ∃ t ∈ T, ∃ u ∈ U', s * x = ι h * t * u) →
    (∀ y : G ⧸ U', Γ₀.relIndex ((stabilizer G y).comap ι) ≠ 0) →
    (Γ₁ ⊔ Γ₀).relIndex ((S ⊔ U').comap ι) ≠ 0 → Nat.card (Γ₀.subgroupOf Γ₁) ≠ 0 →
    (Nat.card (Γ₀.subgroupOf Γ₁) : ℂ) * gqOn (ι.comp Γ₁.subtype) ⊥ U' ((orbit S (x : G ⧸ U')).indicator fun y => Φ y.out) =
      ((Γ₁ ⊔ Γ₀).relIndex ((S ⊔ U').comap ι) : ℂ) *
        gqOn (ι.comp ((S ⊔ U').comap ι).subtype) (Γ₀.subgroupOf ((S ⊔ U').comap ι)) U'
          ((orbit S (x : G ⧸ U')).indicator fun y => Φ y.out)

def Master : Prop :=
  ∀ (Γ G : Type) [Group Γ] [Group G] (ι : Γ →* G) (S U U' : Subgroup G) (Γ₁ Γ₀ : Subgroup Γ) (ι₁ : Γ₁ →* S),
    (∀ γ, (ι₁ γ : G) = ι γ) → (∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ S) → Γ₁.Normal → Γ₀.Normal →
    (∀ z ∈ Γ₀, ∀ y : G ⧸ U', ι z • y = y) → U ≤ U' → U.relIndex (U' ⊓ S) ≠ 0 →
    (∀ x : G, ∃ T : Finset S, ∀ s, ∃ h, ∃ t ∈ T, ∃ u : S, x⁻¹ * u * x ∈ U ∧ s = ι₁ h * t * u) →
    (∀ x : G, {h | x⁻¹ * ι₁ h * x ∈ U}.Finite) →
    (∃ T : Finset G, ∀ g, ∃ γ, ∃ s ∈ T, ∃ u ∈ U', g = ι γ * s * u) →
    (∀ y : G ⧸ U', Γ₀.relIndex ((stabilizer G y).comap ι) ≠ 0) →
    ∃ c : ℝ, 0 < c ∧ ∀ (I : Type) [Fintype I] (x : I → G) (Ux : I → Subgroup S) (Φ : G → ℂ),
      (∀ i j γ, ∀ s ∈ S, ∀ u ∈ U', x j = ι γ * s * x i * u → i = j) → (∀ g, ∃ i γ, ∃ s ∈ S, ∃ u ∈ U', g = ι γ * s * x i * u) →
      (∀ i (s : S), s ∈ Ux i ↔ (x i)⁻¹ * s * x i ∈ U) → (∀ h g, Φ (ι h * g) = Φ g) → (∀ u ∈ U', ∀ g, Φ (g * u) = Φ g) →
      ∑ i, gqOn ι₁ ⊥ (Ux i) (fun s => Φ (s.out * x i)) = c * gqOn ι Γ₀ U' fun y => Φ y.out

end UpperTheory.V.Z.Sym.Glob.Fib
