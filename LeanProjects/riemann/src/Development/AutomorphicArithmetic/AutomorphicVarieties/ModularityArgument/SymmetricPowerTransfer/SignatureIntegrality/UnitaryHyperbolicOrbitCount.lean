import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.UnitaryDoubleCosetIndicator

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

namespace UpperTheory.V.Z.Sym.Sig

open Classical

def MemJ : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (V : Lev k) (n : ℕ) (g : GL (Fin n) k), g ∈ V.J n ↔
    (∀ i j, valuation k (g i j) ≤ 1) ∧ (∀ i j, j < i → valuation k (g i j) ≤ valuation k (unif k : k) ^ (V.c + 1)) ∧
      ∀ i, ∃ u ∈ V.H, (u : k) = g i i

def FactJ : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (V : Lev k) (n : ℕ), (∀ g ∈ V.J n, ∃ a ∈ (glIwa k n).N, ∃ s ∈ V.TH n, ∃ b ∈ (glIwa k n).Nm V.c, g = a * s * b) ∧
    ∀ (m : ℕ), ∀ a ∈ (glIwa k n).N, ∀ a' ∈ (glIwa k n).N, ∀ s ∈ V.TH n, ∀ s' ∈ V.TH n, ∀ b ∈ (glIwa k n).Nm V.c,
      ∀ b' ∈ (glIwa k n).Nm V.c, (a * s * b)⁻¹ * (a' * s' * b') ∈ Kc k n m → a⁻¹ * a' ∈ Kc k n m

def Shrink : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (d : Fin n → kˣ), SDom d → ∀ m : ℕ,
    (∀ a ∈ (glIwa k n).N, a ∈ Kc k n m → dg d * a * (dg d)⁻¹ ∈ (glIwa k n).N ⊓ Kc k n (m + 1)) ∧
      ∀ c, ∀ b ∈ (glIwa k n).Nm c, b ∈ Kc k n m → (dg d)⁻¹ * b * dg d ∈ (glIwa k n).Nm c ⊓ Kc k n (m + 1)

def FixPt : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (P : Subgroup (GL (Fin n) k)),
    (P = (glIwa k n).N ∨ ∃ c, P = (glIwa k n).Nm c) → ∀ Ψ : P → P,
    (∀ (m : ℕ) (a b : P), (a : GL (Fin n) k)⁻¹ * b ∈ Kc k n m → (Ψ a : GL (Fin n) k)⁻¹ * Ψ b ∈ Kc k n (m + 1)) → ∃ a, Ψ a = a

def Contract : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (V : Lev k) (n : ℕ) (σ : GL (Fin n) k →* GL (Fin n) k), Pres V σ → ∀ d : Fin n → kˣ, SDom d →
    ∀ g ∈ V.DC d, ∃ j ∈ V.J n, ∃ s ∈ V.TH n, j⁻¹ * g * σ j = s * dg d

def DiagDC : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (V : Lev k) (n : ℕ) (d s : Fin n → kˣ), Dom d → (dg s ∈ V.DC d ↔ ∀ i, s i / d i ∈ V.H)

def ThFacts : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (V : Lev k), Pres V (th' k) ∧ (∀ g ∈ V.J 3, th' k g ∈ V.J 3) ∧ (∀ x y z : kˣ, th' k (dg ![x, y, z]) = dg ![z⁻¹, y⁻¹, x⁻¹]) ∧
    (∀ (n : ℕ) (g : GL (Fin n) k), th k n (th k n g) = g) ∧ th k 3 (Phi k) = (Phi k)⁻¹ ∧ (Phi k)⁻¹ = Phi k ∧
    ∀ g, th' k g * Phi k = Phi k * th k 3 g

def ConjDiag : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (s s' : Fin n → kˣ), SDom s → SDom s' →
    ∀ y : GL (Fin n) k, y⁻¹ * dg s * y = dg s' → s = s' ∧ ∃ u, y = dg u

def FinFacts : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (V : Lev k), V.H.relIndex (Uo k) ≠ 0 ∧ V.H2 ≤ Uo k ∧ V.H ≤ V.H2 ∧ (∃ R, V.IsSigns R) ∧ (∃ R, V.IsSqReps R) ∧
    ∀ n : ℕ, HeckePair (V.J n) ∧ IsOpen (V.J n : Set (GL (Fin n) k)) ∧ IsCompact (V.J n : Set (GL (Fin n) k)) ∧ V.J n ≤ KO k (Fin n)

def Link : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ),
    (Lev.iw k).J n = iwC k n ⊤ ∧ (Lev.iw k).J n = (glIwa k n).Iw 0 ∧ ∀ c, (Lev.deep k c).J n = (glIwa k n).I1 c

def HkMul : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (V : Lev k) (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ (GL (Fin n) k) M),
    (∀ d d' : Fin n → kˣ, Dom d → Dom d' → hk ρ (V.J n) (dg d) * hk ρ (V.J n) (dg d') = hk ρ (V.J n) (dg (d * d'))) ∧
    ∀ d : Fin n → kˣ, Dom d → ∀ v : fixd ρ (V.J n), (hk ρ (V.J n) (dg d) v : M) = (glIwa k n).uOp ρ (dg d) v

def DCMul : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (V : Lev k) (n : ℕ) (d d' : Fin n → kˣ), Dom d → Dom d' → ∀ g : GL (Fin n) k,
    (g ∈ V.DC (d * d') → ∃! y : GL (Fin n) k ⧸ V.J n, y.out ∈ V.DC d ∧ y.out⁻¹ * g ∈ V.DC d') ∧
      ∀ y ∈ V.DC d, y⁻¹ * g ∈ V.DC d' → g ∈ V.DC (d * d')

def EqG : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (V : Lev k) (ω : kˣ →* ℂˣ) (Rs Ry : Finset kˣ) (x z : kˣ) (d : Fin 3 → kˣ),
    (∀ u ∈ V.J 3, ∀ u' ∈ V.J 3, ∀ g, V.unitaryDoubleCosetIndicator d (u * g * th k 3 u') = V.unitaryDoubleCosetIndicator d g ∧
      V.fG ω Rs Ry x z (u * g * th k 3 u') = V.fG ω Rs Ry x z g) ∧
    {y : GL (Fin 3) k ⧸ (V.J 3).map (th k 3) | V.unitaryDoubleCosetIndicator d y.out ≠ 0}.Finite ∧
    {y : GL (Fin 3) k ⧸ (V.J 3).map (th k 3) | V.fG ω Rs Ry x z y.out ≠ 0}.Finite

def EqZ : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (V : Lev k) (ω : kˣ →* ℂˣ), (∀ u ∈ V.H, ω u = 1) → ∀ (n : ℕ), 0 < n →
    (∃ Ω : V.ZJ n →* ℂˣ, ∀ (z : kˣ) (j : GL (Fin n) k) (u : V.ZJ n), j ∈ V.J n →
      (u : GL (Fin n) k) = GeneralLinearGroup.scalar (Fin n) z * j → Ω u = ω z) ∧
    (∀ u, u ∈ V.ZJ n ↔ ∃ z : kˣ, ∃ j ∈ V.J n, u = GeneralLinearGroup.scalar (Fin n) z * j) ∧
    ∀ d : Fin n → kˣ, SDom d →
      (∀ (z : kˣ), ∀ g ∈ V.DC d, V.fZ ω d (GeneralLinearGroup.scalar (Fin n) z * g) = (((ω z)⁻¹ : ℂˣ) : ℂ)) ∧
      (∀ (z : kˣ) g, V.fZ ω d (GeneralLinearGroup.scalar (Fin n) z * g) = (((ω z)⁻¹ : ℂˣ) : ℂ) * V.fZ ω d g) ∧
      (∀ u ∈ V.J n, ∀ u' ∈ V.J n, ∀ g, V.fZ ω d (u * g * u') = V.fZ ω d g) ∧
      {y : GL (Fin n) k ⧸ V.ZJ n | V.fZ ω d y.out ≠ 0}.Finite

def SuppG : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (V : Lev k) (ω : kˣ →* ℂˣ) (Rs Ry : Finset kˣ), V.IsSigns Rs → V.IsSqReps Ry → ∀ t x z : kˣ, Cone t x z →
    ∀ g, V.fG ω Rs Ry x z g ≠ 0 → ∃ (g₀ : GL (Fin 3) k) (x₁ y₁ z₁ : kˣ),
      g = g₀ * dg ![x₁, y₁, z₁] * Phi k * (th k 3 g₀)⁻¹ ∧ x₁ / z₁ / t ∈ V.H2

def SuppZ : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (V : Lev k) (ω : kˣ →* ℂˣ) (d : Fin 2 → kˣ), SDom d → ∀ g, V.fZ ω d g ≠ 0 →
    ∃ (g₀ : GL (Fin 2) k) (a b : kˣ), g = g₀ * dg ![a, b] * g₀⁻¹ ∧ a / b / (d 0 / d 1) ∈ V.H

def NormalG : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    (∀ (g₀ : GL (Fin 3) k) (x y z : kˣ), (g₀ * dg ![x, y, z] * Phi k * (th k 3 g₀)⁻¹) * th k 3 (g₀ * dg ![x, y, z] * Phi k * (th k 3 g₀)⁻¹) =
      g₀ * dg ![x / z, 1, z / x] * g₀⁻¹) ∧
    ∀ (δ : GL (Fin 3) k) (a : kˣ), valuation k (a : k) < 1 →
      ((δ * th k 3 δ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).charpoly = (X - C 1) * (X - C (a : k)) * (X - C ((a⁻¹ : kˣ) : k)) →
      ∃ (g₀ : GL (Fin 3) k) (x y z : kˣ), δ = g₀ * dg ![x, y, z] * Phi k * (th k 3 g₀)⁻¹ ∧ x / z = a

def NormalD : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (γ : GL (Fin 2) k) (a b : kˣ), a ≠ b →
    (γ : Matrix (Fin 2) (Fin 2) k).charpoly = (X - C (a : k)) * (X - C (b : k)) → ∃ g₀ : GL (Fin 2) k, γ = g₀ * dg ![a, b] * g₀⁻¹

def FixG : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (V : Lev k) (d : Fin 3 → kˣ), SDom d → ∀ x₁ y₁ z₁ : kˣ, valuation k ((x₁ / z₁ : kˣ) : k) < 1 → ∀ y : GL (Fin 3) k,
    (y⁻¹ * (dg ![x₁, y₁, z₁] * Phi k) * th k 3 y * (Phi k)⁻¹ ∈ V.DC d ↔ ∃ u : Fin 3 → kˣ, ∃ j ∈ V.J 3, y = dg u * j ∧
      x₁ / (u 0 * u 2) / d 0 ∈ V.H ∧ y₁ / u 1 ^ 2 / d 1 ∈ V.H ∧ z₁ / (u 0 * u 2) / d 2 ∈ V.H)

def UnitaryHyperbolicOrbitCount : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (V : Lev k) (T : Type) [Group T] (r : T →* kˣ), Function.Surjective r → ∀ (g₀ : GL (Fin 3) k) (ι : T →* GL (Fin 3) k),
    (∀ s, ι s = g₀ * dg ![r s, 1, (r s)⁻¹] * g₀⁻¹) → ∀ d : Fin 3 → kˣ, SDom d → ∀ x₁ y₁ z₁ : kˣ, valuation k ((x₁ / z₁ : kˣ) : k) < 1 →
    (letI : MulAction T (GL (Fin 3) k ⧸ V.J 3) := MulAction.compHom _ ι
     {o : MulAction.orbitRel.Quotient T (GL (Fin 3) k ⧸ V.J 3) |
       V.unitaryDoubleCosetIndicator d (o.out.out⁻¹ * (g₀ * dg ![x₁, y₁, z₁] * Phi k * (th k 3 g₀)⁻¹) * th k 3 o.out.out) ≠ 0}.Finite) ∧
    orb ι ((Uo k).comap r) (th k 3) (V.J 3) (V.unitaryDoubleCosetIndicator d) (g₀ * dg ![x₁, y₁, z₁] * Phi k * (th k 3 g₀)⁻¹) =
      if x₁ / z₁ / (d 0 / d 2) ∈ V.H ∧ ∃ s : kˣ, y₁ / (d 1 * s ^ 2) ∈ V.H then (V.H.relIndex (Uo k) : ℂ) * (V.H.relIndex V.H2 : ℂ) else 0

def OrbG : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (V : Lev k) (ω : kˣ →* ℂˣ), (∀ u ∈ V.H, ω u = 1) → ∀ (Rs Ry : Finset kˣ), V.IsSigns Rs → V.IsSqReps Ry → ∀ t x z : kˣ, Cone t x z →
    ∀ (T : Type) [Group T] (r : T →* kˣ), Function.Surjective r → ∀ (g₀ : GL (Fin 3) k) (ι : T →* GL (Fin 3) k),
    (∀ s, ι s = g₀ * dg ![r s, 1, (r s)⁻¹] * g₀⁻¹) → ∀ x₁ y₁ z₁ : kˣ, valuation k ((x₁ / z₁ : kˣ) : k) < 1 →
    orb ι ((Uo k).comap r) (th k 3) (V.J 3) (V.fG ω Rs Ry x z) (g₀ * dg ![x₁, y₁, z₁] * Phi k * (th k 3 g₀)⁻¹) =
      (V.H.relIndex V.H2 : ℂ) * V.val ω t (x₁ / z₁)

def OrbZ : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (V : Lev k) (ω : kˣ →* ℂˣ), (∀ u ∈ V.H, ω u = 1) → ∀ d : Fin 2 → kˣ, SDom d →
    ∀ (T : Type) [Group T] (p q : T →* kˣ), Function.Surjective (p / q) → ∀ (g₀ : GL (Fin 2) k) (ι : T →* GL (Fin 2) k),
    (∀ s, ι s = g₀ * dg ![p s, q s] * g₀⁻¹) → ∀ a b : kˣ, valuation k (a : k) < valuation k (b : k) →
    (letI : MulAction T (GL (Fin 2) k ⧸ V.ZJ 2) := MulAction.compHom _ ι
     {o : MulAction.orbitRel.Quotient T (GL (Fin 2) k ⧸ V.ZJ 2) | V.fZ ω d (o.out.out⁻¹ * (g₀ * dg ![a, b] * g₀⁻¹) * o.out.out) ≠ 0}.Finite) ∧
    orb ι ((Uo k).comap (p / q)) (MonoidHom.id _) (V.ZJ 2) (V.fZ ω d) (g₀ * dg ![a, b] * g₀⁻¹) =
      if a / b / (d 0 / d 1) ∈ V.H then (V.H.relIndex (Uo k) : ℂ) * (ω (d 1 / b) : ℂ) else 0

def OrbSK : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (V : Lev k) (ω : kˣ →* ℂˣ), (∀ u ∈ V.H, ω u = 1) → ∀ t : kˣ, valuation k (t : k) < 1 →
    ∀ (T : Type) [Group T] (p q : T →* kˣ), Function.Surjective (p / q) → ∀ (g₀ : GL (Fin 2) k) (ι : T →* GL (Fin 2) k),
    (∀ s, ι s = g₀ * dg ![p s, q s] * g₀⁻¹) →
    (∀ a : kˣ, valuation k (a : k) < 1 →
      orb ι ((Uo k).comap (p / q)) (MonoidHom.id _) (V.ZJ 2) (V.fS ω t) (g₀ * dg ![a, a⁻¹] * g₀⁻¹) = V.val ω t a) ∧
    ∀ ω' : kˣ →* ℂˣ, (∀ u ∈ V.H, ω' u = 1) → ∀ Rs : Finset kˣ, V.IsSigns Rs → ∀ a b : kˣ, valuation k (a : k) < valuation k (b : k) →
      orb ι ((Uo k).comap (p / q)) (MonoidHom.id _) (V.ZJ 2) (V.fK ω ω' Rs t) (g₀ * dg ![a, b] * g₀⁻¹) = V.val ω t (a / b) * (((ω' b)⁻¹ : ℂˣ) : ℂ)

end UpperTheory.V.Z.Sym.Sig

end
