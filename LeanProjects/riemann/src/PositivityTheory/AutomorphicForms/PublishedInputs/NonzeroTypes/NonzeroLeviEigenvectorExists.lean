import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.CIface
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.GIface
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.TensorProductVectors
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsUnif (ϖ : kˣ) : Prop := ∃ w : 𝒪[k], Irreducible w ∧ algebraMap 𝒪[k] k w = ϖ

namespace Grp

variable {n : ℕ} (G : Grp k n)

def Nbar : Set (GL (Fin n) k) :=
  {g | ∀ i j, (G.bl i < G.bl j → (g : Matrix (Fin n) (Fin n) k) i j = 0) ∧
    (G.bl i = G.bl j → (g : Matrix (Fin n) (Fin n) k) i j = if i = j then 1 else 0)}

def NO : Subgroup (GL (Fin n) k) := unipRad k G.e ⊓ KO k (Fin n)

def zEl (ϖ : kˣ) : GL (Fin n) k :=
  leviEmb k G.e fun a => Units.map (Matrix.scalar (Fin (G.d a)) : k →+* Matrix (Fin (G.d a)) (Fin (G.d a)) k).toMonoidHom
    (ϖ ^ (G.s - 1 - (a : ℕ)))

def zN (ϖ : kˣ) (m : ℕ) : Subgroup ↥G.NO := (G.NO.map (MulAut.conj (G.zEl ϖ ^ m)).toMonoidHom).subgroupOf G.NO

def Eig {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) : Set V :=
  {x | ∀ g ∈ G.JSet, π g x = G.lam g • x}

def Tz {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (ϖ : kˣ) (m : ℕ) (x : V) : V :=
  ∑ᶠ c : ↥G.NO ⧸ G.zN ϖ m, π ((Quotient.out c : ↥G.NO) : GL (Fin n) k) (π (G.zEl ϖ ^ m) x)

def PJ {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (r : ℕ) (v : V) : V :=
  ∑ᶠ c : ↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg,
    (G.lam ((Quotient.out c : ↥G.Jg) : GL (Fin n) k))⁻¹ • π ((Quotient.out c : ↥G.Jg) : GL (Fin n) k) v

def eta (m : Levi k fun a : Fin G.s => Fin (G.d a)) : ℂ := ∏ a, ((G.μ a (GeneralLinearGroup.det (m a)) : ℂˣ) : ℂ)

def CompactConductorBasicProp : Prop :=
  ∀ (s : ℕ) (μ : Fin s → kˣ →* ℂˣ),
    (∀ a b : Fin s, ∃ c : ℕ, ∀ u : 𝒪[k]ˣ, (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c → res (μ a / μ b) u = 1) →
    ∀ a b c : Fin s, cc μ a a = 0 ∧ cc μ a b = cc μ b a ∧ cc μ a c ≤ max (cc μ a b) (cc μ b c)

def CompactConductorBoundProp : Prop :=
  (∀ a b : Fin G.s, a ≠ b → 1 ≤ cc G.μ a b) ∧ (∀ a b : Fin G.s, cc G.μ a b < G.lev) ∧
    (∀ a : Fin G.s, cond (res (G.μ a)) < G.lev) ∧
    ∀ a b : Fin G.s, ∀ u : 𝒪[k]ˣ, (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ cc G.μ a b →
      res (G.μ a / G.μ b) u = 1

def JacquetOneProp : Prop := (1 : GL (Fin n) k) ∈ G.JSet ∧ G.PO ⊆ G.JSet

def JacquetMultiplicativeProp : Prop := CompactConductorBasicProp (k := k) → CompactConductorBoundProp G → ∀ g ∈ G.JSet, ∀ h ∈ G.JSet, g * h ∈ G.JSet

def JacquetInverseProp : Prop := CompactConductorBasicProp (k := k) → CompactConductorBoundProp G → ∀ g ∈ G.JSet, g⁻¹ ∈ G.JSet

def CompactOpenKernelProp : Prop :=
  CompactConductorBoundProp G → ∀ r : ℕ, ((KCg k n r : Set (GL (Fin n) k)) = KC k n r) ∧
    (∀ g ∈ KO k (Fin n), ∀ u ∈ KC k n r, g * u * g⁻¹ ∈ KC k n r) ∧ IsOpen (KC k n r) ∧ KC k n r ⊆ (KO k (Fin n) : Set _) ∧
    (G.lev ≤ r → KC k n r ⊆ G.JSet)

def ModulusOnUnitsProp : Prop := CompactConductorBoundProp G → ∀ g ∈ G.JSet, ∀ a, ∃ u : 𝒪[k]ˣ, G.Δ a g = algebraMap 𝒪[k] k u

def ModulusMultiplicativeProp : Prop :=
  CompactConductorBasicProp (k := k) → CompactConductorBoundProp G → ∀ g ∈ G.JSet, ∀ h ∈ G.JSet, ∀ (a : Fin G.s) (h1 : (a : ℕ) + 1 < G.s),
    ∃ u : 𝒪[k]ˣ, (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ cc G.μ a ⟨a + 1, h1⟩ ∧
      G.Δ a (g * h) = G.Δ a g * G.Δ a h * algebraMap 𝒪[k] k u

def LambdaMultiplicativeProp : Prop :=
  CompactConductorBasicProp (k := k) → ModulusOnUnitsProp G → ModulusMultiplicativeProp G → CompactConductorBoundProp G → ∀ g ∈ G.JSet, ∀ h ∈ G.JSet, G.lam (g * h) = G.lam g * G.lam h

def LambdaBasicProp : Prop :=
  CompactConductorBoundProp G → G.lam 1 = 1 ∧ (∀ g, G.lam g ≠ 0) ∧ ∀ g ∈ KC k n G.lev, G.lam g = 1

def LambdaUnipotentProp : Prop :=
  (∀ u ∈ G.NO, (u : GL (Fin n) k) ∈ G.JSet ∧ G.lam u = 1) ∧ ∀ u ∈ G.Nbar, u ∈ G.JSet → G.lam u = 1

def IwahoriDecompositionProp : Prop :=
  CompactConductorBasicProp (k := k) → CompactConductorBoundProp G → ModulusOnUnitsProp G → JacquetMultiplicativeProp G → JacquetInverseProp G → ∀ g ∈ G.JSet, ∃ v ∈ G.Nbar, v ∈ G.JSet ∧
    ∃ m : Levi k (fun a : Fin G.s => Fin (G.d a)), m ∈ leviK k (m := fun a : Fin G.s => Fin (G.d a)) ∧
      ∃ u ∈ G.NO, g = v * leviEmb k G.e m * u

def FixedSubspaceStableProp : Prop :=
  CompactConductorBoundProp G → CompactOpenKernelProp G → ∀ g : ↥(KO k (Fin n)), ∀ φ ∈ G.V0sp, Rreg (k := k) (n := n) g φ ∈ G.V0sp

def FixedSubspaceFiniteProp : Prop := CompactConductorBoundProp G → CompactOpenKernelProp G → FiniteDimensional ℂ G.V0sp

def NonzeroLeviEigenvectorExists : Prop :=
  CompactConductorBasicProp (k := k) → CompactConductorBoundProp G → ModulusOnUnitsProp G → ModulusMultiplicativeProp G →
  JacquetOneProp G → JacquetMultiplicativeProp G → JacquetInverseProp G → LambdaMultiplicativeProp G → LambdaBasicProp G → CompactOpenKernelProp G →
    G.v0 ∈ G.V0sp ∧ G.v0 ≠ 0 ∧ ∀ j : ↥(KO k (Fin n)), (j : GL (Fin n) k) ∈ G.JSet → Rreg (k := k) (n := n) j G.v0 = G.lam j • G.v0

def ParabolicJacquetProp : Prop :=
  CompactConductorBasicProp (k := k) → CompactConductorBoundProp G → ModulusOnUnitsProp G → ModulusMultiplicativeProp G →
  JacquetOneProp G → JacquetMultiplicativeProp G → JacquetInverseProp G → LambdaMultiplicativeProp G → LambdaBasicProp G → CompactOpenKernelProp G →
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (r : ℕ), G.lev ≤ r →
    Finite (↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) ∧
    ∀ v : V, (∀ u ∈ KC k n r, π u v = v) →
      G.PJ π r v ∈ G.Eig π ∧ (∀ j ∈ G.JSet, G.PJ π r (π j v) = G.lam j • G.PJ π r v) ∧
      (v ∈ G.Eig π → G.PJ π r v = (Nat.card (↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) : ℂ) • v)

def AnnihilationProp : Prop :=
  CompactConductorBasicProp (k := k) → CompactConductorBoundProp G → ModulusOnUnitsProp G → ModulusMultiplicativeProp G →
  JacquetOneProp G → JacquetMultiplicativeProp G → JacquetInverseProp G → LambdaMultiplicativeProp G → LambdaBasicProp G → CompactOpenKernelProp G →
  ParabolicJacquetProp G → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (r : ℕ), G.lev ≤ r →
    ∀ x ∈ G.Eig π, ∀ y : GL (Fin n) k, (∀ u ∈ KC k n r, π u (π y x) = π y x) →
      (∃ j ∈ G.JSet, y⁻¹ * j * y ∈ G.JSet ∧ G.lam (y⁻¹ * j * y) ≠ G.lam j) → G.PJ π r (π y x) = 0

def NonIntegralProp : Prop :=
  CompactConductorBasicProp (k := k) → CompactConductorBoundProp G → ∀ y ∈ unipRad k G.e, y ∉ KO k (Fin n) →
    ∃ j ∈ G.JSet, y⁻¹ * j * y ∈ G.JSet ∧ G.lam (y⁻¹ * j * y) ≠ G.lam j

def TorusCentreEigenProp : Prop :=
  CompactConductorBasicProp (k := k) → CompactConductorBoundProp G → ModulusOnUnitsProp G → ModulusMultiplicativeProp G →
  JacquetMultiplicativeProp G → JacquetInverseProp G → LambdaMultiplicativeProp G → LambdaUnipotentProp G → IwahoriDecompositionProp G →
  ∀ (ϖ : kˣ), IsUnif ϖ → ∀ m : ℕ, Finite (↥G.NO ⧸ G.zN ϖ m) ∧
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
      ∀ x ∈ G.Eig π, G.Tz π ϖ m x ∈ G.Eig π

def TorusPowerProp : Prop :=
  CompactConductorBasicProp (k := k) → CompactConductorBoundProp G → ModulusOnUnitsProp G → ModulusMultiplicativeProp G →
  JacquetMultiplicativeProp G → JacquetInverseProp G → LambdaMultiplicativeProp G → LambdaUnipotentProp G → IwahoriDecompositionProp G → TorusCentreEigenProp G → ∀ (ϖ : kˣ), IsUnif ϖ → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
    ∀ x ∈ G.Eig π, ∀ m : ℕ, G.Tz π ϖ m x = (G.Tz π ϖ 1)^[m] x

def JacquetKernelProp : Prop :=
  CompactConductorBasicProp (k := k) → CompactConductorBoundProp G → ModulusOnUnitsProp G → ModulusMultiplicativeProp G →
  JacquetMultiplicativeProp G → JacquetInverseProp G → LambdaMultiplicativeProp G → IwahoriDecompositionProp G → TorusCentreEigenProp G → LambdaUnipotentProp G → ∀ (ϖ : kˣ), IsUnif ϖ → ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → ∀ x ∈ G.Eig π,
      (Submodule.Quotient.mk x : Jacquet π (unipRad k G.e)) = 0 → ∃ m : ℕ, G.Tz π ϖ m x = 0

def TorusCentreInjectiveProp : Prop :=
  CompactConductorBasicProp (k := k) → CompactConductorBoundProp G → ModulusOnUnitsProp G → ModulusMultiplicativeProp G →
  JacquetOneProp G → JacquetMultiplicativeProp G → JacquetInverseProp G → LambdaMultiplicativeProp G → LambdaBasicProp G → LambdaUnipotentProp G →
  IwahoriDecompositionProp G → ParabolicJacquetProp G → AnnihilationProp G → NonIntegralProp G → TorusCentreEigenProp G → CompactOpenKernelProp G → ∀ (ϖ : kˣ), IsUnif ϖ →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π →
      ∀ x ∈ G.Eig π, G.Tz π ϖ 1 x = 0 → x = 0

def JacquetImageProp : Prop :=
  LeviSubgroupRestriction → JacquetOneProp G → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
    ∀ x ∈ G.Eig π, ∀ m ∈ leviK k (m := fun a : Fin G.s => Fin (G.d a)),
      jacU G.e π m (Submodule.Quotient.mk x : Jacquet π (unipRad k G.e)) = G.eta m • Submodule.Quotient.mk x

def UniformizerProp : Prop := ∃ ϖ : kˣ, IsUnif ϖ

def JacquetProductProp : Prop :=
  GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
    IsSmooth π → π.IsIrreducible →
    (∃ y : Jacquet π (unipRad k G.e), y ≠ 0 ∧ ∀ m ∈ leviK k (m := fun a : Fin G.s => Fin (G.d a)), jacU G.e π m y = G.eta m • y) →
    IsTwSphProd π G.d G.hd G.μ

def CMainFor : Prop :=
  GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
    IsSmooth π → π.IsIrreducible → (∃ x : V, x ≠ 0 ∧ x ∈ G.Eig π) → IsTwSphProd π G.d G.hd G.μ

end Grp

end UpperTheory.TNZ
