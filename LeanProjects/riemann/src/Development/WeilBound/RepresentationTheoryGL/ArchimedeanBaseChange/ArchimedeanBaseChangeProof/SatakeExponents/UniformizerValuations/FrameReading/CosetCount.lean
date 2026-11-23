import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsIrreducibleIff
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IwahoriDoubleCosets
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.GenericPrincipalSeries.GenericPrincipalSeries

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.CuspRep ValuativeRel GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open scoped TensorProduct

namespace PositivityTheory.Rg.BcB.F.Tail.PExp

def hkS {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G)
    (f : G → ℂ) (v : V) : V :=
  ∑ᶠ q : G ⧸ K, f q.out • ρ q.out v

def hkE {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G)
    (f : G → ℂ) : Module.End ℂ V :=
  ∑ᶠ q : G ⧸ K, f q.out • ρ q.out

def HkEFin : Prop :=
  ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G) (f : G → ℂ),
    {q : G ⧸ K | f q.out ≠ 0}.Finite → ∀ v, hkE ρ K f v = hkS ρ K f v

def TensHk : Prop :=
  ∀ (G H V W : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ H W) (K : Subgroup G) (L : Subgroup H) (f : G → ℂ)
    (e : H → ℂ), (∀ g, ∀ k ∈ K, f (g * k) = f g) → (∀ h, ∀ l ∈ L, e (h * l) = e h) →
    {q : G ⧸ K | f q.out ≠ 0}.Finite → {q : H ⧸ L | e q.out ≠ 0}.Finite →
    ∀ v ∈ fixed (extTensor ρ σ) (K.prod L),
      hkS (extTensor ρ σ) (K.prod L) (fun m => f m.1 * e m.2) v = TensorProduct.map (hkE ρ K f) (hkE σ L e) v

def TensEig : Prop :=
  ∀ (V W X Y : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (A : X → Module.End ℂ V)
    (B : Y → Module.End ℂ W) (lam : X → ℂ) (mu : Y → ℂ) (v : V ⊗[ℂ] W), v ≠ 0 → Nonempty Y →
    (∀ x, lam x ≠ 0) → (∀ y, mu y ≠ 0) → (∀ x y, TensorProduct.map (A x) (B y) v = (lam x * mu y) • v) →
    ∃ (l : Module.Dual ℂ W) (c : ℂ), c ≠ 0 ∧ TensorProduct.rid ℂ V (LinearMap.lTensor V l v) ≠ 0 ∧
      ∀ x, A x (TensorProduct.rid ℂ V (LinearMap.lTensor V l v)) =
        (c * lam x) • TensorProduct.rid ℂ V (LinearMap.lTensor V l v)

def TensEigR : Prop :=
  ∀ (V W X Y : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (A : X → Module.End ℂ V)
    (B : Y → Module.End ℂ W) (lam : X → ℂ) (mu : Y → ℂ) (v : V ⊗[ℂ] W), v ≠ 0 → Nonempty X →
    (∀ x, lam x ≠ 0) → (∀ y, mu y ≠ 0) → (∀ x y, TensorProduct.map (A x) (B y) v = (lam x * mu y) • v) →
    ∃ (l : Module.Dual ℂ V) (c : ℂ), c ≠ 0 ∧ TensorProduct.lid ℂ W (LinearMap.rTensor W l v) ≠ 0 ∧
      ∀ y, B y (TensorProduct.lid ℂ W (LinearMap.rTensor W l v)) =
        (c * mu y) • TensorProduct.lid ℂ W (LinearMap.rTensor W l v)

def ContrFix : Prop :=
  ∀ (G H V W : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ H W) (K : Subgroup G) (L : Subgroup H),
    ∀ v ∈ fixed (extTensor ρ σ) (K.prod L),
      (∀ l : Module.Dual ℂ W, TensorProduct.rid ℂ V (LinearMap.lTensor V l v) ∈ fixed ρ K) ∧
      ∀ l : Module.Dual ℂ V, TensorProduct.lid ℂ W (LinearMap.rTensor W l v) ∈ fixed σ L

def SubEig : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V), IsSmooth ρ → ∀ (K : Subgroup G) (X : Type) (f : X → G → ℂ) (e : X → ℂ),
    (∀ x, {q : G ⧸ K | f x q.out ≠ 0}.Finite) → ∀ u ∈ fixed ρ K, u ≠ 0 → (∀ x, hkS ρ K (f x) u = e x • u) →
    ∃ P : SmIrr G, IsSubquotient P.ρ ρ ∧ ∃ u' ∈ fixed P.ρ K, u' ≠ 0 ∧ ∀ x, hkS P.ρ K (f x) u' = e x • u'

def CosetCount : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (t : Fin n → kˣ), Contracts t →
    {q : GL (Fin n) k ⧸ iwahori k (Fin n) | cosetInd t q.out ≠ 0}.Finite ∧
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
      ∀ v ∈ fixed π (iwahori k (Fin n)),
        (Submodule.Quotient.mk (hkS π (iwahori k (Fin n)) (cosetInd t) v) : Jacquet π (unipB k (Fin n))) =
          (((deltaB t)⁻¹ : ℝ) : ℂ) • jacBU π t (Submodule.Quotient.mk v)

def TorusExp : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (ϖ : kˣ),
    valuation k (ϖ : k) = uniformizer k → ∀ (ξ : Fin n → ℂˣ) (c : ℂ) (y : Jacquet π (unipB k (Fin n))), y ≠ 0 →
    y ∈ fixed (jacBU π) (torusO k (Fin n)) →
    (∀ x : Fin n → ℤ, StrictAnti x → jacBU π (fun i => ϖ ^ x i) y =
      (c * (∏ i, ((ξ i ^ x i : ℂˣ) : ℂ)) *
        (deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) fun i => ϖ ^ x i) : ℂ)) • y) →
    ∀ t : Fin n → kˣ, jacB π t y = (torusChar (fun i => unrChar k (ξ i)) t : ℂ) • y

def StdBridge : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (hd : ∑ _a : Fin n, 1 = n) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
    (χ : Fin n → kˣ →* ℂˣ) (y : Jacquet π (unipB k (Fin n))), y ≠ 0 →
    (∀ t, jacB π t y = (torusChar χ t : ℂ) • y) →
    ∃ v : Jacquet π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd)), v ≠ 0 ∧
      ∀ t : Levi k (fun _ : Fin n => Fin 1),
        v ∈ Module.End.maxGenEigenspace (jac (stdBlocks (fun _ : Fin n => 1) hd) π t) (PositivityTheory.Lbc.torusChar χ t)

end PositivityTheory.Rg.BcB.F.Tail.PExp

end
