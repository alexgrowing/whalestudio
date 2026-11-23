import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsG
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic
import ReciprocityTheory.ClassFieldTheory.LocalClassField.FinCoh

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Euler

open _root_.Neutral.B1

noncomputable section

section Q

variable {R : Type} [CommRing R] {G : Type} [Group G] [TopologicalSpace G]
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M]

def qEd (p d : ℕ) (rho : Representation R G M) : ℚ :=
  ((Nat.card (H0 rho) : ℚ) * (Nat.card (H2 rho) : ℚ) * (p : ℚ) ^ (d * padicValNat p (Nat.card M))) /
    (Nat.card (H1 rho) : ℚ)

def SimpleRep (rho : Representation R G M) : Prop :=
  Nontrivial M ∧ ∀ S : Submodule R M, (∀ g, ∀ m ∈ S, rho g m ∈ S) → S = ⊥ ∨ S = ⊤

def fnRep (rho : Representation R G M) (U : Subgroup G) : Representation R G (G ⧸ U → M) where
  toFun g :=
    { toFun := fun F x => rho g (F (g⁻¹ • x))
      map_add' := fun F F' => funext fun x => map_add (rho g) _ _
      map_smul' := fun c F => funext fun x => map_smul (rho g) _ _ }
  map_one' := LinearMap.ext fun F => funext fun x => by
    show rho 1 (F ((1 : G)⁻¹ • x)) = F x
    rw [inv_one, one_smul, map_one]; rfl
  map_mul' g h := LinearMap.ext fun F => funext fun x => by
    show rho (g * h) (F ((g * h)⁻¹ • x)) = rho g (rho h (F (h⁻¹ • g⁻¹ • x)))
    rw [mul_inv_rev, mul_smul, map_mul]; rfl

def intRep (rho : Representation R G M) : Representation ℤ G M where
  toFun g := (rho g).toAddMonoidHom.toIntLinearMap
  map_one' := LinearMap.ext fun m => by
    show rho 1 m = m
    rw [map_one]; rfl
  map_mul' g h := LinearMap.ext fun m => by
    show rho (g * h) m = rho g (rho h m)
    rw [map_mul]; rfl

end Q

def qE (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) {R : Type} [CommRing R]
    {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul R M] (rho : Representation R (GK p K) M) : ℚ :=
  qEd p (Module.finrank ℚ_[p] K) rho

section ZG

variable (G : Type) [Group G]

abbrev ZG : Type := MonoidAlgebra ℤ G

variable {G} (l : ℕ) (D A : Type) [AddCommGroup D] [Module (ZG G) D] [AddCommGroup A] [Module (ZG G) A]

def mulL : A →ₗ[ZG G] A := l • LinearMap.id

abbrev modL : Type := A ⧸ LinearMap.range (mulL (G := G) l A)

abbrev torL : Submodule (ZG G) A := LinearMap.ker (mulL (G := G) l A)

def eps : ℚ := (Nat.card (D →ₗ[ZG G] modL (G := G) l A) : ℚ) / (Nat.card (D →ₗ[ZG G] torL (G := G) l A) : ℚ)

variable (G) in

def fixG : Type := {d : D // ∀ g : G, MonoidAlgebra.of ℤ G g • d = d}

end ZG

section Hom

variable (N : Type) [Group N] [TopologicalSpace N] (M : Type) [AddCommGroup M] [TopologicalSpace M]
  [IsTopologicalAddGroup M]

def homSub : AddSubgroup (N → M) where
  carrier := {f | Continuous f ∧ ∀ a b, f (a * b) = f a + f b}
  zero_mem' := ⟨continuous_const, fun _ _ => (add_zero (0 : M)).symm⟩
  add_mem' := fun {f f'} hf hf' => ⟨hf.1.add hf'.1, fun a b => by
    show f (a * b) + f' (a * b) = f a + f' a + (f b + f' b)
    rw [hf.2, hf'.2]; abel⟩
  neg_mem' := fun {f} hf => ⟨hf.1.neg, fun a b => by
    show - f (a * b) = - f a + - f b
    rw [hf.2]; abel⟩

end Hom

def conjN {G : Type} [Group G] (N : Subgroup G) [hN : N.Normal] (s : G) (g : N) : N :=
  ⟨s⁻¹ * g * s, by simpa using hN.conj_mem g.1 g.2 s⁻¹⟩

section OL

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

def OLadd : AddSubgroup (PadicAlgCl p) where
  carrier := {x | x ∈ L ∧ ‖x‖ ≤ 1}
  zero_mem' := ⟨L.zero_mem, by simp⟩
  add_mem' := fun {x y} hx hy => ⟨L.add_mem hx.1 hy.1,
    (PadicAlgCl.isNonarchimedean p x y).trans (max_le hx.2 hy.2)⟩
  neg_mem' := fun {x} hx => ⟨L.neg_mem hx.1, by rw [norm_neg]; exact hx.2⟩

variable {p K L}

def integerRingGaloisAction (hKL : K ≤ L) [hN : (subG p K L).Normal] : Representation ℤ (GK p K) (OLadd p L) where
  toFun σ := AddMonoidHom.toIntLinearMap
    { toFun := fun x => ⟨σ x.1, (subG_normal_iff hKL).1 hN σ x.1 x.2.1, by rw [norm_map_GK]; exact x.2.2⟩
      map_zero' := Subtype.ext (map_zero σ)
      map_add' := fun x y => Subtype.ext (map_add σ x.1 y.1) }
  map_one' := rfl
  map_mul' _ _ := rfl

def OLrep (hKL : K ≤ L) [(subG p K L).Normal] : Representation ℤ (GalLK p K L) (OLadd p L) :=
  QuotientGroup.lift (subG p K L) (integerRingGaloisAction hKL) fun _ hσ =>
    LinearMap.ext fun x => Subtype.ext (hσ x.1 x.2.1)

end OL

end

end ReciprocityTheory.DiscreteGroups.LocalClassField.Euler
