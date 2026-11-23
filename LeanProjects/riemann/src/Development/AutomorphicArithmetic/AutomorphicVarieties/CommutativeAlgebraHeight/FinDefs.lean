import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom

noncomputable section

open IsLocalRing TensorProduct Polynomial UpperTheory.V.W UpperTheory.V.Alg

namespace UpperTheory.V.CA

def Z1 {G k : Type} [Group G] [TopologicalSpace G] [Field k] (χ ψ : G →* kˣ) : Submodule k (G → k) where
  carrier := {a | IsLocallyConstant a ∧ ∀ g h, a (g * h) = χ g * a h + a g * ψ h}
  add_mem' {a b} ha hb := ⟨ha.1.add hb.1, fun g h => by simp only [Pi.add_apply, ha.2, hb.2]; ring⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, fun g h => by simp⟩
  smul_mem' c a ha := ⟨ha.1.comp fun x => c * x, fun g h => by simp only [Pi.smul_apply, smul_eq_mul, ha.2]; ring⟩

structure MultFree {n : ℕ} {G k : Type} [Group G] [TopologicalSpace G] [Field k] (χ : Fin n → G →* kˣ) (h : ℕ) :
    Prop where
  isOpen : ∀ i, IsOpen ((χ i).ker : Set G)
  inj : Function.Injective χ
  fin : ∀ i j, i ≠ j → Module.Finite k (Z1 (χ i) (χ j)) ∧ Module.finrank k (Z1 (χ i) (χ j)) ≤ h

def finBound (n h : ℕ) : ℕ := n + ∑ p ∈ Finset.range n, (n ^ 2 * h) ^ p

structure IsGMA {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (e : Fin n → E) : Prop where
  ch : D.IsCH
  idem : CompleteOrthogonalIdempotents e
  rank : ∀ i, D.D A[X] (1 + X ⊗ₜ e i) = 1 + X

structure IsDef (O : Type) [CommRing O] [IsLocalRing O] {n : ℕ} {G : Type} [Group G] [TopologicalSpace G]
    (Dbar : GDet n (ResidueField O) G) {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (D : GDet n R G) : Prop where
  cont : D.IsCont (maximalIdeal R)
  red : D.map (res O R : R →+* ResidueField O) = Dbar

structure IsUnivDet (O : Type) [CommRing O] [IsLocalRing O] {n : ℕ} {G : Type} [Group G] [TopologicalSpace G]
    (Dbar : GDet n (ResidueField O) G) {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (D : GDet n R G) : Prop where
  isDef : IsDef O Dbar D
  univ : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (D' : GDet n R' G), IsDef O Dbar D' →
    ∃! f : R →ₐ[O] R', D.map (f : R →+* R') = D'

end UpperTheory.V.CA
