import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.IsAlgClosureField

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.Ws

def RedTo {l : ℕ} [Fact l.Prime] (c : Coef l) {Γ : Type} [Group Γ] {n : ℕ} (ρ : Γ →* GL (Fin n) (PadicAlgCl l))
    (χ : Fin n → Γ →* (ResidueField c.O)ˣ) : Prop :=
  ∀ y : MonoidAlgebra c.O Γ, ∀ z ∈ (MonoidAlgebra.lift c.O (Matrix (Fin n) (Fin n) (PadicAlgCl l)) Γ (W.mat ρ) y).charpoly.roots,
    ∃ (i : Fin n) (a : c.O), residue c.O a = MonoidAlgebra.lift c.O (ResidueField c.O) Γ ((Units.coeHom _).comp (χ i)) y ∧
      ‖z - (a : PadicAlgCl l)‖ < 1

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}
  {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h)

def Link.kapQ : G T.L Ω →* (PadicAlgCl l)ˣ := W.pushCh (algebraMap c'.O (PadicAlgCl l)) K.κ

variable {K} in

def Link.pt {X : Space (T.fr ∅) (inc h)} {B : W.UniversalOrdinaryDeterminantRing K.r} (φ : B.B →ₐ[c'.O] X.B) (y : X.A →ₐ[c'.O] PadicAlgCl l) : B.Pt :=
  (y.comp (IsScalarTower.toAlgHom c'.O X.B X.A)).comp φ

theorem Link.pt_apply {X : Space (T.fr ∅) (inc h)} {B : W.UniversalOrdinaryDeterminantRing K.r} (φ : B.B →ₐ[c'.O] X.B) (y : X.A →ₐ[c'.O] PadicAlgCl l)
    (b : B.B) : Link.pt φ y b = y (algebraMap X.B X.A (φ b)) := rfl

theorem Link.le_ker_pt {X : Space (T.fr ∅) (inc h)} {B : W.UniversalOrdinaryDeterminantRing K.r} (φ : B.B →ₐ[c'.O] X.B) (y : X.A →ₐ[c'.O] PadicAlgCl l)
    (J₀ : Ideal B.B) (hy : ∀ b ∈ J₀.map φ, y (algebraMap X.B X.A b) = 0) : J₀ ≤ RingHom.ker (Link.pt φ y) := by
  intro b hb
  rw [RingHom.mem_ker]
  change Link.pt φ y b = 0
  rw [Link.pt_apply]
  exact hy (φ b) (Ideal.mem_map_of_mem _ hb)

end UpperTheory.V.Ws

end
