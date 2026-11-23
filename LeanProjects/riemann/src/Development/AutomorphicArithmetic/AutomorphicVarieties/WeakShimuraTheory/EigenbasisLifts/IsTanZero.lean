import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.IsAlgClosureField
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems

noncomputable section

open Matrix

namespace UpperTheory.V.Ws.Eb

abbrev dF (K : Type) [CommRing K] : DualNumber K →+* K := (TrivSqZeroExt.fstHom K K K : DualNumber K →+* K)

section

variable {H K : Type} [Group H] [CommRing K] {n : ℕ}

def Full (ρ : H →* GL (Fin n) K) : Prop := Submodule.span K (Set.range (W.mat ρ)) = ⊤

def IsTan (ρ : H →* GL (Fin n) K) (y : H → Matrix (Fin n) (Fin n) K) (ρ' : H →* GL (Fin n) (DualNumber K)) : Prop :=
  ∀ g i j, (ρ' g : Matrix (Fin n) (Fin n) (DualNumber K)) i j =
    ⟨(ρ g : Matrix (Fin n) (Fin n) K) i j, (y g * (ρ g : Matrix (Fin n) (Fin n) K)) i j⟩

theorem IsTan.comp {ρ : H →* GL (Fin n) K} {y : H → Matrix (Fin n) (Fin n) K} {ρ' : H →* GL (Fin n) (DualNumber K)}
    (h : IsTan ρ y ρ') {H' : Type} [Group H'] (φ : H' →* H) : IsTan (ρ.comp φ) (fun g => y (φ g)) (ρ'.comp φ) :=
  fun g => h (φ g)

theorem isTan_zero (ρ : H →* GL (Fin n) K) : IsTan ρ 0 (W.pushRep (algebraMap K (DualNumber K)) ρ) := fun g i j =>
  TrivSqZeroExt.ext rfl (by simp; rfl)

end

structure IsAdExt {l : ℕ} [Fact l.Prime] (F : W.GFrame l) {K : Type} [CommRing K] {n : ℕ} (ρ : F.G₀ →* GL (Fin n) K)
    (P : GL (Fin n) K) (R : Representation K F.Γ (Matrix (Fin n) (Fin n) K)) : Prop where
  ad : ∀ (g : F.G₀) X, R g X = Loc.adGL ρ g X
  c : ∀ X, R F.c X = -((P⁻¹ : GL (Fin n) K) * Xᵀ * (P : Matrix (Fin n) (Fin n) K))

end UpperTheory.V.Ws.Eb

end
