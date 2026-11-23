import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.LevelGatherings
import Formalism.LocalRingCardinality.DataKerI

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.UG Formalism.MainNotions.G Formalism.FrobeniusOrbits
open scoped TensorProduct

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem emb_mul {R : Ranks} (H : Host R) (g g' : R.GG) (x : H.E) : H.emb (g * g') x = H.emb g (H.sigmaOf g' x) := by
  show H.φ₀ ((H.sigmaOf (g * g')) x) = H.φ₀ ((H.sigmaOf g) ((H.sigmaOf g') x))
  simp only [Formalism.BasicNotions.Host.sigmaOf, map_mul, AlgEquiv.mul_apply]

theorem sigmaOf_pow {R : Ranks} (H : Host R) (g : R.GG) (s : ℕ) (x : H.E) :
    H.sigmaOf (g ^ s) x = ((H.sigmaOf g) ^ s) x := by
  simp only [Formalism.BasicNotions.Host.sigmaOf, map_pow]

variable {p : ℕ} [Fact p.Prime] {W Qq Kf : Type} [CommRing W] [Field Qq] [Algebra W Qq] [Field Kf]

def PosCompat {R : Ranks} (H : Host R) (h : R.MA) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq)
    (iw : Fin (nOrb (zPsi R.toFrame h)) → (H.E →+* Qq)) (iK : Kf →+* ℂ_[p]) (lam : (algebraicClosure ℚ ℂ) →+* ℂ_[p]) : Prop :=
  ∀ (v : Fin (nOrb (zPsi R.toFrame h))) (s : Fin (orderOf (zPsi R.toFrame h))) (x : H.E),
    iK (ι ((σ ^ s.val) (iw v x))) =
      lamV lam (H.emb (((posG (zPsi R.toFrame h) ⟨v, s⟩ : R.Psi) : R.GG) * R.cc ^ s.val) x)

theorem posCompat_of_base {R : Ranks} (H : Host R) (h : R.MA) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq)
    (iw : Fin (nOrb (zPsi R.toFrame h)) → (H.E →+* Qq)) (iK : Kf →+* ℂ_[p]) (lam : (algebraicClosure ℚ ℂ) →+* ℂ_[p])
    (hbase : ∀ v x, iK (ι (iw v x)) = lamV lam (H.emb ((orbRep (zPsi R.toFrame h) v : R.Psi) : R.GG) x))
    (hfrob : ∀ v x, σ (iw v x) = iw v (H.sigmaOf ((c0, h) : R.GG) x)) :
    PosCompat H h ι σ iw iK lam := by
  intro v s x
  have key : ∀ (k : ℕ) (y : H.E), (σ ^ k) (iw v y) = iw v ((H.sigmaOf ((c0, h) : R.GG) ^ k) y) := by
    intro k
    induction k with
    | zero => intro y; rfl
    | succ k ih =>
      intro y
      rw [pow_succ, pow_succ]
      show (σ ^ k) (σ (iw v y)) = iw v ((H.sigmaOf ((c0, h) : R.GG) ^ k) (H.sigmaOf ((c0, h) : R.GG) y))
      rw [hfrob, ih]
  have e1 : ((posG (zPsi R.toFrame h) ⟨v, s⟩ : R.Psi) : R.GG) * R.cc ^ s.val =
      ((orbRep (zPsi R.toFrame h) v : R.Psi) : R.GG) * ((c0, h) : R.GG) ^ s.val := by
    rw [posG_apply, Subgroup.coe_mul, Subgroup.coe_pow, mul_assoc]
    congr 1
    show ((1, h) : R.GG) ^ s.val * (c0, 1) ^ s.val = ((c0, h) : R.GG) ^ s.val
    ext <;> simp
  rw [e1, emb_mul, sigmaOf_pow, key, hbase]

end Formalism.L2.G
