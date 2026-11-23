import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.PeriodIntegrals.ScRefExists

noncomputable section

open NumberField Formalism.MainNotions.S PI.ScRefExists
open scoped TensorProduct
open Matrix

namespace PI.ScXuExists

def OneOff (I : Formalism.MainNotions.S.AutInst) (g : ℕ) (x : I.Gf) : Prop :=
  ∀ m : ℕ, Nat.Coprime m g → ∀ y ∈ I.Lf, InAt I m m ((I.fmat x - 1) *ᵥ y)

def Target : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (g r k : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
    (Rf : RefData I g r k e f), 1 ≤ g →
    (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 I.F), (g : 𝓞 I.F) ∈ v.asIdeal →
      Nat.card {w : IsDedekindDomain.HeightOneSpectrum (𝓞 I.E) //
        w.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) = v.asIdeal} = 2) →
    I.n = 2 * r + k + 1 →
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (e b) = 0) →
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (f a) (f b) = 0) →
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (f b) = if a = b then 1 else 0) →
    (∀ a, Formalism.UG.hform (starRingEnd I.E) I.J (e a) z = 0 ∧ Formalism.UG.hform (starRingEnd I.E) I.J (f a) z = 0) →
    (∃ t : ℕ, t ≡ 1 [MOD g] ∧ Formalism.UG.hform (starRingEnd I.E) I.J z z = -(t : I.E)) →
    (∀ a, InAt I g 1 (incl I (e a)) ∧ InAt I g 1 (incl I (f a))) →
    InAt I g 1 (incl I z) →
    ∃ x : I.Gf, (∀ a, I.fmat x *ᵥ incl I (e a) = incl I (e a) ∧ I.fmat x *ᵥ incl I (f a) = incl I (f a)) ∧
      InAt I g g (I.fmat x⁻¹ *ᵥ incl I z - Rf.z0) ∧ OneOff I g x ∧ x ∈ I.Kset

end PI.ScXuExists
