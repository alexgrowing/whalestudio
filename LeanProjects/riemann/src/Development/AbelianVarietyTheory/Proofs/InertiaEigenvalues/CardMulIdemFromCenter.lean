import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceMemAdjoin
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.CentralIdem

theorem exists_central_lift {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) {Γ : Type} [Group Γ] [Finite Γ] (x : MonoidAlgebra B Γ)
    (hx : ∀ z, x * z = z * x) (hr : ∀ h, x.coeff h ∈ f.range) :
    ∃ z ∈ Subalgebra.center A (MonoidAlgebra A Γ), ∀ h : Γ, f (z.coeff h) = x.coeff h := by
  choose c hc using hr
  let z : MonoidAlgebra A Γ := MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm c)
  have hz : ∀ h, f (z.coeff h) = x.coeff h := fun h => hc h
  have hco : ∀ (y : MonoidAlgebra A Γ) h, (MonoidAlgebra.mapRingHom Γ f y).coeff h = f (y.coeff h) := by
    intro y h; simp
  have hinj : Function.Injective (MonoidAlgebra.mapRingHom Γ f) := by
    intro a b hab
    ext h
    apply hf
    rw [← hco, ← hco, hab]
  have hzx : MonoidAlgebra.mapRingHom Γ f z = x := by
    ext h
    rw [hco, hz]
  refine ⟨z, ?_, hz⟩
  rw [Subalgebra.mem_center_iff]
  intro b
  apply hinj
  rw [map_mul, map_mul, hzx, hx]

theorem card_mul_idem_from_center : ∀ (D : D7) (i : D.nd.Loc) (Γ : Type) [Group Γ] [Finite Γ] (e : MonoidAlgebra ℂ Γ), e * e = e → (∀ z, e * z = z * e) → (∃ ζ : D.nd.O i, IsPrimitiveRoot (iotaO D.nd D.naut i ζ) (Nat.card Γ)) → ∃ z ∈ Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) Γ), ∀ h : Γ, iotaO D.nd D.naut i (MonoidAlgebra.coeff z h) = (Nat.card Γ : ℂ) * e.coeff h := by
  intro D i Γ _ _ e he hc ⟨ζ, hζ⟩
  have hinj : Function.Injective (iotaO D.nd D.naut i) :=
    ((D.naut.iotaQC i).injective.comp (D.naut.iotaQ i).injective).comp (IsFractionRing.injective _ _)
  have hco : ∀ h, ((Nat.card Γ : ℂ) • e).coeff h = (Nat.card Γ : ℂ) * e.coeff h := by
    intro h; simp
  obtain ⟨z, hz, hz'⟩ := exists_central_lift (iotaO D.nd D.naut i) hinj ((Nat.card Γ : ℂ) • e)
    (fun z => by rw [smul_mul_assoc, mul_smul_comm, hc]) (fun h => by
      rw [hco]
      have h1 := centralIdemCoeff Γ e he hc _ hζ h
      have h2 : Algebra.adjoin ℤ ({iotaO D.nd D.naut i ζ} : Set ℂ) ≤
          subalgebraOfSubring (iotaO D.nd D.naut i).range :=
        Algebra.adjoin_le (by rintro _ rfl; exact ⟨ζ, rfl⟩)
      exact h2 h1)
  exact ⟨z, hz, fun h => by rw [hz', hco]⟩

end GlobalTheory.CentralIdem
