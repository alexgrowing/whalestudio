import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSimR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleCosetOfInvolutive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousFiniteAdeleEquivRatIntStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousRestrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatFiniteAdelesSplitAwayFromPrimePadicStatement

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.CentTorus
open scoped TensorProduct

namespace GlobalTheory.CentTorus.ClassSplit

section Tmap

variable {A B L : Type} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B] [CommRing L] [Algebra ℚ L]

def tmap (π : A →ₐ[ℚ] B) : L ⊗[ℚ] A →ₐ[ℚ] B ⊗[ℚ] L :=
  Algebra.TensorProduct.lift Algebra.TensorProduct.includeRight (Algebra.TensorProduct.includeLeft.comp π)
    (fun _ _ => Commute.all _ _)

@[simp] theorem tmap_tmul (π : A →ₐ[ℚ] B) (l : L) (a : A) : tmap π (l ⊗ₜ[ℚ] a) = π a ⊗ₜ[ℚ] l := by
  simp [tmap]

end Tmap

end GlobalTheory.CentTorus.ClassSplit

namespace GlobalTheory.CentTorus.ClassSplit

end GlobalTheory.CentTorus.ClassSplit

namespace GlobalTheory.CentTorus.ClassSplit

theorem adele_split (p : ℕ) [Fact p.Prime] :
    ∃ (π₁ : FiniteAdeleRing (𝓞 ℚ) ℚ →ₐ[ℚ] AfP p) (π₂ : FiniteAdeleRing (𝓞 ℚ) ℚ →ₐ[ℚ] ℚ_[p]),
      Continuous π₁ ∧ Continuous π₂ ∧ Function.Bijective (fun a => (π₁ a, π₂ a)) := by
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_continuous_finiteAdele_equiv_rat_int
  obtain ⟨π, hπc, hπb⟩ := GlobalTheory.T.ratFiniteAdeles_split_awayFromPrime_padic p
  let r : FiniteAdeleRing ℤ ℚ →ₐ[ℚ] AfP p := { AfP.restr p with commutes' := fun _ => rfl }
  exact ⟨r.comp e.toAlgHom, π.comp e.toAlgHom, (GlobalTheory.T.continuous_afP_restr p).comp he, hπc.comp he, hπb.comp e.bijective⟩

end GlobalTheory.CentTorus.ClassSplit

section Final

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.CentTorus
open scoped TensorProduct Classical

end Final
