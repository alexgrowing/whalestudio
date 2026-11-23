import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RealGal

theorem bridge_j_mem_Kw_of_dec_le : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O), Dec (F := F) A ≤ (res F Ω K).range → ∀ x : K, Bw.j (algebraMap K Ω x) ∈ Bw.Kw.1 := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ l _ A O _ _ _ Bw hD x
  have hfix : ∀ σ ∈ (Bw.Kw.1).fixingSubgroup, σ (Bw.j (algebraMap K Ω x)) = Bw.j (algebraMap K Ω x) := by
    intro σ hσ
    obtain ⟨g, hg⟩ := Bw.e.surjective ⟨σ, hσ⟩
    have h1 := Bw.e_comm g (algebraMap K Ω x)
    rw [hg] at h1
    obtain ⟨h, hh⟩ := hD g.2
    have h2 : (g : Ω ≃ₐ[F] Ω) (algebraMap K Ω x) = algebraMap K Ω x := by
      rw [← hh]
      exact h.commutes x
    simpa [h2] using h1
  haveI : IsGalois ℚ_[l] (Om l) := inferInstance
  rw [← InfiniteGalois.fixedField_fixingSubgroup Bw.Kw.1]
  exact fun σ => hfix σ.1 σ.2

end GlobalTheory.RealGal
