import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JSmul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleQuotientKerIffFullLattices
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTopDataOfSlotHyps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleClassesPropsOfFlatCoefficient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSumsTwistsCharactersExpectedJumps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCyclotomicChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDcrisLetterDeRhamComponentEqDim
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrComplete
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

namespace GlobalTheory.AdmQuotExt

section Gen
variable {G : Type} [Group G] [TopologicalSpace G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    (L : Lattice (O := O) ρ) (X : Type) [AddCommGroup X] [Module O X]

def redExt (c : O) : ((↥L.T ⊗[O] X) × O) →ₗ[O] ((↥L.T ⊗[O] X) × (O ⧸ Ideal.span {c})) :=
  LinearMap.prodMap LinearMap.id (Ideal.span {c}).mkQ

omit [TopologicalSpace G] in
theorem redExt_surjective (c : O) : Function.Surjective (redExt L X c) := by
  rintro ⟨m, y⟩
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
  exact ⟨(m, y), rfl⟩

omit [TopologicalSpace G] in
theorem ker_redExt (lam : O) (a : ℕ) : LinearMap.ker (redExt L X (lam ^ a)) = tableLineDegreeTwo.kerExt L X lam a := by
  rw [redExt, LinearMap.ker_prodMap, LinearMap.ker_id, Submodule.ker_mkQ]
  rfl

theorem redExt_actExt (χ₁ : G →* Oˣ) {c : O} (hc : ∀ x : X, c • x = 0)
    (z : G → ↥L.T ⊗[O] X) (hz : z ∈ Z1 (twCoef (latRep L) χ₁ X) ⊤) (g : G) (x : (↥L.T ⊗[O] X) × O) :
    redExt L X c (tableLineDegreeTwo.actExt L X χ₁ z g x) = Ea (latRep L) χ₁ hc ⟨z, hz⟩ g (redExt L X c x) := by
  obtain ⟨m, y⟩ := x
  have h := Ea_apply (latRep L) χ₁ hc ⟨z, hz⟩ g m y
  change (_, _) = Ea (latRep L) χ₁ hc ⟨z, hz⟩ g (m, Ideal.Quotient.mk _ y)
  rw [h]
  simp only [tableLineDegreeTwo.actExt, smul_smul, mul_comm y]
  rfl

end Gen

set_option maxHeartbeats 2000000 in

theorem admissible_quotientExtension_iff_admissible_ext' : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P) (jT : ZMod S.n → ℤ → ℤ),
    (∀ i a, ((S.D.Ut i).count a : ℤ) = jT i a) →
    ∀ (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (L : Lattice (O := S.O) T.ρ) (X : Type) [AddCommGroup X] [Module S.O X]
      (z : S.G → ↥L.T ⊗[S.O] X) (hz : z ∈ Z1 (twCoef (latRep L) S.Γ.χ₁ X) ⊤) (a : ℕ)
      (ha : ∀ x : X, S.Γ.lam ^ a • x = 0),
      (tableLineDegreeTwo.AdmQ (P.PD S.K) S.emb S.Γ.lam jT (tableLineDegreeTwo.resPoly S.Γ.T₀.ρ S.Γ.chi S.D.t) (tableLineDegreeTwo.actExt L X S.Γ.χ₁ z)
                         (tableLineDegreeTwo.kerExt L X S.Γ.lam a) ↔ S.admitted (Ea (latRep L) S.Γ.χ₁ ha ⟨z, hz⟩)) := by
  intro l _ P S jT hj T L X _ _ z hz a ha
  have h := GlobalTheory.FullCharpoly.admissibleQuotient_iff_admissible_module S jT hj _ _ (tableLineDegreeTwo.actExt L X S.Γ.χ₁ z)
    (Ea (latRep L) S.Γ.χ₁ ha ⟨z, hz⟩) (redExt L X (S.Γ.lam ^ a)) (redExt_surjective L X _)
    (redExt_actExt L X S.Γ.χ₁ ha z hz)
  rw [ker_redExt L X S.Γ.lam a] at h
  exact h

end GlobalTheory.AdmQuotExt
