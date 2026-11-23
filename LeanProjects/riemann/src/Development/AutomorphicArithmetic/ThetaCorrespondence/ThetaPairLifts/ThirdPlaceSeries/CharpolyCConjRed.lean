import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeneralAdmissibleOfIrreducibilityStmt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.IsPotCrysAtOfMono0
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Triple

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.TripleResidual
open NumberField IsDedekindDomain Polynomial Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.TameLabels GlobalTheory.AntiRamConj GlobalTheory.TwistDet
open GlobalTheory.TypeLeaf (WildOne FrobDense)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (OnW IsBaseChange IsGaloisRepOf IsReduction Zbar GaloisReps GalE toFb)
open scoped Pointwise
section Wild
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
end Wild
section Row
variable {D : D7} (Y : NTw D.R D.host D.what₂ D.LL0 D.nd)
theorem charpoly_cConj_eq_charpoly_inv_of_mem_ine (hD : FrobDense D) {n : ℕ} {π : D.naut.CG n} (hπ : D.naut.csd π) {l : ℕ} [Fact l.Prime]
    {ι : Qbar l ≃+* ℂ} {red : Zbar l →+* Formalism.CyclotomicNorms.Fbar l} {r : GalE D →* GL (Fin n) (Qbar l)}
    {ρ : GalE D →* GL (Fin n) (Formalism.CyclotomicNorms.Fbar l)} (hr : _root_.UpperTheory.GalS.IsGaloisRepOfN D π l ι r) (hρ : IsReduction D red r ρ)
    {v : PlE D.host} (hv : v ∉ placesOver D.host.E l) {A : ValuationSubring D.nd.Om} (hA : IsPlaceOver A v)
    {s : GalE D} (hs : s ∈ Ine (F := D.host.E) A) :
    ((ρ (cConj Y s) : GL _ _) : Matrix (Fin n) (Fin n) (Formalism.CyclotomicNorms.Fbar l)).charpoly =
      ((ρ s⁻¹ : GL _ _) : Matrix (Fin n) (Fin n) (Formalism.CyclotomicNorms.Fbar l)).charpoly := by
  have h := _root_.GlobalTheory.TripleResidual.charpoly_cConj_eq_charpoly_cyc_zpow_smul_inv Y hD hπ hr s
  rw [cyc_eq_one_of_mem_Ine hv hA hs, Units.val_one, one_zpow, one_smul] at h
  obtain ⟨p, p1, p2⟩ := hρ.2.2 (cConj Y s)
  obtain ⟨q, q1, q2⟩ := hρ.2.2 s⁻¹
  rw [← p2, ← q2, Polynomial.map_injective _ Subtype.val_injective (p1.trans (h.trans q1.symm))]
end Row
section Triples
end Triples
end GlobalTheory.TripleResidual
end
end
