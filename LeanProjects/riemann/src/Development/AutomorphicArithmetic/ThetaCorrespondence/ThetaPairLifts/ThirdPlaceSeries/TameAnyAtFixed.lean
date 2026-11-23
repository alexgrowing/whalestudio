import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TameAnyAtOfIsConjPl
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TrivialLocalCondition
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AdmissibleResidualTameEigenvalues

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.IneAway
open GlobalTheory.TypeLeaf
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
end GlobalTheory.IneAway
namespace GlobalTheory.TypeLeaf
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels
theorem tameAnyAt_fixed_alt_alt : ∀ D : D7, _root_.UpperTheory.GalS.GalAwayN D → FrobDense D → ∀ (i : D.nd.Loc) (π : D.naut.CG D.R.r) (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)), D.naut.csd π → D.naut.ralg π → _root_.UpperTheory.GalS.FullLabS D [⟨D.R.r, π, 1⟩] → IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] ρ → ∀ k : Fin 2, D.nd.l i ≠ D.host.g k → ∀ v : D.nd.PlG k, TameAnyAt D i [⟨D.R.r, π, 1⟩] ρ k (D.naut.plGw k v) := by
  intro D hA hF i π ρ hc hr hfull hρ k hk v
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨ι, hinj, hred⟩ := GlobalTheory.T.exists_reduction_teichmullerEmbedding_at_localisation D i k hk
  have hpol := _root_.GlobalTheory.IneAway.ineAt' D hA hF i π ρ hc hr hfull hρ k v _ rfl (tameAnyFix_not_over D i k hk v) _ (D.ntypes.tg_mem k v)
  have hlab := D.ntypes.inertiaCharpoly_type k v _ (_root_.UpperTheory.GalS.fl0' hfull k v)
  rw [← tameAnyFix_isoLoc D π, hlab] at hpol
  have h1 := hred _ _ hpol
  have hchar : Matrix.charpoly ((redF D i ρ (D.nd.gam0 i (D.naut.plGw k v)) : GL (Fin D.R.r) _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i))) =
      ((Formalism.CyclotomicNorms.rootsBar (labSig D [⟨D.R.r, π, 1⟩] k v)).map
        fun x => X - C (ι (Formalism.CyclotomicNorms.primeToPart (D.nd.l i) x) ^ (1 : ℤ))).prod := by
    rw [D.ntypes.heckeLoc_gamma_places]
    simp only [zpow_one, tameAnyFix_map_primeToPart]
    rw [← h1, ← Matrix.charpoly_map]
    rfl
  have hval : ∀ y : Fb (D.host.g k) (D.host.g_prime k),
      iotaO D.nd D.naut i (chi1 D.nd i (D.ntypes.tg k v)) = D.ntypes.teichC k y →
      D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i (D.naut.plGw k v)))) = ι y := by
    intro y hy
    have h2 := hred (X - C (chi1 D.nd i (D.ntypes.tg k v))) {y} (by simp [hy])
    rw [D.ntypes.heckeLoc_gamma_places]
    simpa using h2
  rcases D.ntypes.chiT_tg i k v hk with h | h
  · refine ⟨v, ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩, ι, 1, 1, Or.inl rfl, Or.inl rfl, hinj, hchar, ?_⟩
    rw [zpow_one, tameAnyFix_map_primeToPart]
    exact hval _ h
  · refine ⟨v, ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩, ι, 1, -1, Or.inl rfl, Or.inr rfl, hinj, hchar, ?_⟩
    rw [zpow_neg_one, tameAnyFix_map_primeToPart, hval _ h]
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
end GlobalTheory.TypeLeaf
namespace GlobalTheory.TypeLeaf.ConjPlace
end GlobalTheory.TypeLeaf.ConjPlace
namespace GlobalTheory.AdmTame
end GlobalTheory.AdmTame
end
end
