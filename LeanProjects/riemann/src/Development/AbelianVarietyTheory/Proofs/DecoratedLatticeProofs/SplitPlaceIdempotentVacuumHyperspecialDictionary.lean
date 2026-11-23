import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOverBoth
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedCharTrivialOnIntegralUnitsAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHyperspecialSubgroupAtPlaceIffLocalStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLatticeVacuumSplitPlaceVacuumAtPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLatticeVacuumNonsplitPlaceVacuumAtPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceUniformiserIdeleValueUnramifiedCharStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (hyp IsVacAt UnrPl)

namespace GlobalTheory.PlaceDict

theorem conjP_eq_conjPl (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) : Formalism.L2.Col.conjPrime₂ P = Formalism.DivisionValues.conjPl P := by
  apply HeightOneSpectrum.ext
  ext x
  show Formalism.L2.Col.cO _ x ∈ P.asIdeal ↔ x ∈ Ideal.map (Formalism.DivisionValues.cO D.host.E) P.asIdeal
  rw [← Ideal.comap_symm, Ideal.mem_comap]
  have : (Formalism.DivisionValues.cO D.host.E).symm x = Formalism.L2.Col.cO _ x := by
    apply RingOfIntegers.ext
    simp [Formalism.DivisionValues.cO, Formalism.L2.Col.cO]
    rfl
  rw [this]

theorem isSplit_iff_conjPl_ne (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hvw : w.under (𝓞 D.host.F) = v) : IsSplit (E := D.host.E) v ↔ Formalism.DivisionValues.conjPl w ≠ w := by
  have hu : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Q.under (𝓞 D.host.F) = v ↔
      Ideal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) Q.asIdeal = v.asIdeal := fun Q =>
    ⟨fun h => congrArg HeightOneSpectrum.asIdeal h, fun h => HeightOneSpectrum.ext h⟩
  constructor
  · rintro ⟨P, Q, hPQ, hP, hQ⟩ hc
    have hP' := (hu P).2 hP
    have hQ' := (hu Q).2 hQ
    have key : ∀ R : HeightOneSpectrum (𝓞 D.host.E), R.under (𝓞 D.host.F) = v → R = w := fun R hR => by
      rcases GlobalTheory.GridPlaces.eq_or_eq_conjP (P := w) (Q := R) (by rw [hR, hvw]) with h | h
      · exact h
      · rw [h, conjP_eq_conjPl, hc]
    exact hPQ ((key P hP').trans (key Q hQ').symm)
  · intro hne
    refine ⟨w, Formalism.DivisionValues.conjPl w, hne.symm, (hu w).1 hvw, (hu _).1 ?_⟩
    rw [← conjP_eq_conjPl, GlobalTheory.GridPlaces.under_conjP, hvw]

theorem dictionary : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → (IsSplit (E := D.host.E) v ↔ Formalism.DivisionValues.conjPl w ≠ w) ∧ (∀ χ : (AE D)ˣ →* Circle, (∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = v → UnrAt χ w') → UnrPl w χ) ∧ (∀ (V : HSp D) (g : GA D V), g ∈ hyp V w ↔ ∃ k ∈ Kv V v, g = embV V v k) ∧ (∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ), VacFin ψ S T v f → IsVacAt ψ S T w f) ∧ (IsSplit (E := D.host.E) v → ∀ χ : (AE D)ˣ →* Circle, UnrAt χ w → ∃ (e : AE D) (ϖ : 𝓞 D.host.E) (x : (AE D)ˣ), Formalism.L2.NTheta.IsIdemAt e w ∧ ϖ ∈ w.asIdeal ∧ ϖ ∉ w.asIdeal ^ 2 ∧ (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) ∧ ∀ χ' : (AE D)ˣ →* Circle, UnrAt χ' w → ((χ' x : Circle) : ℂ) = ((val (F := D.host.F) χ' w : ℂˣ) : ℂ)) := by
  intro D v w hvw
  refine ⟨isSplit_iff_conjPl_ne D v w hvw, GlobalTheory.T.unramified_char_trivial_on_integral_units_at_place D v w hvw, GlobalTheory.T.mem_hyperspecialSubgroupAtPlace_iff_local_stabilizer D v w hvw, fun ψ S T f hf => ?_, GlobalTheory.T.splitPlace_uniformiserIdele_value_unramifiedChar D v w hvw⟩
  by_cases hc : Formalism.DivisionValues.conjPl w = w
  · exact GlobalTheory.T.theta_lattice_vacuum_nonsplit_place_vacuum_at_prime D v w hvw hc ψ S T f hf
  · exact GlobalTheory.T.theta_lattice_vacuum_split_place_vacuum_at_prime D v w hvw hc ψ S T f hf

end GlobalTheory.PlaceDict
