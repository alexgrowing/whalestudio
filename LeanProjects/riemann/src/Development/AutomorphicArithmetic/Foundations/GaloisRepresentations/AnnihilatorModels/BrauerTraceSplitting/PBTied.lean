import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.LocFacts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.BrauerTraceSplitting.LocFacts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.BrauerTraceSplitting.AwayEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.LocalComparison.LocTied6
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.TiedAInvOfTheta
import GroundTheory.PAdicHodge.ACrisPhi

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison GroundTheory.PAdicHodge

namespace UpperTheory.Gal.crystallineComparison.Br

variable {l : ℕ} [Fact l.Prime]

private theorem l_dvd : ∃ r : ℕ, (l : Acris l) ∣ tA l ^ r := by
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1
    (ACris.periodT_pow_mem' (K := ℂ_[l]) (p := l) (untilt_epsilon (p := l)))
  exact ⟨l - 1, u, by rw [tA, ← hu, mul_comm]⟩

private def cT {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) : Acris l →+* P.R.B :=
  T.eB.symm.toRingHom.comp (Formalism.Per6.cB l)

private theorem eB_cT {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) (a : Acris l) :
    T.eB (cT T a) = Formalism.Per6.cB l a :=
  T.eB.apply_symm_apply _

private theorem cT_unit {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) : IsUnit (cT T (tA l)) :=
  (Formalism.Per6.Loc2.isUnit_right (l : Acris l) (tA l)).map T.eB.symm

private theorem cT_loc {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) (x : P.R.B) :
    ∃ (r : ℕ) (a : Acris l), cT T (tA l) ^ r * x = cT T a := by
  obtain ⟨r, y, h⟩ := (locFacts (Acris l) (l : Acris l) (tA l) l_dvd).1 (T.eB x)
  refine ⟨r, y, T.eB.injective ?_⟩
  rw [map_mul, map_pow, eB_cT, eB_cT]
  exact h

private theorem cT_ker {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) (a : Acris l)
    (h : cT T a = 0) : ∃ r : ℕ, tA l ^ r * a = 0 := by
  refine (locFacts (Acris l) (l : Acris l) (tA l) l_dvd).2 a ?_
  have h1 := eB_cT T a
  rw [h, map_zero] at h1
  exact h1.symm

private theorem cT_φ {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) (a : Acris l) :
    P.φB (cT T a) = cT T (phiA l a) := by
  refine T.eB.injective ?_
  rw [T.frob, eB_cT, eB_cT]
  exact PositivityTheory.LocInh.φB_cB a

private theorem cT_σ {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI)
    (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (g : K.fixingSubgroup) (a : Acris l) :
    P.actQ g.1 (cT T a) = cT T (galA g a) := by
  refine T.eB.injective ?_
  rw [T.actB, eB_cT, eB_cT, ((actEq l).1 K g a)]
  exact PositivityTheory.LocInh.σB_cB _ a

private theorem algebraMap_padic_int_eq_period {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) (x : ℤ_[l]) :
    algebraMap ℚ_[l] P.R.B (x : ℚ_[l]) = cT T (zA l x) := by
  refine T.eB.injective ?_
  rw [T.zB, eB_cT]
  exact (actEq l).2 x

private def pullbackToFiniteExtension {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) (K : FinExt l) : PB l K.1 where
  C := P.R.B
  c := cT T
  φ := P.φB
  σ g := (P.actQ g.1).toAlgHom
  t_unit := cT_unit T
  loc := cT_loc T
  ker := cT_ker T
  φ_c := cT_φ T
  σ_c := cT_σ T K.1
  z_c := algebraMap_padic_int_eq_period T

theorem pBTied : PBTied := by
  intro l _ P AI hT K
  obtain ⟨T⟩ := UpperTheory.Lit.Cmp.locTied6 l P AI hT
  exact ⟨pullbackToFiniteExtension T K, AlgEquiv.refl, fun _ _ => rfl, fun _ => rfl, PositivityTheory.LocInh.tiedA_φ_injective P⟩

end UpperTheory.Gal.crystallineComparison.Br
