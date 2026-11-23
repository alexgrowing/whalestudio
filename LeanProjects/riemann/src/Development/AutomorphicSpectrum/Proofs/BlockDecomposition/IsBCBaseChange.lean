import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentIdealRat

noncomputable section

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver

namespace GlobalTheory.CompanionTheory.BaseChangeData

variable {K : Type} [Field K] [NumberField K]

def below (w : PlK K) : Pl := w.under (𝓞 ℚ)

instance liesOver_below (w : PlK K) : w.asIdeal.LiesOver (below w).asIdeal := ⟨rfl⟩

theorem eq_below (v : Pl) (w : PlK K) [h : w.asIdeal.LiesOver v.asIdeal] : v = below w :=
  HeightOneSpectrum.ext h.over

theorem continuous_nrm (v : Pl) (w : PlK K) [w.asIdeal.LiesOver v.asIdeal] : Continuous (nrm v w) :=
  continuous_normUnits (Qv v) (Kv K w)

theorem isUnit1_comp_nrm (v : Pl) (w : PlK K) [w.asIdeal.LiesOver v.asIdeal] {χ : (Qv v)ˣ →* ℂˣ}
    (h : IsUnit1 χ) : IsUnit1 (χ.comp (nrm v w)) :=
  ⟨h.1.comp (continuous_nrm v w), fun x => h.2 _⟩

theorem isUnramifiedChar_comp_nrm (v : Pl) (w : PlK K) [w.asIdeal.LiesOver v.asIdeal] {χ : (Qv v)ˣ →* ℂˣ}
    (h : IsUnramifiedChar χ) : IsUnramifiedChar (χ.comp (nrm v w)) := by
  intro u hu
  have h1 : nrm v w u ∈ unitFiltrationUnits (Qv v) 0 :=
    map_normUnits_unitFiltrationUnits_zero_le (K := Qv v) (L := Kv K w) (Subgroup.mem_map_of_mem _ hu)
  exact h h1

attribute [local instance] FractionRing.liftAlgebra in

theorem differentIdeal_eq : differentIdeal ℤ (𝓞 K) = differentIdeal (𝓞 ℚ) (𝓞 K) := by
  have h := differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 ℚ) (𝓞 K)
  rw [GlobalTheory.CompanionTheory.StdCharQ.differentIdeal_rat, Ideal.map_top, Ideal.mul_top] at h
  exact h

attribute [local instance] FractionRing.liftAlgebra in

theorem dvd_different_iff (w : PlK K) :
    w.asIdeal ∣ differentIdeal ℤ (𝓞 K) ↔ w.asIdeal.ramificationIdx (𝓞 ℚ) ≠ 1 := by
  rw [differentIdeal_eq, dvd_differentIdeal_iff, ne_eq, Ideal.ramificationIdx'_eq_one_iff]

def badSet (D : Dat) : Set (PlK K) := {w | below w ∈ D.bad ∨ w.asIdeal.ramificationIdx (𝓞 ℚ) ≠ 1}

theorem finite_badSet (D : Dat) : (badSet (K := K) D).Finite := by
  have h1 : ({w : PlK K | w.asIdeal ∣ differentIdeal ℤ (𝓞 K)}).Finite :=
    Ideal.finite_factors GroundTheory.Global.differentIdeal_ne_bot
  have h2 : (⋃ v ∈ D.bad, {w : PlK K | w.asIdeal ∣ v.asIdeal.map (algebraMap (𝓞 ℚ) (𝓞 K))}).Finite :=
    Set.Finite.biUnion D.bad.finite_toSet fun v _ =>
      Ideal.finite_factors (Ideal.map_ne_bot_of_ne_bot v.ne_bot)
  refine (h2.union h1).subset ?_
  rintro w (hw | hw)
  · refine Or.inl (Set.mem_biUnion (Finset.mem_coe.2 hw) ?_)
    exact Ideal.dvd_iff_le.2 (Ideal.map_le_iff_le_comap.2 (le_of_eq (liesOver_below w).over))
  · exact Or.inr ((dvd_different_iff w).2 hw)

theorem isStd_of_unramified (w : PlK K) (h : w.asIdeal.ramificationIdx (𝓞 ℚ) = 1) :
    IsStd (localAdelicChar K w) := by
  refine ⟨continuous_localAdelicChar w, localAdelicChar_ne_one w, ?_⟩
  have hd : ¬ w.asIdeal ∣ differentIdeal ℤ (𝓞 K) := fun hd => (dvd_different_iff w).1 hd h
  rw [addCharConductor_localAdelicChar, differentExp,
    count_coeIdeal_eq_multiplicity w GroundTheory.Global.differentIdeal_ne_bot, multiplicity_eq_zero.2 hd]
  simp

def baseChange (K : Type) [Field K] [NumberField K] (D : Dat) : DatK K where
  k := D.k
  three := D.three
  ν w := (D.ν (below w)).comp (nrm (below w) w)
  unit w := isUnit1_comp_nrm _ w (D.unit _)
  bad := (finite_badSet D).toFinset
  unr w hw := by
    have hw' : w ∉ badSet D := by simpa using hw
    exact isUnramifiedChar_comp_nrm _ w (D.unr _ fun h => hw' (Or.inl h))
  std w hw := by
    have hw' : w ∉ badSet D := by simpa using hw
    exact isStd_of_unramified w (by_contra fun h => hw' (Or.inr h))

theorem isBC_baseChange (D : Dat) : IsBC D (baseChange K D) where
  k := rfl
  nu v w _ := by
    obtain rfl := eq_below v w
    rfl
  bad v w _ := by
    obtain rfl := eq_below v w
    simp [baseChange, badSet]

theorem bcex : ∀ (K : Type) [Field K] [NumberField K], Ad3.K.QuadraticBaseChangeGL3.BCEX K :=
  fun K _ _ D => ⟨baseChange K D, isBC_baseChange D⟩

end GlobalTheory.CompanionTheory.BaseChangeData
