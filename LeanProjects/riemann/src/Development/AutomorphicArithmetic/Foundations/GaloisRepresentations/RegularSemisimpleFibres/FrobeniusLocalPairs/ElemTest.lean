import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.MatchSmulAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.BallSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubiniHolds

open MeasureTheory NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc
open GlobalTheory.SmGL hiding iwahori
open PositivityTheory.Rg.Tf.Geo (incFin galFin)
open UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L

section

variable {E : Type} [Field E] [ValuativeRel E] {n : ℕ}

private theorem near_mul {r : ValueGroupWithZero E} (h1 : r < 1) {x y : E} (hx : valuation E (x - 1) ≤ r)
    (hy : valuation E (y - 1) ≤ r) : valuation E (x * y - 1) ≤ r := by
  have hx1 : valuation E x ≤ 1 := by
    have e : x = (x - 1) + 1 := by ring
    rw [e]
    exact (Valuation.map_add_le _ (hx.trans h1.le) (by simp))
  have e : x * y - 1 = x * (y - 1) + (x - 1) := by ring
  rw [e]
  refine Valuation.map_add_le _ ?_ hx
  rw [map_mul]
  exact (mul_le_mul' hx1 hy).trans (by simp)

private theorem near_prod {r : ValueGroupWithZero E} (h0 : 0 < r) (h1 : r < 1) {ι : Type} (s : Finset ι) (f : ι → E)
    (hf : ∀ i ∈ s, valuation E (f i - 1) ≤ r) : valuation E (∏ i ∈ s, f i - 1) ≤ r := by
  induction s using Finset.induction_on with
  | empty => simpa using h0.le
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact near_mul h1 (hf a (Finset.mem_insert_self _ _))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private theorem small_prod {r : ValueGroupWithZero E} {ι : Type} (s : Finset ι) (f : ι → E) (hs : ∀ i ∈ s, valuation E (f i) ≤ 1)
    (a : ι) (ha : a ∈ s) (hr : valuation E (f a) ≤ r) : valuation E (∏ i ∈ s, f i) ≤ r := by
  rw [← Finset.mul_prod_erase s f ha, map_mul, map_prod]
  exact (mul_le_of_le_one_right' (Finset.prod_le_one' fun i hi => hs i (Finset.mem_of_mem_erase hi))).trans hr

private theorem det_near {r : ValueGroupWithZero E} (h0 : 0 < r) (h1 : r < 1) {M : Matrix (Fin n) (Fin n) E}
    (hM : ∀ i j, valuation E (M i j - (1 : Matrix (Fin n) (Fin n) E) i j) ≤ r) : valuation E (M.det - 1) ≤ r := by
  have hb : ∀ i j, valuation E (M i j) ≤ 1 := fun i j => by
    have e : M i j = (M i j - (1 : Matrix (Fin n) (Fin n) E) i j) + (1 : Matrix (Fin n) (Fin n) E) i j := by ring
    rw [e]
    refine Valuation.map_add_le _ ((hM i j).trans h1.le) ?_
    rw [Matrix.one_apply]
    split_ifs <;> simp
  rw [Matrix.det_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : Equiv.Perm (Fin n))), add_sub_right_comm]
  refine Valuation.map_add_le _ ?_ (Valuation.map_sum_le _ fun p hp => ?_)
  · have hd : valuation E (∏ i, M i i - 1) ≤ r := near_prod h0 h1 _ _ fun i _ => by simpa using hM i i
    simpa using hd
  · have hp1 : p ≠ 1 := Finset.ne_of_mem_erase hp
    obtain ⟨a, ha⟩ : ∃ a, p a ≠ a := by
      by_contra hc
      push Not at hc
      exact hp1 (Equiv.ext hc)
    have hs : valuation E (∏ i, M (p i) i) ≤ r := by
      refine small_prod _ _ (fun i _ => hb _ _) a (Finset.mem_univ _) ?_
      simpa [Matrix.one_apply, ha] using hM (p a) a
    rcases Int.units_eq_one_or (Equiv.Perm.sign p) with e | e <;> simpa [e, Units.smul_def] using hs

end

private theorem diag_cont (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) :
    Continuous (diagT E (Fin n)) :=
  (continuous_leviEmb E (points (Fin n))).comp (continuous_leviTorus E (Fin n))

theorem elemTest : ElemTest := by
  intro E _ _ _ _ n r h0 h1 A hA
  obtain ⟨K, hK, hKo, hKc⟩ := UpperTheory.ConvolutionTheory.Loc.ballSub E n r h0 h1
  haveI := (UpperTheory.V.Z.Tf.Orb.gLTop E n).2.2.1
  have mK : ∀ g : GL (Fin n) E, g ∈ ball n r ↔ g ∈ K := fun g => by rw [← hK]; rfl
  have e : elemSet r A = (fun z : GL (Fin n) E × (Fin n → Eˣ) × GL (Fin n) E => z.1 * diagT E (Fin n) z.2.1 * z.2.2) ''
      ((K : Set (GL (Fin n) E)) ×ˢ (A ×ˢ (K : Set (GL (Fin n) E)))) := by
    ext g
    constructor
    · rintro ⟨a, ha, b, hb, s, hs, rfl⟩
      exact ⟨(a, s, b), ⟨(mK a).1 ha, hs, (mK b).1 hb⟩, rfl⟩
    · rintro ⟨⟨a, s, b⟩, ⟨ha, hs, hb⟩, rfl⟩
      exact ⟨a, (mK a).2 ha, b, (mK b).2 hb, s, hs, rfl⟩
  have hS : IsCompact (elemSet r A) := by
    rw [e]
    refine (hKc.prod (hA.prod hKc)).image ?_
    exact (continuous_fst.mul ((diag_cont E n).comp (continuous_fst.comp continuous_snd))).mul
      (continuous_snd.comp continuous_snd)
  have hO : IsOpen (elemSet r A) := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨a, ha, b, hb, s, hs, rfl⟩
    refine Filter.mem_of_superset ((hKo.preimage (f := fun g => (a * diagT E (Fin n) s)⁻¹ * g) (by fun_prop)).mem_nhds
      (by simpa [mul_assoc] using (mK b).1 hb)) fun g hg => ?_
    exact ⟨a, ha, _, (mK _).2 hg, s, hs, by group⟩
  have hT : UpperTheory.ConvolutionTheory.C.Test ((elemSet r A).indicator (1 : GL (Fin n) E → ℂ)) := by
    refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_, HasCompactSupport.intro hS fun g hg => Set.indicator_of_notMem hg _⟩
    by_cases h : g ∈ elemSet r A
    · filter_upwards [hO.mem_nhds h] with y hy
      exact (Set.indicator_of_mem hy _).trans (Set.indicator_of_mem h (1 : GL (Fin n) E → ℂ)).symm
    · filter_upwards [hS.isClosed.isOpen_compl.mem_nhds h] with y hy
      exact (Set.indicator_of_notMem hy _).trans (Set.indicator_of_notMem h _).symm
  refine ⟨hO, hS, hT, hT, ?_⟩
  rintro _ ⟨a, ha, b, hb, s, hs, rfl⟩
  have hd : ∀ g ∈ ball (E := E) n r, valuation E (((GeneralLinearGroup.det g : Eˣ) : E) - 1) ≤ r := fun g hg => by
    simpa [GeneralLinearGroup.val_det_apply] using det_near h0 h1 hg
  refine ⟨s, hs, GeneralLinearGroup.det a * GeneralLinearGroup.det b, ?_, ?_⟩
  · rw [Units.val_mul]
    exact near_mul h1 (hd a ha) (hd b hb)
  · have hdiag : GeneralLinearGroup.det (diagT E (Fin n) s) = ∏ i, s i := by
      ext
      simp [GeneralLinearGroup.val_det_apply, val_diagT, Matrix.det_diagonal]
    rw [map_mul, map_mul, hdiag]
    simp only [mul_comm, mul_left_comm, mul_assoc]

end UpperTheory.Gal.InertialTypesAlt.L
