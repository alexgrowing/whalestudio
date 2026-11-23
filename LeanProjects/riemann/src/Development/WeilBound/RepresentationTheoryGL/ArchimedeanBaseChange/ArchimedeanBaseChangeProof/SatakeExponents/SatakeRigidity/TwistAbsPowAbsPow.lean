import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.ThetaOfCsdR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmGaloisRepresentationCrystalline
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLanglandsGaloisCompatStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalGlobalOfGelfandKazhdanStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatakeOfIsLocComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EventuallyResidueDegreeOnePrimeMovedByGalois
import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.TameCongruences.LocallyConstantOneCochain
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PInfAsc
import Formalism.SharpRestriction.LevelLetterCocycles.LinearIndependentSmulOfNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.WeilBound.CoreStatements.PublishedTheorems.FiniteGLInvariants.AffineLieInvariants.Imports
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.FinIdx
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.GelfandKazhdanDuality.GelfandKazhdanDualOfHyp
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.BaseChangeSpehOfDiscreteSeries
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspRapidDecaySiegelGL

noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Rig

namespace GalX

open GlobalTheory.HeckeGal.Model (absPow absPow_isAbsPow)

theorem absPow_mul_absPow (E : Type) [Field E] [NumberField E] (x y : ℝ) :
    absPow E x * absPow E y = absPow E (x + y) := by
  refine Subtype.ext (MonoidHom.ext fun z => Units.ext ?_)
  change (((absPow E x).1 z : ℂˣ) : ℂ) * (((absPow E y).1 z : ℂˣ) : ℂ) = (((absPow E (x + y)).1 z : ℂˣ) : ℂ)
  rw [CG.absPow_val_apply, CG.absPow_val_apply, CG.absPow_val_apply, ← Complex.exp_add]
  push_cast
  ring_nf

theorem twist_absPow_absPow {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (P : CuspSub E a)
    (x y : ℝ) : (CG.mk (P.twist (absPow E x))).twist (absPow E y) = CG.mk (P.twist (absPow E (x + y))) := by
  rw [← absPow_mul_absPow]
  exact (CG.twist_mul (CG.mk P) _ _).symm

theorem infOfWeight_nodup {n : ℕ} (lam : DomWeight n) : (infOfWeight lam).Nodup := by
  unfold infOfWeight
  refine Multiset.Nodup.map (fun j k h => ?_) Finset.univ.nodup
  have h1 : (((lam.w j - (j : ℕ) : ℤ)) : ℂ) = ((lam.w k - (k : ℕ) : ℤ) : ℂ) := by
    push_cast
    linear_combination h
  have h2 : lam.w j - (j : ℕ) = lam.w k - (k : ℕ) := Int.cast_injective h1
  rcases lt_trichotomy j k with hjk | rfl | hjk
  · have := lam.anti hjk.le
    have : (j : ℕ) < k := hjk
    omega
  · rfl
  · have := lam.anti hjk.le
    have : (k : ℕ) < j := hjk
    omega

theorem mem_infOfWeight {n : ℕ} {lam : DomWeight n} {z : ℂ} (hz : z ∈ infOfWeight lam) :
    ∃ k : ℤ, z = k + ((n : ℂ) - 1) / 2 := by
  unfold infOfWeight at hz
  obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hz
  exact ⟨lam.w j - (j : ℕ), by push_cast; ring⟩

theorem prod_map_sum {ι α β : Type*} [CommMonoid β] (s : Finset ι) (M : ι → Multiset α) (f : α → β) :
    ((∑ i ∈ s, M i).map f).prod = ∏ i ∈ s, ((M i).map f).prod := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons j s hj ih => rw [Finset.sum_cons, Finset.prod_cons, Multiset.map_add, Multiset.prod_add, ih]

theorem regTw {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (D : Pre E n) (hr : D.Reg)
    (i : Fin D.c) {a d : ℕ} (P : CuspSub E a) (he : AscEmb (D.V i) P d) (k : Fin d) :
    (CG.mk (P.twist (absPow E (spehExp d k + ((a : ℝ) - n) / 2)))).IsRegAlg := by
  refine (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_
  obtain ⟨lam, hlam⟩ := hr τ
  obtain ⟨m0, hm0, hsum⟩ := infAsc_holds E (D.N i) a d (D.V i) P (D.discrete i) he τ _ (D.inf i τ)
  set s : ℝ := spehExp d k + ((a : ℝ) - n) / 2 with hs
  have hexpo : ∀ τ, expo (absPow E s) τ = s :=
    (GlobalTheory.CuspRep.InfType.expo_of_infType E _).2.1 s (absPow_isAbsPow E s)
  have hm' : (P.twist (absPow E s)).HasInfChar τ (m0.map (· + (s : ℂ))) := by
    have := hm0.twist (absPow E s)
    rwa [hexpo] at this
  rw [CG.HasInfChar.infChar_eq (π := CG.mk _) hm']
  have hle : D.m i τ ≤ infOfWeight lam := by
    rw [← hlam]
    exact Finset.single_le_sum (f := fun j => D.m j τ) (fun _ _ => Multiset.zero_le _) (Finset.mem_univ i)
  have hk : m0.map (· + (spehExp d k : ℂ)) ≤ D.m i τ := by
    rw [hsum]
    exact Finset.single_le_sum (f := fun j : Fin d => m0.map (· + (spehExp d j : ℂ))) (fun _ _ => Multiset.zero_le _)
      (Finset.mem_univ k)
  have hnd : (m0.map (· + (spehExp d k : ℂ))).Nodup := Multiset.nodup_of_le (hk.trans hle) (infOfWeight_nodup lam)
  refine ⟨(Multiset.Nodup.of_map _ hnd).map (add_left_injective _), fun z hz => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
  obtain ⟨j, hj⟩ := mem_infOfWeight (Multiset.mem_of_le (hk.trans hle) (Multiset.mem_map_of_mem _ hy))
  refine ⟨j, ?_⟩
  rw [hs]
  push_cast
  linear_combination hj

end GalX

end PositivityTheory.Rg.BcB.F.Rig

end
