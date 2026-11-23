import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMulVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClopenCoset
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZpowMulVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormIntDilatedConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SetIntegralInvMulVec
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair GlobalTheory.CompanionTheory.BZCore
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.BZCore

theorem exists_vol_cosub {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) :
    ∃ vol : COSub k d → ℝ, (∀ L, 0 < vol L) ∧
      (∀ (L' L : COSub k d) (S : Finset (Fin d → k)), L'.sub ≤ L.sub → IsReps L' L S →
        vol L = (S.card : ℝ) * vol L') ∧
      ∀ (g : GL (Fin d) k) (L : COSub k d),
        ((vol (L.act g) : ℝ) : ℂ) ^ 2 * ((dpow d (-2) g : ℂˣ) : ℂ) = ((vol L : ℝ) : ℂ) ^ 2 := by
  classical
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  let ν : Measure k := Measure.addHaar
  haveI : ν.IsAddHaarMeasure := inferInstanceAs (Measure.addHaar : Measure k).IsAddHaarMeasure
  haveI hμ : (piHaar ν d).IsAddHaarMeasure := GlobalTheory.CompanionTheory.MirStable.isAddHaar_piHaar ν d
  have hfin : ∀ L : COSub k d, piHaar ν d (L.sub : Set (Fin d → k)) ≠ ⊤ := fun L =>
    L.isCompact.measure_lt_top.ne
  have hne : ∀ L : COSub k d, piHaar ν d (L.sub : Set (Fin d → k)) ≠ 0 := fun L =>
    L.isOpen.measure_ne_zero _ ⟨0, L.sub.zero_mem⟩
  refine ⟨fun L => (piHaar ν d (L.sub : Set (Fin d → k))).toReal, fun L => ENNReal.toReal_pos (hne L) (hfin L), ?_, ?_⟩
  · intro L' L S hle hS
    have hU : (L.sub : Set (Fin d → k)) = ⋃ s ∈ S, {y | y - s ∈ L'.sub} := by
      ext y
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, SetLike.mem_coe, exists_prop]
      constructor
      · intro hy
        obtain ⟨s, ⟨hs, hys⟩, -⟩ := hS.2 y hy
        exact ⟨s, hs, hys⟩
      · rintro ⟨s, hs, hys⟩
        have := L.sub.add_mem (hle hys) (hS.1 s hs)
        simpa using this
    have hdisj : Set.PairwiseDisjoint (S : Set (Fin d → k)) fun s => {y | y - s ∈ L'.sub} := by
      intro s hs t ht hst
      refine Set.disjoint_left.2 fun y hys hyt => hst ?_
      have hy : y ∈ L.sub := by
        have := L.sub.add_mem (hle hys) (hS.1 s hs)
        simpa using this
      exact (hS.2 y hy).unique ⟨hs, hys⟩ ⟨ht, hyt⟩
    have hcos : ∀ s : Fin d → k, piHaar ν d {y | y - s ∈ L'.sub} = piHaar ν d (L'.sub : Set (Fin d → k)) := by
      intro s
      have : {y | y - s ∈ L'.sub} = (fun y => y + (-s)) ⁻¹' (L'.sub : Set (Fin d → k)) := by
        ext y
        simp [sub_eq_add_neg]
      rw [this, measure_preimage_add_right]
    have hm : piHaar ν d (L.sub : Set (Fin d → k)) = (S.card : ENNReal) * piHaar ν d (L'.sub : Set (Fin d → k)) := by
      rw [hU, measure_biUnion_finset hdisj fun s _ => (isClopen_coset L' s).isOpen.measurableSet]
      simp [hcos]
    show (piHaar ν d (L.sub : Set (Fin d → k))).toReal = _
    rw [hm, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  · intro g L
    have hI := setIntegral_inv_mulVec ν d g ((L.act g).sub : Set (Fin d → k)) (fun _ => (1 : ℂ))
    have hset : {y | (g : Matrix (Fin d) (Fin d) k) *ᵥ y ∈ ((L.act g).sub : Set (Fin d → k))} = (L.sub : Set (Fin d → k)) := by
      ext y
      exact COSub.mulVec_mem_act g
    rw [hset, setIntegral_const, setIntegral_const] at hI
    simp only [Measure.real, Complex.real_smul, mul_one] at hI
    have hn := nabs_pos' k (Matrix.GeneralLinearGroup.det g)
    have hd : ((dpow d (-2) g : ℂˣ) : ℂ) = (((nabs k (Matrix.GeneralLinearGroup.det g)) ^ (-2 : ℝ) : ℝ) : ℂ) := by
      simp only [dpow, detChar_apply]
      exact val_absPow_ofReal k (-2) _
    rw [hd, hI]
    have hr : (nabs k (Matrix.GeneralLinearGroup.det g)) ^ (-2 : ℝ) = ((nabs k (Matrix.GeneralLinearGroup.det g)) ^ 2)⁻¹ := by
      rw [Real.rpow_neg hn.le, Real.rpow_two]
    rw [hr]
    have hn' : ((nabs k (Matrix.GeneralLinearGroup.det g) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    push_cast
    field_simp

end GlobalTheory.CompanionTheory.BZCore

end
