import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointsLieOverDistinctPlacesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianStepLevelOfChartFormsLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderTBijective

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem GlobalTheory.AdForm.level_col_sub_one_mem : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ j (hj : j ≤ B.R.m) b, ∀ κ ∈ A.U j b, ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal → ∀ s : Fin ((I.rec7 l Z).R.N j), (fun r => Formalism.UG.prV (E := (I.rec7 l Z).host.E) v (GlobalTheory.AdForm.finM _ (rankN (I.rec7 l Z) j hj) κ r s) - (1 : Matrix (Fin ((I.rec7 l Z).R.N j)) (Fin ((I.rec7 l Z).R.N j)) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F)) r s) ∈ Formalism.UG.latS (F := (I.rec7 l Z).host.F) (v.adicCompletion (I.rec7 l Z).host.F) (intV (I.rec7 l Z).host.E v) (A.K j hj b).lev.Lb := by
  intro B X I hI hP l Z u a Ch A hA j hj b κ hκ v hv s
  obtain ⟨-, κ', hκ'⟩ := (hA.U j hj b κ).1 hκ
  have hgram : gramN (I.rec7 l Z) j hj = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 j hj).1
  haveI : NeZero ((I.rec7 l Z).R.N j) := ⟨by
    have := (I.rec7 l Z).R.m_add_three_le_k
    simp only [Ranks.N]; omega⟩
  obtain ⟨At, -, hpi, -⟩ := GlobalTheory.Mem.AtLevel.exists_atTTied I hI hP l Z u
  let sg : 𝓞 (I.rec7 l Z).host.E →+* 𝓞 (I.rec7 l Z).host.E := RingOfIntegers.mapRingHom (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E)
  have hsc : ∀ x, (sg x : (I.rec7 l Z).host.E) = (I.rec7 l Z).host.conj (x : (I.rec7 l Z).host.E) := fun x => Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.forms_involution_eq_host_conj _
  have hpq : ((At.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) * (sg At.piU : (I.rec7 l Z).host.E) = (((I.rec7 l Z).mem u).A.T : (I.rec7 l Z).host.E) := by
    rw [hsc]; exact At.piU_norm
  have hTp := ((I.rec7 l Z).mem u).A.T_prime
  have hp0 : ((At.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) ≠ 0 := fun h => (Nat.cast_ne_zero.2 hTp.ne_zero) (by rw [← hpq, h, zero_mul])
  have hL : (A.K j hj b).lev.Lb = Formalism.L2.Col.rll_dLat ((I.rec7 l Z).R.N j) (((At.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E)⁻¹) := by
    refine GlobalTheory.Mem.Col2.Lv.baseL_eq B _ At.piU hp0 _ ?_
    rw [hpi]; exact (hA.reads j hj).lb b
  have hx := (((A.K j hj b).lev.U_eq κ'.1).1 κ'.2).2 v
  have hT := (GlobalTheory.Mem.Col2.Lv.uloc_T_iff (sigD (I.rec7 l Z)) (I.rec7 l Z).sp.cm.deg2 (fun x => star_star x) (fun x hx => ((I.rec7 l Z).sp.cm.fixed x).1 hx)
      (I.rec7 l Z).sp.cm.cmUnram.2.2 hgram (A.K j hj b).lev At.piU (sg At.piU) rfl hpq hTp hL v hv (GlobalTheory.T.levelPrime_dvd_of_adicValuation_lt_one (I.rec7 l Z) u At v hv) _).1 hx
  have hsp : Submodule.span (𝓞 (I.rec7 l Z).host.E) (dualSet ((sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →ₐ[(I.rec7 l Z).host.F] (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) j hj) (A.K j hj b).lev.Lb) = Formalism.L2.Col.rll_dLat ((I.rec7 l Z).R.N j) ((sg At.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) := by
    rw [hL, hgram]; exact GlobalTheory.uLocDual_eq (sigD (I.rec7 l Z)) (fun x => star_star x) _ At.piU (sg At.piU) hp0 rfl
  have hy : (fun r => Formalism.UG.inclE (F := (I.rec7 l Z).host.F) (v.adicCompletion (I.rec7 l Z).host.F) ((Pi.single s 1 : Fin ((I.rec7 l Z).R.N j) → (I.rec7 l Z).host.E) r)) ∈ Formalism.UG.latS (F := (I.rec7 l Z).host.F) (v.adicCompletion (I.rec7 l Z).host.F) (intV (I.rec7 l Z).host.E v) (Submodule.span (𝓞 (I.rec7 l Z).host.E) (dualSet ((sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →ₐ[(I.rec7 l Z).host.F] (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) j hj) (A.K j hj b).lev.Lb)) := by
    rw [hsp]
    refine Submodule.subset_span ⟨Pi.single s 1, ?_, rfl⟩
    rw [SetLike.mem_coe, Formalism.L2.Col.rll_mem_dLat]
    refine ⟨fun i _ => ?_, ?_⟩
    · by_cases h : i = s
      · subst h; rw [Pi.single_eq_same]; exact one_mem _
      · rw [Pi.single_eq_of_ne h]; exact zero_mem _
    · by_cases h : Formalism.L2.Col.lastIdx ((I.rec7 l Z).R.N j) = s
      · rw [h, Pi.single_eq_same, mul_one]; exact ⟨sg At.piU, rfl⟩
      · rw [Pi.single_eq_of_ne h, mul_zero]; exact zero_mem _
  have key := hT.2 _ hy
  convert key using 1
  funext r
  have hm : ((Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) κ'.1 : GL _ _) : Matrix _ _ _) = (κ'.1.1).map (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) := rfl
  rw [Pi.sub_apply, hm, hκ']
  congr 1
  · simp [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.map_apply]
  · simp [Pi.single_apply, Matrix.one_apply]

end
