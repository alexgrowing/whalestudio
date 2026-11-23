import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleIndexBoundAllPowers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLatInOfIndexLe

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen Formalism.MainNotions.IntegralHeckeForms
open scoped TensorProduct

namespace GlobalTheory.ExportFromInputs

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

open GlobalTheory.TwistInputsTest GlobalTheory.TwAll

theorem twistModule_all_character_powers_of_admissible (bkP : BKPh X) (E : ExpDat Y) (N0 : X.Tw → ℕ) (h2 : TwAll.admissibleIndexBoundAllPowers Y bkP N0) (h3 : IsotypicPartsInternalDirectSum Y E)
    (h5 : GroupAlgebraIntegrality Y) (h7 : admT4 Y E) (h10 : TwistedSeriesSpecialisation Y) (h11 : GoodLatticePoints Y) (i : X.Tw) (hi : X.NonzeroIndexPlace i) :
    TwAll.goodTwistExistsAllCoprimePowers Y bkP E N0 i := by
  classical
  intro hs eps' he hF S hS A
  choose z hz using fun b => (h5 i hi b).1
  have hAB := fun j hj b => abHyp_fam Y E i hi j hj b z (hz b) S h3 h5 h11 (hF j hj b) (hS j hj b)
  obtain ⟨Q, k, ψ₀, hall⟩ := h2 i hi hs eps' he (fam Y i z S) hAB (levs Y i S ∪ A)
  refine ⟨Q, k, ψ₀, fun n hn => ?_⟩
  have hn' := hall n hn
  generalize ψ₀ ^ n = ψ' at hn' ⊢
  obtain ⟨hok, ha, hc, hd, M, χ, hχ, epsB, h0, hsum, H⟩ := hn'
  have key : ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, _ := fun j hj b => by
    obtain ⟨htw, hu, hdis⟩ := twOK_of_psiOk i _ Q k ψ' hok b
    refine export_at Y E i hi j hj b (S j b) h3 h7 (hF j hj b) (hS j hj b) k Q _ htw hu (epsB j b) ?_
    intro T hT hle
    obtain ⟨-, hfg, hsp, -⟩ := h3 i hi j hj b
    have hA : (fam Y i z S).A j b = AO Y i j b := zO_eq Y i j b _ (hz b)
    have hTh : (fam Y i z S).Th j b = (Th Y i j b (SgJ Y E i j b)).map (AO Y i j b) := by
      rw [← (hS j hj b).2.2, RFam.Th, hA]; rfl
    rw [← hTh]
    refine H j hj b T ?_ fun a ha => ?_
    · have : Submodule.span (FractionRing (X.O i)) ((fam Y i z S).B j b : Set (Y.Fm i j b)) = V0 Y i j b :=
        span_of_isLatIn (isLatIn_B Y i j b hfg hsp)
      rw [this]; exact hT
    · have ha' : a ∈ S j b := ha
      rw [hχ, psiAt_comp] at htw hle
      have hlev : Disjoint Q (Y.lev i j b a) := by
        refine hdis.mono_right (le_trans ?_ Finset.subset_union_left)
        intro v hv
        simp only [levs, Finset.mem_biUnion]
        exact ⟨j, hj, b, Finset.mem_univ _, a, ha', hv⟩
      rw [hA]
      refine hle ⟨_, ?_, rfl⟩
      refine Submodule.span_mono ?_ (h10 i hi j hj b k Q M _ htw a hlev)
      exact Set.biUnion_subset_biUnion_left (Set.singleton_subset_iff.2 ((hS j hj b).1 ha'))
  exact ⟨hok, ⟨epsB, h0, hsum, fun j hj b => (key j hj b).1⟩, fun j hj b => (key j hj b).2, ha, hc, hd⟩

end GlobalTheory.ExportFromInputs

open GlobalTheory.TwAll in

theorem GlobalTheory.exportAll_of_inputs :
    ∀ (D : Formalism.BasicNotions.D7) (bkP : Formalism.MainNotions.BlochKatoReduction.BK D) (E : Formalism.MainNotions.IntegralHeckeForms.XD D) (N0 : D.ntw.Tw → ℕ),
      Formalism.MainNotions.IntegralHeckeForms.admitted D bkP E N0 → admissibleIndexBoundAllPowers D.nexp (Formalism.MainNotions.BlochKatoReduction.pin bkP) N0 →
      ∀ i, D.ntw.NonzeroIndexPlace i → goodTwistExistsAllCoprimePowers D.nexp (Formalism.MainNotions.BlochKatoReduction.pin bkP) E N0 i := by
  rintro D bkP E N0 ⟨-, -, h3, -, h5, h7, -, -, h10, h11⟩ h2 i hi
  exact GlobalTheory.ExportFromInputs.twistModule_all_character_powers_of_admissible D.nexp _ E N0 h2 h3 h5 h7 h10 h11 i hi

end
