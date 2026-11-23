import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClsOmNonneg
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPairsWeightMulClassLeMulSum
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagFrameVectorMemCommonSubspace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrEqvEquivalence
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvVolPos
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EmbeddedDatumOfTermDefiniteSpaceStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsStarStableIdealAbsorbingMinorsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHostFieldArithmeticConditionsProofStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EquivFramesSameSecondLatticeFiberProofStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameClassTermCountLeCardAutStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermDeterminedByFrameClassAndIsometryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsOverRowCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdaptedNormalFormRelevantTermProofStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdaptedNormalFormNormsMinorsEqLabelProofStatement
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm GlobalTheory.TypeAsm.PerRow
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeAsm.PerRow

theorem sum_pairs_le_classes_pf : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ →
    ∀ (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W),
    GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype → ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V) (h : GTu Y u → (W ≃ₗ[D.host.E] W)),
    (∀ t ∈ relSet Y u, GlobalTheory.DegAsm.IsH (F0 X u) (Ft t) W.subtype t.lin (h t)) → ∀ (Sf : Finset (GTu Y u × GTu Y u)),
    (∀ p ∈ Sf, p ∈ (Y.tO u u).allPairs (relSet Y u) ∧ p.1.lam = Λ) →
    (∀ p ∈ Sf, ∀ q ∈ Sf, h p.1 * (h p.2)⁻¹ = h q.1 * (h q.2)⁻¹) →
    ∑ p ∈ Sf, wRow D (X.Fu u) p.1.lam' * (omT p.1 * omT p.2) ≤
      (∑ b ∈ Sf.image (fun p => frCls Λ p.1), clsOm Y u Λ b) * ∑ b ∈ Sf.image (fun p => frCls Λ p.2), clsOm Y u Λ b := by
  intro D large₂ X Y u hS W HW he Λ h hh Sf hSf hη
  obtain ⟨hK, -⟩ := GlobalTheory.T.unitaryHostFieldArithmeticConditions D large₂ hS
  have hlam : ∀ p ∈ Sf, p.2.lam = Λ ∧ p.2.lam' = p.1.lam' := by
    intro p hp
    obtain ⟨hl, hl', -⟩ := GlobalTheory.T.termsOverRow_compatible D X Y u p ⟨trivial, trivial, (hSf p hp).1.2.2⟩
    exact ⟨hl.symm.trans (hSf p hp).2, hl'.symm⟩
  have hL : ∑ p ∈ Sf, wRow D (X.Fu u) p.1.lam' * (omT p.1 * omT p.2) =
      ∑ p ∈ Sf, wRow D (X.Fu u) p.1.lam' * (clsOm Y u Λ (frCls Λ p.1) * clsOm Y u Λ (frCls Λ p.2)) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [clsOm_frCls hK Λ p.1 (hSf p hp).2, clsOm_frCls hK Λ p.2 (hlam p hp).1]
  rw [hL]
  generalize hT1 : Sf.image (fun p => frCls Λ p.1) = T₁
  generalize hT2 : Sf.image (fun p => frCls Λ p.2) = T₂
  refine GlobalTheory.sum_pairs_weight_mul_class_le_mul_sum (GTu Y u) _ Sf (frCls Λ)
    (fun t => wRow D (X.Fu u) t.lam') (clsOm Y u Λ) T₁ T₂ ?_ (clsOm_nonneg Y u Λ hK) ?_ ?_ ?_
  · intro t
    show 0 ≤ wRow D (X.Fu u) t.lam'
    unfold wRow; positivity
  · intro p hp
    subst hT1 hT2
    exact ⟨Finset.mem_image.2 ⟨p, hp, rfl⟩, Finset.mem_image.2 ⟨p, hp, rfl⟩⟩
  · intro p hp q hq h1 hc
    have hrel2 : p.2 ∈ relSet Y u := (hSf p hp).1.2.1
    have hrelq : q.2 ∈ relSet Y u := (hSf q hq).1.2.1
    have hhe : h p.2 = h q.2 := by
      have e := hη p hp q hq
      rw [h1] at e
      have e2 := congrArg (fun g => (h q.1)⁻¹ * g) e
      simp only [inv_mul_cancel_left] at e2
      exact inv_injective e2
    have hfe := (frCls_eq_iff hK Λ p.2 q.2).1 hc
    have hl : p.2.lam = q.2.lam := ((hlam p hp).1).trans ((hlam q hq).1).symm
    obtain ⟨N, hN, -⟩ := GlobalTheory.T.exists_adaptedNormalForm_relevantTerm D large₂ X Y u hS p.2 hrel2
    have hfe' : GlobalTheory.DegAsm.FrEqv (F0 X u) p.2.lam (Ft p.2) (Ft q.2) := by rw [(hlam p hp).1]; exact hfe
    have := GlobalTheory.T.term_determined_by_frameClass_and_isometry D large₂ X Y u hS W HW he p.2 q.2 ⟨N, hN⟩ hl hfe' (h p.2) (hh p.2 hrel2)
      (by rw [hhe]; exact hh q.2 hrelq)
    exact Prod.ext h1 this
  · intro b
    have gen : ∀ s : Finset (GTu Y u), (∀ t ∈ s, t.lam = Λ ∧ frCls Λ t = b) →
        ∑ a ∈ s, wRow D (X.Fu u) a.lam' ≤ 1 := by
      intro s hmem
      rcases s.eq_empty_or_nonempty with he0 | ⟨t₀, ht₀⟩
      · rw [he0, Finset.sum_empty]; exact zero_le_one
      obtain ⟨hl0, hb0⟩ := hmem t₀ ht₀
      have hrel : ∀ t ∈ s, t₀.lam = t.lam ∧ GlobalTheory.DegAsm.FrEqv (F0 X u) t₀.lam (Ft t₀) (Ft t) := by
        intro t ht
        obtain ⟨hl, hb⟩ := hmem t ht
        refine ⟨hl0.trans hl.symm, ?_⟩
        rw [hl0]
        exact (frCls_eq_iff hK Λ t₀ t).1 (hb0.trans hb.symm)
      have hw : ∀ t ∈ s, wRow D (X.Fu u) t.lam' = wRow D (X.Fu u) t₀.lam' := by
        intro t ht
        obtain ⟨hl, hf⟩ := hrel t ht
        rw [(GlobalTheory.T.equivFramesSameSecondLatticeFiber_proof D large₂ X Y u hS t₀ t hl hf).1]
      rw [Finset.sum_congr rfl hw, Finset.sum_const, nsmul_eq_mul]
      exact GlobalTheory.T.frameClass_termCount_le_card_aut D large₂ X Y u hS t₀ s hrel
    refine gen _ fun t ht => ?_
    simp only [Finset.mem_filter, Finset.mem_image] at ht
    obtain ⟨⟨p, hp, rfl⟩, ht2⟩ := ht
    exact ⟨(hSf p hp).2, ht2⟩

end GlobalTheory.TypeAsm.PerRow
