import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceFormLelongCompact
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceIdeal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceComponents
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceFormLelongCompactLimit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem SliceFormLelongCompact.proof (hSt : StokesOnVariety.Statement) (hLI : LogIntegrable.Statement)
    (hPL : PoincareLelong.Statement) (hCM : ChartMassCompact.Statement) (hI : SliceIdeal.Statement)
    (hC : SliceComponents.Statement) : SliceFormLelongCompact.Statement := by
  intro n e h W F u' ℓ f hW hF hu hℓ hℓP hf hfc
  obtain ⟨hprime, hdim, huS⟩ := hI n (e + 1) W F ℓ hW hF hℓ
  obtain ⟨hinj, himg, hmult⟩ := hC n W u' ℓ hW hℓP
  have h0 : ∀ x ∈ zeroSet (W ⊔ Ideal.span {linForm ℓ - 1}), x ≠ 0 := fun x hx =>
    SliceFormLelongCompact.ne_zero_of_mem_zeroSet (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) hx
  have hsm := smoothNear_log_dualNorm_slice h W ℓ
  obtain ⟨g, hg, hgc, hgf⟩ :=
    SliceFormLelongCompact.exists_contDiff_eqOn (SheetSumMeasurable.isClosed_zeroSet _) hf hfc
  have hSP : ∀ P ∈ (divCycle W u').support,
      W ⊔ Ideal.span {linForm ℓ - 1} ≤ P ⊔ Ideal.span {linForm ℓ - 1} := by
    intro P hP
    have hm : P ⊔ Ideal.span {linForm ℓ - 1} ∈
        (W ⊔ Ideal.span {linForm ℓ - 1} ⊔ Ideal.span {linForm u'}).minimalPrimes := by
      rw [← himg]
      exact ⟨P, Finset.mem_coe.2 hP, rfl⟩
    exact le_sup_left.trans hm.1.2
  have hw : ∀ (I : Ideal (MvPolynomial (Fin n) ℂ)) (d : ℕ) (ψ : Fin d → (Fin n → ℂ) → ℝ),
      W ⊔ Ideal.span {linForm ℓ - 1} ≤ I → varInt I d f ψ = varInt I d g ψ := fun I d ψ hle =>
    SliceFormLelongCompact.varInt_congr_weight
      (fun x hx => (hgf x (SliceFormLelongCompact.zeroSet_anti hle hx)).symm) ψ
  have hsumf : ∑ P ∈ (divCycle W u').support, ((divCycle W u' P : ℕ) : ℝ) *
        varInt (P ⊔ Ideal.span {linForm ℓ - 1}) e f (fun _ x => Real.log (h.dualNorm x)) =
      ∑ P ∈ (divCycle W u').support, ((divCycle W u' P : ℕ) : ℝ) *
        varInt (P ⊔ Ideal.span {linForm ℓ - 1}) e g (fun _ x => Real.log (h.dualNorm x)) :=
    Finset.sum_congr rfl fun P hP => by rw [hw _ _ _ (hSP P hP)]
  rw [hsumf, hw (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun _ x => Real.log (h.dualNorm x)) le_rfl]
  refine Tendsto.congr (fun ε => (hw _ _ _ le_rfl).symm) ?_
  have hgS : SmoothNear (zeroSet (W ⊔ Ideal.span {linForm ℓ - 1})) g := smoothNear_of_contDiff hg
  have hlim := SliceFormLelongCompact.tendsto_varInt_fsLogReg hLI hCM h _ u' g
    (fun (_ : Fin e) x => Real.log (h.dualNorm x)) hprime hdim (huS u' hu) h0 hgS hgc (fun _ => hsm)
  have hP := hPL n e _ u' g (fun _ x => Real.log (h.dualNorm x)) hprime hdim (huS u' hu) hg hgc
    (fun _ => hsm)
  have hS2 := hSt n e _ g (fun x => Real.log (h.dualNorm x)) (fun _ x => Real.log (h.dualNorm x)) hprime
    hdim hgS hsm (fun _ => hsm) (Or.inl hgc)
  have hcons : (vecCons (fun x => Real.log (h.dualNorm x)) fun (_ : Fin e) x =>
      Real.log (h.dualNorm x)) = fun _ x => Real.log (h.dualNorm x) :=
    funext fun i => Fin.cases rfl (fun _ => rfl) i
  rw [hcons] at hS2
  have hsum : ∑ P ∈ (divCycle W u').support,
      (localMult (W ⊔ Ideal.span {linForm ℓ - 1} ⊔ Ideal.span {linForm u'})
        (P ⊔ Ideal.span {linForm ℓ - 1}) : ℝ) *
        varInt (P ⊔ Ideal.span {linForm ℓ - 1}) e g (fun _ x => Real.log (h.dualNorm x)) =
      ∑ P ∈ (divCycle W u').support, ((divCycle W u' P : ℕ) : ℝ) *
        varInt (P ⊔ Ideal.span {linForm ℓ - 1}) e g (fun _ x => Real.log (h.dualNorm x)) :=
    Finset.sum_congr rfl fun P hP => by rw [hmult P hP]
  rw [hP, ← himg, finsum_mem_image hinj, finsum_mem_coe_finset, hsum, ← hS2] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hSt n e _ g (fsLogReg h u' ε) _ hprime hdim hgS
    ⟨{0}ᶜ, isOpen_compl_singleton, fun x hx => h0 x hx, contDiffOn_fsLogReg h u' hε⟩ (fun _ => hsm)
    (Or.inl hgc)).symm

end GroundTheory.Heights₂.Heights
