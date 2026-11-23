import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceChartOfSplitIdempotent

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitIdemDict

open GlobalTheory.AdelicU

variable {D : D7} {v : FinPl D}

theorem exists_eq_splitProj (φ : SplitProj D v) :
    ∃ τ : D.host.E →ₐ[D.host.F] Fv D.host.F v, φ = splitProj τ := by
  refine ⟨(φ.restrictScalars D.host.F).comp Algebra.TensorProduct.includeRight, ?_⟩
  refine AlgHom.ext fun y => ?_
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x =>

    have hax : a ⊗ₜ[D.host.F] x = a • ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] x) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [splitProj_tmul, hax, map_smul, smul_eq_mul]
    rfl
  | add y z hy hz => rw [map_add, map_add, hy, hz]

theorem isProjAt_iff (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (PP : Formalism.L2.DIV.Pl D.host.E) :
    IsProjAt (D := D) (v := v) (splitProj τ) PP ↔ PP = splitPrime τ := by

  have hred : ∀ x : 𝓞 D.host.E, rdQ (D := D) (v := v) (splitProj τ) (x : D.host.E) = τ x := fun x => by
    simp only [rdQ, splitProj_tmul, one_mul]
  unfold IsProjAt
  constructor
  · intro h
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    rw [h x, hred, mem_splitPrime]
  · rintro rfl x
    rw [hred, mem_splitPrime]

theorem sigR_compFin {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (v : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E) :
    sigR _ σ (compFin F E v z) = compFin F E v (sigR _ σ z) := by

  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => simp [sigR, compFin]
  | add y z hy hz => simp only [map_add, hy, hz]

theorem compFin_cA (z : AE D) :
    sigR _ D.sp.cm.sig (compFin D.host.F D.host.E v z) = compFin D.host.F D.host.E v (cA D z) := by

  have h := sigR_compFin D.sp.cm.sig v z
  exact h

private theorem idem_inl_eq_tensAt_one (D : D7) (v : FinPl D) :
    GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.idem D (.inl v) = GlobalTheory.EmbChart.tensAt D.host.E v 1 := by
  rw [Algebra.TensorProduct.one_def, GlobalTheory.EmbChart.tensAt_tmul, GlobalTheory.EmbChart.atPlace_apply]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.idem, Algebra.TensorProduct.algebraMap_apply]
  rfl

theorem eq_idem {τ : D.host.E →ₐ[D.host.F] Fv D.host.F v} {e : AE D} (he : IsIdemOf (D := D) (v := v) (splitProj τ) e) :
    e = GlobalTheory.EmbChart.idem τ := by
  obtain ⟨⟨hee, hce, -⟩, hsum, hone⟩ := he
  have hone' : splitProj τ (compFin D.host.F D.host.E v e) = 1 := hone
  have hε := idem_inl_eq_tensAt_one D v

  have h1 : e = GlobalTheory.EmbChart.tensAt D.host.E v (compFin D.host.F D.host.E v e) := by
    calc e = GlobalTheory.EmbChart.tensAt D.host.E v 1 * e := by
          rw [← hε, ← hsum, add_mul, hee, mul_comm (cA D e) e, hce, add_zero]
      _ = _ := by rw [GlobalTheory.EmbChart.tensAt_mul_right, one_mul]
  have hc : cA D e = GlobalTheory.EmbChart.tensAt D.host.E v 1 - e := by
    rw [← hε, ← hsum, add_sub_cancel_left]

  have h2 : compFin D.host.F D.host.E v e = splitIdem (isCMExt_host D) τ := by
    apply split_ext (isCMExt_host D) τ
    · rw [splitProj_splitIdem, hone']
    · rw [splitProj_comp_splitIdem, splitProj_comp, compFin_cA, hc, map_sub, GlobalTheory.EmbChart.compFin_tensAt,
        map_sub, map_one, hone', sub_self]
  rw [h1, h2]
  rfl

private theorem eq_of_isIdemAt_of_isIdemAt' {e : AE D} {P Q : HeightOneSpectrum (𝓞 D.host.E)}
    (hP : Formalism.L2.NTheta.IsIdemAt e P) (hQ : Formalism.L2.NTheta.IsIdemAt e Q) : P = Q := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  by_cases hx : x = 0
  · subst hx
    exact ⟨fun _ => Q.asIdeal.zero_mem, fun _ => P.asIdeal.zero_mem⟩
  · exact (hP.2 x hx).trans (hQ.2 x hx).symm

theorem exists_emb {e : AE D} {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt e PP) :
    ∃ (v : FinPl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v), IsIdemOf (D := D) (v := v) (splitProj τ) e ∧ PP = splitPrime τ := by
  obtain ⟨⟨hee, hce, w, ε, ⟨α, rfl, hαw, hαo⟩, hsum⟩, -⟩ := id he

  have hα : α = singleV D.host.F w 1 := by
    classical
    apply RestrictedProduct.ext
    intro u
    by_cases hu : u = w
    · subst hu
      rw [singleV, RestrictedProduct.single_eq_same]
      exact hαw
    · rw [singleV, RestrictedProduct.single_eq_of_ne _ _ hu]
      exact hαo u hu
  subst hα
  have hsum' : e + cA D e = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.idem D (.inl w) := hsum
  have hε := idem_inl_eq_tensAt_one D w

  set y := compFin D.host.F D.host.E w e with hy
  have hy1 : y * y = y := by rw [hy, ← map_mul, hee]
  have hy2 : y + sigR _ D.sp.cm.sig y = 1 := by
    rw [hy, compFin_cA, ← map_add, hsum', hε, GlobalTheory.EmbChart.compFin_tensAt]
  have hσy : sigR _ D.sp.cm.sig y = 1 - y := eq_sub_of_add_eq' hy2

  have hnf : ¬ IsField (Fv D.host.F w ⊗[D.host.F] D.host.E) := by
    intro hf
    by_cases hy0 : y = 0
    · rw [hy0, map_zero, add_zero] at hy2
      exact hf.exists_pair_ne.elim fun a ha => ha.elim fun b hab =>
        hab (by rw [← mul_one a, ← mul_one b, ← hy2, mul_zero, mul_zero])
    · obtain ⟨z, hz⟩ := hf.mul_inv_cancel hy0
      have hy1' : y = 1 := by
        calc y = y * (y * z) := by rw [hz, mul_one]
          _ = y * y * z := by rw [mul_assoc]
          _ = 1 := by rw [hy1, hz]
      rw [hy1', map_one] at hy2
      have h10 : (1 : Fv D.host.F w ⊗[D.host.F] D.host.E) = 0 := add_left_cancel (hy2.trans (add_zero 1).symm)
      exact hf.exists_pair_ne.elim fun a ha => ha.elim fun b hab =>
        hab (by rw [← mul_one a, ← mul_one b, h10, mul_zero, mul_zero])
  have hfin : Module.finrank (Fv D.host.F w) (Fv D.host.F w ⊗[D.host.F] D.host.E) = 2 := by
    rw [Module.finrank_baseChange]
    exact (isCMExt_host D).2.2.1
  obtain ⟨φ₀⟩ := nonempty_algHom_of_not_isField hfin hnf
  obtain ⟨τ₀, rfl⟩ := exists_eq_splitProj (D := D) (v := w) φ₀

  have hτ : ∃ τ : D.host.E →ₐ[D.host.F] Fv D.host.F w, splitProj τ y = 1 := by
    have hp : IsIdempotentElem (splitProj τ₀ y) := by
      unfold IsIdempotentElem
      rw [← map_mul, hy1]
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp hp with h0 | h1
    · refine ⟨τ₀.comp D.sp.cm.sig, ?_⟩
      rw [splitProj_comp, hσy, map_sub, map_one, h0, sub_zero]
    · exact ⟨τ₀, h1⟩
  obtain ⟨τ, hτ⟩ := hτ
  have hi : IsIdemOf (D := D) (v := w) (splitProj τ) e := ⟨he.1, hsum', hτ⟩
  refine ⟨w, τ, hi, ?_⟩

  have he' := he
  rw [eq_idem hi] at he'
  exact eq_of_isIdemAt_of_isIdemAt' he' (GlobalTheory.EmbChart.isIdemAt_idem τ)

theorem idem_dictionary : ∀ (D : D7), (∀ (e : AE D) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e PP → ∃ (v : FinPl D) (φ : SplitProj D v), IsIdemOf φ e ∧ IsProjAt φ PP) ∧ ∀ (v : FinPl D) (φ : SplitProj D v) (PP : Formalism.L2.DIV.Pl D.host.E), IsProjAt φ PP → PP.asIdeal.under (𝓞 D.host.F) = v.asIdeal ∧ (∀ PP', IsProjAt φ PP' → PP' = PP) ∧ ∀ e, IsIdemOf φ e → Formalism.L2.NTheta.IsIdemAt e PP ∧ (∀ e', Formalism.L2.NTheta.IsIdemAt e' PP → e' = e) ∧ ∀ φ' : SplitProj D v, IsIdemOf φ' e → φ' = φ := by
  intro D
  refine ⟨fun e PP he => ?_, fun v φ PP hφ => ?_⟩
  · obtain ⟨w, τ, hi, rfl⟩ := exists_emb he
    exact ⟨w, splitProj τ, hi, (isProjAt_iff τ _).2 rfl⟩
  · obtain ⟨τ, rfl⟩ := exists_eq_splitProj φ
    obtain rfl : PP = splitPrime τ := (isProjAt_iff τ PP).1 hφ
    refine ⟨(splitPrime_liesOver τ).over.symm, fun PP' h' => (isProjAt_iff τ PP').1 h', fun e he => ?_⟩
    obtain rfl := eq_idem he
    refine ⟨GlobalTheory.EmbChart.isIdemAt_idem τ, fun e' he' => ?_, fun φ' hφ' => ?_⟩
    ·
      obtain ⟨w, τ', hi', hP'⟩ := exists_emb he'
      have hw : w = v := by
        calc w = (splitPrime τ').under (𝓞 D.host.F) := (splitPrime_under τ').symm
          _ = (splitPrime τ).under (𝓞 D.host.F) := by rw [hP']
          _ = v := splitPrime_under τ
      subst hw
      rw [eq_idem hi', splitPrime_injective (isCMExt_host D) hP'.symm]
    ·
      obtain ⟨τ'', rfl⟩ := exists_eq_splitProj φ'
      have h2 := GlobalTheory.EmbChart.isIdemAt_idem τ''
      rw [← eq_idem hφ'] at h2
      rw [splitPrime_injective (isCMExt_host D) (eq_of_isIdemAt_of_isIdemAt' h2 (GlobalTheory.EmbChart.isIdemAt_idem τ))]

end GlobalTheory.SplitIdemDict

end
