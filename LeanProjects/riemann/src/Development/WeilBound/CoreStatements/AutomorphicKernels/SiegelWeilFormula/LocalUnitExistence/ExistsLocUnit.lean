import Development.WeilBound.ThetaLifts.LatticeBasics.FrameConj
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationAlgebraMapEqOfInertPlace

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace PositivityTheory.SiegelWeilFormula.Ldexb.UnitA

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sig_sig (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact τ.injective (by rw [h.2.2.2, h.2.2.2, star_star])

theorem exists_xi (h : IsCMExt F E σ) : ∃ ξ : E, ξ ≠ 0 ∧ σ ξ = -ξ := by
  by_cases hx : ∃ x : E, σ x ≠ x
  · obtain ⟨x, hx⟩ := hx
    refine ⟨x - σ x, sub_ne_zero.2 (Ne.symm hx), ?_⟩
    rw [map_sub, sig_sig h]; ring
  · push Not at hx
    exfalso
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have hr : ComplexEmbedding.IsReal τ := by
      rw [ComplexEmbedding.isReal_iff]
      ext x
      rw [ComplexEmbedding.conjugate_coe_eq]
      have := h.2.2.2 τ x
      rw [hx] at this
      exact this.symm
    have := h.2.1
    exact (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex _)) (InfinitePlace.isReal_mk_iff.2 hr)

omit [NumberField E] in
theorem compFin_cA (v : Pl F) (z : AE F E) : compFin F E v (cA σ z) = sigR (Fv F v) σ (compFin F E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x => rfl

omit [NumberField E] in
theorem compInf_cA (w : InfinitePlace F) (z : AE F E) :
    compInf F E w (cA σ z) = sigR w.Completion σ (compInf F E w z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x => rfl

omit [NumberField E] in
theorem compFin_inclR (v : Pl F) (x : E) : compFin F E v (inclR (AF F) x) = inclR (Fv F v) x := by
  change Algebra.TensorProduct.map _ _ ((1 : AF F) ⊗ₜ[F] x) = (1 : Fv F v) ⊗ₜ[F] x
  simp

omit [NumberField E] in
theorem compInf_inclR (w : InfinitePlace F) (x : E) : compInf F E w (inclR (AF F) x) = inclR w.Completion x := by
  change Algebra.TensorProduct.map _ _ ((1 : AF F) ⊗ₜ[F] x) = (1 : w.Completion) ⊗ₜ[F] x
  simp

omit [NumberField F] [NumberField E] in
theorem sigR_inclR (R : Type) [CommRing R] [Algebra F R] (x : E) : sigR R σ (inclR R x) = inclR R (σ x) := rfl

theorem exists_S (ξ : E) : ∃ S : Finset (Pl F), ∀ v ∉ S,
    inclR (Fv F v) ξ ∈ intLoc F E v ∧ inclR (Fv F v) ξ⁻¹ ∈ intLoc F E v := by
  have h := (GlobalTheory.ThK.Dbl.Frame.ae_locInt (F := F) ξ).and (GlobalTheory.ThK.Dbl.Frame.ae_locInt (F := F) ξ⁻¹)
  refine ⟨(Filter.eventually_cofinite.1 h).toFinset, fun v hv => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hv
  exact ⟨hv.1.mem, hv.2.mem⟩

theorem exists_locUnit {B : Base F E} (hB : B.IsGood σ) {ξ : E} (hξ : ξ ≠ 0) (hσξ : σ ξ = -ξ) (v : Pl F) :
    ∃ u : (Fv F v ⊗[F] E)ˣ, (u : Fv F v ⊗[F] E) ∈ intLoc F E v ∧
      ((u⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ intLoc F E v ∧ sigR (Fv F v) σ u = -(u : Fv F v ⊗[F] E) := by
  have hc := hB.cm
  rcases GlobalTheory.KFinLoc.split_or_inert F E σ B hB v with ⟨⟨τ⟩⟩ | ⟨w, hw⟩
  · set e := splitAlgEquiv hc τ
    have hu : e.symm (1, -1) * e.symm (1, -1) = 1 := by
      rw [← map_mul, Prod.mk_mul_mk, one_mul, neg_mul_neg, mul_one]
      exact map_one _
    let u : (Fv F v ⊗[F] E)ˣ := ⟨e.symm (1, -1), e.symm (1, -1), hu, hu⟩
    have hm : e.symm (1, -1) ∈ intLoc F E v := (mem_intLoc_iff_split hc τ).2
      ⟨by rw [splitProj_symm]; exact one_mem _, by rw [splitProj_comp_symm]; exact neg_mem (one_mem _)⟩
    refine ⟨u, hm, hm, ?_⟩
    apply e.injective
    change e (sigR (Fv F v) σ (e.symm (1, -1))) = e (-(e.symm (1, -1)))
    rw [splitAlgEquiv_sigR, map_neg, AlgEquiv.apply_symm_apply]
    simp
  · have h : w.under (𝓞 F) = v := (GlobalTheory.LFun.InertChart.under_eq_iff hw w).2 rfl
    obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer F v
    have hv0 : w.valuation E ξ ≠ 0 := (Valuation.ne_zero_iff _).2 hξ
    set m := WithZero.log (w.valuation E ξ)
    set z : E := algebraMap F E (π ^ m) * ξ with hzdef
    have hz : w.valuation E z = 1 := by
      rw [hzdef, map_mul, GlobalTheory.InertValRestr.valuation_algebraMap_of_isInertAt F E v w hw, map_zpow₀, hπ,
        ← WithZero.exp_log hv0, ← WithZero.exp_zsmul, ← WithZero.exp_add]
      simp [m]
    have hz0 : z ≠ 0 := by
      intro h0; rw [h0, map_zero] at hz; exact zero_ne_one hz
    have hint : ∀ y : E, w.valuation E y = 1 → inclR (Fv F v) y ∈ intLoc F E v := by
      intro y hy
      rw [GlobalTheory.LFun.InertChart.mem_intLoc_iff hw h]
      change GlobalTheory.LFun.toCompl h ((1 : Fv F v) ⊗ₜ[F] y) ∈ _
      rw [GlobalTheory.LFun.toCompl_tmul, map_one, one_mul]
      change _ ∈ HeightOneSpectrum.adicCompletionIntegers E w
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w y
      exact (this.trans hy).le
    have h1 : inclR (F := F) (Fv F v) z * inclR (F := F) (Fv F v) z⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hz0, map_one]
    have h2 : inclR (F := F) (Fv F v) z⁻¹ * inclR (F := F) (Fv F v) z = 1 := by rw [← map_mul, inv_mul_cancel₀ hz0, map_one]
    refine ⟨⟨inclR (Fv F v) z, inclR (Fv F v) z⁻¹, h1, h2⟩, hint z hz, hint z⁻¹ (by rw [map_inv₀, hz, inv_one]), ?_⟩
    change sigR (Fv F v) σ (inclR (Fv F v) z) = -inclR (Fv F v) z
    rw [sigR_inclR, hzdef, map_mul, AlgHom.commutes, hσξ, mul_neg, map_neg]

end PositivityTheory.SiegelWeilFormula.Ldexb.UnitA

end
