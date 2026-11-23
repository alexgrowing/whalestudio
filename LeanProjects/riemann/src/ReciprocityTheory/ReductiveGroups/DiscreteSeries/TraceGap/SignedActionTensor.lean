import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.CoordSpan
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.ExistsNonzeroPhysicalHighestWeightVectorTensFock
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFPrimeB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.VNormSqLowKSubRootLt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CsqDdPt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CARUnit

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ}

section Gen

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem mem_highestWeightSub_iff (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ W) (γ : Fin n → ℝ) (x : W) :
    x ∈ khwSub ε F γ ↔ IsKHWVec ε F γ x := by
  simp only [khwSub, IsKHWVec, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun a b hab he => h2 a b ⟨hab, he⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun a b h => h2 a b h.1 h.2⟩

theorem support_subset_physicalModes {ε : Fin n → Bool} {z : TensorProduct ℂ W (Fock n)} (hz : z ∈ physicalSubspace ε)
    {s : Finset (Fin (n * n))} (hs : tcoef ((fockBasis n).coord s) z ≠ 0) : s ⊆ lfPhysModes ε := by
  intro m hm
  by_contra hnot
  obtain ⟨x, rfl⟩ := finProdFinEquiv.surjective m
  have hx : ¬ (ε x.1 = true ∧ ε x.2 = false) := fun h => hnot ((lf_mem_phys ε x.1 x.2).2 h)
  have h0 : cmT (N := W) x.1 x.2 z = 0 := by
    simp only [physicalSubspace, Submodule.mem_iInf, LinearMap.mem_ker] at hz
    exact hz x.1 x.2 hx
  have h1 : LinearMap.lTensor W (cpFock x.1 x.2 ∘ₗ cmFock x.1 x.2) z = 0 := by
    rw [LinearMap.lTensor_comp, LinearMap.comp_apply]
    have : LinearMap.lTensor W (cmFock x.1 x.2) z = 0 := h0
    rw [this, map_zero]
  have h2 := congrArg (tcoef ((fockBasis n).coord s)) h1
  rw [tcoef_lTensor, gc_coord_num x s, if_pos hm, one_smul, map_zero] at h2
  exact hs h2

theorem signedAction_tensor (ε : Fin n → Bool) (a b : Fin n) :
    sgE ε (cpT (N := W) (n := n)) cmT a b = LinearMap.lTensor W (sgE ε cpFock cmFock a b) := by
  apply TensorProduct.ext'
  intro m f
  unfold sgE
  split_ifs <;> simp [cpT, cmT, LinearMap.sum_apply, TensorProduct.tmul_sum]

end Gen

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

theorem line_exists {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : StrictAnti lam) {E : Fin n → Fin n → Module.End ℂ M}
    (hE : IsGlRep E) {W : Submodule ℂ M} (hW : IsKIrrHW ε E (lowK ε lam) W) :
    ∃ z ∈ lineSub ε E lam W, z ≠ 0 := by
  obtain ⟨x, hxT, hxP, hx0, hxK⟩ := lowFock_exists ε hE hlam hW
  exact ⟨x, ⟨⟨(mem_highestWeightSub_iff _ _ _ x).2 hxK, hxT⟩, hxP⟩, hx0⟩

theorem tensorCoeff_diagAction (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (a : Fin n)
    (s : Finset (Fin (n * n))) (z : TensorProduct ℂ M (Fock n)) :
    tcoef ((fockBasis n).coord s) (diagE ε (eT E) cpT cmT a a z) =
      E a a (tcoef ((fockBasis n).coord s) z) + ((fockWt ε s a : ℝ) : ℂ) • tcoef ((fockBasis n).coord s) z := by
  rw [diagE, LinearMap.add_apply, map_add, signedAction_tensor, eT, tcoef_map_left, tcoef_lTensor, coord_comp_sg, tcoef_smul]

theorem line_deg {ε : Fin n → Bool} {lam : Fin n → ℝ} {E : Fin n → Fin n → Module.End ℂ M}
    (hE : IsGlRep E) (hU : IsInfUnitary ε E) {W : Submodule ℂ M} (hW : IsKIrrHW ε E (lowK ε lam) W)
    {z : TensorProduct ℂ M (Fock n)} (hz : z ∈ lineSub ε E lam W) :
    z ∈ LinearMap.range (TensorProduct.map W.subtype (⋀[ℂ]^(sDeg ε) (Fin n × Fin n → ℂ)).subtype) := by
  obtain ⟨⟨hK, hT⟩, hP⟩ := hz
  replace hK := (mem_highestWeightSub_iff _ _ _ z).1 hK
  have hdeg : ∀ s, tcoef ((fockBasis n).coord s) z ≠ 0 → s.card = sDeg ε := by
    intro s hs
    have hsub := support_subset_physicalModes hP hs
    have hmem : tcoef ((fockBasis n).coord s) z ∈ W := tcoef_mem hT _
    have hEa : ∀ a, E a a (tcoef ((fockBasis n).coord s) z) =
        (((gaW ε lam a - fockWt ε s a : ℝ) : ℂ)) • tcoef ((fockBasis n).coord s) z := by
      intro a
      have h := congrArg (tcoef ((fockBasis n).coord s)) (hK.1 a)
      rw [tensorCoeff_diagAction, map_smul] at h
      rw [Complex.ofReal_sub, sub_smul, ← h]
      abel
    have hZ := zPlus_V hE hW _ hmem
    have hZ' : zPlus ε E (tcoef ((fockBasis n).coord s) z) =
        (∑ c ∈ plusIdx ε, (((gaW ε lam c - fockWt ε s c : ℝ) : ℂ))) • tcoef ((fockBasis n).coord s) z := by
      unfold zPlus
      rw [LinearMap.sum_apply, Finset.sum_smul]
      exact Finset.sum_congr rfl fun c _ => hEa c
    rw [hZ] at hZ'
    have hc : (∑ c ∈ plusIdx ε, ((lowK ε lam c : ℝ) : ℂ)) = ∑ c ∈ plusIdx ε, (((gaW ε lam c - fockWt ε s c : ℝ) : ℂ)) :=
      smul_left_injective ℂ hs hZ'
    have hr : (∑ c ∈ plusIdx ε, lowK ε lam c) = ∑ c ∈ plusIdx ε, (gaW ε lam c - fockWt ε s c) := by
      exact_mod_cast hc
    rw [Finset.sum_sub_distrib, gc_plus_sum hsub] at hr
    have h2 := sDeg_eq_sum ε
    have h3 : (sDeg ε : ℝ) = (s.card : ℝ) := by
      rw [h2]
      have : ∀ c, (rhoHol ε - rhoN ε) c = gaW ε lam c - lowK ε lam c := by
        intro c
        simp only [gaW, lowK, Pi.add_apply, Pi.sub_apply]
        ring
      rw [Finset.sum_congr rfl fun c _ => this c, Finset.sum_sub_distrib]
      linarith
    exact_mod_cast h3.symm
  rw [tcoef_expand z]
  refine Submodule.sum_mem _ fun s _ => ?_
  by_cases hs : tcoef ((fockBasis n).coord s) z = 0
  · rw [hs, TensorProduct.zero_tmul]
    exact Submodule.zero_mem _
  · have hb : fockBasis n s ∈ ⋀[ℂ]^(sDeg ε) (Fin n × Fin n → ℂ) := by
      rw [← hdeg s hs]
      exact gs_basis_deg s
    exact ⟨(⟨tcoef ((fockBasis n).coord s) z, tcoef_mem hT _⟩ : W) ⊗ₜ (⟨fockBasis n s, hb⟩ : ⋀[ℂ]^(sDeg ε) (Fin n × Fin n → ℂ)), by
      simp [TensorProduct.map_tmul]⟩

theorem line_ker {ε : Fin n → Bool} {lam : Fin n → ℝ} {E : Fin n → Fin n → Module.End ℂ M}
    (hE : IsGlRep E) (hU : IsInfUnitary ε E) {W : Submodule ℂ M} (hW : IsKIrrHW ε E (lowK ε lam) W)
    (hc : ∀ v ∈ W, casimir E v = ((casVal lam : ℝ) : ℂ) • v)
    {z : TensorProduct ℂ M (Fock n)} (hz : z ∈ lineSub ε E lam W) : (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) z = 0 := by
  obtain ⟨⟨hK, hT⟩, hP⟩ := hz
  replace hK := (mem_highestWeightSub_iff _ _ _ z).1 hK
  have hKv : IsKHWVec ε (diagE ε (eT E) cpT cmT) ((lam - rhoC ε) + rhoHol ε) z := hK
  have hcas : casimir (eT (n := n) E) z = ((casVal lam : ℝ) : ℂ) • z := by
    rw [ssh_casimir_eT]
    obtain ⟨y, rfl⟩ := hT
    have hcomp : casimir E ∘ₗ W.subtype = ((casVal lam : ℝ) : ℂ) • W.subtype := by
      ext v
      simp [hc v v.2]
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.id_comp, hcomp, TensorProduct.map_smul_left,
      LinearMap.smul_apply]
  have h2 := two_D_sq_khw (eT_isGlRep hE) cpT_cmT_isCAR (eT_commutesCAR E) hKv hcas
  have hzero : (((nsq (lam - rhoC ε + rhoC ε) - nsq (rho n) : ℝ) : ℂ) - ((casVal lam : ℝ) : ℂ)) = 0 := by
    rw [sub_add_cancel, casVal, sub_self]
  rw [hzero, zero_smul] at h2
  set D := dOp ε (eT E) cpT + dOp' ε (eT E) cmT with hD
  have hDD : D (D z) = 0 := by
    have h3 : (2 : ℂ) • (D * D) z = 0 := h2
    rw [smul_eq_zero] at h3
    rcases h3 with h3 | h3
    · norm_num at h3
    · exact h3
  have hf : tform (D z) (D z) = 0 := by
    rw [hD, tform_D hU, ← hD, hDD]
    unfold tform
    simp
  by_contra hne
  have := tform_self_re_pos hne
  rw [hf] at this
  simp at this

end ReciprocityTheory.ChartRestriction.DS.TRGap
