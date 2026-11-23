import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCountPfLeviSteps
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHDef

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped InnerProductSpace ComplexConjugate
open Matrix Finset

namespace Formalism.L2.SG.PoincareInHH.Cut

section PosDef

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem wu_pos (ι : X.B.I.F →+* ℝ) (x : Fin X.B.I.n → X.B.I.E) (hx0 : x ≠ 0)
    (hxS : ∀ s ∈ fixSet X u, Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J s x = 0) :
    ∃ a : X.B.I.F, algebraMap X.B.I.F X.B.I.E a = Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J x x ∧ 0 < ι a := by

  have hherm : star (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J x x) = Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J x x := by
    have hJh := X.B.I.J_herm
    unfold Formalism.UG.IsHerm Formalism.UG.cT at hJh
    have hji : ∀ i j, starRingEnd X.B.I.E (X.B.I.J i j) = X.B.I.J j i := fun i j => by
      have := congrFun (congrFun hJh j) i
      simpa using this
    simp only [Formalism.UG.hform, star_sum, star_mul', starRingEnd_apply, star_star]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have := hji j i
    rw [starRingEnd_apply] at this
    rw [this]; ring
  obtain ⟨a, ha⟩ := (X.B.I.cm.fixed _).1 hherm
  refine ⟨a, ha, ?_⟩

  set ψ : X.B.I.F →+* ℂ := Complex.ofRealHom.comp ι
  have hψr : NumberField.ComplexEmbedding.IsReal ψ := by
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext b; simp [ψ, NumberField.ComplexEmbedding.conjugate_coe_eq]
  set v : InfinitePlace X.B.I.F := InfinitePlace.mk ψ
  have hemb : v.embedding = ψ := NumberField.InfinitePlace.embedding_mk_eq_of_isReal hψr
  have hval : ((ι a : ℝ) : ℂ) = hJ (X.B.I.ε v) (rv X.B.I v x) (rv X.B.I v x) := by
    rw [← phi_hform, ← ha, X.B.I.φ_over v a, hemb]; rfl
  have hre : ι a = (hJ (X.B.I.ε v) (rv X.B.I v x) (rv X.B.I v x)).re := by rw [← hval]; simp
  rw [hre]
  by_contra hle
  push_neg at hle

  let nv : Fin (D.R.rS + 1) → Fin X.B.I.n → ℂ := fun j =>
    if h : j.1 < D.R.rS then rv X.B.I v (X.eR ⟨j.1, h⟩) - rv X.B.I v (X.fR ⟨j.1, h⟩) else rv X.B.I v (X.zR u)
  have hTpos : (0 : ℝ) < ((D.mem u).A.T : ℝ) := by exact_mod_cast (D.mem u).A.T_prime.pos
  have hb := card_le_of_orth' (X.B.I.ε v) (D.R.rS + 1) nv (rv X.B.I v x) ?_ ?_ ?_ hle ?_
  · rw [card_eps_false X v] at hb
    omega
  · intro j k hjk
    simp only [nv]
    split_ifs with hj hk hk
    · rw [hJ_sub_left, hJ_sub_right, hJ_sub_right]
      simp only [HidaSetting.eR, HidaSetting.fR, hJ_crd, X.ee, X.ff, X.ef, hT_f_e]
      have hne : (⟨k.1, hk⟩ : Fin D.R.rS) ≠ ⟨j.1, hj⟩ := fun h => hjk (Fin.ext (by simpa using (congrArg Fin.val h).symm))
      have hne' : (⟨j.1, hj⟩ : Fin D.R.rS) ≠ ⟨k.1, hk⟩ := fun h => hne h.symm
      simp [hne, hne']
    · rw [hJ_sub_left]
      simp only [HidaSetting.eR, HidaSetting.fR, HidaSetting.zR, hJ_crd, (X.zu_orth u _).1, (X.zu_orth u _).2]
      simp
    · rw [hJ_sub_right]
      have h1 := hJ_crd X v (X.zu u) (X.eX ⟨k.1, hk⟩)
      have h2 := hJ_crd X v (X.zu u) (X.fY ⟨k.1, hk⟩)
      have e1 : (VS D).hT (X.zu u) (X.eX ⟨k.1, hk⟩) = 0 := by
        rw [← (VS D).herm.eq, (X.zu_orth u _).1]; simp
      have e2 : (VS D).hT (X.zu u) (X.fY ⟨k.1, hk⟩) = 0 := by
        rw [← (VS D).herm.eq, (X.zu_orth u _).2]; simp
      simp only [HidaSetting.eR, HidaSetting.fR, HidaSetting.zR, h1, h2, e1, e2, map_zero, sub_zero]
    · exfalso; apply hjk; ext; omega
  · intro j
    simp only [nv]
    split_ifs with hj
    · rw [hJ_sub_left, hJ_sub_right, hJ_sub_right]
      simp only [HidaSetting.eR, HidaSetting.fR, hJ_crd, X.ee, X.ff, X.ef, hT_f_e, if_true, map_zero, map_one]
      norm_num
    · simp only [HidaSetting.zR, hJ_crd, X.zu_norm, map_neg, map_natCast]
      simp only [Complex.neg_re, Complex.natCast_re, Left.neg_neg_iff]
      exact_mod_cast (D.mem u).A.T_prime.pos
  · intro j
    simp only [nv]
    split_ifs with hj
    · rw [hJ_sub_left, ← phi_hform, ← phi_hform, hxS _ (eR_mem_fix X u _), hxS _ (fR_mem_fix X u _)]
      simp
    · rw [← phi_hform, hxS _ (zR_mem_fix X u)]; simp
  · intro h0
    apply hx0
    have hPu : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
    have hφ : (fun i => X.B.I.φ v (x i)) = 0 := by
      have : X.B.I.P v *ᵥ rv X.B.I v x = fun i => X.B.I.φ v (x i) := by
        unfold rv; rw [mulVec_mulVec, mul_nonsing_inv _ hPu, one_mulVec]
      rw [← this, h0, mulVec_zero]
    funext i
    have := congrFun hφ i
    simpa using this

end PosDef

end Formalism.L2.SG.PoincareInHH.Cut

namespace Formalism.L2.SG.Pf.SlabCount

open Formalism.L2.SG.PoincareInHH.Cut Formalism.MainNotions.S.Lat

theorem trace_pos_of_totPos {F : Type} [Field F] [NumberField F] (hF : NumberField.IsTotallyReal F) (a : F)
    (ha : ∀ ι : F →+* ℝ, 0 < ι a) : 0 < Algebra.trace ℚ F a := by
  have := hF
  have h := trace_eq_sum_embeddings (K := ℚ) (L := F) (E := ℂ) (x := a)
  have hre : ∀ σ : F →ₐ[ℚ] ℂ, 0 < (σ a).re ∧ (σ a).im = 0 := by
    intro σ
    have hr : NumberField.ComplexEmbedding.IsReal (σ : F →+* ℂ) := IsTotallyReal.complexEmbedding_isReal _
    have e := NumberField.ComplexEmbedding.IsReal.coe_embedding_apply hr a
    have e2 : σ a = ((hr.embedding a : ℝ) : ℂ) := e.symm
    refine ⟨?_, ?_⟩
    · simp only [e2, Complex.ofReal_re]; exact ha hr.embedding
    · simp only [e2, Complex.ofReal_im]
  have hsum : (0 : ℝ) < (∑ σ : F →ₐ[ℚ] ℂ, σ a).re := by
    rw [Complex.re_sum]
    obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
    let σ0 : F →ₐ[ℚ] ℂ := v.embedding.toRatAlgHom
    exact Finset.sum_pos (fun σ _ => (hre σ).1) ⟨σ0, Finset.mem_univ _⟩
  rw [← h] at hsum
  simpa using hsum

theorem levi_totally_positive_definite : LeviPosC := by
  intro D X u' w hw hw0
  have hc0 : X.crd (0 : (VS D).V) = 0 := by
    funext i; simp [Formalism.L2.SG.HidaSetting.HidaSetting.crd, Formalism.L2.SG.HidaSetting.crdOf]
  have hx0 : X.crd w ≠ 0 := fun h => hw0 (Formalism.L2.SG.Pf.RegroupPf.crd_inj' X (h.trans hc0.symm))
  have horth : ∀ v ∈ Usp X u', (VS D).hT v w = 0 := by
    intro v hv
    have h := hw
    simp only [Wsp, orth, Submodule.mem_iInf, LinearMap.mem_ker] at h
    exact h v hv
  have hz0 : ∀ v ∈ Usp X u', Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.crd v) (X.crd w) = 0 := by
    intro v hv
    apply X.ιE.injective
    rw [hform_crd X v w, map_zero, horth v hv]
  have hxS : ∀ s ∈ fixSet X u', Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J s (X.crd w) = 0 := by
    rintro s ((⟨a, rfl⟩ | ⟨a, rfl⟩) | hs)
    · exact hz0 _ (Submodule.subset_span (Or.inl (Or.inl ⟨a, rfl⟩)))
    · exact hz0 _ (Submodule.subset_span (Or.inl (Or.inr ⟨a, rfl⟩)))
    · rw [Set.mem_singleton_iff.1 hs]
      exact hz0 _ (Submodule.subset_span (Or.inr rfl))
  have hTR : NumberField.IsTotallyReal X.B.I.F := X.B.I.cm.totReal
  obtain ⟨v⟩ : Nonempty (NumberField.InfinitePlace X.B.I.F) := inferInstance
  obtain ⟨a, ha, -⟩ := wu_pos X u' (NumberField.InfinitePlace.embedding_of_isReal (hTR.isReal v)) (X.crd w) hx0 hxS
  have hpos : ∀ ι : X.B.I.F →+* ℝ, 0 < ι a := by
    intro ι
    obtain ⟨b, hb, hbpos⟩ := wu_pos X u' ι (X.crd w) hx0 hxS
    have hba : b = a := (algebraMap X.B.I.F X.B.I.E).injective (hb.trans ha.symm)
    rw [← hba]; exact hbpos
  have : FiniteDimensional X.B.I.F X.B.I.E := Module.Finite.of_restrictScalars_finite ℚ X.B.I.F X.B.I.E
  rw [← hform_crd X w w, show X.ιE (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.crd w) (X.crd w)) =
      (RingEquiv.toRatAlgEquiv X.ιE) (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.crd w) (X.crd w)) from rfl,
    Algebra.trace_eq_of_algEquiv, ← ha, ← Algebra.trace_trace (R := ℚ) (S := X.B.I.F) (T := X.B.I.E),
    Algebra.trace_algebraMap, map_nsmul]
  exact nsmul_pos (trace_pos_of_totPos hTR a hpos) (by rw [X.B.I.cm.deg2]; norm_num)

end Formalism.L2.SG.Pf.SlabCount
