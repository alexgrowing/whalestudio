import Formalism.LocalToGlobal.HermitianForms.TiedBrRow

noncomputable section

namespace Formalism.L2.Forms

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Matrix

theorem exists_change {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ)
    (M M' : ι → Matrix (Fin n) (Fin n) ℂ) (hM : ∀ τ, IsUnit (M τ).det) (P : MvPolynomial (ι × Fin n × Fin n) ℂ)
    (hP : P ∈ CSpan lam) : ∃ Q ∈ CSpan lam, fnOf G s M' P = fnOf G s M Q := by
  refine ⟨_, ?_, fnOf_change G s M M' hM P⟩
  exact Submodule.smul_mem _ _ (blkRow_mem _ _ hP)

variable {D : D7} {u : D.what₂.Word}

theorem bZg_isUnit (Tf : FormsTied D u) (B' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) (hB' : IsUnit B'.det) :
    IsUnit (bZg u Tf.til.z0 B').det := by
  have hBi : Function.Injective B'.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hB')
  refine isUnit_det_cols (Nm_succ D.R) (iXm D * B') (fun i => Tf.til.z0 i / ((D.mem u).A.T : D.host.E)) ?_ ?_
  · intro x y h
    simp only [← Matrix.mulVec_mulVec] at h
    exact hBi (iXm_mulVec_injective D h)
  · intro x h
    apply vector_quotient_not_in_range Tf (B' *ᵥ x)
    rw [Matrix.mulVec_mulVec]; exact h

theorem atInf_inv_isUnit {n : ℕ} (A : Matrix (Fin n) (Fin n) D.host.E) (hA : IsUnit A.det) (τ : D.what₂.Tau) :
    IsUnit (atInf (embT D) A⁻¹ τ).det := by
  unfold atInf
  have h := (Matrix.isUnit_nonsing_inv_det A hA).map (embT D τ)
  first
  | (rw [RingHom.map_det, RingHom.mapMatrix_apply] at h; exact h)
  | simpa [RingHom.map_det] using h
  | simpa [AlgHom.map_det] using h

theorem trEv_rep (Tf : FormsTied D u) (B' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) (hB' : IsUnit B'.det)
    (φ : Fn D u D.R.m) (hφ : φ ∈ (D.fm u).Fi D.R.m) (c : (D.fm u).clsP) :
    ∃ Q ∈ CSpan ((D.fm u).lam D.R.m), trEv Tf c (φ ((D.fm u).til c)) =
      fnOf _ (shiftOf (lamT u D.R.m)) (atInf (embT D) (bZg u Tf.til.z0 B')⁻¹) Q := by
  obtain ⟨P, hP, hv⟩ := val_rep Tf φ hφ c
  have hM : trEv Tf c (φ ((D.fm u).til c)) = fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P := by
    funext y
    rw [trEv_eq, hv, Equiv.apply_symm_apply]
  have hU := atInf_inv_isUnit _ (bZg_isUnit Tf B' hB')
  rw [hM]
  exact exists_change _ _ _ _ _ hU P hP

theorem eW_rep (Tf : FormsTied D u) (B' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) (hB' : IsUnit B'.det)
    (z : (D.mem u).P.Wrow) (hz : z ∈ (D.fm u).ptC) (c : (D.fm u).clsP) :
    ∃ Q ∈ CSpan (D.fm u).sg, Tf.valP.eW z c = fnOf _ (shiftOf (sgT u)) (atInf (embT D) B'⁻¹) Q := by
  have hF := (Tf.valP.ptC z).1 hz
  obtain ⟨g, hg, hres⟩ := Submodule.mem_map.1 hF
  have hval := (Submodule.mem_pi.1 (Submodule.mem_inf.1 hg).2) (Tf.clsP.y c) (Set.mem_univ _)
  obtain ⟨Q0, hQ0, hfn⟩ := Submodule.mem_map.1 hval
  have hQ0' : Q0 ∈ CSpan (D.fm u).sg := by
    have := CSpan_shW (D.fm u).sg (fun _ => ((D.R.m * (D.R.t + 1) / 2 : ℕ) : ℤ))
    unfold sgT at hQ0
    rw [this] at hQ0
    exact hQ0
  have he : Tf.valP.eW z c = fnOf _ (shiftOf (sgT u)) 1 Q0 := by
    rw [hfn, ← hres]; rfl
  have hU := atInf_inv_isUnit _ hB'
  rw [he]
  exact exists_change _ _ _ _ _ hU Q0 hQ0'

variable (Tf : FormsTied D u)
  (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
  (hB : ∀ w c, IsUnit (B w c).det)

include hB

theorem coM_mem_of : ∀ w c, ∀ φ ∈ (D.fm u).Fi D.R.m,
    coMT Tf B w c (φ ((D.fm u).til c)) ∈ Formalism.MainNotions.product_first_zeroth_parts.CSpan ((D.fm u).lam D.R.m) := by
  intro w c φ hφ
  obtain ⟨Q, hQ, hE⟩ := trEv_rep Tf (B w c) (hB w c) φ hφ c
  unfold coMT
  rw [LinearMap.comp_apply, hE,
    fnInv_fnOf _ _ _ (fun τ => atInf_inv_isUnit _ (bZg_isUnit Tf (B w c) (hB w c)) τ)]
  exact hQ

theorem coP_mem_of_isUnit_det : ∀ w, ∀ z ∈ (D.fm u).ptC, ∀ c, coPT Tf B w z c ∈ Formalism.MainNotions.product_first_zeroth_parts.CSpan (D.fm u).sg := by
  intro w z hz c
  obtain ⟨Q, hQ, hE⟩ := eW_rep Tf (B w c) (hB w c) z hz c
  unfold coPT
  simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, LinearEquiv.coe_coe]
  rw [hE, fnInv_fnOf _ _ _ (fun τ => atInf_inv_isUnit _ (hB w c) τ)]
  exact hQ

theorem coP_inj_of_isUnit_det : ∀ w, ∀ z ∈ (D.fm u).ptC, coPT Tf B w z = 0 → z = 0 := by
  intro w z hz h
  have hc : ∀ c, Tf.valP.eW z c = 0 := by
    intro c
    obtain ⟨Q, hQ, hE⟩ := eW_rep Tf (B w c) (hB w c) z hz c
    have h1 := congrFun h c
    unfold coPT at h1
    simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, LinearEquiv.coe_coe,
      Pi.zero_apply] at h1
    rw [hE, fnInv_fnOf _ _ _ (fun τ => atInf_inv_isUnit _ (hB w c) τ)] at h1
    rw [hE, h1, map_zero]
  have h0 : Tf.valP.eW z = 0 := funext hc
  first
  | exact Tf.valP.eW.injective (h0.trans (map_zero _).symm)
  | exact (LinearEquiv.map_eq_zero_iff _).1 h0
  | simpa using h0

theorem coM_inj_of : ∀ w c, ∀ φ ∈ (D.fm u).Fi D.R.m, coMT Tf B w c (φ ((D.fm u).til c)) = 0 → φ ((D.fm u).til c) = 0 := by
  intro w c φ hφ h0
  obtain ⟨Q, hQ, hq⟩ := trEv_rep Tf (B w c) (hB w c) φ hφ c
  have hc : coMT Tf B w c (φ ((D.fm u).til c)) = Q := by
    simp only [coMT, LinearMap.coe_comp, Function.comp_apply]
    rw [hq, fnInv_fnOf _ _ _ (atInf_inv_isUnit _ (bZg_isUnit Tf (B w c) (hB w c)))]
  have ht : trEv Tf c (φ ((D.fm u).til c)) = 0 := by rw [hq, ← hc, h0, map_zero]
  funext s'
  let ga : GL (Fin (D.R.N D.R.m)) D.host.E := (Tf.til.ga c).1
  have hy := congrFun ht (((Tf.val D.R.m le_rfl).eY s').tr (atInf (embT D) (ga : Matrix _ _ D.host.E)) (isUnit_det_atInf (embT D) ga))
  simp only [trEv, LinearMap.smul_apply, LinearMap.funLeft_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hy
  have hback : (((Tf.val D.R.m le_rfl).eY s').tr (atInf (embT D) (ga : Matrix _ _ D.host.E)) (isUnit_det_atInf (embT D) ga)).tr
      (atInf (embT D) ((ga⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E)) (isUnit_det_atInf (embT D) ga⁻¹) =
      (Tf.val D.R.m le_rfl).eY s' := by
    apply Subtype.ext
    funext τ
    show atInf (embT D) ((ga⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E) τ *
      (atInf (embT D) (ga : Matrix _ _ D.host.E) τ * ((Tf.val D.R.m le_rfl).eY s').1 τ) = ((Tf.val D.R.m le_rfl).eY s').1 τ
    have h1 := atInf_mul_inv (embT D) ga⁻¹ τ
    rw [inv_inv] at h1
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [hback, Equiv.symm_apply_apply] at hy
  exact (mul_eq_zero.mp hy).resolve_left (Units.ne_zero _)

omit hB in

structure PendRest (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) : Prop where
  exP : ∀ w, ∀ φ ∈ (D.fm u).Fi D.R.m, ∀ c, ∃ P ∈ CSpan ((D.fm u).lam D.R.m),
    (∀ s, Tf.eWz ((D.mem u).P.evz φ) c s =
      fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P ((Tf.val D.R.m le_rfl).eY s)) ∧
    ∀ z : (D.mem u).P.Wrow, Tf.valP.eW z c = fnOf _ (shiftOf (sgT u)) 1 (Formalism.L2.Ker.brTen D u P) →
      coPT Tf B w z c = Formalism.L2.Ker.brTen D u (coMT Tf B w c (φ ((D.fm u).til c)))
  lat_co : ∀ w, ∀ x ∈ (D.fm u).S D.R.m w, ∀ c,
    coMT Tf B w c ((D.fm u).emb D.R.m x ((D.fm u).til c)) ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w ((D.fm u).lam D.R.m)
  pt_co : ∀ w, ∀ z ∈ (D.fm u).ptC, (∃ y ∈ (D.fm u).SP w, (D.fm u).ptEmb y = z) ↔
    ∀ c, coPT Tf B w z c ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w (D.fm u).sg
  ipV_co : ∀ w c, ∀ φ ∈ (D.fm u).Fi D.R.m,
    ((D.fm u).ipV D.R.m ((D.fm u).til c) (φ ((D.fm u).til c)) (φ ((D.fm u).til c))).re =
    (Formalism.MainNotions.product_first_zeroth_parts.nfAll ((D.fm u).lam D.R.m)
      (blk (fun τ => sqAct ℂ _ (lamTr D u τ) (gFull D u (gP w c τ))) (coMT Tf B w c (φ ((D.fm u).til c))))
      (blk (fun τ => sqAct ℂ _ (lamTr D u τ) (gFull D u (gP w c τ))) (coMT Tf B w c (φ ((D.fm u).til c))))).re
  re_petersson_self_eq_sum_coord : ∀ w, ∀ z ∈ (D.fm u).ptC, ((D.fm u).ipP z z).re = ∑ c, ((Nat.card ((D.fm u).stabilizer₂ c) : ℝ))⁻¹ *
    (Formalism.MainNotions.product_first_zeroth_parts.nfAll (D.fm u).sg (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gP w c τ)) (coPT Tf B w z c))
      (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gP w c τ)) (coPT Tf B w z c))).re

theorem brExists_of_rest (hL : LowerLevelCompatible Tf)
    (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) (h : PendRest Tf B gP) :
    ∃ P : Pend D u, ArchimedeanSignatureMatching P :=
  brExists_of_tied Tf hL B gP
    { coM_mem := coM_mem_of Tf B hB, coM_inj := coM_inj_of Tf B hB, coP_mem := coP_mem_of_isUnit_det Tf B hB,
      coP_inj := coP_inj_of_isUnit_det Tf B hB, exP := h.exP, lat_co := h.lat_co, pt_co := h.pt_co, ipV_co := h.ipV_co,
      re_petersson_self_eq_sum_coord := h.re_petersson_self_eq_sum_coord }

end Formalism.L2.Forms
