import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ArchimedeanSignatureMatchingOfTrivialBranchingSymm

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix MvPolynomial NumberField

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

structure PendClausesS (Tf : FormsTiedSym D u Ch chOf)
    (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) : Prop where
  coM_mem : ∀ w c, ∀ φ ∈ (D.fm u).Fi D.R.m, coMTS Tf B w c (φ ((D.fm u).til c)) ∈ Formalism.MainNotions.product_first_zeroth_parts.CSpan ((D.fm u).lam D.R.m)
  coM_inj : ∀ w c, ∀ φ ∈ (D.fm u).Fi D.R.m, coMTS Tf B w c (φ ((D.fm u).til c)) = 0 → φ ((D.fm u).til c) = 0
  coP_mem : ∀ w, ∀ z ∈ (D.fm u).ptC, ∀ c, coPTS Tf B w z c ∈ Formalism.MainNotions.product_first_zeroth_parts.CSpan (D.fm u).sg
  coP_inj : ∀ w, ∀ z ∈ (D.fm u).ptC, coPTS Tf B w z = 0 → z = 0
  exP : ∀ w, ∀ φ ∈ (D.fm u).Fi D.R.m, ∀ c, ∃ P ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m),
    (∀ s, Tf.eWz ((D.mem u).P.evz φ) c s =
      fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s)) ∧
    ∀ z : (D.mem u).P.Wrow, Tf.valP.eW z c = fnOf _ (shiftOf (sgT u)) 1 (Formalism.L2.Ker.brTen D u P) →
      coPTS Tf B w z c = Formalism.L2.Ker.brTen D u (coMTS Tf B w c (φ ((D.fm u).til c)))
  lat_co : ∀ w, ∀ x ∈ (D.fm u).S D.R.m w, ∀ c,
    coMTS Tf B w c ((D.fm u).emb D.R.m x ((D.fm u).til c)) ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w ((D.fm u).lam D.R.m)
  pt_co : ∀ w, ∀ z ∈ (D.fm u).ptC, (∃ y ∈ (D.fm u).SP w, (D.fm u).ptEmb y = z) ↔
    ∀ c, coPTS Tf B w z c ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w (D.fm u).sg
  ipV_co : ∀ w c, ∀ φ ∈ (D.fm u).Fi D.R.m,
    ((D.fm u).ipV D.R.m ((D.fm u).til c) (φ ((D.fm u).til c)) (φ ((D.fm u).til c))).re =
    (Formalism.MainNotions.product_first_zeroth_parts.nfAll ((D.fm u).lam D.R.m)
      (blk (fun τ => sqAct ℂ _ (lamTr D u τ) (gFull D u (gP w c τ))) (coMTS Tf B w c (φ ((D.fm u).til c))))
      (blk (fun τ => sqAct ℂ _ (lamTr D u τ) (gFull D u (gP w c τ))) (coMTS Tf B w c (φ ((D.fm u).til c))))).re
  re_petersson_self_eq_sum_coord : ∀ w, ∀ z ∈ (D.fm u).ptC, ((D.fm u).ipP z z).re = ∑ c, ((Nat.card ((D.fm u).stabilizer₂ c) : ℝ))⁻¹ *
    (Formalism.MainNotions.product_first_zeroth_parts.nfAll (D.fm u).sg (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gP w c τ)) (coPTS Tf B w z c))
      (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gP w c τ)) (coPTS Tf B w z c))).re

def pendOfS (Tf : FormsTiedSym D u Ch chOf) (hL : LowerSymmetricCompatible Tf)
    (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) (h : PendClausesS Tf B gP) : Pend D u where
  br τ := Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ)
  coM := coMTS Tf B
  coP := coPTS Tf B
  coM_mem := h.coM_mem
  coM_inj := h.coM_inj
  coP_mem := h.coP_mem
  coP_inj := h.coP_inj
  Pt_eq := by
    intro w φ hφ c
    obtain ⟨P, hP, hv, hz⟩ := h.exP w φ hφ c
    exact hz _ (hL.map.pt_eq (bZ_isUnitS Tf) φ c P hP hv)
  lat_co := h.lat_co
  pt_co := h.pt_co
  gP := gP
  ipV_co := h.ipV_co
  re_petersson_self_eq_sum_coord := h.re_petersson_self_eq_sum_coord
  beOn_eq := hL.beOn
  interlace := sg_interlace Tf.valP

theorem brExists_of_tiedS (Tf : FormsTiedSym D u Ch chOf) (hL : LowerSymmetricCompatible Tf)
    (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) (h : PendClausesS Tf B gP) :
    ∃ P : Pend D u, ArchimedeanSignatureMatching P :=
  ⟨pendOfS Tf hL B gP h, archimedeanSignatureMatching_of_trivial_branching_symm Tf _ fun _ => rfl⟩

section Cl

theorem bZg_isUnitS (Tf : FormsTiedSym D u Ch chOf) (B' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) (hB' : IsUnit B'.det) :
    IsUnit (bZg u Tf.til.z0 B').det := by
  have hBi : Function.Injective B'.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hB')
  refine isUnit_det_cols (Nm_succ D.R) (iXm D * B') (fun i => Tf.til.z0 i / ((D.mem u).A.T : D.host.E)) ?_ ?_
  · intro x y h
    simp only [← Matrix.mulVec_mulVec] at h
    exact hBi (iXm_mulVec_injective D h)
  · intro x h
    apply quotient_not_in_range_symmetric Tf (B' *ᵥ x)
    rw [Matrix.mulVec_mulVec]; exact h

theorem trEv_repS (Tf : FormsTiedSym D u Ch chOf) (B' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) (hB' : IsUnit B'.det)
    (φ : Fn D u D.R.m) (hφ : φ ∈ (D.fm u).Fi D.R.m) (c : (D.fm u).clsP) :
    ∃ Q ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m), trEvS Tf c (φ ((D.fm u).til c)) =
      fnOf _ (shiftOf (lamT u D.R.m)) (atInf (embT D) (bZg u Tf.til.z0 B')⁻¹) Q := by
  obtain ⟨P, hP, hv⟩ := val_repS Tf φ hφ c
  have hM : trEvS Tf c (φ ((D.fm u).til c)) = fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P := by
    funext y
    rw [trEv_eqS, hv, Equiv.apply_symm_apply]
  have hU := atInf_inv_isUnit _ (bZg_isUnitS Tf B' hB')
  rw [hM]
  exact exists_change _ _ _ _ _ hU P hP

theorem eW_repS (Tf : FormsTiedSym D u Ch chOf) (B' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) (hB' : IsUnit B'.det)
    (z : (D.mem u).P.Wrow) (hz : z ∈ (D.fm u).ptC) (c : (D.fm u).clsP) :
    ∃ Q ∈ Formalism.L2.Forms.CSpan (D.fm u).sg, Tf.valP.eW z c = fnOf _ (shiftOf (sgT u)) (atInf (embT D) B'⁻¹) Q := by
  have hF := (Tf.valP.ptC z).1 hz
  obtain ⟨g, hg, hres⟩ := Submodule.mem_map.1 hF
  have hval := (Submodule.mem_pi.1 (Submodule.mem_inf.1 hg).2) (Tf.clsP.y c) (Set.mem_univ _)
  obtain ⟨Q0, hQ0, hfn⟩ := Submodule.mem_map.1 hval
  have hQ0' : Q0 ∈ Formalism.L2.Forms.CSpan (D.fm u).sg := by
    have := CSpan_shW (D.fm u).sg (fun _ => ((D.R.m * (D.R.t + 1) / 2 : ℕ) : ℤ))
    unfold sgT at hQ0
    rw [this] at hQ0
    exact hQ0
  have he : Tf.valP.eW z c = fnOf _ (shiftOf (sgT u)) 1 Q0 := by
    rw [hfn, ← hres]; rfl
  have hU := atInf_inv_isUnit _ hB'
  rw [he]
  exact exists_change _ _ _ _ _ hU Q0 hQ0'

variable (Tf : FormsTiedSym D u Ch chOf)
  (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
  (hB : ∀ w c, IsUnit (B w c).det)

include hB

theorem coM_mem_ofS : ∀ w c, ∀ φ ∈ (D.fm u).Fi D.R.m,
    coMTS Tf B w c (φ ((D.fm u).til c)) ∈ Formalism.MainNotions.product_first_zeroth_parts.CSpan ((D.fm u).lam D.R.m) := by
  intro w c φ hφ
  obtain ⟨Q, hQ, hq⟩ := trEv_repS Tf (B w c) (hB w c) φ hφ c
  have : coMTS Tf B w c (φ ((D.fm u).til c)) = Q := by
    simp only [coMTS, LinearMap.coe_comp, Function.comp_apply]
    rw [hq, fnInv_fnOf _ _ _ (atInf_inv_isUnit _ (bZg_isUnitS Tf (B w c) (hB w c)))]
  rw [this]; exact hQ

theorem coP_mem_of_isUnit_det' : ∀ w, ∀ z ∈ (D.fm u).ptC, ∀ c, coPTS Tf B w z c ∈ Formalism.MainNotions.product_first_zeroth_parts.CSpan (D.fm u).sg := by
  intro w z hz c
  obtain ⟨Q, hQ, hq⟩ := eW_repS Tf (B w c) (hB w c) z hz c
  have : coPTS Tf B w z c = Q := by
    simp only [coPTS, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval,
      LinearEquiv.coe_coe]
    rw [hq, fnInv_fnOf _ _ _ (atInf_inv_isUnit _ (hB w c))]
  rw [this]; exact hQ

theorem coP_inj_of_isUnit_det' : ∀ w, ∀ z ∈ (D.fm u).ptC, coPTS Tf B w z = 0 → z = 0 := by
  intro w z hz h0
  apply Tf.valP.eW.injective
  rw [map_zero]
  funext c
  obtain ⟨Q, hQ, hq⟩ := eW_repS Tf (B w c) (hB w c) z hz c
  have : coPTS Tf B w z c = Q := by
    simp only [coPTS, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval,
      LinearEquiv.coe_coe]
    rw [hq, fnInv_fnOf _ _ _ (atInf_inv_isUnit _ (hB w c))]
  have hQ0 : Q = 0 := by rw [← this, h0]; rfl
  rw [hq, hQ0, map_zero]; rfl

theorem coM_inj_ofS : ∀ w c, ∀ φ ∈ (D.fm u).Fi D.R.m, coMTS Tf B w c (φ ((D.fm u).til c)) = 0 → φ ((D.fm u).til c) = 0 := by
  intro w c φ hφ h0
  obtain ⟨Q, hQ, hq⟩ := trEv_repS Tf (B w c) (hB w c) φ hφ c
  have hc : coMTS Tf B w c (φ ((D.fm u).til c)) = Q := by
    simp only [coMTS, LinearMap.coe_comp, Function.comp_apply]
    rw [hq, fnInv_fnOf _ _ _ (atInf_inv_isUnit _ (bZg_isUnitS Tf (B w c) (hB w c)))]
  have ht : trEvS Tf c (φ ((D.fm u).til c)) = 0 := by rw [hq, ← hc, h0, map_zero]
  funext s'
  let ga : GL (Fin (D.R.N D.R.m)) D.host.E := (Tf.til.ga c).1
  have hy := congrFun ht (((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s').tr (atInf (embT D) (ga : Matrix _ _ D.host.E)) (isUnit_det_atInf (embT D) ga))
  simp only [trEvS, LinearMap.smul_apply, LinearMap.funLeft_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hy
  have hback : (((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s').tr (atInf (embT D) (ga : Matrix _ _ D.host.E)) (isUnit_det_atInf (embT D) ga)).tr
      (atInf (embT D) ((ga⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E)) (isUnit_det_atInf (embT D) ga⁻¹) =
      (Tf.val D.R.m le_rfl (Or.inr rfl)).eY s' := by
    apply Subtype.ext
    funext τ
    show atInf (embT D) ((ga⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E) τ *
      (atInf (embT D) (ga : Matrix _ _ D.host.E) τ * ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s').1 τ) = ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s').1 τ
    have h1 := atInf_mul_inv (embT D) ga⁻¹ τ
    rw [inv_inv] at h1
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [hback, Equiv.symm_apply_apply] at hy
  exact (mul_eq_zero.mp hy).resolve_left (Units.ne_zero _)

omit hB in

structure PendRestS (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) : Prop where
  exP : ∀ w, ∀ φ ∈ (D.fm u).Fi D.R.m, ∀ c, ∃ P ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m),
    (∀ s, Tf.eWz ((D.mem u).P.evz φ) c s =
      fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s)) ∧
    ∀ z : (D.mem u).P.Wrow, Tf.valP.eW z c = fnOf _ (shiftOf (sgT u)) 1 (Formalism.L2.Ker.brTen D u P) →
      coPTS Tf B w z c = Formalism.L2.Ker.brTen D u (coMTS Tf B w c (φ ((D.fm u).til c)))
  lat_co : ∀ w, ∀ x ∈ (D.fm u).S D.R.m w, ∀ c,
    coMTS Tf B w c ((D.fm u).emb D.R.m x ((D.fm u).til c)) ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w ((D.fm u).lam D.R.m)
  pt_co : ∀ w, ∀ z ∈ (D.fm u).ptC, (∃ y ∈ (D.fm u).SP w, (D.fm u).ptEmb y = z) ↔
    ∀ c, coPTS Tf B w z c ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w (D.fm u).sg
  ipV_co : ∀ w c, ∀ φ ∈ (D.fm u).Fi D.R.m,
    ((D.fm u).ipV D.R.m ((D.fm u).til c) (φ ((D.fm u).til c)) (φ ((D.fm u).til c))).re =
    (Formalism.MainNotions.product_first_zeroth_parts.nfAll ((D.fm u).lam D.R.m)
      (blk (fun τ => sqAct ℂ _ (lamTr D u τ) (gFull D u (gP w c τ))) (coMTS Tf B w c (φ ((D.fm u).til c))))
      (blk (fun τ => sqAct ℂ _ (lamTr D u τ) (gFull D u (gP w c τ))) (coMTS Tf B w c (φ ((D.fm u).til c))))).re
  re_petersson_self_eq_sum_coord : ∀ w, ∀ z ∈ (D.fm u).ptC, ((D.fm u).ipP z z).re = ∑ c, ((Nat.card ((D.fm u).stabilizer₂ c) : ℝ))⁻¹ *
    (Formalism.MainNotions.product_first_zeroth_parts.nfAll (D.fm u).sg (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gP w c τ)) (coPTS Tf B w z c))
      (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gP w c τ)) (coPTS Tf B w z c))).re

theorem brExists_of_restS (hL : LowerSymmetricCompatible Tf)
    (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) (h : PendRestS Tf B gP) :
    ∃ P : Pend D u, ArchimedeanSignatureMatching P :=
  brExists_of_tiedS Tf hL B gP
    { coM_mem := coM_mem_ofS Tf B hB, coM_inj := coM_inj_ofS Tf B hB, coP_mem := coP_mem_of_isUnit_det' Tf B hB,
      coP_inj := coP_inj_of_isUnit_det' Tf B hB, exP := h.exP, lat_co := h.lat_co, pt_co := h.pt_co, ipV_co := h.ipV_co,
      re_petersson_self_eq_sum_coord := h.re_petersson_self_eq_sum_coord }

end Cl

end Formalism.L2.GlobalTheoryTheory.Br
