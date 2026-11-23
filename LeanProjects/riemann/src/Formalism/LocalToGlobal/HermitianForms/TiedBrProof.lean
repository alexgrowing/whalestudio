import Formalism.LocalToGlobal.HermitianForms.TiedBrCl
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.LowerTieChain

noncomputable section

namespace Formalism.L2.Forms

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Matrix MvPolynomial

section GlobalTheory

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem blkRow_ten (K : ι → Matrix (Fin n) (Fin n) ℂ) (f : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    blkRow K (Formalism.MainNotions.product_first_zeroth_parts.ten f) = Formalism.MainNotions.product_first_zeroth_parts.ten (fun τ => Formalism.GradedWeylDivisibility.rowAct ℂ (K τ) (f τ)) := by
  unfold Formalism.MainNotions.product_first_zeroth_parts.ten
  rw [map_prod]
  exact Finset.prod_congr rfl fun τ _ => blkRow_rename K τ (f τ)

theorem blkRow_eq_blk (K : ι → Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    blkRow K P = Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => ⇑((Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (K τ)).toLinearMap)) P := by
  have h : (blkRow K).toLinearMap = Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => ⇑((Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (K τ)).toLinearMap)) := by
    apply (MvPolynomial.basisMonomials (ι × Fin n × Fin n) ℂ).ext
    intro mon
    rw [MvPolynomial.coe_basisMonomials, Formalism.L2.Ker.ta_blk_monomial]
    have hm : (MvPolynomial.monomial mon (1 : ℂ)) = Formalism.MainNotions.product_first_zeroth_parts.ten fun τ => MvPolynomial.monomial
        (mon.comapDomain (Prod.mk τ) (Prod.mk_right_injective τ).injOn) (1 : ℂ) := by
      rw [Formalism.MainNotions.product_first_zeroth_parts.ten_monomial, Formalism.L2.Ker.ta_sum_map_comap]
    rw [AlgHom.toLinearMap_apply]
    dsimp only
    rw [hm, blkRow_ten]
    rfl
  exact LinearMap.congr_fun h P

end GlobalTheory

section GLBlk

theorem embGL_val {R : Type} [CommRing R] {n N : ℕ} (h : n + 1 = N) (G : GL (Fin n) R) :
    ((Formalism.MainNotions.PrimeDegreeVariant.embGL R n N h G : GL (Fin N) R) : Matrix (Fin N) (Fin N) R) =
      Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (Matrix.fromBlocks (G : Matrix (Fin n) (Fin n) R) 0 0 (1 : Matrix (Fin 1) (Fin 1) R)) := rfl

theorem detPow_embGL {R : Type} [CommRing R] {n N : ℕ} (h : n + 1 = N) (G : GL (Fin n) R) (c : ℤ) :
    detPow R N (Formalism.MainNotions.PrimeDegreeVariant.embGL R n N h G) c = detPow R n G c := by
  unfold detPow
  congr 2
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, embGL_val, Matrix.det_reindex_self,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

theorem rowAct_tr_eq {k : ℕ} (l : DomWeight k) (G : GL (Fin k) ℂ) (f : MvPolynomial (Fin k × Fin k) ℂ) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (n := k) (G : Matrix (Fin k) (Fin k) ℂ).transpose f = (detPow ℂ k G l.detShift)⁻¹ • sqAct ℂ k l G f := by
  unfold sqAct
  rw [smul_smul, inv_mul_cancel₀ (by unfold detPow; exact Units.ne_zero _), one_smul]

theorem brOne_rowAct {N n : ℕ} (hN : N = n + 1) (l : DomWeight N) (s : DomWeight n)
    (hS : Formalism.L2.Col.Br.SameShift l s) (G : GL (Fin n) ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    Formalism.L2.Ker.brOne ℂ hN l s (Formalism.GradedWeylDivisibility.rowAct ℂ (n := N)
              ((Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm G : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ).transpose f) =
      Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (G : Matrix (Fin n) (Fin n) ℂ).transpose (Formalism.L2.Ker.brOne ℂ hN l s f) := by
  rw [rowAct_tr_eq l, rowAct_tr_eq s, map_smul, Formalism.L2.Ker.brOne_sqAct hN l s hS G f, detPow_embGL]
  rw [show s.detShift = l.detShift from hS]

end GLBlk

variable {D : D7} {u : D.what₂.Word}

theorem brTen_blkRow (Tf : FormsTied D u) (G : D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ) :
    Formalism.L2.Ker.brTen D u (blkRow (fun τ => ((Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) (G τ) : GL (Fin (D.R.N D.R.m)) ℂ) :
              Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ).transpose) P) =
      blkRow (fun τ => (G τ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ).transpose) (Formalism.L2.Ker.brTen D u P) := by
  have hS : ∀ τ, Formalism.L2.Col.Br.SameShift (lamTr D u τ) (sgTr D u τ) :=
    fun τ => Formalism.L2.Ker.sameShiftTr D u τ (interlaceTr D u (sg_interlace Tf.valP) τ)
  rw [blkRow_eq_blk, blkRow_eq_blk]
  unfold Formalism.L2.Ker.brTen
  rw [Formalism.L2.Ker.ta_blk_comp, Formalism.L2.Ker.ta_blk_comp]
  have e : (fun τ => ⇑(Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) ∘ₗ
      (Formalism.GradedWeylDivisibility.rowAct ℂ (n := D.R.N D.R.m) ((Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) (G τ) : GL (Fin (D.R.N D.R.m)) ℂ) :
        Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ).transpose).toLinearMap)) =
      fun τ => ⇑((Formalism.GradedWeylDivisibility.rowAct ℂ (n := D.R.N D.R.m - 1) (G τ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ).transpose).toLinearMap ∘ₗ
        Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ)) := by
    funext τ f
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    exact brOne_rowAct (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) (hS τ) (G τ) f
  rw [e]

def dgE (B' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) :
    Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E :=
  Matrix.reindex (finSumFinEquiv.trans (finCongr (Nm_succ D.R))) (finSumFinEquiv.trans (finCongr (Nm_succ D.R)))
    (Matrix.fromBlocks B' 0 0 (1 : Matrix (Fin 1) (Fin 1) D.host.E))

theorem bZg_eq_mul (z0 : Fin (D.R.N D.R.m) → D.host.E) (B' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) :
    bZg u z0 B' = bZ u z0 * dgE B' := by
  ext a b
  obtain ⟨x, rfl⟩ := (finSumFinEquiv.trans (finCongr (Nm_succ D.R))).surjective b
  rw [Matrix.mul_apply, ← (finSumFinEquiv.trans (finCongr (Nm_succ D.R))).sum_comp, Fintype.sum_sum_type]
  rcases x with i | i
  · simp [bZg, bZ, dgE, Matrix.mul_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  · have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simp [bZg, bZ, dgE, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem atInf_inv_inv {n : ℕ} (A : Matrix (Fin n) (Fin n) D.host.E) (hA : IsUnit A.det) (τ : D.what₂.Tau) :
    (atInf (embT D) A⁻¹ τ)⁻¹ = atInf (embT D) A τ := by
  apply Matrix.inv_eq_left_inv
  show A.map (embT D τ) * (A⁻¹).map (embT D τ) = 1
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hA, Matrix.map_one _ (map_zero _) (map_one _)]

def glT (B' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) (hB' : IsUnit B'.det) (τ : D.what₂.Tau) :
    GL (Fin (D.R.N D.R.m - 1)) ℂ :=
  Matrix.nonsingInvUnit ((B'.map (embT D τ)).transpose) (by
    rw [Matrix.det_transpose, show B'.map (embT D τ) = (embT D τ).mapMatrix B' from rfl, ← RingHom.map_det]
    exact hB'.map _)

theorem glT_val (B' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) (hB' : IsUnit B'.det) (τ : D.what₂.Tau) :
    ((glT B' hB' τ : GL (Fin (D.R.N D.R.m - 1)) ℂ) : Matrix _ _ ℂ) = (B'.map (embT D τ)).transpose := rfl

theorem embGL_glT (B' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) (hB' : IsUnit B'.det) (τ : D.what₂.Tau) :
    ((Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) (glT B' hB' τ) : GL (Fin (D.R.N D.R.m)) ℂ) : Matrix _ _ ℂ).transpose =
      (dgE B').map (embT D τ) := by
  rw [embGL_val, Matrix.transpose_reindex, Matrix.fromBlocks_transpose, glT_val, Matrix.transpose_transpose,
    Matrix.transpose_zero, Matrix.transpose_zero, Matrix.transpose_one]
  unfold dgE
  rw [Matrix.reindex_apply, Matrix.reindex_apply, ← Matrix.submatrix_map, Matrix.fromBlocks_map,
    Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]

theorem shift_lamT_sgT (Tf : FormsTied D u) (τ : D.what₂.Tau) :
    shiftOf (lamT u D.R.m) τ = shiftOf (sgT u) τ := by
  have hS : Formalism.L2.Col.Br.SameShift (lamTr D u τ) (sgTr D u τ) :=
    Formalism.L2.Ker.sameShiftTr D u τ (interlaceTr D u (sg_interlace Tf.valP) τ)
  have hk := D.R.m_add_three_le_k
  have hN : D.R.N D.R.m = D.R.k + D.R.m * (D.R.t + 1) := rfl
  have h1 : 0 < D.R.N D.R.m := by omega
  have h2 : 0 < D.R.N D.R.m - 1 := by omega
  have hS' : (sgTr D u τ).detShift = (lamTr D u τ).detShift := hS
  unfold lamTr sgTr at hS'
  rw [detShift_wSh _ _ h1, detShift_wSh _ _ h2] at hS'
  simp only [shiftOf, lamT, sgT]
  rw [detShift_shW _ _ h1, detShift_shW _ _ h2]
  unfold cTw at hS'
  omega

theorem exP_of (Tf : FormsTied D u)
    (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (hB : ∀ w c, IsUnit (B w c).det) :
    ∀ w, ∀ φ ∈ (D.fm u).Fi D.R.m, ∀ c, ∃ P ∈ CSpan ((D.fm u).lam D.R.m),
    (∀ s, Tf.eWz ((D.mem u).P.evz φ) c s =
      fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P ((Tf.val D.R.m le_rfl).eY s)) ∧
    ∀ z : (D.mem u).P.Wrow, Tf.valP.eW z c = fnOf _ (shiftOf (sgT u)) 1 (Formalism.L2.Ker.brTen D u P) →
      coPT Tf B w z c = Formalism.L2.Ker.brTen D u (coMT Tf B w c (φ ((D.fm u).til c))) := by
  intro w φ hφ c
  obtain ⟨P, hP, hv⟩ := val_rep Tf φ hφ c
  refine ⟨P, hP, hv, fun z hz => ?_⟩
  have hBc := hB w c
  have hU1 := atInf_inv_isUnit _ hBc
  have hbZ := bZ_isUnit Tf
  have hbZg := bZg_isUnit Tf (B w c) hBc
  have hU2 := atInf_inv_isUnit _ hbZg

  have hL : coPT Tf B w z c = (∏ τ, ((1 : D.what₂.Tau → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ) τ *
      (atInf (embT D) (B w c)⁻¹ τ)⁻¹).det ^ shiftOf (sgT u) τ) •
      blkRow (fun τ => (1 : D.what₂.Tau → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ) τ *
        (atInf (embT D) (B w c)⁻¹ τ)⁻¹) (Formalism.L2.Ker.brTen D u P) := by
    have e1 : coPT Tf B w z c = fnInv (gramC (gramP D) (embT D)) (shiftOf (sgT u)) (atInf (embT D) (B w c)⁻¹) (Tf.valP.eW z c) := by
      simp only [coPT, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval,
        LinearEquiv.coe_coe]
    rw [e1, hz, fnOf_change _ _ (atInf (embT D) (B w c)⁻¹) 1 hU1, fnInv_fnOf _ _ _ hU1]

  have hM : trEv Tf c (φ ((D.fm u).til c)) = fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P := by
    funext y
    rw [trEv_eq, hv, Equiv.apply_symm_apply]
  have hR : coMT Tf B w c (φ ((D.fm u).til c)) = (∏ τ, (atInf (embT D) (bZ u Tf.til.z0)⁻¹ τ *
      (atInf (embT D) (bZg u Tf.til.z0 (B w c))⁻¹ τ)⁻¹).det ^ shiftOf (lamT u D.R.m) τ) •
      blkRow (fun τ => atInf (embT D) (bZ u Tf.til.z0)⁻¹ τ * (atInf (embT D) (bZg u Tf.til.z0 (B w c))⁻¹ τ)⁻¹) P := by
    simp only [coMT, LinearMap.coe_comp, Function.comp_apply]
    rw [hM, mZ, fnOf_change _ _ (atInf (embT D) (bZg u Tf.til.z0 (B w c))⁻¹) (atInf (embT D) (bZ u Tf.til.z0)⁻¹) hU2,
      fnInv_fnOf _ _ _ hU2]
  have hKm : (fun τ => atInf (embT D) (bZ u Tf.til.z0)⁻¹ τ * (atInf (embT D) (bZg u Tf.til.z0 (B w c))⁻¹ τ)⁻¹) =
      fun τ => ((Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) (glT (B w c) hBc τ) : GL (Fin (D.R.N D.R.m)) ℂ) : Matrix _ _ ℂ).transpose := by
    funext τ
    rw [embGL_glT, atInf_inv_inv _ hbZg, bZg_eq_mul]
    show (bZ u Tf.til.z0)⁻¹.map (embT D τ) * (bZ u Tf.til.z0 * dgE (B w c)).map (embT D τ) = _
    rw [← Matrix.map_mul, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hbZ, Matrix.one_mul]
  have hKp : (fun τ => (1 : D.what₂.Tau → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ) τ *
      (atInf (embT D) (B w c)⁻¹ τ)⁻¹) = fun τ => ((glT (B w c) hBc τ : GL (Fin (D.R.N D.R.m - 1)) ℂ) : Matrix _ _ ℂ).transpose := by
    funext τ
    rw [glT_val, Matrix.transpose_transpose, Pi.one_apply, Matrix.one_mul, atInf_inv_inv _ hBc]
    rfl
  rw [hL, hR, hKm, hKp, map_smul, brTen_blkRow Tf]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h1 := congrFun hKm τ
  have h2 := congrFun hKp τ
  rw [h1, h2, shift_lamT_sgT Tf τ, embGL_glT, glT_val, Matrix.det_transpose]
  unfold dgE
  rw [Matrix.reindex_apply, ← Matrix.submatrix_map, Matrix.det_submatrix_equiv_self, Matrix.fromBlocks_map,
    Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one, Matrix.det_transpose]

structure RestrictionLatticeIntegralCoordinates (Tf : FormsTied D u)
    (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) : Prop where
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

theorem pendRest_of (Tf : FormsTied D u)
    (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (hB : ∀ w c, IsUnit (B w c).det)
    (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) (h : RestrictionLatticeIntegralCoordinates Tf B gP) :
    PendRest Tf B gP :=
  ⟨exP_of Tf B hB, h.lat_co, h.pt_co, h.ipV_co, h.re_petersson_self_eq_sum_coord⟩

theorem pendClauses_of (Tf : FormsTied D u)
    (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (hB : ∀ w c, IsUnit (B w c).det)
    (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) (h : RestrictionLatticeIntegralCoordinates Tf B gP) :
    PendClauses Tf B gP :=
  { coM_mem := coM_mem_of Tf B hB, coM_inj := coM_inj_of Tf B hB, coP_mem := coP_mem_of_isUnit_det Tf B hB,
    coP_inj := coP_inj_of_isUnit_det Tf B hB, exP := exP_of Tf B hB, lat_co := h.lat_co, pt_co := h.pt_co, ipV_co := h.ipV_co,
    re_petersson_self_eq_sum_coord := h.re_petersson_self_eq_sum_coord }

theorem brExists_of_rest4 (Tf : FormsTied D u) (hL : LowerLevelCompatible Tf)
    (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (hB : ∀ w c, IsUnit (B w c).det)
    (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) (h : RestrictionLatticeIntegralCoordinates Tf B gP) :
    ∃ P : Pend D u, ArchimedeanSignatureMatching P :=
  brExists_of_rest Tf B hB hL gP (pendRest_of Tf B hB gP h)

theorem blk_sqAct_eq {ι : Type} [Fintype ι] {n : ℕ} (l : ι → DomWeight n) (g : ι → GL (Fin n) ℂ)
    (Q : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => sqAct ℂ n (l τ) (g τ)) Q =
      (∏ τ, detPow ℂ n (g τ) (l τ).detShift) • blkRow (fun τ => (g τ : Matrix (Fin n) (Fin n) ℂ).transpose) Q := by
  have e : (fun τ => sqAct ℂ n (l τ) (g τ)) = fun τ => ⇑(detPow ℂ n (g τ) (l τ).detShift •
      (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (g τ : Matrix (Fin n) (Fin n) ℂ).transpose).toLinearMap) :=
    funext fun τ => (Formalism.L2.Ker.ta_sqActL_coe _ _).symm
  rw [e, Formalism.L2.Ker.blk_smul, blkRow_eq_blk]
  rfl

theorem fnOf_sqAct {ι : Type} [Fintype ι] {n : ℕ} (G : ι → Matrix (Fin n) (Fin n) ℂ) (l : ι → DomWeight n)
    (M o : ι → Matrix (Fin n) (Fin n) ℂ) (ho : ∀ τ, IsUnit (o τ).det) (g : ι → GL (Fin n) ℂ)
    (hg : ∀ τ, (g τ : Matrix (Fin n) (Fin n) ℂ) = (M τ * o τ).transpose) (Q : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    fnOf G (fun τ => (l τ).detShift) (fun τ => (o τ)⁻¹) (Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => sqAct ℂ n (l τ) (g τ)) Q) =
      fnOf G (fun τ => (l τ).detShift) M Q := by
  have hi : ∀ τ, IsUnit ((o τ)⁻¹).det := fun τ => Matrix.isUnit_nonsing_inv_det _ (ho τ)
  rw [fnOf_change G _ (fun τ => (o τ)⁻¹) M hi Q, blk_sqAct_eq]
  have hK : (fun τ => M τ * ((fun τ => (o τ)⁻¹) τ)⁻¹) = fun τ => (g τ : Matrix (Fin n) (Fin n) ℂ).transpose := by
    funext τ
    simp only [hg, Matrix.transpose_transpose, Matrix.nonsing_inv_nonsing_inv _ (ho τ)]
  rw [hK]
  congr 2
  refine Finset.prod_congr rfl fun τ _ => ?_
  unfold detPow
  rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, hg, Matrix.det_transpose,
    Matrix.nonsing_inv_nonsing_inv _ (ho τ)]

def gPof (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (hB : ∀ w c, IsUnit (B w c).det) (o : FrP D) :
    D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ :=
  fun w c τ => Matrix.nonsingInvUnit ((atInf (embT D) (B w c)⁻¹ τ * o.1 τ).transpose) (by
    rw [Matrix.det_transpose, Matrix.det_mul]; exact (atInf_inv_isUnit _ (hB w c) τ).mul (o.2 τ))

theorem shift_sgTr (τ : D.what₂.Tau) : (sgTr D u τ).detShift = shiftOf (sgT u) τ := by
  have hk := D.R.m_add_three_le_k
  have hN : D.R.N D.R.m = D.R.k + D.R.m * (D.R.t + 1) := rfl
  have h2 : 0 < D.R.N D.R.m - 1 := by omega
  simp only [shiftOf, sgT, sgTr]
  rw [detShift_shW _ _ h2, detShift_wSh _ _ h2]
  rfl

theorem cspan_sgTr : Formalism.MainNotions.product_first_zeroth_parts.CSpan (sgTr D u) = Formalism.MainNotions.product_first_zeroth_parts.CSpan (D.fm u).sg := by
  simp only [Formalism.MainNotions.product_first_zeroth_parts.CSpan, sgTr, delSq_wSh]

theorem re_petersson_self_eq_sum_coord_of_isOrthonormal (Tf : FormsTied D u)
    (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (hB : ∀ w c, IsUnit (B w c).det) (o : FrP D) (ho : o.IsON) :
    ∀ w, ∀ z ∈ (D.fm u).ptC, ((D.fm u).ipP z z).re = ∑ c, ((Nat.card ((D.fm u).stabilizer₂ c) : ℝ))⁻¹ *
      (Formalism.MainNotions.product_first_zeroth_parts.nfAll (D.fm u).sg (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gPof B hB o w c τ)) (coPT Tf B w z c))
        (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gPof B hB o w c τ)) (coPT Tf B w z c))).re := by
  classical
  intro w z hz
  have hQ : ∀ c, blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gPof B hB o w c τ)) (coPT Tf B w z c) ∈ CSpan (D.fm u).sg := by
    intro c
    have h0 := coP_mem_of_isUnit_det Tf B hB w z hz c
    rw [← cspan_sgTr] at h0
    have h1 := Formalism.L2.Ker.lc_blk_sqAct_mem _ (gPof B hB o w c) _ h0
    rw [cspan_sgTr] at h1
    exact h1
  have hE : ∀ c, Tf.valP.eW z c = fnOf _ (shiftOf (sgT u)) (fun τ => (o.1 τ)⁻¹)
      (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gPof B hB o w c τ)) (coPT Tf B w z c)) := by
    intro c
    obtain ⟨Q, _, hq⟩ := eW_rep Tf (B w c) (hB w c) z hz c
    have hc : coPT Tf B w z c = Q := by
      simp only [coPT, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval,
        LinearEquiv.coe_coe]
      rw [hq, fnInv_fnOf _ _ _ (atInf_inv_isUnit _ (hB w c))]
    have hs : shiftOf (sgT u) = fun τ => (sgTr D u τ).detShift := funext fun τ => (shift_sgTr τ).symm
    rw [hc, hq, hs, fnOf_sqAct _ (sgTr D u) (atInf (embT D) (B w c)⁻¹) o.1 o.2 _ (fun τ => rfl)]
  rw [Tf.valP.ipP o ho z z _ _ hQ hQ hE hE, Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [show ((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : ℂ)⁻¹ = (((Nat.card ((D.fm u).stabilizer₂ c) : ℝ))⁻¹ : ℝ) by push_cast; rfl,
    Complex.re_ofReal_mul]
  rfl

end Formalism.L2.Forms
