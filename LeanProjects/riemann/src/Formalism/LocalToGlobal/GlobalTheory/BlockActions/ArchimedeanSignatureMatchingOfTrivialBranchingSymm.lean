import Formalism.LocalToGlobal.HermitianForms.TiedBrProof
import Formalism.LocalToGlobal.HermitianForms.TiedSym

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix MvPolynomial NumberField

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem beOn_closedS (Tf : FormsTiedSym D u Ch chOf) (h : Formalism.L2.Ker.BeOnTie D u) (τ : D.what₂.Tau) :
    (D.fm u).beOn τ = Formalism.L2.Ker.beOnVal (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) := by
  rw [h τ]
  exact Formalism.L2.Ker.beOnEq D u τ (interlaceTr D u (sg_interlace Tf.valP) τ)

theorem beOn_posS (Tf : FormsTiedSym D u Ch chOf) (h : Formalism.L2.Ker.BeOnTie D u) (τ : D.what₂.Tau) :
    0 < (D.fm u).beOn τ := by
  rw [beOn_closedS Tf h τ]
  have hI0 := interlaceTr D u (sg_interlace Tf.valP) τ
  have hI := (Formalism.L2.Ker.interlace_iff _ _ (Nm_succ D.R)).1 hI0
  unfold Formalism.L2.Ker.beOnVal
  apply mul_pos
  · exact abs_pos.mpr (by exact_mod_cast Formalism.L2.Ker.cBr_ne_zero (Nm_succ D.R).symm _ _ hI)
  · exact Real.sqrt_pos.mpr (Formalism.L2.Ker.nm_kapR_pos _ _ _ hI (Formalism.L2.Ker.sameShiftTr D u τ hI0))

def LowerMapTieSym (Tf : FormsTiedSym D u Ch chOf) : Prop :=
  IsUnit (bZ u Tf.til.z0).det → ∀ (ψ : (D.mem u).P.Wz) (c : (D.fm u).clsP)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ),
    P ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m) →
    (∀ s, Tf.eWz ψ c s =
      fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s)) →
    Tf.valP.eW ((D.mem u).P.lowerMap ψ) c = fnOf _ (shiftOf (sgT u)) 1 (Formalism.L2.Ker.brTen D u P)

structure LowerSymmetricCompatible (Tf : FormsTiedSym D u Ch chOf) : Prop where
  beOn : Formalism.L2.Ker.BeOnTie D u
  map : LowerMapTieSym Tf

theorem LowerMapTieSym.pt_eq {Tf : FormsTiedSym D u Ch chOf} (h : LowerMapTieSym Tf) (hB : IsUnit (bZ u Tf.til.z0).det) (φ : Fn D u D.R.m) (c : (D.fm u).clsP)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ) (hP : P ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m))
    (hv : ∀ s, Tf.eWz ((D.mem u).P.evz φ) c s =
      fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s)) :
    Tf.valP.eW (Pt D u φ) c = fnOf _ (shiftOf (sgT u)) 1 (Formalism.L2.Ker.brTen D u P) :=
  h hB _ c P hP hv

theorem archimedeanSignatureMatching_of_trivial_branching_symm (Tf : FormsTiedSym D u Ch chOf) (P : Pend D u)
    (hP : ∀ τ, P.br τ = Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ)) : ArchimedeanSignatureMatching P := by
  intro τ
  rw [hP τ]
  exact Formalism.L2.Ker.brOneIsBr D u τ (interlaceTr D u (sg_interlace Tf.valP) τ)

theorem rep_uniqueS (Tf : FormsTiedSym D u Ch chOf) (hB : IsUnit (bZ u Tf.til.z0).det)
    (P P' : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ)
    (h : ∀ s, fnOf (gramC (gramN D D.R.m le_rfl) (embT D)) (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s) =
      fnOf (gramC (gramN D D.R.m le_rfl) (embT D)) (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P' ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s)) :
    P = P' := by
  apply fnOf_injective _ _ _ (mZ_isUnit hB)
  funext y
  obtain ⟨s, rfl⟩ := (Tf.val D.R.m le_rfl (Or.inr rfl)).eY.surjective y
  exact h s

theorem quotient_not_in_range_symmetric (Tf : FormsTiedSym D u Ch chOf) (x : Fin (D.R.N D.R.m - 1) → D.host.E) :
    iXm D *ᵥ x ≠ fun i => Tf.til.z0 i / ((D.mem u).A.T : D.host.E) := by
  letI := D.host.cmStar
  obtain ⟨a, ha⟩ := Tf.til.lastCoordinateUniformizerVector_spans_orthogonal_line
  have hT : ((D.mem u).A.T : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero
  have ha0 : a ≠ 0 := by
    rintro rfl
    have h := Tf.til.hermitianForm_lastCoordinateUniformizerVector_self
    rw [ha, zero_smul] at h
    simp [Formalism.UG.hform] at h
    exact hT h.symm
  intro hx
  simp only [iXm, LinearMap.toMatrix'_mulVec] at hx
  have hc : iXc D x = (a / ((D.mem u).A.T : D.host.E)) • zc D := by
    rw [hx]; funext i; rw [ha]; simp [Pi.smul_apply, smul_eq_mul]; ring
  unfold iXc zc at hc
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, ← map_smul,
    EmbeddingLike.apply_eq_iff_eq] at hc
  have h1 := D.sp.z_orth ((D.sp.X'.frame.equivFun.trans
      (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankP D)).symm)).symm x)
  rw [hc, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul] at h1
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact div_ne_zero ha0 hT ((map_eq_zero _).mp h2)
  · exact D.sp.z_anis h2

theorem bZ_isUnitS (Tf : FormsTiedSym D u Ch chOf) : IsUnit (bZ u Tf.til.z0).det :=
  isUnit_det_cols (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ D.R) (iXm D) (fun i => Tf.til.z0 i / ((D.mem u).A.T : D.host.E))
    (iXm_mulVec_injective D) (quotient_not_in_range_symmetric Tf)

def trEvS (Tf : FormsTiedSym D u Ch chOf) (c : (D.fm u).clsP) :
    ((D.mem u).C.Y D.R.m → ℂ) →ₗ[ℂ] (Fr D D.R.m le_rfl → ℂ) :=
  ((((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi (Tf.tilAd.ka c))⁻¹ : ℂˣ) : ℂ) •
    LinearMap.funLeft ℂ ℂ (fun y : Fr D D.R.m le_rfl => (Tf.val D.R.m le_rfl (Or.inr rfl)).eY.symm
      (y.tr (atInf (embT D) ((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E))
        (isUnit_det_atInf (embT D) ((Tf.til.ga c).1)⁻¹)))

def coMTS (Tf : FormsTiedSym D u Ch chOf) (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (w : D.what₂.places.Pl) (c : (D.fm u).clsP) :
    ((D.mem u).C.Y D.R.m → ℂ) →ₗ[ℂ] MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ :=
  fnInv (gramC (gramN D D.R.m le_rfl) (embT D)) (shiftOf (lamT u D.R.m))
    (atInf (embT D) (bZg u Tf.til.z0 (B w c))⁻¹) ∘ₗ trEvS Tf c

def coPTS (Tf : FormsTiedSym D u Ch chOf) (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (w : D.what₂.places.Pl) :
    (D.mem u).P.Wrow →ₗ[ℂ] ((D.fm u).clsP → MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ) :=
  LinearMap.pi fun c => fnInv (gramC (gramP D) (embT D)) (shiftOf (sgT u)) (atInf (embT D) (B w c)⁻¹) ∘ₗ
    (LinearMap.proj c ∘ₗ Tf.valP.eW.toLinearMap)

theorem trEv_eqS (Tf : FormsTiedSym D u Ch chOf) (φ : Fn D u D.R.m) (c : (D.fm u).clsP) (y : Fr D D.R.m le_rfl) :
    trEvS Tf c (φ ((D.fm u).til c)) y = Tf.eWz ((D.mem u).P.evz φ) c ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY.symm y) := by
  rw [Tf.evz φ c _ ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY.symm
      (y.tr (atInf (embT D) ((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E))
        (isUnit_det_atInf (embT D) ((Tf.til.ga c).1)⁻¹)))]
  · rfl
  · intro τ
    simp only [Equiv.apply_symm_apply]
    show y.1 τ = atInf (embT D) (Tf.til.ga c).1.1 τ *
      (atInf (embT D) ((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E) τ * y.1 τ)
    rw [← Matrix.mul_assoc, atInf_mul_inv, Matrix.one_mul]

theorem coPTS_Pt_eq_brTen_coMTS (Tf : FormsTiedSym D u Ch chOf) (hB : IsUnit (bZ u Tf.til.z0).det) (hL : LowerMapTieSym Tf) (φ : Fn D u D.R.m)
    (c : (D.fm u).clsP) (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ)
    (hP : P ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m))
    (hv : ∀ s, Tf.eWz ((D.mem u).P.evz φ) c s =
      fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s)) (w : D.what₂.places.Pl) :
    coPTS Tf (fun _ _ => 1) w (Pt D u φ) c = Formalism.L2.Ker.brTen D u (coMTS Tf (fun _ _ => 1) w c (φ ((D.fm u).til c))) := by
  have hM : trEvS Tf c (φ ((D.fm u).til c)) =
      fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P := by
    funext y
    rw [trEv_eqS, hv, Equiv.apply_symm_apply]
  simp only [coPTS, coMTS, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
    Function.eval, LinearEquiv.coe_coe]
  rw [hL.pt_eq hB φ c P hP hv, hM, bZg_one]
  have e2 : fnInv (gramC (gramN D D.R.m le_rfl) (embT D)) (shiftOf (lamT u D.R.m)) (atInf (embT D) (bZ u Tf.til.z0)⁻¹)
      (fnOf (gramC (gramN D D.R.m le_rfl) (embT D)) (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P) = P :=
    fnInv_fnOf _ _ _ (mZ_isUnit hB) P
  have h1 : atInf (embT D) ((1 : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)⁻¹) =
      (1 : D.what₂.Tau → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ) := by
    funext τ; simp [atInf]
  have e1 : fnInv (gramC (gramP D) (embT D)) (shiftOf (sgT u))
      (atInf (embT D) ((1 : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)⁻¹))
      (fnOf (gramC (gramP D) (embT D)) (shiftOf (sgT u)) 1 (Formalism.L2.Ker.brTen D u P)) = Formalism.L2.Ker.brTen D u P := by
    rw [h1]; exact fnInv_fnOf _ _ _ (fun τ => by simp) _
  rw [e1, e2]

set_option maxHeartbeats 2000000 in

theorem val_repS (Tf : FormsTiedSym D u Ch chOf) (φ : Formalism.MainNotions.product_first_zeroth_parts.Fn D u D.R.m) (hφ : φ ∈ (D.fm u).Fi D.R.m) (c : (D.fm u).clsP) :
    ∃ P ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m), ∀ s, Tf.eWz ((D.mem u).P.evz φ) c s =
      fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s) := by
  have hF := ((Tf.val D.R.m le_rfl (Or.inr rfl)).Fi φ).1 hφ
  obtain ⟨g, hg, hres⟩ := Submodule.mem_map.1 hF
  have hval := (Submodule.mem_pi.1 (Submodule.mem_inf.1 hg).2) ((Tf.cls D.R.m le_rfl (Or.inr rfl)).y ((D.fm u).til c)) (Set.mem_univ _)
  obtain ⟨P0, hP0, hfn⟩ := Submodule.mem_map.1 hval
  have hP0' : P0 ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m) := by
    have := CSpan_shW ((D.fm u).lam D.R.m) (fun _ => ((D.R.m * (D.R.t + 1) / 2 : ℕ) : ℤ))
    unfold lamT at hP0
    rw [this] at hP0
    exact hP0
  have hφv : ∀ z, φ ((D.fm u).til c) ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY.symm z) =
      fnOf _ (shiftOf (lamT u D.R.m)) 1 P0 z := by
    intro z
    have := congrFun (congrFun hres ((D.fm u).til c)) z
    rw [← this, hfn]
    rfl
  set ginv : GL (Fin (D.R.N D.R.m)) D.host.E := ((Tf.til.ga c).1)⁻¹
  set M' : D.what₂.Tau → Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ := atInf (embT D) (ginv : Matrix _ _ D.host.E)
  have hB := mZ_isUnit (bZ_isUnitS Tf)
  obtain ⟨P, hP, hPy⟩ := exists_rep ((D.fm u).lam D.R.m) _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) M' hB
    (isUnit_det_atInf (embT D) ginv) P0 hP0' ((((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi (Tf.tilAd.ka c))⁻¹ : ℂˣ) : ℂ)
  refine ⟨P, hP, fun s => ?_⟩
  rw [Tf.evz φ c s ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY.symm (((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s).tr M' (isUnit_det_atInf (embT D) ginv)))]
  · rw [hφv]; exact hPy _
  · intro τ
    simp only [Equiv.apply_symm_apply]
    show ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s).1 τ = atInf (embT D) (Tf.til.ga c).1.1 τ * (M' τ * ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s).1 τ)
    rw [← Matrix.mul_assoc, atInf_mul_inv, Matrix.one_mul]

end Formalism.L2.GlobalTheoryTheory.Br
