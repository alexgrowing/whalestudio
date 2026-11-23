import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureUAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFieldTensorOfIsEmptyAlgHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmExistsMoved
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftMatMapSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocCoLocDarboux
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocChrOfResEtaPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiAtContNormNontriv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweDualityForTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnLocOpsNonsplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftEMulEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralEqOfActs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnLocOpsMemberNonsplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDblLocal

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HoweLocal

theorem hTens_transpose {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    hTens c JB JA xᵀ yᵀ = hTens c JA JB x y := by
  simp only [hTens, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem symp_transpose {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) (ξ : E) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    symp c ξ JB JA xᵀ yᵀ = symp c ξ JA JB x y := by
  simp only [symp, hTens_transpose]

def dTr {R E : Type} [CommRing R] [Invertible (2 : R)] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) (ξ : E) {α β : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (JA : Matrix α α E) (JB : Matrix β β E) {κ : Type} [Fintype κ]
    (co : Darboux (symp c ξ JA JB) κ) : Darboux (symp c ξ JB JA) κ where
  e := (Matrix.transposeLinearEquiv β α R E).trans co.e
  form w w' := by
    rw [← symp_transpose c ξ JB JA w w', co.form]
    rfl

theorem dTr_e {R E : Type} [CommRing R] [Invertible (2 : R)] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) (ξ : E) {α β : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (JA : Matrix α α E) (JB : Matrix β β E) {κ : Type} [Fintype κ]
    (co : Darboux (symp c ξ JA JB) κ) (y : Matrix β α E) : (dTr c ξ JA JB co).e y = co.e yᵀ := rfl

theorem weilX : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) → ∀ [Invertible (2 : Fv F v)],
      ∀ om' : UAtGrp σ X (evFin F v) × UAtGrp σ W (evFin F v) →* Module.End ℂ ((Fin n × Fin d → Fv F v) → ℂ),
        (∀ g h, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), om' (g, h) φ ∈ SB (Fin n × Fin d → Fv F v) ∧
          Acts (evFin F v) (om (g.1, h.1)) φ (om' (g, h) φ)) →
      ∀ (eX : UAtGrp σ X (evFin F v) ≃* UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v X.J)),
        GlobalTheory.HoweLocal.IsCompIso σ X v eX →
      ∀ (eW : UAtGrp σ W (evFin F v) ≃* UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v W.J)),
        GlobalTheory.HoweLocal.IsCompIso σ W v eW →
      ∀ (co : Darboux (symp (R := Fv F v) (GlobalTheory.HoweLocal.cv σ v) (-1) (GlobalTheory.HoweLocal.Jv v X.J) (GlobalTheory.HoweLocal.Jv v W.J))
        (Fin n × Fin d)), GlobalTheory.HoweLocal.IsLocCo σ M v co →
      ∀ χXv χWv : (Fv F v ⊗[F] E)ˣ →* Circle, GlobalTheory.HoweLocal.IsLocChr χX v χXv → GlobalTheory.HoweLocal.IsLocChr χW v χWv →
      ∃ d' : Darboux (symp (R := Fv F v) (GlobalTheory.HoweLocal.cv σ v) (-1) (GlobalTheory.HoweLocal.Jv v W.J) (GlobalTheory.HoweLocal.Jv v X.J))
        (Fin n × Fin d), (∀ x : Matrix (Fin n) (Fin d) (Fv F v ⊗[F] E), d'.e xᵀ = co.e x) ∧
        IsUWeilB (GlobalTheory.HoweLocal.cv σ v) (sbClass (Fv F v)) (GlobalTheory.LatVac.psiAt ψ v) (-1) (GlobalTheory.HoweLocal.Jv v W.J)
          (GlobalTheory.HoweLocal.Jv v X.J) d' χWv ((om'.comp (eX.symm.toMonoidHom.prodMap eW.symm.toMonoidHom)).comp (MonoidHom.inl _ _)) := by
  intro hP F E _ _ _ _ _ σ hcm n d X W M ψ χX χW om hstd hXh hXd hWh hWd hrX hrW hhX hhW hweil v hv _ om' hom' eX heX eW heW
    co hco χXv χWv hlX hlW
  obtain ⟨-, ⟨dA, hdA, hB⟩, -⟩ := hweil
  refine ⟨dTr _ _ _ _ co, fun x => by rw [dTr_e, Matrix.transpose_transpose], ?_⟩
  have hL : ∀ g, ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      ((om'.comp (eX.symm.toMonoidHom.prodMap eW.symm.toMonoidHom)).comp (MonoidHom.inl _ _)) g φ ∈ SB _ ∧
      Acts (evFin F v) ((om.comp (MonoidHom.inl _ _)) (eX.symm g).1) φ
        (((om'.comp (eX.symm.toMonoidHom.prodMap eW.symm.toMonoidHom)).comp (MonoidHom.inl _ _)) g φ) := by
    intro g φ hφ
    have h := hom' (eX.symm g) 1 φ hφ
    simpa using h
  have hc : ∀ y, (dTr _ _ _ _ co).e y = GlobalTheory.LatVac.locCo dA v (y.map (GlobalTheory.HoweLocal.liftE v)) := by
    intro y
    rw [dTr_e, hco]
    have := hdA (yᵀ.map (GlobalTheory.HoweLocal.liftE v))
    simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [← this]
    rfl
  have hS := hB.1
  obtain ⟨dd, omd, h1, h2, h3⟩ := GlobalTheory.HoweLocal.DblLocal.exists_dbl_local F E σ hcm d n W.J X (Fin n × Fin d) dA ψ χW (om.comp (MonoidHom.inl _ _)) hstd hWd hXd
    hrW hhW hB v hv eX heX _ hL _ hc χWv hlW
  exact ⟨⟨⟨fun g φ hφ => (hL g φ hφ).1,
    GlobalTheory.HoweLocal.WeilImpl.impl_local F E σ d n W.J X (Fin n × Fin d) dA ψ (om.comp (MonoidHom.inl _ _)) hstd hS v hv eX heX _ hL _ hc,
    fun _ _ _ => Set.mem_univ _⟩,
    GlobalTheory.HoweLocal.LocUnitNonsplit.isUnitaryOn_local F E σ d n W.J X (Fin n × Fin d) dA ψ (om.comp (MonoidHom.inl _ _)) hstd hS v hv eX heX _ hL _ hc,
    GlobalTheory.HoweLocal.isContOn_locOps_member_nonsplit F E σ d n W.J X (Fin n × Fin d) dA ψ (om.comp (MonoidHom.inl _ _)) hstd hS v hv eX heX _ hL _ hc⟩,
    dd, omd, h1, h2, h3⟩

theorem weilW : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) → ∀ [Invertible (2 : Fv F v)],
      ∀ om' : UAtGrp σ X (evFin F v) × UAtGrp σ W (evFin F v) →* Module.End ℂ ((Fin n × Fin d → Fv F v) → ℂ),
        (∀ g h, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), om' (g, h) φ ∈ SB (Fin n × Fin d → Fv F v) ∧
          Acts (evFin F v) (om (g.1, h.1)) φ (om' (g, h) φ)) →
      ∀ (eX : UAtGrp σ X (evFin F v) ≃* UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v X.J)),
        GlobalTheory.HoweLocal.IsCompIso σ X v eX →
      ∀ (eW : UAtGrp σ W (evFin F v) ≃* UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v W.J)),
        GlobalTheory.HoweLocal.IsCompIso σ W v eW →
      ∀ (co : Darboux (symp (R := Fv F v) (GlobalTheory.HoweLocal.cv σ v) (-1) (GlobalTheory.HoweLocal.Jv v X.J) (GlobalTheory.HoweLocal.Jv v W.J))
        (Fin n × Fin d)), GlobalTheory.HoweLocal.IsLocCo σ M v co →
      ∀ χXv χWv : (Fv F v ⊗[F] E)ˣ →* Circle, GlobalTheory.HoweLocal.IsLocChr χX v χXv → GlobalTheory.HoweLocal.IsLocChr χW v χWv →
      IsUWeilB (GlobalTheory.HoweLocal.cv σ v) (sbClass (Fv F v)) (GlobalTheory.LatVac.psiAt ψ v) (-1) (GlobalTheory.HoweLocal.Jv v X.J)
        (GlobalTheory.HoweLocal.Jv v W.J) co χXv ((om'.comp (eX.symm.toMonoidHom.prodMap eW.symm.toMonoidHom)).comp (MonoidHom.inr _ _)) := by
  intro hP F E _ _ _ _ _ σ hcm n d X W M ψ χX χW om hstd hXh hXd hWh hWd hrX hrW hhX hhW hweil v hv _ om' hom' eX heX eW heW
    co hco χXv χWv hlX hlW
  obtain ⟨hB, -, -⟩ := hweil
  have hL : ∀ g, ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      ((om'.comp (eX.symm.toMonoidHom.prodMap eW.symm.toMonoidHom)).comp (MonoidHom.inr _ _)) g φ ∈ SB _ ∧
      Acts (evFin F v) ((om.comp (MonoidHom.inr _ _)) (eW.symm g).1) φ
        (((om'.comp (eX.symm.toMonoidHom.prodMap eW.symm.toMonoidHom)).comp (MonoidHom.inr _ _)) g φ) := by
    intro g φ hφ
    have h := hom' 1 (eW.symm g) φ hφ
    simpa using h
  have hS := hB.1
  obtain ⟨dd, omd, h1, h2, h3⟩ := GlobalTheory.HoweLocal.DblLocal.exists_dbl_local F E σ hcm n d X.J W (Fin n × Fin d) M.co ψ χX (om.comp (MonoidHom.inr _ _)) hstd
    hXd hWd hrX hhX hB v hv eW heW _ hL _ hco χXv hlX
  exact ⟨⟨⟨fun g φ hφ => (hL g φ hφ).1,
    GlobalTheory.HoweLocal.WeilImpl.impl_local F E σ n d X.J W (Fin n × Fin d) M.co ψ (om.comp (MonoidHom.inr _ _)) hstd hS v hv eW heW _ hL _ hco,
    fun _ _ _ => Set.mem_univ _⟩,
    GlobalTheory.HoweLocal.LocUnitNonsplit.isUnitaryOn_local F E σ n d X.J W (Fin n × Fin d) M.co ψ (om.comp (MonoidHom.inr _ _)) hstd hS v hv eW heW _ hL _ hco,
    GlobalTheory.HoweLocal.isContOn_locOps_member_nonsplit F E σ n d X.J W (Fin n × Fin d) M.co ψ (om.comp (MonoidHom.inr _ _)) hstd hS v hv eW heW _ hL _ hco⟩,
    dd, omd, h1, h2, h3⟩

theorem howeDualityFor_locOps : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.Published.HoweDualityUnitary → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) →
      ∀ om' : UAtGrp σ X (evFin F v) × UAtGrp σ W (evFin F v) →* Module.End ℂ ((Fin n × Fin d → Fv F v) → ℂ),
        (∀ g h, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), om' (g, h) φ ∈ SB (Fin n × Fin d → Fv F v) ∧
          Acts (evFin F v) (om (g.1, h.1)) φ (om' (g, h) φ)) → GlobalTheory.Published.HoweDualityFor om' := by
  intro hP hHD F E _ _ _ _ _ σ hCM n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hom v hv om' hom'
  have hinj : Function.Injective (algebraMap F (Fv F v)) := (algebraMap F (Fv F v)).injective
  haveI : CharZero (Fv F v) := charZero_of_injective_algebraMap hinj
  letI : Invertible (2 : Fv F v) := invertibleOfNonzero two_ne_zero
  letI : Field (Fv F v ⊗[F] E) := (GlobalTheory.HoweLocal.Fld.isField_of_isEmpty F E σ hCM v hv).toField
  obtain ⟨δ, hδ⟩ := GlobalTheory.HoweLocal.quad_exists F E σ hCM v
  obtain ⟨eX, heX⟩ := GlobalTheory.HoweLocal.compIso_exists F E σ hCM n X v
  obtain ⟨eW, heW⟩ := GlobalTheory.HoweLocal.compIso_exists F E σ hCM d W v
  obtain ⟨co, hco⟩ := GlobalTheory.HoweLocal.exists_isLocCo F E σ hCM n d X W M v
  obtain ⟨χXv, hcX, hrXv, hlX⟩ := GlobalTheory.HoweLocal.exists_locChr_of_resEtaPow hP F E σ hCM n χX hhX hrX v hv
  obtain ⟨χWv, hcW, hrWv, hlW⟩ := GlobalTheory.HoweLocal.exists_locChr_of_resEtaPow hP F E σ hCM d χW hhW hrW v hv
  obtain ⟨hψc, hψn, hψ1⟩ := GlobalTheory.HoweLocal.Psi.psiAt_cont_norm_nontriv F ψ hψ v
  have hcv : ∀ x : E, GlobalTheory.HoweLocal.cv σ v (Algebra.TensorProduct.includeRight x) =
      Algebra.TensorProduct.includeRight (σ x) := fun x => by
    simp [GlobalTheory.HoweLocal.cv]
  have hdet : ∀ {m : ℕ} (J : Matrix (Fin m) (Fin m) E), (GlobalTheory.HoweLocal.Jv v J).det =
      Algebra.TensorProduct.includeRight (R := F) (A := Fv F v) J.det := fun J => by
    simp only [GlobalTheory.HoweLocal.Jv]
    exact (AlgHom.map_det _ J).symm
  have hiR : Function.Injective (Algebra.TensorProduct.includeRight (R := F) (A := Fv F v) (B := E)) :=
    Algebra.TensorProduct.includeRight_injective hinj
  have hHX : IsHerm (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v X.J) := by
    refine ⟨fun i j => ?_, ?_⟩
    · simp only [GlobalTheory.HoweLocal.Jv, Matrix.map_apply, hcv, hX]
    · rw [hdet]; exact (isUnit_iff_ne_zero.mpr hXd).map _
  have hWs : ∀ i j, GlobalTheory.HoweLocal.cv σ v ((-1) * GlobalTheory.HoweLocal.Jv v W.J j i) =
      -((-1) * GlobalTheory.HoweLocal.Jv v W.J i j) := fun i j => by
    simp only [GlobalTheory.HoweLocal.Jv, Matrix.map_apply, map_mul, map_neg, map_one, hcv, hW]
    ring
  have hWd' : (GlobalTheory.HoweLocal.Jv v W.J).det ≠ 0 := by
    rw [hdet]; intro h; exact hWd (hiR (h.trans (map_zero _).symm))
  have hWeil : IsUWeilPair (GlobalTheory.HoweLocal.cv σ v) (sbClass (Fv F v)) (GlobalTheory.LatVac.psiAt ψ v) (-1)
      (GlobalTheory.HoweLocal.Jv v X.J) (GlobalTheory.HoweLocal.Jv v W.J) co χXv χWv
      (om'.comp (eX.symm.toMonoidHom.prodMap eW.symm.toMonoidHom)) :=
    ⟨weilW hP F E σ hCM n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hom v hv om' hom' eX heX eW heW co hco
        χXv χWv hlX hlW,
      weilX hP F E σ hCM n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hom v hv om' hom' eX heX eW heW co hco
        χXv χWv hlX hlW,
      GlobalTheory.HoweLocal.isContOn_locOps_nonsplit hP F E σ hCM n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hom v hv om' hom' eX heX eW heW co hco
        χXv χWv hlX hlW⟩
  have hHD' := (hHD (Fv F v) (Fv F v ⊗[F] E) (GlobalTheory.HoweLocal.cv σ v) δ hδ (GlobalTheory.LatVac.psiAt ψ v) hψc hψn hψ1 n d (-1)
    (GlobalTheory.HoweLocal.Jv v X.J) (GlobalTheory.HoweLocal.Jv v W.J) hHX (neg_ne_zero.mpr one_ne_zero) hWs hWd' χXv χWv hcX hcW
    hrXv hrWv (Fin n × Fin d) co _ hWeil).1
  have e : (om'.comp (eX.symm.toMonoidHom.prodMap eW.symm.toMonoidHom)).comp (eX.toMonoidHom.prodMap eW.toMonoidHom) = om' := by
    ext ⟨a, b⟩ : 1
    simp
  have := GlobalTheory.HoweLocal.HoweTransport.howeDualityFor_transport eX eW heX.2.1 heX.2.2 heW.2.1 heW.2.2 _ hHD'
  rwa [e] at this

theorem howeDualityFor_closure : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.Published.HoweDualityUnitary → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) →
      ∀ om' : Subgroup.closure (UAt σ X (evFin F v)) × Subgroup.closure (UAt σ W (evFin F v)) →*
          Module.End ℂ ((Fin n × Fin d → Fv F v) → ℂ),
        (∀ g h, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), om' (g, h) φ ∈ SB (Fin n × Fin d → Fv F v) ∧
          Acts (evFin F v) (om (g.1, h.1)) φ (om' (g, h) φ)) → GlobalTheory.Published.HoweDualityFor om' := by
  intro hP hHD F E _ _ _ _ _ σ hCM n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hom v hv
  have key := howeDualityFor_locOps hP hHD F E σ hCM n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hom v hv
  rw [closure_UAt σ X (evFin F v), closure_UAt σ W (evFin F v)]
  exact key

end GlobalTheory.HoweLocal
