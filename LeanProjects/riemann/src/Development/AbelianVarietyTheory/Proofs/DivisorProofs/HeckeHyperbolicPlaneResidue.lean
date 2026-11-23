import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLocType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBThetaDescentIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlCastRfl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegralBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianPlaneUnipotentIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviCharacterCuspIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneGramRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantInducedRepEquivProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentationRestrictionIntertwinerExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedCharacterCompositionSeries
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.LocTypeGood

noncomputable section

namespace GlobalTheory.LocTypeStep

section General

variable {G V V' X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup X]
  [Module ℂ X]

theorem range_le_imgSpan {I : Representation ℂ G V} {ρ : Representation ℂ G X} (T : V →ₗ[ℂ] X)
    (hT : ∀ g, T ∘ₗ I g = ρ g ∘ₗ T) : LinearMap.range T ≤ imgSpan I ρ :=
  le_iSup₂_of_le (f := fun (T : V →ₗ[ℂ] X) (_ : ∀ g, T ∘ₗ I g = ρ g ∘ₗ T) => LinearMap.range T) T hT le_rfl

theorem imgSpan_conj_le (I : Representation ℂ G V) (ρ ρ' : Representation ℂ G X) (c : G)
    (h : ∀ g, ρ' g = ρ (c * g * c⁻¹)) : imgSpan I ρ' ≤ imgSpan I ρ := by
  refine iSup₂_le fun T hT => ?_
  rintro _ ⟨v, rfl⟩
  refine range_le_imgSpan (T ∘ₗ I c⁻¹) (fun g => ?_) ⟨I c v, ?_⟩
  · refine LinearMap.ext fun w => ?_
    have h1 := LinearMap.congr_fun (hT (c⁻¹ * g * c)) (I c⁻¹ w)
    simp only [LinearMap.comp_apply, h] at h1 ⊢
    rw [show c * (c⁻¹ * g * c) * c⁻¹ = g by group] at h1
    rw [← h1, ← Module.End.mul_apply (I c⁻¹), ← Module.End.mul_apply (I _) (I c⁻¹), ← map_mul, ← map_mul]
    congr 3
    group
  · rw [LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem imgSpan_equiv_le {I : Representation ℂ G V} {I' : Representation ℂ G V'} (φ : I.Equiv I')
    (ρ : Representation ℂ G X) : imgSpan I' ρ ≤ imgSpan I ρ := by
  refine iSup₂_le fun T hT => ?_
  rintro _ ⟨v, rfl⟩
  refine range_le_imgSpan (T ∘ₗ φ.toIntertwiningMap.toLinearMap) (fun g => ?_) ⟨φ.symm v, ?_⟩
  · rw [LinearMap.comp_assoc, φ.toIntertwiningMap.isIntertwining' g, ← LinearMap.comp_assoc, hT, LinearMap.comp_assoc]
  · exact congrArg T (φ.toLinearEquiv.apply_symm_apply v)

theorem imgSpan_stable (I : Representation ℂ G V) (ρ : Representation ℂ G X) (g : G) :
    ∀ x ∈ imgSpan I ρ, ρ g x ∈ imgSpan I ρ := by
  have : imgSpan I ρ ≤ (imgSpan I ρ).comap (ρ g) := by
    refine iSup₂_le fun T hT => ?_
    rintro _ ⟨v, rfl⟩
    exact range_le_imgSpan T hT ⟨I g v, LinearMap.congr_fun (hT g) v⟩
  exact fun x hx => this hx

end General

theorem exists_glReindex_eq_conj {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] (e : n ≃ n) :
    ∃ w : GL n k, ∀ g, glReindex e g = w * g * w⁻¹ := by
  refine ⟨⟨e.symm.toPEquiv.toMatrix, e.toPEquiv.toMatrix, ?_, ?_⟩, fun g => Units.ext ?_⟩
  · rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp
  · rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp
  · show Matrix.reindex e e g.val = e.symm.toPEquiv.toMatrix * g.val * e.toPEquiv.toMatrix
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    rfl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isLevi_mul {n n₁ : ℕ} {W : Spc F E n} {W₁ : Spc F E n₁} {H : Plane E n n₁} {t s : (AE F E)ˣ}
    {γ h₁ : UA σ W₁.J} {m m' : UA σ W.J} (h : IsLevi (W₁ := W₁) H t γ m) (h' : IsLevi (W₁ := W₁) H s h₁ m') :
    IsLevi (W₁ := W₁) H (t * s) (γ * h₁) (m * m') := by
  have e : mat (m * m') = mat m * mat m' := rfl
  have e1 : mat (γ * h₁) = mat γ * mat h₁ := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [e, ← Matrix.mulVec_mulVec, h'.1, Matrix.mulVec_smul, h.1, smul_smul, Units.val_mul, mul_comm]
  · rw [e, ← Matrix.mulVec_mulVec, h'.2.1, Matrix.mulVec_smul, h.2.1, smul_smul, mul_inv_rev, Units.val_mul, map_mul]
  · rw [e, Matrix.mul_assoc, h'.2.2, e1, ← Matrix.mul_assoc, h.2.2, Matrix.mul_assoc]

theorem isLevi_inv {n n₁ : ℕ} {W : Spc F E n} {W₁ : Spc F E n₁} {H : Plane E n n₁}
    {γ : UA σ W₁.J} {m : UA σ W.J} (h : IsLevi (W₁ := W₁) H 1 γ m) : IsLevi (W₁ := W₁) H 1 γ⁻¹ m⁻¹ := by
  have hi : mat m⁻¹ * mat m = 1 := GlobalTheory.UnipCT.mat_inv_mul' m
  have hg : mat γ * mat γ⁻¹ = 1 := GlobalTheory.CTLevi.mat_mul_inv' γ
  have h1 : mat m *ᵥ incV F H.x = incV F H.x := by simpa using h.1
  have h2 : mat m *ᵥ incV F H.y = incV F H.y := by simpa using h.2.1
  refine ⟨?_, ?_, ?_⟩
  · simp only [Units.val_one, one_smul]
    conv_lhs => rw [← h1]
    rw [Matrix.mulVec_mulVec, hi, Matrix.one_mulVec]
  · simp only [inv_one, Units.val_one, map_one, one_smul]
    conv_lhs => rw [← h2]
    rw [Matrix.mulVec_mulVec, hi, Matrix.one_mulVec]
  · calc mat m⁻¹ * incM F H.ι = mat m⁻¹ * incM F H.ι * (mat γ * mat γ⁻¹) := by rw [hg, Matrix.mul_one]
      _ = mat m⁻¹ * (incM F H.ι * mat γ) * mat γ⁻¹ := by simp only [Matrix.mul_assoc]
      _ = mat m⁻¹ * (mat m * incM F H.ι) * mat γ⁻¹ := by rw [h.2.2]
      _ = incM F H.ι * mat γ⁻¹ := by rw [← Matrix.mul_assoc (mat m⁻¹), hi, Matrix.one_mul]

theorem law_levi {n n₁ : ℕ} {W : Spc F E n} {W₁ : Spc F E n₁} {H : Plane E n n₁} {χ : Chr F E} {z : ℝ}
    {T : UA σ W.J → ℂ} (hT : HasLaw W₁ H χ z T) {t : (AE F E)ˣ} {γ : UA σ W₁.J} {m m' : UA σ W.J}
    (h : IsLevi (W₁ := W₁) H t γ m) (h' : IsLevi (W₁ := W₁) H 1 γ m') (y : UA σ W.J) :
    T (m * y) = (χ t : ℂ) * (((GlobalTheory.Doubling.absE F E t : ℝ) ^ z : ℝ) : ℂ) * T (m' * y) := by
  have hc : IsLevi (W₁ := W₁) H t 1 (m * m'⁻¹) := by
    simpa using isLevi_mul h (isLevi_inv h')
  rw [← hT t _ hc (m' * y), mul_assoc, inv_mul_cancel_left]

theorem law_levi_one {n n₁ : ℕ} {W : Spc F E n} {W₁ : Spc F E n₁} {H : Plane E n n₁} {χ : Chr F E} {z : ℝ}
    {T : UA σ W.J → ℂ} (hT : HasLaw W₁ H χ z T) {γ : UA σ W₁.J} {m m' : UA σ W.J}
    (h : IsLevi (W₁ := W₁) H 1 γ m) (h' : IsLevi (W₁ := W₁) H 1 γ m') (y : UA σ W.J) :
    T (m * y) = T (m' * y) := by
  rw [law_levi hT h h']
  simp

theorem conj_mem_unip {n n₁ : ℕ} {W : Spc F E n} {W₁ : Spc F E n₁} {H : Plane E n n₁} {γ : UA σ W₁.J} {m u : UA σ W.J}
    (h : IsLevi (W₁ := W₁) H 1 γ m) (hu : u ∈ unip σ W H) : m * u * m⁻¹ ∈ unip σ W H := by
  have h' := isLevi_inv h
  have := GlobalTheory.CTLevi.conj_mem m⁻¹ u (by simpa using h'.1)
    (fun z => ⟨mat γ⁻¹ *ᵥ z, by rw [Matrix.mulVec_mulVec, h'.2.2, ← Matrix.mulVec_mulVec]⟩) hu
  simpa using this

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem exists_law_ne (hcm : IsCMExt F E σ) {α β : Chr F E} {v : Pl F} {τ : E →ₐ[F] Fv F v} (h : NotRealPow τ α β)
    (za zb : ℝ) : ∃ a : (Fv F v)ˣ,
      (α (GlobalTheory.JacGeom.idl hcm τ (a, 1⁻¹)) : ℂ) * (((GlobalTheory.Doubling.absE F E (GlobalTheory.JacGeom.idl hcm τ (a, 1⁻¹)) : ℝ) ^ za : ℝ) : ℂ) ≠
      (β (GlobalTheory.JacGeom.idl hcm τ (a, 1⁻¹)) : ℂ) * (((GlobalTheory.Doubling.absE F E (GlobalTheory.JacGeom.idl hcm τ (a, 1⁻¹)) : ℝ) ^ zb : ℝ) : ℂ) := by
  by_contra hne
  push Not at hne
  refine h (zb - za) (MonoidHom.ext fun a => Units.ext ?_)
  have h1 := hne a
  have n1 : GlobalTheory.SplitWeil.nabs (Fv F v) 1 = 1 := GlobalTheory.SmGL.nabs_eq_one _ (by simp)
  rw [inv_one, GlobalTheory.JacGeom.chr_idl, GlobalTheory.JacGeom.chr_idl, GlobalTheory.JacGeom.absE_idl, n1, map_one, map_one, Units.val_one,
    mul_one, mul_one, mul_one] at h1
  have hp := GlobalTheory.SmGL.nabs_pos' (Fv F v) a
  have hz : ((GlobalTheory.SplitWeil.nabs (Fv F v) a ^ za : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.rpow_pos_of_pos hp za).ne'
  rw [GlobalTheory.SmGL.val_absPow_ofReal, Real.rpow_sub hp, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul,
    Units.val_inv_eq_inv_val, Complex.ofReal_div, eq_div_iff hz]
  have hb : ((chrW β τ a : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  field_simp
  rw [h1]

open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.IndLineGL GlobalTheory.SplitUnitLift in

theorem hasLocType_alphaSpan : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hcm : IsCMExt F E σ) (α β : Chr F E) (v : Pl F) (τ : E →ₐ[F] Fv F v), NotRealPow τ α β →
    IsHecke F E α → IsHecke F E β → ∀ kα : ℕ, ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range α kα →
    ∀ (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), n = n₁ + 2 → form σ W.J H.x H.x = 0 →
    form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
    (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
    ∀ (εW : F) (hermW : ∀ i j, σ (W.J j i) = algebraMap F E εW * W.J i j) (hJW : IsUnit (W.J.map τ).det)
      (ε₁ : F) (herm₁ : ∀ i j, σ (W₁.J j i) = algebraMap F E ε₁ * W₁.J i j) (hJ₁ : IsUnit (W₁.J.map τ).det)
      (x x' : ℕ) (eW : Fin (x + 2 + x') ≃ Fin n) (e₁ : Fin (x + x') ≃ Fin n₁) (Kh : Set (UA σ W.J))
      (S : Submodule ℂ (UA σ W.J → ℂ)),
      (∀ f ∈ S, Continuous f ∧ ∀ γ ∈ ratU σ W.J, ∀ z, f (γ * z) = f z) →
      (∀ f ∈ S, HasLocType hcm τ W.J εW hermW hJW eW (chrW α τ) (chrW β τ) f) →
      ∀ g ∈ alphaSpan W₁ H α β ((x' : ℝ) / 2) (((x + 2 : ℕ) : ℝ) / 2) Kh S,
        HasLocType hcm τ W₁.J ε₁ herm₁ hJ₁ e₁ (chrW α τ) (chrW β τ) g := by
  intro hK F E _ _ _ _ _ σ hcm α β v τ hgen hα hβ kα hres n n₁ W W₁ H hn hxx hyy hxy horth hgram εW hermW hJW ε₁ herm₁ hJ₁
    x x' eW e₁ Kh S hreg hloc
  obtain rfl : n = x + 2 + x' := by simpa using (Fintype.card_congr eW).symm
  obtain rfl : n₁ = x + x' := by simpa using (Fintype.card_congr e₁).symm
  have hdet : ∀ {d : ℕ} (J : Matrix (Fin d) (Fin d) E), IsUnit (J.map τ).det → J.det ≠ 0 := fun J hJ h0 => by
    have hd : (J.map τ).det = τ J.det := (AlgHom.map_det τ J).symm
    rw [hd, h0, map_zero] at hJ
    exact not_isUnit_zero hJ
  have hcc := GlobalTheory.T.skew_hermitian_plane_unipotent_identity F E σ hcm _ _ W W₁ H hn hxx hyy hxy horth hgram εW hermW (hdet _ hJW) (hdet _ hJ₁)
  let e : (Σ i : Fin 3, Fin (blk3 (x + x') i)) ≃ Fin (x + 2 + x') :=
    Fintype.equivOfCardEq (by simp [Fin.sum_univ_three]; omega)
  obtain ⟨c, hcu, hcm1, hct⟩ := GlobalTheory.T.hyperbolic_plane_gram_restriction F E σ hcm v τ _ _ W W₁ H hn hxx hyy hxy horth hgram εW hermW hJW ε₁ herm₁ hJ₁ e
  obtain ⟨a, ha⟩ := exists_law_ne hcm hgen ((x' : ℝ) / 2) (((x + 2 : ℕ) : ℝ) / 2)
  obtain ⟨D, Λ, hD1, hD2, hD3⟩ := GlobalTheory.T.levi_character_cusp_integral F E σ _ _ W W₁ H α β _ _ hcc _ _ (hct a 1) ha
  have sα : IsSmoothChar (chrW α τ) := (GlobalTheory.ChrWLocal.chrW_local F E α hα v τ).1.1
  have sβ : IsSmoothChar (chrW β τ) := (GlobalTheory.ChrWLocal.chrW_local F E β hβ v τ).1.1
  obtain ⟨l, A, hl, hA1, hA2⟩ := GlobalTheory.T.induced_character_composition_series hK.geometricLemmaFiltration (Fv F v) x x' _ _ sα sβ hgen e
  obtain ⟨φW⟩ := GlobalTheory.T.determinant_induced_rep_equiv_product (Fv F v) (x + 2) x' (chrW α τ) (chrW β τ)
  obtain ⟨φ₁⟩ := GlobalTheory.T.determinant_induced_rep_equiv_product (Fv F v) x x' (chrW α τ) (chrW β τ)
  obtain ⟨w, hw⟩ := exists_glReindex_eq_conj (k := Fv F v) eW
  obtain ⟨w₁, hw₁⟩ := exists_glReindex_eq_conj (k := Fv F v) e₁
  let π : Representation ℂ (GL (Fin (x + 2 + x')) (Fv F v)) (UA σ W.J → ℂ) :=
    (rightReg ℂ (UA σ W.J) ℂ).comp ((liftU hcm τ W.J εW hermW hJW).comp (MulAut.conj c).toMonoidHom)
  have hπ : ∀ g φ, π g φ = fun z => φ (z * liftU hcm τ W.J εW hermW hJW (c * g * c⁻¹)) := fun _ _ => rfl
  have hle : imgSpan (GlobalTheory.ThK.MidJac.detInd (x + 2) x' (chrW α τ) (chrW β τ)) (rtrAt hcm τ W.J εW hermW hJW eW) ≤
      imgSpan (prod₂ (detRep (Fin (x + 2)) (chrW α τ)) (detRep (Fin x') (chrW β τ))) π := by
    refine (imgSpan_equiv_le φW.symm _).trans (imgSpan_conj_le _ _ _ (c⁻¹ * w) fun g => ?_)
    show rightReg ℂ (UA σ W.J) ℂ (liftU hcm τ W.J εW hermW hJW (glReindex eW g)) =
      rightReg ℂ (UA σ W.J) ℂ (liftU hcm τ W.J εW hermW hJW (c * (c⁻¹ * w * g * (c⁻¹ * w)⁻¹) * c⁻¹))
    rw [hw]
    congr 2
    group
  have hle₁ : imgSpan (prod₂ (detRep (Fin x) (chrW α τ)) (detRep (Fin x') (chrW β τ)))
      ((rightReg ℂ (UA σ W₁.J) ℂ).comp (liftU hcm τ W₁.J ε₁ herm₁ hJ₁)) ≤
      imgSpan (GlobalTheory.ThK.MidJac.detInd x x' (chrW α τ) (chrW β τ)) (rtrAt hcm τ W₁.J ε₁ herm₁ hJ₁ e₁) := by
    refine (imgSpan_equiv_le φ₁ _).trans (imgSpan_conj_le _ _ _ w₁⁻¹ fun g => ?_)
    show rightReg ℂ (UA σ W₁.J) ℂ (liftU hcm τ W₁.J ε₁ herm₁ hJ₁ g) =
      rightReg ℂ (UA σ W₁.J) ℂ (liftU hcm τ W₁.J ε₁ herm₁ hJ₁ (glReindex e₁ (w₁⁻¹ * g * w₁⁻¹⁻¹)))
    rw [hw₁]
    congr 2
    group
  have hinj : Function.Injective (liftU hcm τ W₁.J ε₁ herm₁ hJ₁) := fun g g' h => Units.ext (by
    rw [← liftU_piW hcm τ W₁.J ε₁ herm₁ hJ₁ g, ← liftU_piW hcm τ W₁.J ε₁ herm₁ hJ₁ g', h])
  intro g hg y₁
  unfold alphaSpan at hg
  induction hg using Submodule.span_induction with
  | zero => exact zero_mem _
  | add g g' _ _ h h' => exact add_mem h h'
  | smul r g _ h => exact Submodule.smul_mem _ r h
  | mem g hg =>
    obtain ⟨f, hf, fa, fb, hs, h, -, hex, hg⟩ := hg
    choose M hM using hex
    obtain ⟨hfD, hfa⟩ := hD1 f fa fb (hreg f hf).1 (hreg f hf).2 hs
    let Λ₁ : (UA σ W.J → ℂ) →ₗ[ℂ] (UA σ W₁.J → ℂ) := LinearMap.funLeft ℂ ℂ M ∘ₗ Λ
    have hΛ₁ : ∀ φ ∈ D, ∀ g' h₁, Λ₁ (π g' φ) h₁ = Λ φ (M h₁ * liftU hcm τ W.J εW hermW hJW (c * g' * c⁻¹)) :=
      fun φ hφ g' h₁ => congrFun (hD2 φ hφ _).2 (M h₁)
    have key := GlobalTheory.T.representation_restriction_intertwiner_exists (Fv F v) _ _ e _ _ _ _ (prod₂ (detRep (Fin (x + 2)) (chrW α τ)) (detRep (Fin x') (chrW β τ)))
      (prod₂ (detRep (Fin x) (chrW α τ)) (detRep (Fin x') (chrW β τ))) π (liftU hcm τ W₁.J ε₁ herm₁ hJ₁)
      (isSmooth_prod₂ _ _) hinj
      (fun p => (((chrW α τ * absPow (Fv F v) ((x' : ℂ) / 2)) p.1 * (chrW α τ * absPow (Fv F v) (-(x' : ℂ) / 2)) p.2 : ℂˣ) : ℂ))
      l hl A hA1 hA2 (D ⊓ imgSpan (prod₂ (detRep (Fin (x + 2)) (chrW α τ)) (detRep (Fin x') (chrW β τ))) π) Λ₁ inf_le_right
      (fun g' φ hφ => ⟨(hD2 φ hφ.1 _).1, imgSpan_stable _ _ g' φ hφ.2⟩)
      (fun φ hφ u hu => funext fun h₁ => by
        rw [hΛ₁ φ hφ.1, show M h₁ * liftU hcm τ W.J εW hermW hJW (c * u * c⁻¹) =
          M h₁ * liftU hcm τ W.J εW hermW hJW (c * u * c⁻¹) * (M h₁)⁻¹ * M h₁ by group]
        exact (hD3 φ hφ.1).2 _ (conj_mem_unip (hM h₁) (hcu u hu)) _)
      (fun φ hφ k => funext fun h₁ => by
        rw [hΛ₁ φ hφ.1]
        have := law_levi_one (hD3 φ hφ.1).1 (by simpa using isLevi_mul (hM h₁) (hcm1 k))
          (hM (h₁ * liftU hcm τ W₁.J ε₁ herm₁ hJ₁ k)) 1
        rw [mul_one, mul_one] at this
        refine Eq.trans ?_ this
        simp)
      (fun φ hφ t₁ t₂ => funext fun h₁ => by
        rw [hΛ₁ φ hφ.1]
        have h2 := isLevi_mul (hM h₁) (hct t₁ t₂)
        rw [one_mul, mul_one] at h2
        have := law_levi (hD3 φ hφ.1).1 h2 (hM h₁) 1
        rw [mul_one, mul_one, GlobalTheory.JacGeom.char_idl hcm α hres] at this
        exact this)
      (fun z => f (z * (M y₁ * h))) ⟨(hD2 f hfD _).1, hle (hloc f hf _)⟩
    refine hle₁ ?_
    convert key using 1
    funext h₁
    have h2 := isLevi_mul (hM h₁) (hM y₁)
    rw [one_mul] at h2
    rw [hg _ _ h2, mul_assoc, ← hfa]
    exact (congrFun (hD2 f hfD (M y₁ * h)).2 (M h₁)).symm

end GlobalTheory.LocTypeStep
