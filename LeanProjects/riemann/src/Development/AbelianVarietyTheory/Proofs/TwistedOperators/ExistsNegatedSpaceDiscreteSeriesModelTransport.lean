import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsDiscreteSeriesNegSignatureOfIsDiscreteSeriesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AutomorphicCuspFormsHermitianSpaceSignTwistStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompatStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

namespace GlobalTheory.NegModel

variable {D : D7}

def negM {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) : DSModel (sgn true V) fun τ => GlobalTheory.SignedHC.flip (S τ) where
  H := M.H
  σ := M.σ
  lam := M.lam
  ε τ a := !M.ε τ a
  fr := M.fr
  enum τ := by
    obtain ⟨h1, q, hq, hS⟩ := M.enum τ
    refine ⟨h1, q, hq, ?_⟩
    rw [hS, GlobalTheory.SignedHC.flip, Finset.image_image]
    rfl
  ds τ := GlobalTheory.T.isDiscreteSeries_neg_signature_of_isDiscreteSeries _ _ _ _ _ (M.ds τ)
  fr_unit := M.fr_unit
  fr_gram τ := by
    have e : gramAt D (neg V) τ = -gramAt D V τ := by ext i j; simp [gramAt, neg_gram]
    have h : Formalism.REAL.Jm (fun a => !M.ε τ a) = -Formalism.REAL.Jm (M.ε τ) := by
      ext a b
      by_cases hab : a = b
      · subst hab; cases h : M.ε τ a <;> simp [Formalism.REAL.Jm, h]
      · simp [Formalism.REAL.Jm, hab]
    show _ = gramAt D (neg V) τ
    rw [e, h, ← M.fr_gram τ, Matrix.mul_neg, Matrix.neg_mul]

variable {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)

theorem negM_rep (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : (negM M).rep τ g = M.rep τ g := rfl

variable (θ : InfFam D)

theorem negM_sm (hθ : IsInfFam θ) (τ : D.what₂.Tau) : (negM M).sm τ = M.sm τ := by
  unfold DSModel.sm
  rw [(GlobalTheory.T.signedUnitaryGroup_compat D θ hθ true V).lie τ]
  rfl

end GlobalTheory.NegModel

namespace GlobalTheory.NegModel
variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (θ : InfFam D) (hθ : IsInfFam θ)

def smEquiv (τ : D.what₂.Tau) : (negM M).sm τ ≃ₗ[ℂ] M.sm τ := LinearEquiv.ofEq _ _ (negM_sm M θ hθ τ)

theorem coe_smEquiv (τ : D.what₂.Tau) (w : (negM M).sm τ) : ((smEquiv M θ hθ τ w : M.sm τ) : M.H τ) = (w : (negM M).H τ) :=
  LinearEquiv.coe_ofEq_apply (negM_sm M θ hθ τ) w

def smTEquiv : SmT (negM M) ≃ₗ[ℂ] SmT M := PiTensorProduct.congr fun τ => smEquiv M θ hθ τ

theorem smTEquiv_tprod (v : (negM M).Vec) :
    smTEquiv M θ hθ (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ fun τ => smEquiv M θ hθ τ (v τ) :=
  PiTensorProduct.congr_tprod _ _

theorem inclT_smTEquiv_tprod (v : (negM M).Vec) :
    inclT M (smTEquiv M θ hθ (PiTensorProduct.tprod ℂ v)) = inclT (negM M) (PiTensorProduct.tprod ℂ v) := by
  rw [smTEquiv_tprod]
  unfold inclT
  rw [PiTensorProduct.map_tprod, PiTensorProduct.map_tprod]
  exact congrArg (PiTensorProduct.tprod ℂ) (funext fun i => coe_smEquiv M θ hθ i (v i))

theorem inclT_smTEquiv (x : SmT (negM M)) : inclT M (smTEquiv M θ hθ x) = inclT (negM M) x := by
  have : (inclT M).comp (smTEquiv M θ hθ).toLinearMap = inclT (negM M) :=
    PiTensorProduct.ext (MultilinearMap.ext fun v => inclT_smTEquiv_tprod M θ hθ v)
  exact LinearMap.congr_fun this x

theorem cart_negM (τ : D.what₂.Tau) : cart (negM M) τ = sgnM true (cart M τ) := by
  have h : Formalism.REAL.Jm (fun a => !M.ε τ a) = -Formalism.REAL.Jm (M.ε τ) := by
    ext a b
    by_cases hab : a = b
    · subst hab; cases h : M.ε τ a <;> simp [Formalism.REAL.Jm, h]
    · simp [Formalism.REAL.Jm, hab]
  show (M.fr τ)⁻¹ * Formalism.REAL.Jm (fun a => !M.ε τ a) * M.fr τ = -((M.fr τ)⁻¹ * Formalism.REAL.Jm (M.ε τ) * M.fr τ)
  rw [h, Matrix.mul_neg, Matrix.neg_mul]

end GlobalTheory.NegModel

namespace GlobalTheory.NegModel
variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (θ : InfFam D) (hθ : IsInfFam θ)

theorem coe_smEquiv_symm (τ : D.what₂.Tau) (w : M.sm τ) : (((smEquiv M θ hθ τ).symm w : (negM M).sm τ) : (negM M).H τ) = (w : M.H τ) := by
  have h := coe_smEquiv M θ hθ τ ((smEquiv M θ hθ τ).symm w)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

def toNeg : MMap M →ₗ[ℂ] MMap (negM M) where
  toFun T := (LinearMap.funLeft ℂ ℂ (ofSgn true V)).compMultilinearMap
    (T.compLinearMap fun τ => (smEquiv M θ hθ τ).toLinearMap)
  map_add' T T' := by ext v x; simp
  map_smul' c T := by ext v x; simp

def ofNeg : MMap (negM M) →ₗ[ℂ] MMap M where
  toFun T := (LinearMap.funLeft ℂ ℂ (ofSgn true V).symm).compMultilinearMap
    (T.compLinearMap fun τ => (smEquiv M θ hθ τ).symm.toLinearMap)
  map_add' T T' := by ext v x; simp
  map_smul' c T := by ext v x; simp

theorem toNeg_apply (T : MMap M) (v : (negM M).Vec) (x : GA D (sgn true V)) :
    toNeg M θ hθ T v x = T (fun τ => smEquiv M θ hθ τ (v τ)) (ofSgn true V x) := rfl

theorem ofNeg_apply (T : MMap (negM M)) (v : M.Vec) (x : GA D V) :
    ofNeg M θ hθ T v x = T (fun τ => (smEquiv M θ hθ τ).symm (v τ)) ((ofSgn true V).symm x) := rfl

open Classical in
theorem eq_update (v : (negM M).Vec) (τ : D.what₂.Tau) (w : (negM M).sm τ) :
    (fun ρ => smEquiv M θ hθ ρ (Function.update v τ w ρ)) = Function.update (fun ρ => smEquiv M θ hθ ρ (v ρ)) τ (smEquiv M θ hθ τ w) :=
  funext fun ρ => Function.apply_update (fun ρ (u : (negM M).sm ρ) => smEquiv M θ hθ ρ u) v τ w ρ

open Classical in
theorem eq_symm_update (v : M.Vec) (τ : D.what₂.Tau) (w : M.sm τ) :
    (fun ρ => (smEquiv M θ hθ ρ).symm (Function.update v τ w ρ)) =
      Function.update (fun ρ => (smEquiv M θ hθ ρ).symm (v ρ)) τ ((smEquiv M θ hθ τ).symm w) :=
  funext fun ρ => Function.apply_update (fun ρ (u : M.sm ρ) => (smEquiv M θ hθ ρ).symm u) v τ w ρ

theorem isMultMap_toNeg {T : MMap M} (hT : IsMultMap θ M ∅ 1 T) : IsMultMap θ (negM M) ∅ 1 (toNeg M θ hθ T) where
  aut v := ((GlobalTheory.T.automorphic_cusp_forms_hermitianSpaceSignTwist D θ hθ true V _).1).2 (hT.aut _)
  cusp v := ((GlobalTheory.T.automorphic_cusp_forms_hermitianSpaceSignTwist D θ hθ true V _).2).2 (hT.cusp _)
  lev v k hk := absurd hk (Set.notMem_empty _)
  equiv τ g hg v w hw := by
    classical
    have hg' : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := (GlobalTheory.T.signedUnitaryGroup_compat D θ hθ true V).grp τ ▸ hg
    have hw' : ((smEquiv M θ hθ τ w : M.sm τ) : M.H τ) = M.rep τ g ((smEquiv M θ hθ τ (v τ) : M.sm τ) : M.H τ) := by
      rw [coe_smEquiv, coe_smEquiv]; exact hw
    have h := hT.equiv τ g hg' (fun ρ => smEquiv M θ hθ ρ (v ρ)) (smEquiv M θ hθ τ w) hw'
    funext x
    rw [toNeg_apply, eq_update, h]
    show T (fun ρ => smEquiv M θ hθ ρ (v ρ)) (ofSgn true V x * atTau θ V τ g) =
      T (fun ρ => smEquiv M θ hθ ρ (v ρ)) (ofSgn true V (x * atTau θ (sgn true V) τ g))
    rw [map_mul, (GlobalTheory.T.signedUnitaryGroup_compat D θ hθ true V).atTau τ g]
  cont τ v x := by
    classical
    obtain ⟨ℓ, hℓ, hℓw⟩ := hT.cont τ (fun ρ => smEquiv M θ hθ ρ (v ρ)) (ofSgn true V x)
    refine ⟨ℓ, ?_, fun w => ?_⟩
    · rw [(GlobalTheory.T.signedUnitaryGroup_compat D θ hθ true V).lie τ]; exact hℓ
    · rw [toNeg_apply, eq_update, ← hℓw, coe_smEquiv]; rfl

theorem isMultMap_ofNeg {T : MMap (negM M)} (hT : IsMultMap θ (negM M) ∅ 1 T) : IsMultMap θ M ∅ 1 (ofNeg M θ hθ T) where
  aut v := by
    have e : (fun g => ofNeg M θ hθ T v (ofSgn true V g)) = T (fun τ => (smEquiv M θ hθ τ).symm (v τ)) := by
      funext g; rw [ofNeg_apply, MulEquiv.symm_apply_apply]
    exact ((GlobalTheory.T.automorphic_cusp_forms_hermitianSpaceSignTwist D θ hθ true V _).1).1 (e ▸ hT.aut _)
  cusp v := by
    have e : (fun g => ofNeg M θ hθ T v (ofSgn true V g)) = T (fun τ => (smEquiv M θ hθ τ).symm (v τ)) := by
      funext g; rw [ofNeg_apply, MulEquiv.symm_apply_apply]
    exact ((GlobalTheory.T.automorphic_cusp_forms_hermitianSpaceSignTwist D θ hθ true V _).2).1 (e ▸ hT.cusp _)
  lev v k hk := absurd hk (Set.notMem_empty _)
  equiv τ g hg v w hw := by
    classical
    have hg' : g ∈ Formalism.QuantumDeterminants.UH (gramAt D (sgn true V) τ) := ((GlobalTheory.T.signedUnitaryGroup_compat D θ hθ true V).grp τ).symm ▸ hg
    have hw' : (((smEquiv M θ hθ τ).symm w : (negM M).sm τ) : (negM M).H τ) =
        (negM M).rep τ g (((smEquiv M θ hθ τ).symm (v τ) : (negM M).sm τ) : (negM M).H τ) := by
      rw [coe_smEquiv_symm, coe_smEquiv_symm]; exact hw
    have h := hT.equiv τ g hg' (fun ρ => (smEquiv M θ hθ ρ).symm (v ρ)) ((smEquiv M θ hθ τ).symm w) hw'
    funext x
    rw [ofNeg_apply, eq_symm_update, h]
    show T (fun ρ => (smEquiv M θ hθ ρ).symm (v ρ)) ((ofSgn true V).symm x * atTau θ (sgn true V) τ g) =
      T (fun ρ => (smEquiv M θ hθ ρ).symm (v ρ)) ((ofSgn true V).symm (x * atTau θ V τ g))
    rw [map_mul, ← (GlobalTheory.T.signedUnitaryGroup_compat D θ hθ true V).atTau τ g, MulEquiv.symm_apply_apply]
  cont τ v x := by
    classical
    obtain ⟨ℓ, hℓ, hℓw⟩ := hT.cont τ (fun ρ => (smEquiv M θ hθ ρ).symm (v ρ)) ((ofSgn true V).symm x)
    refine ⟨ℓ, ?_, fun w => ?_⟩
    · rw [← (GlobalTheory.T.signedUnitaryGroup_compat D θ hθ true V).lie τ]; exact hℓ
    · rw [ofNeg_apply, eq_symm_update, ← hℓw, coe_smEquiv_symm]; rfl

theorem toNeg_mem {T : MMap M} (hT : T ∈ Mult θ M ∅ 1) : toNeg M θ hθ T ∈ Mult θ (negM M) ∅ 1 := by
  unfold Mult at hT ⊢
  induction hT using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (isMultMap_toNeg M θ hθ hx)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem ofNeg_mem {T : MMap (negM M)} (hT : T ∈ Mult θ (negM M) ∅ 1) : ofNeg M θ hθ T ∈ Mult θ M ∅ 1 := by
  unfold Mult at hT ⊢
  induction hT using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (isMultMap_ofNeg M θ hθ hx)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

end GlobalTheory.NegModel

namespace GlobalTheory.NegModel
variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (θ : InfFam D) (hθ : IsInfFam θ)

theorem smTEquiv_symm_tprod (v : M.Vec) :
    (smTEquiv M θ hθ).symm (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ fun τ => (smEquiv M θ hθ τ).symm (v τ) := by
  rw [LinearEquiv.symm_apply_eq, smTEquiv_tprod]
  exact congrArg (PiTensorProduct.tprod ℂ) (funext fun τ => (LinearEquiv.apply_symm_apply (smEquiv M θ hθ τ) (v τ)).symm)

theorem multT_toNeg {F : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hF : F ∈ MultT θ M ∅ 1) :
    (LinearMap.funLeft ℂ ℂ (ofSgn true V)) ∘ₗ F ∘ₗ (smTEquiv M θ hθ).toLinearMap ∈ MultT θ (negM M) ∅ 1 := by
  rw [mem_multT] at hF ⊢
  have e : PiTensorProduct.lift.symm ((LinearMap.funLeft ℂ ℂ (ofSgn true V)) ∘ₗ F ∘ₗ (smTEquiv M θ hθ).toLinearMap) =
      toNeg M θ hθ (PiTensorProduct.lift.symm F) := by
    ext v g
    rw [toNeg_apply, PiTensorProduct.lift_symm, PiTensorProduct.lift_symm]
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, smTEquiv_tprod]
    rfl
  rw [e]
  exact toNeg_mem M θ hθ hF

theorem multT_ofNeg {F : SmT (negM M) →ₗ[ℂ] (GA D (sgn true V) → ℂ)} (hF : F ∈ MultT θ (negM M) ∅ 1) :
    (LinearMap.funLeft ℂ ℂ (ofSgn true V).symm) ∘ₗ F ∘ₗ (smTEquiv M θ hθ).symm.toLinearMap ∈ MultT θ M ∅ 1 := by
  rw [mem_multT] at hF ⊢
  have e : PiTensorProduct.lift.symm ((LinearMap.funLeft ℂ ℂ (ofSgn true V).symm) ∘ₗ F ∘ₗ (smTEquiv M θ hθ).symm.toLinearMap) =
      ofNeg M θ hθ (PiTensorProduct.lift.symm F) := by
    ext v g
    rw [ofNeg_apply, PiTensorProduct.lift_symm, PiTensorProduct.lift_symm]
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, smTEquiv_symm_tprod]
    rfl
  rw [e]
  exact ofNeg_mem M θ hθ hF

theorem modelTr_negM : ModelTr (RingHom.id ℂ) true θ (negM M) M (smTEquiv M θ hθ).toAddEquiv where
  smul c x := by
    show smTEquiv M θ hθ (c • x) = c • smTEquiv M θ hθ x
    exact map_smul _ c x
  cart τ := cart_negM M τ
  act τ g _ x y := by
    show _ ↔ inclT M (smTEquiv M θ hθ y) = actT M τ g (inclT M (smTEquiv M θ hθ x))
    rw [inclT_smTEquiv, inclT_smTEquiv]
    rfl
  der τ Y _ x y := by
    show _ ↔ DerT M τ Y (smTEquiv M θ hθ x) (smTEquiv M θ hθ y)
    unfold DerT
    rw [inclT_smTEquiv, inclT_smTEquiv]
    rfl
  ell w₁ := ⟨w₁, fun x => by
    show _ = ellT M w₁ (inclT M (smTEquiv M θ hθ x))
    rw [inclT_smTEquiv]
    rfl⟩
  vec v₁ := ⟨fun τ => smEquiv M θ hθ τ (v₁ τ), smTEquiv_tprod M θ hθ v₁, fun τ => by rw [coe_smEquiv]; rfl⟩
  mult F hF := ⟨_, multT_toNeg M θ hθ hF, fun x g => rfl⟩
  mult' F₁ hF₁ := ⟨_, multT_ofNeg M θ hθ hF₁, fun x g => by
    show F₁ x g = F₁ ((smTEquiv M θ hθ).symm (smTEquiv M θ hθ x)) ((ofSgn true V).symm (ofSgn true V g))
    rw [LinearEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]⟩

end GlobalTheory.NegModel

open GlobalTheory.NegModel in

theorem GlobalTheory.negModel_tr : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S),
    ∃ (M₁ : DSModel (sgn true V) fun τ => GlobalTheory.SignedHC.flip (S τ)) (κ : SmT M₁ ≃+ SmT M),
      ModelTr (RingHom.id ℂ) true θ M₁ M κ :=
  fun _ θ hθ _ _ M => ⟨negM M, (smTEquiv M θ hθ).toAddEquiv, modelTr_negM M θ hθ⟩
