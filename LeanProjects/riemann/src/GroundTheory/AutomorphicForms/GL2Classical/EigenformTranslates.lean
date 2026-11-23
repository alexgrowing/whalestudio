import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.TranslateSpanLeCuspForms
import GroundTheory.AutomorphicForms.GL2Classical.Automorphic
import GroundTheory.AutomorphicForms.GL2Classical.EigenQExpansion
import GroundTheory.AutomorphicForms.GL2Classical.CuspFormsFiniteDim
import GroundTheory.AutomorphicForms.GL2Classical.UnitaryEigenSpan
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsDecay

open NumberField Matrix CongruenceSubgroup ModularForm Complex Filter
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ModularForm Real InnerProductSpace Manifold NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm

set_option linter.unusedSectionVars false

variable {N : ℕ} [NeZero N] {k : ℤ}

theorem descend_archLift_mul_borelGL (f : ℍ → ℂ) {β : GL (Fin 2) ℝ} (hβ : 0 < β.det.val) (z : ℍ) :
    (Real.sqrt z.im : ℂ) ^ (-k) * archLift k f (β * borelGL z) =
      ((Real.sqrt β.det.val : ℂ) ^ k * (((β.det.val : ℝ) : ℂ) ^ (k - 1))⁻¹) * (f ∣[k] β) z := by
  have hy := z.im_pos
  rw [archLift, map_mul, Units.val_mul, det_borelGL, mul_smul, borelGL_smul_I,
    denom_mul_of_det_pos _ (det_borelGL_pos z), borelGL_smul_I, denom_borelGL, mul_one,
    Real.sqrt_mul hβ.le, slash_apply, σ_of_det_pos hβ, abs_of_pos hβ]
  have hs : (Real.sqrt z.im : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hy).ne'
  have hd : ((β.det.val : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hβ.ne'
  have e1 : (Real.sqrt z.im : ℂ) ^ (-k) * (Real.sqrt z.im : ℂ) ^ k = 1 := by
    rw [← zpow_add₀ hs, neg_add_cancel, zpow_zero]
  have e2 : (((β.det.val : ℝ) : ℂ) ^ (k - 1))⁻¹ * ((β.det.val : ℝ) : ℂ) ^ (k - 1) = 1 :=
    inv_mul_cancel₀ (zpow_ne_zero _ hd)
  push_cast
  rw [mul_zpow]
  set A := (Real.sqrt β.det.val : ℂ) ^ k * f (β • z) * denom β (z : ℂ) ^ (-k)
  linear_combination A * e1 - A * e2

theorem exists_eq_finiteDiagonal_mul_pos (g : FiniteAdelicGL ℚ 2) :
    ∃ ξ : GL (Fin 2) ℚ, ∃ u ∈ Gamma0Level N, 0 < (ξ.det.val : ℚ) ∧ g = finiteDiagonal ℚ 2 ξ * u := by
  obtain ⟨γ, u, hu, rfl⟩ := exists_eq_finiteDiagonal_mul N g
  by_cases hd : 0 < (γ.det.val : ℚ)
  · exact ⟨γ, u, hu, hd, rfl⟩
  · refine ⟨γ * epsilon, finiteDiagonal ℚ 2 epsilon * u, mul_mem (finiteDiagonal_epsilon_mem N) hu, ?_, ?_⟩
    · have hne : (γ.det.val : ℚ) ≠ 0 := γ.det.ne_zero
      have hneg : (γ.det.val : ℚ) < 0 := lt_of_le_of_ne (not_lt.1 hd) hne
      have he : (epsilon.det.val : ℚ) = -1 := by
        rw [Matrix.GeneralLinearGroup.val_det_apply]
        simp [epsilon, Matrix.det_fin_two_of]
      rw [map_mul, Units.val_mul, he]
      linarith
    · have hee : epsilon * epsilon = 1 := by
        conv_lhs => rw [← epsilon_inv]
        exact inv_mul_cancel _
      rw [map_mul, mul_assoc, ← mul_assoc (finiteDiagonal ℚ 2 epsilon), ← map_mul, hee, map_one, one_mul]

theorem descend_finRightRep_liftEquiv (f : SlashInvariantForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (g : FiniteAdelicGL ℚ 2) :
    ∃ δ : GL (Fin 2) ℚ, ∃ c : ℂ,
      descend k (finRightRep g (liftEquiv N k f : AdelicGL ℚ 2 → ℂ)) = c • ((f : ℍ → ℂ) ∣[k] toReal δ) := by
  have hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), (f : ℍ → ℂ) ∣[k] γ = f :=
    fun γ hγ => SlashInvariantForm.slash_action_eqn f γ hγ
  obtain ⟨ξ, u, hu, hξ, rfl⟩ := exists_eq_finiteDiagonal_mul_pos (N := N) g
  have hβ : 0 < ((toReal ξ)⁻¹).det.val := by
    have := det_toReal_inv_mul_pos ξ hξ (h := 1) (by simp)
    simpa using this
  refine ⟨ξ⁻¹, (Real.sqrt ((toReal ξ)⁻¹).det.val : ℂ) ^ k *
    ((((toReal ξ)⁻¹.det.val : ℝ) : ℂ) ^ (k - 1))⁻¹, ?_⟩
  funext z
  simp only [descend, finRightRep_apply, liftEquiv_apply, Pi.smul_apply, smul_eq_mul]
  rw [map_mul, ← mul_assoc, (isWeightLevel_adelicLift hf).right_level _ _ hu,
    realEmb_mul_finEmb_finiteDiagonal,
    adelicLift_apply hf ξ (det_toReal_inv_mul_pos ξ hξ (det_borelGL_pos z)) (one_mem _), map_inv]
  exact descend_archLift_mul_borelGL f hβ z

variable (k) in

def holoBddSpace : Submodule ℂ (ℍ → ℂ) where
  carrier := {F | MDiff F ∧ ∀ σ : SL(2, ℤ), IsBoundedAtImInfty (F ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ σ)}
  add_mem' {F G} hF hG := ⟨hF.1.add hG.1, fun σ => by
    rw [SlashAction.add_slash]
    exact (hF.2 σ).add (hG.2 σ)⟩
  zero_mem' := ⟨mdifferentiable_const, fun σ => by
    rw [SlashAction.zero_slash]
    exact zero_form_isBoundedAtImInfty⟩
  smul_mem' c F hF := ⟨hF.1.const_smul c, fun σ => by
    have hpos : 0 < (Matrix.SpecialLinearGroup.mapGL ℝ σ).det.val := by
      rw [Matrix.SpecialLinearGroup.det_mapGL]; exact one_pos
    rw [ModularForm.smul_slash, σ_of_det_pos hpos]
    exact (hF.2 σ).const_smul_left c⟩

theorem slash_toReal_mem_holoBddSpace (f : ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (δ : GL (Fin 2) ℚ) : (f : ℍ → ℂ) ∣[k] toReal δ ∈ holoBddSpace k := by
  refine ⟨f.holo'.slash k _, fun σ => ?_⟩
  rw [← SlashAction.slash_mul, ← toReal_mapGL, ← map_mul]
  exact isBoundedAtImInfty_slash_toReal f _

theorem descend_mem_holoBddSpace (f : ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    {ψ : AdelicGL ℚ 2 → ℂ} (hψ : ψ ∈ translateSpan (liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ)) :
    descend k ψ ∈ holoBddSpace k := by
  induction hψ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    obtain ⟨δ, c, hc⟩ := descend_finRightRep_liftEquiv f.toSlashInvariantForm g
    rw [hc]
    exact Submodule.smul_mem _ c (slash_toReal_mem_holoBddSpace f δ)
  | zero =>
    have : descend k (0 : AdelicGL ℚ 2 → ℂ) = 0 := by funext z; simp [descend]
    rw [this]
    exact zero_mem _
  | add x y _ _ hx hy =>
    have : descend k (x + y) = descend k x + descend k y := by funext z; simp [descend, mul_add]
    rw [this]
    exact add_mem hx hy
  | smul c x _ hx =>
    have : descend k (c • x) = c • descend k x := by funext z; simp [descend]; ring
    rw [this]
    exact Submodule.smul_mem _ c hx

theorem isLeftInvariant_of_mem_translateSpan {φ : AdelicGL ℚ 2 → ℂ} (hφ : IsLeftInvariant φ)
    {ψ : AdelicGL ℚ 2 → ℂ} (hψ : ψ ∈ translateSpan φ) : IsLeftInvariant ψ := by
  induction hψ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    intro γ x
    simp only [finRightRep_apply, mul_assoc]
    exact hφ γ _
  | zero => intro γ x; rfl
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact hx.smul c

theorem right_kGL_of_mem_translateSpan {φ : AdelicGL ℚ 2 → ℂ}
    (hφ : ∀ g (w : ℂ) (hw : w ≠ 0), φ (g * realEmb (kGL w hw)) = (w / (‖w‖ : ℂ)) ^ (-k) * φ g)
    {ψ : AdelicGL ℚ 2 → ℂ} (hψ : ψ ∈ translateSpan φ) :
    ∀ g (w : ℂ) (hw : w ≠ 0), ψ (g * realEmb (kGL w hw)) = (w / (‖w‖ : ℂ)) ^ (-k) * ψ g := by
  induction hψ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    intro g w hw
    simp only [finRightRep_apply]
    rw [mul_assoc, realEmb_mul_finEmb_comm, ← mul_assoc, hφ]
  | zero => intro g w hw; simp
  | add x y _ _ hx hy => intro g w hw; simp [hx g w hw, hy g w hw, mul_add]
  | smul c x _ hx => intro g w hw; simp [hx g w hw]; ring

theorem isWeightLevel_of_mem_translateSpan (f : SlashInvariantForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    {ψ : AdelicGL ℚ 2 → ℂ} (hψ : ψ ∈ translateSpan (liftEquiv N k f : AdelicGL ℚ 2 → ℂ))
    (hK : ∀ u ∈ Gamma0Level N, finRightRep u ψ = ψ) : IsWeightLevel N k ψ :=
  ⟨isLeftInvariant_of_mem_translateSpan (liftEquiv N k f).2.isLeftInvariant hψ,
    fun g u hu => congrFun (hK u hu) g,
    right_kGL_of_mem_translateSpan (liftEquiv N k f).2.right_kGL hψ⟩

theorem exists_cuspForm_of_mem_translateSpan (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    {ψ : AdelicGL ℚ 2 → ℂ} (hψ : ψ ∈ translateSpan (liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ))
    (hK : ∀ u ∈ Gamma0Level N, finRightRep u ψ = ψ) :
    ∃ F : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k,
      (liftEquiv N k F.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ) = ψ := by
  have hW := isWeightLevel_of_mem_translateSpan f.toSlashInvariantForm hψ hK
  set Fs := (liftEquiv N k).symm ⟨ψ, hW⟩
  have hFs : (Fs : ℍ → ℂ) = descend k ψ := funext fun z => liftEquiv_symm_apply _ z
  have hmem : descend k ψ ∈ holoBddSpace k := descend_mem_holoBddSpace (CuspForm.toModularFormₗ f) hψ
  let Fm : ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k :=
    { toSlashInvariantForm := Fs
      holo' := by
        change MDiff (Fs : ℍ → ℂ)
        rw [hFs]
        exact hmem.1
      bdd_at_cusps' := fun {c} hc => by
        rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff'] at hc
        obtain ⟨σ, rfl⟩ := hc
        rw [OnePoint.isBoundedAt_iff rfl]
        change IsBoundedAtImInfty ((Fs : ℍ → ℂ) ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ σ)
        rw [hFs]
        exact hmem.2 σ }
  have hlift : liftEquiv N k Fm.toSlashInvariantForm = ⟨ψ, hW⟩ := (liftEquiv N k).apply_symm_apply _
  obtain ⟨F, hF⟩ := exists_cuspForm_of_liftEquiv_mem_cuspForms Fm (by
    rw [hlift]
    exact translateSpan_le_cuspForms f hψ)
  refine ⟨F, ?_⟩
  have : F.toSlashInvariantForm = Fm.toSlashInvariantForm := SlashInvariantForm.ext fun z => congrFun hF z
  rw [this, hlift]

theorem posIdele_fst_rat (r : ℝ) (hr : 0 < r) :
    ((Reduction.posIdele (K := ℚ) r hr : Global.IdeleGroup ℚ) : 𝔸[ℚ]).1 =
      Global.RationalIdeles.realEquiv.symm r := by
  apply Global.RationalIdeles.realEquiv.injective
  rw [RingEquiv.apply_symm_apply, Global.RationalIdeles.realEquiv_apply]
  have := Reduction.infiniteProj_posIdele (K := ℚ) r hr default
  rw [← Global.IdeleGroup.coe_infiniteProj, this]
  simp [Global.posRealToUnits, Global.posRealElem, Global.RationalIdeles.isReal_infinitePlace]
  exact RingEquiv.apply_symm_apply (InfinitePlace.Completion.ringEquivRealOfIsReal _) r

theorem exists_centralSection_eq_realEmb (s : {r : ℝ // 0 < r}) :
    ∃ (r : ℝ) (hr : 0 < r), Reduction.centralSection ℚ 2 s = realEmb (kGL (r : ℂ) (by exact_mod_cast hr.ne')) := by
  set t := Reduction.rpowHom ((2 * Module.finrank ℚ ℚ : ℝ))⁻¹ s
  refine ⟨t.1, t.2, ?_⟩
  have hc : Reduction.centralSection ℚ 2 s =
      Reduction.diagUnits 2 (fun _ => Reduction.posIdele (K := ℚ) t.1 t.2) := rfl
  rw [hc]
  apply (AdelicGLn.prodEquiv ℚ 2).injective
  rw [prodEquiv_realEmb]
  refine Prod.ext ?_ ?_
  · refine Units.ext (Matrix.ext fun a b => ?_)
    rw [AdelicGLn.prodEquiv_apply_fst]
    simp only [Reduction.coe_diagUnits]
    change _ = Global.RationalIdeles.realEquiv.symm ((kGL (t.1 : ℂ) _ : Matrix (Fin 2) (Fin 2) ℝ) a b)
    rw [coe_kGL]
    fin_cases a <;> fin_cases b <;> simp [posIdele_fst_rat]
  · exact Reduction.prodEquiv_diagUnits_posIdele_snd (fun _ => t.1) (fun _ => t.2)

theorem apply_centralSection_mul {ψ : AdelicGL ℚ 2 → ℂ}
    (hψ : ∀ x (r : ℝ) (hr : 0 < r), ψ (x * realEmb (kGL (r : ℂ) (by exact_mod_cast hr.ne'))) = ψ x)
    (s : {r : ℝ // 0 < r}) (x : AdelicGL ℚ 2) : ψ (Reduction.centralSection ℚ 2 s * x) = ψ x := by
  obtain ⟨r, hr, hs⟩ := exists_centralSection_eq_realEmb s
  rw [Reduction.centralSection_mul_comm, hs, hψ _ _ hr]

def liftCusp (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) : cuspForms ℚ 2 :=
  ⟨(liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ), liftEquiv_mem_cuspForms f⟩

def translateSpanCusp (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) : Submodule ℂ (cuspForms ℚ 2) :=
  Submodule.span ℂ (Set.range fun g : FiniteAdelicGL ℚ 2 => finRepCusp ℚ 2 g (liftCusp f))

theorem coe_mem_translateSpan (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) {ψ : cuspForms ℚ 2}
    (hψ : ψ ∈ translateSpanCusp f) :
    (ψ : AdelicGL ℚ 2 → ℂ) ∈ translateSpan (liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ) := by
  induction hψ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact Submodule.subset_span ⟨g, rfl⟩
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

theorem posScalar_of_mem_translateSpanCusp (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    {ψ : cuspForms ℚ 2} (hψ : ψ ∈ translateSpanCusp f) (x : AdelicGL ℚ 2) (r : ℝ) (hr : 0 < r) :
    (ψ : AdelicGL ℚ 2 → ℂ) (x * realEmb (kGL (r : ℂ) (by exact_mod_cast hr.ne'))) = (ψ : AdelicGL ℚ 2 → ℂ) x := by
  rw [right_kGL_of_mem_translateSpan (liftEquiv N k f.toSlashInvariantForm).2.right_kGL
    (coe_mem_translateSpan f hψ)]
  have hs' : (r : ℂ) / (‖(r : ℂ)‖ : ℂ) = 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hr.le, div_self (by exact_mod_cast hr.ne')]
  rw [hs', _root_.one_zpow, one_mul]

theorem centralSection_of_mem_translateSpanCusp (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    {ψ : cuspForms ℚ 2} (hψ : ψ ∈ translateSpanCusp f) (s : {r : ℝ // 0 < r}) (x : AdelicGL ℚ 2) :
    (ψ : AdelicGL ℚ 2 → ℂ) (Reduction.centralSection ℚ 2 s * x) = (ψ : AdelicGL ℚ 2 → ℂ) x :=
  apply_centralSection_mul (posScalar_of_mem_translateSpanCusp f hψ) s x

theorem finRepCusp_mem_translateSpanCusp (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (g : FiniteAdelicGL ℚ 2) {ψ : cuspForms ℚ 2} (hψ : ψ ∈ translateSpanCusp f) :
    finRepCusp ℚ 2 g ψ ∈ translateSpanCusp f := by
  induction hψ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    exact Submodule.subset_span ⟨g * h, by
      show finRepCusp ℚ 2 (g * h) (liftCusp f) = _
      rw [map_mul, Module.End.mul_apply]⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

end GL2Classical

end

end GroundTheory.Automorphic
