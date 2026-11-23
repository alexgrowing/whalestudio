import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.EqAmOfBarEq
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.CdMeas

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2

section Fund

variable {F : Type} [Field F] [NumberField F]

private theorem int_comp (M : Meas F) (e : G1 F ≃ G1 F) (hm : MeasurePreserving e M.μ M.μ)
    (hemb : MeasurableEmbedding e) (hfd : IsFundamentalDomain (Gam F) (e '' M.D) M.μ) (u : G1 F → ℂ)
    (hu : ∀ γ g, u (ratS F γ * g) = u g) : ∫ g in M.D, u (e g) ∂M.μ = ∫ g in M.D, u g ∂M.μ := by
  haveI := M.haar
  have hinv : ∀ (g : Gam F) x, u (g • x) = u x := by
    rintro ⟨_, γ, rfl⟩ x
    simpa [Subgroup.smul_def] using hu γ x
  have hpre : e ⁻¹' (e '' M.D) = M.D := Set.preimage_image_eq _ e.injective
  have h3 := hm.setIntegral_preimage_emb hemb u (e '' M.D)
  rw [hpre] at h3
  rw [h3]
  exact hfd.setIntegral_eq M.fund hinv

private theorem int_right (M : Meas F) (u : G1 F → ℂ) (hu : ∀ γ g, u (ratS F γ * g) = u g) (k : G1 F) :
    ∫ g in M.D, u (g * k) ∂M.μ = ∫ g in M.D, u g ∂M.μ := by
  haveI := M.haar
  haveI := M.right
  have hfd : IsFundamentalDomain (Gam F) ((Equiv.mulRight k) '' M.D) M.μ := by
    refine M.fund.image_of_equiv (Equiv.mulRight k) ?_ (Equiv.refl _) ?_
    · exact (measurePreserving_mul_right M.μ k⁻¹).quasiMeasurePreserving
    · intro g x
      simp [Subgroup.smul_def, mul_assoc]
  exact int_comp M (Equiv.mulRight k) (measurePreserving_mul_right M.μ k)
    (MeasurableEquiv.mulRight k).measurableEmbedding hfd u hu

private theorem int_cD (M : Meas F) (u : G1 F → ℂ) (hu : ∀ γ g, u (ratS F γ * g) = u g) (c : Fˣ) :
    ∫ g in M.D, u (cD (IdeleGroup.diagonal F c) g) ∂M.μ = ∫ g in M.D, u g ∂M.μ := by
  haveI := M.haar
  set t := IdeleGroup.diagonal F c with ht
  have hti : t⁻¹ = IdeleGroup.diagonal F c⁻¹ := by rw [ht, map_inv]
  have l1 : ∀ g, cD t⁻¹ (cD t g) = g := fun g => by rw [← cD_mul_left, inv_mul_cancel, cD_one_left]
  have l2 : ∀ g, cD t (cD t⁻¹ g) = g := fun g => by rw [← cD_mul_left, mul_inv_cancel, cD_one_left]
  let e : G1 F ≃ₜ G1 F :=
    { toFun := cD t, invFun := cD t⁻¹, left_inv := l1, right_inv := l2,
      continuous_toFun := UpperTheory.ConvolutionTheory.R2.M.continuous_cD t, continuous_invFun := UpperTheory.ConvolutionTheory.R2.M.continuous_cD t⁻¹ }
  let eG : Gam F ≃ Gam F :=
    { toFun := fun g => ⟨cD t⁻¹ g.1, hti ▸ cD_diagonal_mem c⁻¹ g.2⟩
      invFun := fun g => ⟨cD t g.1, cD_diagonal_mem c g.2⟩
      left_inv := fun g => Subtype.ext (l2 g.1)
      right_inv := fun g => Subtype.ext (l1 g.1) }
  have hfd : IsFundamentalDomain (Gam F) (e.toEquiv '' M.D) M.μ := by
    refine M.fund.image_of_equiv e.toEquiv ?_ eG ?_
    · exact (UpperTheory.ConvolutionTheory.R2.M.cdMeas F M t⁻¹).quasiMeasurePreserving
    · intro g x
      change cD t (cD t⁻¹ g.1 * x) = g.1 * cD t x
      rw [cD_mul, l2]
  exact int_comp M e.toEquiv (UpperTheory.ConvolutionTheory.R2.M.cdMeas F M t) e.measurableEmbedding hfd u hu

end Fund

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem nu_mul (x y : GL (Fin 2) (A E)) : nu F (x * y) = nu F x * nu F y := by
  simp only [nu, map_mul]

private theorem nu_scalar (z : (A E)ˣ) :
    nu F (Matrix.GeneralLinearGroup.scalar (Fin 2) z) = ideleNorm F E z ^ 2 := by
  rw [nu, det_scalar, map_pow]

private theorem act_scalar (D : Dat F E) (w : (A E)ˣ) (a : A F) (ha : am E a = w * D.bar w) (v : V4 F) :
    D.act (Matrix.GeneralLinearGroup.scalar (Fin 2) w) v = fun i => a * v i := by
  have hX : ∀ i j, ((Matrix.GeneralLinearGroup.scalar (Fin 2) w).val * D.herm v *
      ((Matrix.GeneralLinearGroup.scalar (Fin 2) w).val.map D.bar)ᵀ) i j = am E a * D.herm v i j := by
    intro i j
    rw [ha]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply,
        Matrix.diagonal_apply] <;> ring
  funext i
  unfold Dat.act Dat.unherm
  simp only [hX]
  fin_cases i <;> simp [D.co_am_mul, Dat.herm]

variable [IsTotallyReal F] [IsTotallyComplex E] {D : Dat F E}

private noncomputable def U (W : Weil D) (f : GL (Fin 2) (A F) → ℂ) (φ : S4 F) (h : GL (Fin 2) (A E)) (g : G1 F) : ℂ :=
  f (gl g * dM (nu F h)) * Th (W.Om g (W.L h φ)).1

private theorem U_inv (W : Weil D) {f : GL (Fin 2) (A F) → ℂ} (hl : ∀ γ g, f (ratGL F 2 γ * g) = f g) (φ : S4 F)
    (h : GL (Fin 2) (A E)) (γ : Matrix.SpecialLinearGroup (Fin 2) F) (g : G1 F) :
    U W f φ h (ratS F γ * g) = U W f φ h g := by
  unfold U
  rw [gl_mul, gl_ratS, mul_assoc, hl, map_mul, Module.End.mul_apply, W.th_Om]

private theorem lift_left (W : Weil D) (M : Meas F) {f : GL (Fin 2) (A F) → ℂ}
    (hl : ∀ γ g, f (ratGL F 2 γ * g) = f g) (φ : S4 F) (γ : GL (Fin 2) E) (h : GL (Fin 2) (A E)) :
    lift W M f φ (ratGL E 2 γ * h) = lift W M f φ h := by
  obtain ⟨c, hc⟩ : ∃ c : Fˣ, nu F (ratGL E 2 γ) = IdeleGroup.diagonal F c :=
    ⟨_, by rw [nu, det_ratGL, ideleNorm_diagonal]⟩
  obtain ⟨γ', hγ'⟩ := exists_ratGL_dM c
  have key : ∀ g, f (gl g * dM (nu F (ratGL E 2 γ * h))) * Th (W.Om g (W.L (ratGL E 2 γ * h) φ)).1 =
      U W f φ h (cD (IdeleGroup.diagonal F c⁻¹) g) := by
    intro g
    set t := IdeleGroup.diagonal F c with ht
    have hti : IdeleGroup.diagonal F c⁻¹ = t⁻¹ := by rw [ht, map_inv]
    rw [hti]
    have hx : cD t (cD t⁻¹ g) = g := by rw [← cD_mul_left, mul_inv_cancel, cD_one_left]
    have e1 : gl g * dM (t * nu F h) = ratGL F 2 γ' * (gl (cD t⁻¹ g) * dM (nu F h)) := by
      rw [hγ', ← mul_assoc, dM_mul_gl t, hx, dM_mul, mul_assoc]
    have e2 : W.Om g (W.L (ratGL E 2 γ * h) φ) = W.L (ratGL E 2 γ) (W.Om (cD t⁻¹ g) (W.L h φ)) := by
      have := LinearMap.congr_fun (W.comm (ratGL E 2 γ) (cD t⁻¹ g)) (W.L h φ)
      rw [hc, hx] at this
      rw [map_mul, Module.End.mul_apply]
      exact this.symm
    rw [nu_mul, hc, e1, hl, e2, W.th_L]
    rfl
  unfold lift
  simp_rw [key]
  exact int_cD M (U W f φ h) (U_inv W hl φ h) c⁻¹

private theorem L_scalar (W : Weil D) (z : (A E)ˣ) :
    W.L (Matrix.GeneralLinearGroup.scalar (Fin 2) z) = W.Om (mD (ideleNorm F E z)⁻¹) := by
  refine LinearMap.ext fun φ => Subtype.ext (funext fun v => ?_)
  have hz : am E (((ideleNorm F E z)⁻¹ : (A F)ˣ) : A F) = ((z⁻¹ : (A E)ˣ) : A E) * D.bar ((z⁻¹ : (A E)ˣ) : A E) := by
    rw [← map_inv, D.am_ideleNorm]
  have hη : W.η.1 (ideleNorm F E z)⁻¹ = 1 := by
    rw [← map_inv]
    exact W.η_norm z⁻¹
  rw [W.L_apply, W.Om_m, ← map_inv, act_scalar D z⁻¹ _ hz, nu_scalar, hη, ab_pow, ab_inv]
  simp

private theorem lift_centre (W : Weil D) (M : Meas F) {f : GL (Fin 2) (A F) → ℂ}
    (hl : ∀ γ g, f (ratGL F 2 γ * g) = f g) (φ : S4 F) (ω : (A F)ˣ →* ℂˣ)
    (hω : ∀ s g, f (Matrix.GeneralLinearGroup.scalar (Fin 2) s * g) = ((ω s : ℂˣ) : ℂ) * f g)
    (z : (A E)ˣ) (h : GL (Fin 2) (A E)) :
    lift W M f φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * h) = ((ω (ideleNorm F E z) : ℂˣ) : ℂ) * lift W M f φ h := by
  set n := ideleNorm F E z with hn
  have key : ∀ g, f (gl g * dM (nu F (Matrix.GeneralLinearGroup.scalar (Fin 2) z * h))) *
      Th (W.Om g (W.L (Matrix.GeneralLinearGroup.scalar (Fin 2) z * h) φ)).1 =
      ((ω n : ℂˣ) : ℂ) * U W f φ h (g * mD n⁻¹) := by
    intro g
    have e0 : dM (n ^ 2) = gl (mD n⁻¹) * Matrix.GeneralLinearGroup.scalar (Fin 2) n := by
      rw [← gl_mD_mul_dM_sq n, mD_inv, gl_inv, inv_mul_cancel_left]
    have e1 : gl g * dM (n ^ 2 * nu F h) =
        Matrix.GeneralLinearGroup.scalar (Fin 2) n * (gl (g * mD n⁻¹) * dM (nu F h)) := by
      rw [dM_mul, e0, mul_assoc (gl _) _ (dM _), UpperTheory.ConvolutionTheory.R2.scalar_comm n (dM _),
        UpperTheory.ConvolutionTheory.R2.scalar_comm n (gl _ * dM _), gl_mul]
      simp only [mul_assoc]
    have e2 : W.Om g (W.L (Matrix.GeneralLinearGroup.scalar (Fin 2) z * h) φ) = W.Om (g * mD n⁻¹) (W.L h φ) := by
      rw [map_mul, L_scalar, map_mul, Module.End.mul_apply, Module.End.mul_apply]
    rw [nu_mul, nu_scalar, e1, hω, e2, U, mul_assoc]
  unfold lift
  simp_rw [key]
  rw [integral_const_mul]
  congr 1
  exact int_right M (U W f φ h) (U_inv W hl φ h) _

end Main

theorem UpperTheory.ConvolutionTheory.R2.equiv :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), St.Equiv W M π := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ
  have hl : ∀ γ g, f.1 (ratGL F 2 γ * g) = f.1 g := (π.cusp f hf).1.left
  exact ⟨fun γ h => lift_left W M hl φ γ h, fun ω hω z h => lift_centre W M hl φ ω hω z h⟩
