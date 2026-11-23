import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalLocalUniqueness
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMomentMatrixTransform
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open GlobalTheory.LatVac GlobalTheory.MixedForm
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SplitScalX

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem lin_zero_basis (h : IsCMExt F E σ) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (χX χW : Chr F E)
    (om : Rep σ X W) (hW : M.IsWeil ψ χX χW om) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
    (ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)) (hι : M.IsLinW ψ t b c ι)
    (g : UA σ X.J) (hg : g ∈ UAt σ X (evFin F v)) (y : (Fv F v)ˣ) (hy : (y : Fv F v) = ((mat g).map (piW (t.comp σ))).det)
    (φ φ₁ : (Fin n × Fin d → Fv F v) → ℂ) (hφ : φ ∈ SB (Fin n × Fin d → Fv F v))
    (hA : Acts (evFin F v) (om (g, 1)) φ φ₁) :
    ι φ₁ 0 = (chrW χW (t.comp σ) y : ℂ) * ((GlobalTheory.SplitWeil.nabs (Fv F v) y ^ ((d : ℝ) / 2) : ℝ) : ℂ) * ι φ 0 := by
  obtain ⟨Λ, hΛ, f, hf, hne⟩ := GlobalTheory.T.exists_translation_invariant_functional F v n d
  obtain ⟨φ₂, hφ₂, rfl⟩ := hι.bij.surjOn hf
  refine form_scalar h M ψ χX χW om hW t (LinearMap.proj 0 ∘ₗ ι) (conjForm (Λ ∘ₗ ι)) (fun w hw φ hφ => ?_)
    (fun w hw φ hφ => ?_) (star φ₂) (star_mem_SB hφ₂) ?_ g hg y hy φ φ₁ hφ hA
  · obtain ⟨u, hu, e1, e2⟩ := exists_at (v := v) M w
    have := hι.mult u hu ((e2 t).trans hw) φ hφ _ (GlobalTheory.SchrSB.schr_mem_SB ψ hψ.1 v _ φ hφ)
      (GlobalTheory.VacBridge.rho_acts_locCo M.co ψ v u hu φ) 0 (fun a _ => smul_zero a) (Matrix.map_zero _ (map_zero _))
    rw [e1] at this
    simpa [symp, hTens] using this
  · obtain ⟨u, hu, e1, e2⟩ := exists_at (v := v) M w
    have := hι.trans u hu ((e2 _).trans hw) _ (star_mem_SB hφ) _ (GlobalTheory.SchrSB.schr_mem_SB ψ hψ.1 v _ _ (star_mem_SB hφ))
      (GlobalTheory.VacBridge.rho_acts_locCo M.co ψ v u hu _)
    rw [e1] at this
    change star (Λ (ι _)) = star (Λ (ι _))
    rw [star_schr (psiAt ψ v) (fun x => GlobalTheory.StdCharFromIsStd.norm_psi hψ _), funext this,
      hΛ _ (hι.bij.mapsTo (star_mem_SB hφ))]
  · change star (Λ (ι (star (star φ₂)))) ≠ 0
    rwa [star_star, star_ne_zero]

theorem chrW_comp_conj (h : IsCMExt F E σ) {K : Subgroup (AF F)ˣ} {χ : Chr F E} {m : ℕ} (hχ : ResEtaPow K χ m)
    (t : E →ₐ[F] Fv F v) (x : (Fv F v)ˣ) : chrW χ (t.comp σ) x = (chrW χ t x)⁻¹ := by
  obtain ⟨ε, e1, e2, e3, e4, e5, e6, e7⟩ := exists_idem h t
  have e8 : piW (t.comp σ) ε = 0 := by simpa [e7] using congrArg (piW (t.comp σ)) e2
  have key : ∀ a a' : Fv F v, a * a' = 1 → (1 + ε * algebraMap (AF F) (AE F E) (liftV v (a - 1))) *
      (1 + ε * algebraMap (AF F) (AE F E) (liftV v (a' - 1))) = 1 := fun a a' haa => by
    have e : liftV v (a - 1) + liftV v (a' - 1) + liftV v (a - 1) * liftV v (a' - 1) = 0 := by
      rw [liftV_mul, evFin_liftV, ← map_add, ← map_add, show a - 1 + (a' - 1) + (a - 1) * (a' - 1) = 0 by
        linear_combination haa, map_zero]
    have e' := congrArg (algebraMap (AF F) (AE F E)) e
    rw [map_add, map_add, map_mul, map_zero] at e'
    linear_combination ε * e' + algebraMap (AF F) (AE F E) (liftV v (a - 1)) *
      algebraMap (AF F) (AE F E) (liftV v (a' - 1)) * e1
  have hat : ∀ a : Fv F v, At (evFin F v) (1 + ε * algebraMap (AF F) (AE F E) (liftV v a) - 1) := fun a u hu => by
    rw [add_sub_cancel_left, ← mul_smul_comm, Algebra.smul_def, ← map_mul,
      show u * liftV v a = 0 from at_liftV v a u hu, map_zero, mul_zero]
  let z : (AE F E)ˣ := ⟨_, _, key _ _ x.mul_inv, key _ _ x.inv_mul⟩
  have hz : At (evFin F v) ((z : AE F E) - 1) := hat _
  have hzi : At (evFin F v) (((z⁻¹ : (AE F E)ˣ) : AE F E) - 1) := hat _
  have z1 : piW t (z : AE F E) = x := by
    change piW t (1 + _) = _
    rw [map_add, map_mul, map_one, e5, piW_algebraMap, evFin_liftV]; ring
  have z2 : piW (t.comp σ) (z : AE F E) = 1 := by
    change piW _ (1 + _) = _
    rw [map_add, map_mul, map_one, e8, zero_mul, add_zero]
  obtain ⟨n1, n2⟩ := GlobalTheory.T.local_norm_unramified_factorization F E σ h v t z hz
  set a : (AF F)ˣ := Units.map (Algebra.norm (AF F) : AE F E →* AF F) z with ha
  have n1' : At (evFin F v) ((a : AF F) - 1) := n1
  have n2' : evFin F v (a : AF F) = x := by rw [← mul_one (x : Fv F v), ← z1, ← z2]; exact n2
  have h1 := hχ a
  rw [if_pos (Subgroup.mem_sup_right (MonoidHom.mem_range.mpr ⟨z, rfl⟩)), Circle.coe_eq_one] at h1
  set A : (AE F E)ˣ := Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) a with hA
  have hAv : (A : AE F E) = algebraMap (AF F) (AE F E) a := rfl
  have w0 : At (evFin F v) (((A * z⁻¹ : (AE F E)ˣ) : AE F E) - 1) := fun u hu => by
    have a1 : u • ((A : AE F E) - 1) = 0 := by
      rw [hAv, ← map_one (algebraMap (AF F) (AE F E)), ← map_sub, Algebra.smul_def, ← map_mul,
        show u * ((a : AF F) - 1) = 0 from n1' u hu, map_zero]
    rw [Units.val_mul, show (A : AE F E) * (z⁻¹ : (AE F E)ˣ) - 1 =
      ((A : AE F E) - 1) * (z⁻¹ : (AE F E)ˣ) + ((z⁻¹ : (AE F E)ˣ) - 1) by ring, smul_add, ← smul_mul_assoc, a1,
      hzi u hu, zero_mul, add_zero]
  have zz : ∀ τ : E →ₐ[F] Fv F v, piW τ ((A * z⁻¹ : (AE F E)ˣ) : AE F E) * piW τ (z : AE F E) = x := fun τ => by
    rw [← map_mul, ← Units.val_mul, inv_mul_cancel_right, hAv, piW_algebraMap, n2']
  have w1 : piW t ((A * z⁻¹ : (AE F E)ˣ) : AE F E) = 1 := by
    have := zz t
    rw [z1] at this
    exact (mul_eq_right₀ x.ne_zero).1 this
  have w2 : piW (t.comp σ) ((A * z⁻¹ : (AE F E)ˣ) : AE F E) = x := by
    have := zz (t.comp σ)
    rwa [z2, mul_one] at this
  have c1 := GlobalTheory.T.local_character_norm_one_unit F E σ h χ v t z hz z2
  have c2 := GlobalTheory.T.local_character_norm_one_unit F E σ h χ v (t.comp σ) (A * z⁻¹) w0 (by rw [comp_conj_conj h]; exact w1)
  rw [show Units.map (piW t).toMonoidHom z = x from Units.ext z1] at c1
  rw [show Units.map (piW (t.comp σ)).toMonoidHom (A * z⁻¹) = x from Units.ext w2] at c2
  rw [c1, c2, map_mul, h1, one_mul, map_inv, map_inv]

theorem scalar_left : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∀ κ : UA σ X.J → ℂ, (∀ g ∈ UAt σ X (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (g, 1)) φ φ₁ → ι φ₁ = κ g • fun Y => ι φ (((locMat t b g)⁻¹ : GL (Fin n) (Fv F v)).val * Y)) →
    ∀ g ∈ UAt σ X (evFin F v), κ g = (chrW χW t (GlobalTheory.SplitFlip.gdet (locMat t b g)) : ℂ) *
      GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet (locMat t b g)) (-(d : ℂ) / 2) := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hT v t b c ι hι κ hκ g hg
  have h := hT.base.cm
  have hJ : (X.J.map t).det ≠ 0 := by
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have h0 := GlobalTheory.LeviAtPlace.det_ne_zero_of_sig (hT.herm.sig (InfinitePlace.mk φ))
    have h1 : X.J.det ≠ 0 := fun e => h0 (by
      rw [show X.J.map _ = RingHom.mapMatrix _ X.J from rfl, ← RingHom.map_det, e, map_zero])
    rw [show X.J.map t = (t : E →+* Fv F v).mapMatrix X.J from rfl, ← RingHom.map_det]
    exact (map_ne_zero _).2 h1
  obtain ⟨φ, hφ, e⟩ := hι.bij.surjOn (indicator_intM_mem_SB (k := Fv F v) (R := Fin n) (D := Fin d))
  have hφ0 : ι φ 0 ≠ 0 := by
    rw [e, Set.indicator_of_mem (show (0 : Matrix (Fin n) (Fin d) (Fv F v)) ∈ intM (Fv F v) (Fin n) (Fin d) from
      fun _ _ => zero_mem _)]
    exact one_ne_zero
  set x : (Fv F v)ˣ := GlobalTheory.SplitFlip.gdet (locMat t b g) with hx
  have hx1 : (x : Fv F v) = ((mat g).map (piW t)).det := by
    change (locMat t b g).val.det = _
    rw [locMat_val, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul, Units.inv_mul, Matrix.det_one,
      one_mul]
  have hx2 : ((x⁻¹ : (Fv F v)ˣ) : Fv F v) = ((mat g).map (piW (t.comp σ))).det := by
    have hu := congrArg Matrix.det (GlobalTheory.Div.CoordOpp.unit_map σ g t)
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← hx1, mul_right_comm, mul_eq_right₀ hJ] at hu
    exact Units.inv_eq_of_mul_eq_one_right hu
  obtain ⟨φ₁, ⟨hφ₁, hA⟩, -⟩ := (GlobalTheory.T.theta_action_exists hP F E σ B _ _ _ _ M _ _ om _ _ _ _ hT v).1 g hg 1 (fun u _ => by
      rw [show mat (1 : UA σ W.J) = 1 from rfl, sub_self, smul_zero]) φ hφ
  have k1 := lin_zero_basis h M B.ψ hT.base.std _ _ om hT.weil t b c ι hι g hg _ hx2 φ φ₁ hφ hA
  rw [hκ g hg φ hφ φ₁ hφ₁ hA, chrW_comp_conj h hT.resW, map_inv, inv_inv] at k1
  have k2 : ((GlobalTheory.SplitWeil.nabs (Fv F v) x⁻¹ ^ ((d : ℝ) / 2) : ℝ) : ℂ) = GlobalTheory.SplitFlip.apow x (-(d : ℂ) / 2) := by
    rw [neg_div, ← GlobalTheory.SplitFlip.apow_inv, GlobalTheory.SplitFlip.apow,
      Complex.ofReal_cpow (show 0 ≤ GlobalTheory.SplitWeil.nabs _ _ from NNReal.coe_nonneg _)]
    push_cast
    rfl
  rw [k2] at k1
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mul_zero] at k1
  exact mul_right_cancel₀ hφ0 k1

end GlobalTheory.SplitScalX

end
