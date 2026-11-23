import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocFieldLP
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSBZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationInvariantFunctional
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.LiftPair
open GlobalTheory.LatVac GlobalTheory.MixedForm
open scoped Matrix TensorProduct GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SplitScalRight

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem form_scalar_right (h : IsCMExt F E σ) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W)
    (hW : M.IsWeil ψ χX χW om) (t : E →ₐ[F] Fv F v) (l₁ l₂ : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ)
    (h₁ : ∀ w : Matrix (Fin n) (Fin d) (AE F E), w.map (piW t) = 0 → ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      l₁ (schr (psiAt ψ v) (locCo M.co v w) φ) = l₁ φ)
    (h₂ : ∀ w : Matrix (Fin n) (Fin d) (AE F E), w.map (piW (t.comp σ)) = 0 → ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      l₂ (schr (psiAt ψ v) ((locCo M.co v w).1, -(locCo M.co v w).2) φ) = l₂ φ)
    (φ₂ : (Fin n × Fin d → Fv F v) → ℂ) (hφ₂ : φ₂ ∈ SB (Fin n × Fin d → Fv F v)) (hne : l₂ φ₂ ≠ 0)
    (g : UA σ W.J) (hg : g ∈ UAt σ W (evFin F v)) (y : (Fv F v)ˣ) (hy : (y : Fv F v) = ((mat g).map (piW (t.comp σ))).det)
    (φ φ₁ : (Fin n × Fin d → Fv F v) → ℂ) (hφ : φ ∈ SB (Fin n × Fin d → Fv F v))
    (hA : Acts (evFin F v) (om (1, g)) φ φ₁) :
    l₁ φ₁ = (chrW χX (t.comp σ) y : ℂ) * ((GlobalTheory.SplitWeil.nabs (Fv F v) y ^ ((n : ℝ) / 2) : ℝ) : ℂ) * l₁ φ := by
  obtain ⟨hB, -, -⟩ := hW
  obtain ⟨ε, e1, e2, e3, e4, e5, e6, e7⟩ := exists_idem h t
  have e8 : piW (t.comp σ) ε = 0 := by simpa [e7] using congrArg (piW (t.comp σ)) e2
  obtain ⟨φ₀, hφ₀, hb₀, R, R', hR, hL⟩ := GlobalTheory.T.box_product_diagonal_functional_ne_zero F (Fin n × Fin d) v
  set u : AF F := 1 - liftV v 1 with hu
  have hu0 : evFin F v u = 0 := by simp [hu, evFin_liftV]
  have huA : algebraMap (AF F) (AE F E) u = 1 - ε - cA σ ε := by rw [hu, map_sub, map_one, ← e4]; ring
  have h4 : cA σ ε * cA σ ε = cA σ ε := by rw [← map_mul, e1]
  obtain ⟨T, hT⟩ := exists_part (cA σ ε) h4 (g : GL (Fin d) (AE F E))
  have hgu : (1 - ε - cA σ ε) • (mat g - 1) = 0 := by rw [← huA, algebraMap_smul]; exact hg u hu0
  have hbox : ∀ a b : (Fin n × Fin d → Fv F v) → ℂ, boxFun (tens (evFin F v) a R) (tens (evFin F v) b R') =
      tens (evFin F v) (boxFun a b) (boxFun R R') := fun a b => by
    funext x; simp only [boxFun, tens, Function.comp_def]; ring
  have hRR : ∀ x z, At (evFin F v) z → boxFun R R' (x + z) = boxFun R R' x := fun x z hz => by
    have a1 := (hR φ hφ).1.1 (x ∘ Sum.inl) (z ∘ Sum.inl) fun u hu => funext fun i => congrFun (hz u hu) _
    have a2 := (hR φ hφ).2.1 (x ∘ Sum.inr) (z ∘ Sum.inr) fun u hu => funext fun i => congrFun (hz u hu) _
    exact congrArg₂ (· * ·) a1 a2
  have key := siegel_mixed hB.isWeilB ε e1 e2 e3
    (GlobalTheory.DiagForm.lDiag F (Fin n × Fin d) ∘ₗ proj v (boxFun φ₀ φ₀) (tensForm l₁ l₂))
    ((GlobalTheory.T.mixed_projection_preserves_schwartz_adm F _ v _ hb₀ _).2 _ GlobalTheory.DiagForm.lDiag_adm) (fun z Φ hΦ => by
      have hz : u • ((1 - ε) • z) = u • ((1 - cA σ ε) • z) := by
        rw [← algebraMap_smul (AE F E) u, ← algebraMap_smul (AE F E) u, smul_smul, smul_smul, huA]
        congr 1
        linear_combination e1 - h4
      have hz' : u • M.co.e ((1 - ε) • z) = u • M.co.e ((1 - cA σ ε) • z) :=
        (M.co.e.map_smul u _).symm.trans ((congrArg M.co.e hz).trans (M.co.e.map_smul u _))
      have hz1 : u • (M.co.e ((1 - ε) • z)).1 = u • (M.co.e ((1 - cA σ ε) • z)).1 := congrArg Prod.fst hz'
      have hz2 : u • (M.co.e ((1 - ε) • z)).2 = u • (M.co.e ((1 - cA σ ε) • z)).2 := congrArg Prod.snd hz'
      refine mixed_inv ψ v _ hb₀ l₁ l₂ _ _ _ _ hz1 hz2 ?_ ?_ Φ hΦ
      · refine h₁ _ ?_
        ext i j; simp [e5]
      · refine h₂ _ ?_
        ext i j; simp [e7])
    g hgu T hT _ _ (hR φ hφ).1.2 (hR φ₂ hφ₂).2.2 (GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ _ (hR φ hφ).1.2 _ (hR φ₂ hφ₂).2.2)
  have hom : (om.comp (MonoidHom.inr _ _)) g (tens (evFin F v) φ R) = tens (evFin F v) φ₁ R := hA R (hR φ hφ).1
  rw [hom, hbox, hbox, LinearMap.comp_apply, LinearMap.comp_apply, proj_tens _ _ _ _ _ hRR, proj_tens _ _ _ _ _ hRR,
    tensForm_box, tensForm_box, map_smul, map_smul, ← hbox, smul_eq_mul, smul_eq_mul] at key
  set z : (AE F E)ˣ := Matrix.GeneralLinearGroup.det T with hzdef
  have hz : (z : AE F E) = (T : Matrix (Fin d) (Fin d) (AE F E)).det := rfl
  have z1 : At (evFin F v) ((z : AE F E) - 1) := at_det _ fun u hu => by
    rw [hT, add_sub_cancel_left, smul_comm]
    rw [show u • (((g : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) - 1) = 0 from hg u hu, smul_zero]
  have z2 : piW t (z : AE F E) = 1 := by
    have : (piW t).mapMatrix (T : Matrix (Fin d) (Fin d) (AE F E)) = (piW t).mapMatrix 1 := by
      rw [hT]; ext i j; simp [e6]
    rw [hz, RingHom.map_det, this, map_one, Matrix.det_one]
  have z3 : piW (t.comp σ) (z : AE F E) = y := by
    have : (piW (t.comp σ)).mapMatrix (T : Matrix (Fin d) (Fin d) (AE F E)) = (mat g).map (piW (t.comp σ)) := by
      rw [hT]; ext i j; simp [e7, mat]
    rw [hz, RingHom.map_det, this, hy]
  have c1 := GlobalTheory.T.local_character_norm_one_unit F E σ h χX v (t.comp σ) z z1 (by rw [comp_conj_conj h]; exact z2)
  rw [show Units.map (piW (t.comp σ)).toMonoidHom z = y from Units.ext z3] at c1
  obtain ⟨n1, n2⟩ := GlobalTheory.T.local_norm_unramified_factorization F E σ h v t z z1
  have c2 := GlobalTheory.T.distribHaarChar_supportedIdele_eq_localAbsValue F v (Units.map (Algebra.norm (AF F) : AE F E →* AF F) z) n1
  rw [show Units.map (evFin F v : AF F →* Fv F v) (Units.map (Algebra.norm (AF F) : AE F E →* AF F) z) = y from
    Units.ext (by rw [← z3, ← one_mul (piW (t.comp σ) _), ← z2]; exact n2)] at c2
  rw [c1, ← c2]
  apply mul_right_cancel₀ hne
  apply mul_right_cancel₀ hL
  rw [key, Fintype.card_fin]
  simp only [mul_assoc]
  rfl

theorem exists_pos_form (v : Pl F) (n d : ℕ) : ∃ Λ : (Matrix (Fin n) (Fin d) (Fv F v) → ℂ) →ₗ[ℂ] ℂ,
    (∀ f ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)), ∀ a, Λ (fun Y => f (Y + a)) = Λ f) ∧
      ∃ f ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)), f 0 ≠ 0 ∧ (∃ m : ℝ, 0 < m ∧ Λ f = m) ∧
        ∀ Q : GL (Fin d) (Fv F v), ∃ m : ℝ, 0 ≤ m ∧ Λ (fun Y => f (Y * Q.1ᵀ)) = m := by
  set O : Set (Fv F v) := (v.adicCompletionIntegers F : Set (Fv F v))
  have hO : IsOpen O := Valued.isOpen_valuationSubring _
  have hOc : IsCompact O := PI.IntAdCpctOpenWork.isCompact_adicCompletionIntegers v
  have h0' : (0 : Fv F v) ∈ O := (v.adicCompletionIntegers F).zero_mem
  set K : Set (Matrix (Fin n) (Fin d) (Fv F v)) := Set.univ.pi fun _ => Set.univ.pi fun _ => O
  have hKc : IsCompact K := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hOc
  have hKo : IsOpen K := isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => hO
  have h0 : (0 : Matrix (Fin n) (Fin d) (Fv F v)) ∈ K := fun _ _ _ _ => h0'
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin d) (Fv F v)) :=
    hKc.locallyCompactSpace_of_mem_nhds_of_addGroup (hKo.mem_nhds h0)
  letI := GlobalTheory.HaarSB.measG (Matrix (Fin n) (Fin d) (Fv F v))
  haveI := GlobalTheory.HaarSB.borelG (Matrix (Fin n) (Fin d) (Fv F v))
  have hind : ∀ S : Set (Matrix (Fin n) (Fin d) (Fv F v)), IsCompact S → IsOpen S →
      GlobalTheory.HaarSB.Lext _ (S.indicator fun _ => (1 : ℂ)) = ((Measure.addHaar : Measure _).real S : ℝ) := fun S hc ho => by
    have hi : Integrable (S.indicator fun _ => (1 : ℂ)) (Measure.addHaar : Measure (Matrix (Fin n) (Fin d) (Fv F v))) :=
      (integrable_indicator_iff ho.measurableSet).2 (integrableOn_const hc.measure_lt_top.ne)
    rw [GlobalTheory.HaarSB.Lext_apply _ hi, integral_indicator_const _ ho.measurableSet]
    simp
  refine ⟨GlobalTheory.HaarSB.Lext _, fun f hf a => GlobalTheory.HaarSB.Lext_translate hf a, K.indicator fun _ => 1, ?_, ?_, ?_, fun Q => ?_⟩
  · exact ⟨(LocallyConstant.indicator (1 : LocallyConstant _ ℂ) ⟨hKc.isClosed, hKo⟩).isLocallyConstant,
      HasCompactSupport.intro hKc fun z hz => Set.indicator_of_notMem hz _⟩
  · rw [Set.indicator_of_mem h0]; exact one_ne_zero
  · exact ⟨_, ENNReal.toReal_pos (hKo.measure_pos _ ⟨0, h0⟩).ne' hKc.measure_lt_top.ne, hind K hKc hKo⟩
  · let e : Matrix (Fin n) (Fin d) (Fv F v) ≃ₜ Matrix (Fin n) (Fin d) (Fv F v) :=
      { toFun := fun Y => Y * Q.1ᵀ
        invFun := fun Y => Y * (Q⁻¹).1ᵀ
        left_inv := fun Y => by
          simp only [Matrix.mul_assoc, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one, Matrix.mul_one]
        right_inv := fun Y => by
          simp only [Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.mul_one]
        continuous_toFun := continuous_id.matrix_mul continuous_const
        continuous_invFun := continuous_id.matrix_mul continuous_const }
    exact ⟨_, measureReal_nonneg, hind (e ⁻¹' K) (e.isCompact_preimage.2 hKc) (hKo.preimage e.continuous)⟩

theorem norm_chrW (χ : Chr F E) (t : E →ₐ[F] Fv F v) (y : (Fv F v)ˣ) : ‖(chrW χ t y : ℂ)‖ = 1 :=
  Circle.norm_coe _

theorem right_action_eq (hcm : IsCMExt F E σ) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (hXh : ∀ i j, σ (X.J j i) = X.J i j) (hXd : X.J.det ≠ 0) (hWh : ∀ i j, σ (W.J j i) = -W.J i j) (hWd : W.J.det ≠ 0)
    (χX χW : Chr F E) (om : Rep σ X W) (hW : M.IsWeil ψ χX χW om) (t : E →ₐ[F] Fv F v)
    (ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)) (hι : M.IsLinW ψ t 1 1 ι)
    (g : UA σ W.J) (hg : g ∈ UAt σ W (evFin F v)) (g' : GL (Fin d) (Fv F v)) (hg' : (mat g).map (piW t) = g'.1) :
    ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁, Acts (evFin F v) (om (1, g)) φ φ₁ →
      ι φ₁ = modelA (chrW χX t) n g' (ι φ) := by
  have hex : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∃ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (1, g)) φ φ₁ := fun φ hφ =>
    GlobalTheory.LocalOpsW.acts_exists hψ hW v (1, g) (GlobalTheory.SplitTransportPair.one_mem_UAt X v) hg φ hφ
  obtain ⟨c, hc⟩ := GlobalTheory.SplitTransportPair.shape hcm M ψ hψ hXh hXd hWh hWd χX χW om hW v t ι hι 1 g hex
  simp only [hg', GlobalTheory.SplitTransportPair.mat_one_map, Matrix.one_mul] at hc
  have hc' : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁, Acts (evFin F v) (om (1, g)) φ φ₁ →
      ι φ₁ = c • fun Y => ι φ (Y * (g'⁻¹).1ᵀ) := by
    intro φ hφ φ₁ hA
    funext Y
    rw [Pi.smul_apply, smul_eq_mul, ← hc φ hφ φ₁ hA, Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv,
      Matrix.transpose_one, Matrix.mul_one]
  obtain ⟨Λ, hΛ, f, hf, hf0, ⟨m, hm, hfm⟩, hQ⟩ := exists_pos_form v n d
  obtain ⟨μ, hμ, hfμ⟩ := hQ g'⁻¹
  obtain ⟨φ₀, hφ₀, rfl⟩ := hι.bij.surjOn hf
  obtain ⟨φ₀', -, hA₀⟩ := hex φ₀ hφ₀
  have H0 : ∀ w : Matrix (Fin n) (Fin d) (AE F E), w.map (piW t) = 0 → ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      (LinearMap.proj 0 ∘ₗ ι) (schr (psiAt ψ v) (locCo M.co v w) φ) = (LinearMap.proj 0 ∘ₗ ι) φ := fun w hw φ hφ => by
    obtain ⟨u, hu, e1, e2⟩ := exists_at (v := v) M w
    have := hι.mult u hu ((e2 t).trans hw) φ hφ _ (GlobalTheory.SchrSB.schr_mem_SB ψ hψ.1 v _ φ hφ)
      (GlobalTheory.VacBridge.rho_acts_locCo M.co ψ v u hu φ) 0 (fun a _ => smul_zero a) (Matrix.map_zero _ (map_zero _))
    rw [e1] at this
    simpa [symp, hTens] using this
  have H1 : ∀ w : Matrix (Fin n) (Fin d) (AE F E), w.map (piW (t.comp σ)) = 0 → ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      (Λ ∘ₗ ι) (schr (psiAt ψ v) (locCo M.co v w) φ) = (Λ ∘ₗ ι) φ := fun w hw φ hφ => by
    obtain ⟨u, hu, e1, e2⟩ := exists_at (v := v) M w
    have := hι.trans u hu ((e2 _).trans hw) _ hφ _ (GlobalTheory.SchrSB.schr_mem_SB ψ hψ.1 v _ _ hφ)
      (GlobalTheory.VacBridge.rho_acts_locCo M.co ψ v u hu _)
    rw [e1] at this
    change Λ (ι _) = Λ (ι _)
    rw [funext this, hΛ _ (hι.bij.mapsTo hφ)]
  have Hc : ∀ (l : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ) (w : Matrix (Fin n) (Fin d) (AE F E)),
      (∀ φ ∈ SB (Fin n × Fin d → Fv F v), l (schr (psiAt ψ v) (locCo M.co v w) φ) = l φ) →
      ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
        conjForm l (schr (psiAt ψ v) ((locCo M.co v w).1, -(locCo M.co v w).2) φ) = conjForm l φ := fun l w hl φ hφ => by
    change star (l _) = star (l _)
    rw [star_schr (psiAt ψ v) (fun x => GlobalTheory.StdCharFromIsStd.norm_psi hψ _), hl _ (star_mem_SB hφ)]
  set y : (Fv F v)ˣ := Matrix.GeneralLinearGroup.det g' with hy
  have hJ := GlobalTheory.SplitTransportPair.isUnit_det_map W.J hWd t
  have g2 : Units.val (y⁻¹ : (Fv F v)ˣ) = ((mat g).map (piW (t.comp σ))).det := by
    have u := congrArg Matrix.det (GlobalTheory.UnitaryInjAtPlace.unitary_at_components v t g)
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hg'] at u
    have u' : (g'.1.det * ((mat g).map (piW (t.comp σ))).det) * (W.J.map t).det = 1 * (W.J.map t).det := by
      linear_combination u
    exact Units.inv_eq_of_mul_eq_one_right (u := y) (mul_right_cancel₀ hJ.ne_zero u')
  have k1 := form_scalar_right hcm M ψ χX χW om hW t (LinearMap.proj 0 ∘ₗ ι) (conjForm (Λ ∘ₗ ι)) H0
    (fun w hw => Hc _ w (H1 w hw)) (star φ₀) (star_mem_SB hφ₀) (by
      change star (Λ (ι (star (star φ₀)))) ≠ 0
      rw [star_star, star_ne_zero, hfm]
      exact_mod_cast hm.ne') g hg y⁻¹ g2 φ₀ φ₀' hφ₀ hA₀
  have k2 := form_scalar_right hcm M ψ χX χW om hW (t.comp σ) (Λ ∘ₗ ι) (conjForm (LinearMap.proj 0 ∘ₗ ι)) H1
    (fun w hw => Hc _ w (H0 w (by rwa [comp_conj_conj hcm] at hw))) (star φ₀) (star_mem_SB hφ₀) (by
      change star (ι (star (star φ₀)) 0) ≠ 0
      rwa [star_star, star_ne_zero]) g hg y (by rw [comp_conj_conj hcm, hg']; rfl) φ₀ φ₀' hφ₀ hA₀
  rw [comp_conj_conj hcm] at k2
  change ι φ₀' 0 = _ * ι φ₀ 0 at k1
  change Λ (ι φ₀') = _ * Λ (ι φ₀) at k2
  rw [hc' φ₀ hφ₀ φ₀' hA₀] at k1 k2
  rw [Pi.smul_apply, smul_eq_mul, Matrix.zero_mul] at k1
  have k3 := mul_right_cancel₀ hf0 k1
  rw [map_smul, smul_eq_mul, hfμ, hfm, k3] at k2
  have hN := GlobalTheory.SplitWeil.Model.nabs_pos y
  have hn : GlobalTheory.SplitWeil.nabs (Fv F v) y⁻¹ ^ ((n : ℝ) / 2) = GlobalTheory.SplitWeil.nabs (Fv F v) y ^ (-(n : ℝ) / 2) := by
    rw [neg_div, Real.rpow_neg hN.le, ← Real.inv_rpow hN.le]
    simp [GlobalTheory.SplitWeil.nabs]
  rw [hn] at k2 k3
  have p1 : 0 ≤ GlobalTheory.SplitWeil.nabs (Fv F v) y ^ (-(n : ℝ) / 2) * μ := mul_nonneg (Real.rpow_nonneg hN.le _) hμ
  have p2 : 0 < GlobalTheory.SplitWeil.nabs (Fv F v) y ^ ((n : ℝ) / 2) * m := mul_pos (Real.rpow_pos_of_pos hN _) hm
  rw [mul_assoc, mul_assoc, ← Complex.ofReal_mul, ← Complex.ofReal_mul] at k2
  have k4 := congrArg norm k2
  rw [norm_mul, norm_mul, norm_chrW, norm_chrW, one_mul, one_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg p1, Real.norm_of_nonneg p2.le] at k4
  rw [k4] at k2
  have k5 := mul_right_cancel₀ (Complex.ofReal_ne_zero.2 p2.ne') k2
  rw [k5] at k3
  intro φ hφ φ₁ hA
  rw [hc' φ hφ φ₁ hA, k3]
  rfl

theorem linModel : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), GlobalTheory.ThK.KP → ∀ (hcm : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (n m : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JY : Matrix (Fin m) (Fin m) E), (∀ i j, σ (JX j i) = JX i j) → JX.det ≠ 0 → ∀ (hY : ∀ i j, σ (JY j i) = -JY i j) (hYd : JY.det ≠ 0) (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JY)) (Fin n × Fin m)), (∀ x : Matrix (Fin n) (Fin m) E, ∃ y z : Fin n × Fin m → F, co.e (incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k))) → ∀ χX χY : Chr F E, IsHecke F E χX → IsHecke F E χY → ∀ om : UA σ JX × UA σ JY →* Module.End ℂ ((Fin n × Fin m → AF F) → ℂ), IsUWeilPair (cA σ) (adeleClass F) ψ (-1) (incM F JX) (incM F JY) co χX χY om → ∀ (v : Pl F) (τ : E →ₐ[F] Fv F v), ∃ ι : ((Fin n × Fin m → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin m) (Fv F v) → ℂ), Set.BijOn ι (SB (Fin n × Fin m → Fv F v) : Set _) (GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin m) (Fv F v)) : Set _) ∧ ∀ (h : GL (Fin m) (Fv F v)), ∀ φ ∈ SB (Fin n × Fin m → Fv F v), ∃ φ₁ ∈ SB (Fin n × Fin m → Fv F v), ι φ₁ = modelA (chrW χX τ) n h (ι φ) ∧ Acts (evFin F v) (om (1, liftSk hcm τ JY hY hYd h)) φ φ₁ := by
  intro F E _ _ _ _ _ σ _ hcm ψ hψ n m JX JY hX hXd hY hYd co _ χX χY _ _ om hom v τ
  let X : Spc F E n := ⟨JX, ⊥, fun _ => 0, fun _ => 1⟩
  let W : Spc F E m := ⟨JY, ⊥, fun _ => 0, fun _ => 1⟩
  let M : Model σ X W := ⟨co, fun _ _ => 0, 0, ∅⟩
  have hW : M.IsWeil ψ χX χY om := hom
  obtain ⟨ι, hι⟩ := GlobalTheory.SplitTransportPair.exists_isLinW hcm M ψ hψ hX hXd hY hYd v τ
  refine ⟨ι, hι.bij, fun h φ hφ => ?_⟩
  have hg : liftSk hcm τ JY hY hYd h ∈ UAt σ W (evFin F v) := GlobalTheory.SplitUnitLift.liftU_mem_UAt hcm τ W (-1) _ _ h
  obtain ⟨φ₁, hφ₁, hA⟩ := GlobalTheory.LocalOpsW.acts_exists hψ hW v (1, liftSk hcm τ JY hY hYd h)
    (GlobalTheory.SplitTransportPair.one_mem_UAt X v) hg φ hφ
  exact ⟨φ₁, hφ₁, right_action_eq hcm M ψ hψ hX hXd hY hYd χX χY om hW τ ι hι _ hg h
    (GlobalTheory.SplitUnitLift.liftU_piW hcm τ JY (-1) _ _ h) φ hφ φ₁ hA, hA⟩

end GlobalTheory.SplitScalRight
