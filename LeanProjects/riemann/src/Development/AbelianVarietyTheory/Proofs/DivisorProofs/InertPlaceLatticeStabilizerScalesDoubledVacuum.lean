import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemAdelicSchwartzSpaceNumberFieldOfMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergEigenProportionalLocalFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryCommutingHeisenbergActsFibrewiseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictFinitePlaceMemSchwartzBruhStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMemOfMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicAddCharNontrivialFinitePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromColsMemLatDbl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdentityOfTensorHeisenbergEigenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticFormUnitaryGroupActionInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergEigenDoubledCoordsProductFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumLatticeStabilizerPreservesDoubledSpStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledLatticeLocalImageFullAtInertPlaceStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVacEigen

open MeasureTheory

theorem sb_boxFun {k : Type} [CommRing k] [TopologicalSpace k] [T2Space k] {κ κ' : Type}
    {φ₁ : (κ → k) → ℂ} {φ₂ : (κ' → k) → ℂ} (h₁ : φ₁ ∈ SB (κ → k)) (h₂ : φ₂ ∈ SB (κ' → k)) :
    boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → k) := by
  have cl : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inl := continuous_pi fun i => continuous_apply _
  have cr : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inr := continuous_pi fun i => continuous_apply _
  refine ⟨(h₁.1.comp_continuous cl).mul (h₂.1.comp_continuous cr), ?_⟩
  let e := (Homeomorph.sumArrowHomeomorphProdArrow (X := k) (ι := κ) (ι' := κ'))
  refine HasCompactSupport.intro ((h₁.2.prod h₂.2).image e.symm.continuous) fun x hx => ?_
  have hx' : e x ∉ tsupport φ₁ ×ˢ tsupport φ₂ := fun h => hx ⟨e x, h, e.symm_apply_apply x⟩
  rw [Homeomorph.sumArrowHomeomorphProdArrow_apply, Set.mem_prod, not_and_or] at hx'
  simp only [boxFun]
  rcases hx' with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

theorem sb_star {X : Type} [TopologicalSpace X] {φ : X → ℂ} (h : φ ∈ SB X) : (fun x => star (φ x)) ∈ SB X :=
  ⟨h.1.comp (fun z : ℂ => star z), h.2.comp_left (g := fun z : ℂ => star z) (star_zero _)⟩

theorem locality_op {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl F) (ψ : AddChar (AF F) ℂ)
    (T : Module.End ℂ ((κ → AF F) → ℂ)) (hψ : IsStd ψ) (hkeep : ∀ Φ ∈ schA F κ, T Φ ∈ schA F κ)
    (hunit : ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ Φ ∈ schA F κ, ∫⁻ y, ‖T Φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖Φ y‖ₑ ^ 2 ∂μ)
    (hcomm : ∀ u : AF F, evFin F v u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ schA F κ,
      T (schr ψ (u • p, u • q) Φ) = schr ψ (u • p, u • q) (T Φ)) :
    ∃ S : ((κ → Fv F v) → ℂ) → (κ → Fv F v) → ℂ, ∀ φ ∈ SB (κ → Fv F v), S φ ∈ SB _ ∧ Acts (evFin F v) T φ (S φ) := by
  have hfib := GlobalTheory.T.isometry_commuting_heisenberg_acts_fibrewise v ψ T hψ (GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace ψ hψ) hkeep hunit hcomm
  have htr : ∀ u : AF F, evFin F v u = 0 → ∀ p : κ → AF F,
      ∀ Φ ∈ schA F κ, T (fun y => Φ (y + u • p)) = fun y => T Φ (y + u • p) := by
    intro u hu p Φ hΦ
    have h := hcomm u hu p 0 Φ hΦ
    have e1 : ∀ Ψ : (κ → AF F) → ℂ, schr ψ (u • p, u • (0 : κ → AF F)) Ψ = fun y => Ψ (y + u • p) := fun Ψ => by
      funext y; simp [schr]
    rw [e1, e1] at h
    exact h
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction κ v
  refine ⟨fun φ t => (R 0)⁻¹ * T (tens (evFin F v) φ R) (fun i => GlobalTheory.LatVac.liftV v (t i)),
    fun φ hφ => ⟨?_, ?_⟩⟩
  · have h4 := GlobalTheory.T.adelicSchwartz_restrict_finitePlace_mem_schwartzBruhat v _ (hkeep _ (hR φ hφ).2)
    exact (SB _).smul_mem (R 0)⁻¹ h4
  · intro r hr
    funext y
    set u : AF F := 1 - GlobalTheory.LatVac.liftV v 1 with hudef
    have hu : evFin F v u = 0 := by simp [hudef, GlobalTheory.LatVac.evFin_liftV]
    set p : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (evFin F v (y i)) with hpdef
    have hyp : y + u • (-y) = p := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hudef, hpdef]
      rw [← GlobalTheory.WeilLocality.liftV_one_mul]
      ring
    have hpat : At (evFin F v) p := by
      intro u' hu'
      funext i
      exact GlobalTheory.LatVac.at_liftV v _ u' hu'
    set Φ₀ := tens (evFin F v) φ R with hΦ₀
    set Φ₁ := tens (evFin F v) φ r with hΦ₁
    set Φ₂ : (κ → AF F) → ℂ := (r y / R 0) • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
    have hm₀ : Φ₀ ∈ schA F _ := (hR φ hφ).2
    have hm₂ : Φ₂ ∈ schA F _ := Submodule.smul_mem _ _ (GlobalTheory.T.adelicSchwartzSpace_translate_mem_of_mem _ _ hm₀)
    have hfz : ∀ z, At (evFin F v) z → (Φ₁ - Φ₂) (y + z) = 0 := by
      intro z hz
      have e1 : r (y + z) = r y := hr.1 y z hz
      have e2 : y + z + u • (-y) = p + z := by rw [← hyp]; abel
      have hpz : At (evFin F v) (p + z) := fun u' hu' => by
        rw [smul_add, hpat u' hu', hz u' hu', add_zero]
      have e3 : R (p + z) = R 0 := by simpa using (hR φ hφ).1 0 (p + z) hpz
      have e4 : (fun i => evFin F v ((y + z + u • (-y)) i)) = fun i => evFin F v ((y + z) i) := by
        funext i
        simp [hu]
      simp only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, tens]
      rw [e4, e2, e3, e1]
      field_simp
      ring
    have h0 := hfib (Φ₁ - Φ₂) (sub_mem hr.2 hm₂) y hfz
    rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
    have h2 : T Φ₂ y = (r y / R 0) * T Φ₀ p := by
      rw [hΦ₂, map_smul, htr u hu (-y) Φ₀ hm₀, Pi.smul_apply, smul_eq_mul, hyp]
    rw [h0, h2]
    simp only [tens, hpdef]
    field_simp
    ring

end GlobalTheory.DblVacEigen

noncomputable section
namespace GlobalTheory.DblVacEigen

theorem eigen_box : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (dd : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.V.J) (dbl (incM F G.W.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.W →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (cA σ) (-1 : AE F E) (incM F G.V.J) (incM F G.W.J) G.M.co dd →
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1 : AE F E) (incM F G.V.J) (dbl (incM F G.W.J)) dd X.β (diagCols (Fin (a + a'))) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r →
    ∀ g ∈ GlobalTheory.DblVac.KD σ G.W v, ∃ μ : ℂ,
      omd g (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hw hv dd omd hdc hsp r hr g hg
  classical
  by_cases hr0 : ∀ x, r x = 0
  · refine ⟨0, ?_⟩
    have h0 : boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) = 0 := by
      funext x; simp [boxFun, tens, hr0]
    rw [h0, map_zero, smul_zero]
  push_neg at hr0
  obtain ⟨x₀, hx₀⟩ := hr0
  obtain ⟨hvSB, hv0, θ, hθ, hvac⟩ := hT.geo.hM.vac v
  have hψ1 : ∀ t, ‖B.ψ t‖ = 1 := GlobalTheory.StdCharFromIsStd.norm_psi hT.base.std
  set vac := G.M.vac v with hvacdef
  set V₀ := tens (evFin F v) vac r with hV₀
  set S := boxFun V₀ (fun x => star (V₀ x)) with hS
  set vd : ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → Fv F v) → ℂ := boxFun vac (fun x => star (vac x)) with hvd
  set R : ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ := boxFun r (fun x => star (r x)) with hR
  have hSt : S = tens (evFin F v) vd R := by
    funext x
    simp only [hS, hvd, hR, hV₀, boxFun, tens, star_mul', Function.comp_def]
    ring
  have hSA : S ∈ schA F _ := GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ V₀ hr.2 _ (GlobalTheory.T.conj_mem_adelicSchwartzSpaceNumberField_of_mem _ V₀ hr.2)
  have hRinv : ∀ x z, At (evFin F v) z → R (x + z) = R x := by
    intro x z hz
    have hl : At (evFin F v) (z ∘ Sum.inl) := fun u hu => by funext i; exact congrFun (hz u hu) (Sum.inl i)
    have hr' : At (evFin F v) (z ∘ Sum.inr) := fun u hu => by funext i; exact congrFun (hz u hu) (Sum.inr i)
    simp only [hR, boxFun]
    rw [show (x + z) ∘ Sum.inl = x ∘ Sum.inl + z ∘ Sum.inl from rfl,
      show (x + z) ∘ Sum.inr = x ∘ Sum.inr + z ∘ Sum.inr from rfl, hr.1 _ _ hl, hr.1 _ _ hr']
  have hRest : Rest (evFin F v) vd R := ⟨hRinv, hSt ▸ hSA⟩
  have hvdSB : vd ∈ SB _ := sb_boxFun hvSB (sb_star hvSB)
  have hvd0 : vd ≠ 0 := by
    obtain ⟨y, hy⟩ := Function.ne_iff.mp hv0
    intro h
    have h1 := congrFun h (Sum.elim y y)
    simp only [hvd, boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr, Pi.zero_apply] at h1 hy
    exact mul_ne_zero hy (star_ne_zero.mpr hy) h1
  have hRx : R (Sum.elim x₀ x₀) ≠ 0 := by
    simp only [hR, boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr]
    exact mul_ne_zero hx₀ (star_ne_zero.mpr hx₀)

  have hspl := hsp.2.1
  have hcomm : ∀ u : AF F, evFin F v u = 0 → ∀ p q : (Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F,
      ∀ Φ ∈ schA F _, omd g (schr B.ψ (u • p, u • q) Φ) = schr B.ψ (u • p, u • q) (omd g Φ) := by
    intro u hu p q Φ hΦ
    set w' := dd.e.symm (p, q) with hw'
    have he : dd.e (u • w') = (u • p, u • q) := by
      rw [LinearEquiv.map_smul, hw', LinearEquiv.apply_symm_apply, Prod.smul_mk]
    have h0 : u • (GlobalTheory.DblVac.matD g - 1) = 0 := hg.1 u hu
    have hact : actB (cA σ) g (u • w') = u • w' := by
      have h1 : (u • w') * (GlobalTheory.DblVac.matD g)ᵀ - u • w' = w' * (u • (GlobalTheory.DblVac.matD g - 1))ᵀ := by
        rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one,
          Matrix.mul_sub, Matrix.mul_one, smul_sub]
      rw [h0, Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero] at h1
      exact h1
    have h2 := hspl.impl g (u • w') Φ hΦ
    simp only [Darboux.rho, he, hact] at h2
    exact h2
  obtain ⟨Tl, hTl⟩ := locality_op v B.ψ (omd g) hT.base.std (fun Φ hΦ => hspl.pres g Φ hΦ)
    (fun μ hμ Φ hΦ => hspl.unit μ hμ g Φ hΦ) hcomm
  have hgS : omd g S = tens (evFin F v) (Tl vd) R := by rw [hSt]; exact (hTl vd hvdSB).2 R hRest

  have hV₀eig : ∀ γ ∈ (latAtV G.V G.W v : Set _), G.M.co.rho B.ψ γ V₀ =
      B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) γ γ) • V₀ := by
    intro γ hγ
    rw [hV₀, hvac γ hγ r hr]
    funext x
    simp [tens, mul_assoc]
  have hSeig : ∀ γ ∈ latDbl G.V G.W v, dd.rho B.ψ γ S =
      B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (dbl (incM F G.W.J)) γ γ) • S :=
    fun γ hγ => GlobalTheory.T.heisenbergEigen_doubledCoords_productFunction (cA σ) (-1) (inclR (F := F) (AF F) (θ : E)) _ _ G.M.co dd hdc B.ψ hψ1 _ V₀ hV₀eig γ hγ.1 hγ.2

  have hgSeig : ∀ γ ∈ latDbl G.V G.W v, dd.rho B.ψ γ (omd g S) =
      B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (dbl (incM F G.W.J)) γ γ) • omd g S := by
    intro γ hγ
    have hK := (GlobalTheory.T.doubledVacuumLatticeStabilizer_preserves_doubledSpaceLattice F E σ G.V G.W v g hg γ hγ).2
    have h1 := hspl.impl g (actB (cA σ) g⁻¹ γ) S hSA
    have h2 : actB (cA σ) g (actB (cA σ) g⁻¹ γ) = γ := by
      simp only [actB, Matrix.mul_assoc, ← Matrix.transpose_mul]
      have e : ((g : GL (Fin (a + a') ⊕ Fin (a + a')) (AE F E)) :
            Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a') ⊕ Fin (a + a')) (AE F E)) *
          (((g⁻¹ : GlobalTheory.DblVac.UD σ G.W) : GL (Fin (a + a') ⊕ Fin (a + a')) (AE F E)) :
            Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a') ⊕ Fin (a + a')) (AE F E)) = 1 := by
        rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]
      rw [e, Matrix.transpose_one, Matrix.mul_one]
    rw [h2] at h1
    rw [← h1, hSeig (actB (cA σ) g⁻¹ γ) hK, map_smul, GlobalTheory.T.traceSymplecticForm_unitaryGroupAction_invariant]

  let Λd := (latDbl G.V G.W v).map (GlobalTheory.LatVac.locCo dd v)
  let χ : (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → Fv F v) × ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → Fv F v)) → ℂ :=
    fun l => if h : ∃ γ ∈ latDbl G.V G.W v, GlobalTheory.LatVac.locCo dd v γ = l then
      B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (dbl (incM F G.W.J)) h.choose h.choose)
      else 0
  have loc : ∀ f : ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → Fv F v) → ℂ,
      (∀ γ ∈ latDbl G.V G.W v, dd.rho B.ψ γ (tens (evFin F v) f R) =
        B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (dbl (incM F G.W.J)) γ γ) •
          tens (evFin F v) f R) →
      ∀ l ∈ Λd, ∀ ξ, GlobalTheory.LatVac.psiAt B.ψ v (ξ ⬝ᵥ l.2 + (2 : Fv F v)⁻¹ * (l.1 ⬝ᵥ l.2)) * f (ξ + l.1) = χ l * f ξ := by
    intro f hf l hl ξ
    have h : ∃ γ ∈ latDbl G.V G.W v, GlobalTheory.LatVac.locCo dd v γ = l := AddSubgroup.mem_map.mp hl
    have key := GlobalTheory.T.localIdentity_of_tensorHeisenbergEigen v dd B.ψ h.choose f R _ (at_of_mem_latDbl _ _ _ h.choose_spec.1) hRinv
      (Sum.elim x₀ x₀) hRx (hf _ h.choose_spec.1) ξ
    simp only [χ, dif_pos h]
    rw [h.choose_spec.2] at key
    exact key
  have hloc1 := loc vd (fun γ hγ => hSt ▸ hSeig γ hγ)
  have hloc2 := loc (Tl vd) (fun γ hγ => hgS ▸ hgSeig γ hγ)
  obtain ⟨c, hc⟩ := GlobalTheory.T.heisenbergEigen_proportional_localField (GlobalTheory.LatVac.psiAt B.ψ v) Λd χ vd (Tl vd) hloc1 hloc2 hvd0
    (GlobalTheory.T.doubled_lattice_local_image_full_at_inert_place F E σ B a a' G X om om' hT v w hw dd hdc)
  refine ⟨c, ?_⟩
  rw [hgS, hc, hSt]
  funext x
  simp [tens, mul_assoc]

end GlobalTheory.DblVacEigen
