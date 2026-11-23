import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalTranslationEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarFunctionalGoodPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryDeterminedBySplitImage
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WFamilyBar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem acts_mul (hT : IsTriple B G X om om') {v : Pl F} {h₁ h₂ : UA σ G.W.J}
    {φ φ₂ φ₃ : (Fin a' × Fin (a + a') → Fv F v) → ℂ}
    (h2 : Acts (evFin F v) (om' (1, h₂)) φ φ₂) (h1 : Acts (evFin F v) (om' (1, h₁)) φ₂ φ₃) :
    Acts (evFin F v) (om' (1, h₁ * h₂)) φ φ₃ := by
  intro r hr
  have hr2 : Rest (evFin F v) φ₂ r :=
    ⟨hr.1, by rw [← h2 r hr]; exact (IsUWeilPair.isUSplitting hT.weil').pres _ _ hr.2⟩
  have e : om' (1, h₁ * h₂) = om' (1, h₁) * om' (1, h₂) := by rw [← map_mul]; simp
  rw [e, Module.End.mul_apply, h2 r hr, h1 r hr2]

theorem acts_id {v : Pl F} (φ : (Fin a' × Fin (a + a') → Fv F v) → ℂ) :
    Acts (evFin F v) (om' (1, 1)) φ φ := by
  intro r _
  rw [show ((1, 1) : UA σ G.V'.J × UA σ G.W.J) = 1 from rfl, map_one, Module.End.one_apply]

end GlobalTheory.WFamilyBar

namespace GlobalTheory.WFamilyBar

theorem family : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ ι, G.M'.IsLinBar B.ψ B.τ₁ 1 1 ι →
    ∃ (S : GL (Fin (a + a')) (Fv F B.v₁) → ((Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ) → (Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ)
      (χ : (Fv F B.v₁)ˣ →* ℂˣ),
      (∀ g, ∃ h ∈ UAt σ G.W (evFin F B.v₁), ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁),
        S g φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁) ∧ Acts (evFin F B.v₁) (om' (1, h)) φ (S g φ)) ∧
      (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁),
        ι (S g φ) = fun Y => (χ (Matrix.GeneralLinearGroup.det g) : ℂ) * ι φ (Y * g.val)) ∧
      ∀ h ∈ UAt σ G.W (evFin F B.v₁), ∀ c : ℂ,
        (∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁), ∀ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁),
          Acts (evFin F B.v₁) (om' (1, h)) φ φ₁ → ι φ₁ = c • fun Y => ι φ (Y * (mat h).map (piW B.τ₁))) →
        c = (χ (Matrix.GeneralLinearGroup.det (GlobalTheory.LocalUnitSubgroupClosure.cmpGL B.τ₁ h)) : ℂ) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT ι hι
  have hcm : IsCMExt F E σ := hT.base.cm
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have skew : ∀ i j, σ (G.W.J j i) = algebraMap F E (-1) * G.W.J i j := fun i j => by
    rw [map_neg, map_one, neg_one_mul]; exact hT.geo.hW.skew i j
  have hdetW : IsUnit (G.W.J.map B.τ₁).det :=
    GlobalTheory.SplitUnitLift.isUnit_det_of_cartan G.W.J B.τ₁ (B.emb w).1 Complex.I Complex.I_ne_zero (G.W.θ w)
      (hT.geo.hW.cartan w)
  obtain ⟨L, hLmem, hLt, hLts⟩ : ∃ L : GL (Fin (a + a')) (Fv F B.v₁) →* UA σ G.W.J,
      (∀ g, L g ∈ UAt σ G.W (evFin F B.v₁)) ∧ (∀ g, (mat (L g)).map (piW B.τ₁) = g.val) ∧
      ∀ g, (mat (L g)).map (piW (B.τ₁.comp σ)) =
        (G.W.J.map B.τ₁)⁻¹ * ((g⁻¹ : GL (Fin (a + a')) (Fv F B.v₁)).val)ᵀ * G.W.J.map B.τ₁ :=
    ⟨GlobalTheory.SplitUnitLift.liftU hcm B.τ₁ G.W.J (-1) skew hdetW,
      GlobalTheory.SplitUnitLift.liftU_mem_UAt hcm B.τ₁ G.W (-1) skew hdetW,
      GlobalTheory.SplitUnitLift.liftU_piW hcm B.τ₁ G.W.J (-1) skew hdetW,
      GlobalTheory.SplitUnitLift.liftU_piW_comp hcm B.τ₁ G.W.J (-1) skew hdetW⟩
  choose S hS hlin hcov hinj using fun g =>
    GlobalTheory.WeilTransferW.local_weil_operator_second_space hP F E σ B a a' G X om om' hT B.v₁ (L g) (hLmem g)
  choose c hc using fun g => GlobalTheory.WeilTransferW.linBar_right_mul F E σ B a a' G X om om' hT B.v₁ B.τ₁ (L g) g (hLmem g)
    (hLt g) (hLts g) (S g) (fun φ hφ => (hS g φ hφ).1) (hlin g) (hcov g) ι hι
  have hEx := (GlobalTheory.T.theta_action_exists hP F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' G.q (a' - G.q)
    (a + a' - (G.p + G.q)) (G.p + G.q) (GlobalTheory.ThK.Inhab.pairV' hT) B.v₁).1 1 (GlobalTheory.LocalUnitSubgroupClosure.one_mem_UAt _ _)
  have hvac := hT.geo.hM'.vac B.v₁
  have hne : ι (G.M'.vac B.v₁) ≠ 0 := fun h0 =>
    hvac.2.1 (hι.bij.injOn hvac.1 (Submodule.zero_mem _) (by rw [h0, map_zero]))
  obtain ⟨Y₀, hY₀⟩ := Function.ne_iff.1 hne
  have uniq : ∀ (g : GL (Fin (a + a')) (Fv F B.v₁)) (d : ℂ),
      ι (S g (G.M'.vac B.v₁)) = (d • fun Y => ι (G.M'.vac B.v₁) (Y * g.val)) → d = c g := by
    intro g d hd
    have e := congrFun (hd.symm.trans (hc g _ hvac.1)) (Y₀ * (g⁻¹ : GL (Fin (a + a')) (Fv F B.v₁)).val)
    simp only [Pi.smul_apply, smul_eq_mul] at e
    rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one] at e
    exact mul_right_cancel₀ hY₀ e
  have c1 : c 1 = 1 := by
    refine (uniq 1 1 ?_).symm
    have e : S 1 (G.M'.vac B.v₁) = G.M'.vac B.v₁ :=
      (hEx (L 1) (hLmem 1) _ hvac.1).unique (hS 1 _ hvac.1) ⟨hvac.1, by rw [map_one L]; exact acts_id _⟩
    rw [e, one_smul]
    funext Y
    rw [Units.val_one, Matrix.mul_one]
  have cmul : ∀ g g', c (g * g') = c g * c g' := by
    intro g g'
    refine (uniq (g * g') _ ?_).symm
    have h2 := hS g' _ hvac.1
    have h1 := hS g _ h2.1
    have e : S (g * g') (G.M'.vac B.v₁) = S g (S g' (G.M'.vac B.v₁)) :=
      (hEx (L (g * g')) (hLmem _) _ hvac.1).unique (hS _ _ hvac.1)
        ⟨h1.1, by rw [map_mul L]; exact acts_mul hT h2.2 h1.2⟩
    rw [e, hc g _ h2.1, hc g' _ hvac.1]
    funext Y
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Units.val_mul, Matrix.mul_assoc, mul_assoc]
  let κ : GL (Fin (a + a')) (Fv F B.v₁) →* ℂ := { toFun := c, map_one' := c1, map_mul' := cmul }
  obtain ⟨χ, hχ⟩ := GlobalTheory.ghom_factors_through_det (GlobalTheory.LocalUnitSubgroupClosure.two_ne_zero_Fv B.v₁) κ.toHomUnits
  have hcχ : ∀ g, c g = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) := by
    intro g
    have := congrArg Units.val (hχ g)
    rw [MonoidHom.coe_toHomUnits] at this
    exact this
  refine ⟨S, χ, fun g => ⟨L g, hLmem g, hS g⟩, fun g φ hφ => ?_, fun h hh d hd => ?_⟩
  · rw [hc g φ hφ, hcχ]
    rfl
  · have hL : L (GlobalTheory.LocalUnitSubgroupClosure.cmpGL B.τ₁ h) = h :=
      GlobalTheory.UnitaryInjAtPlace.eq_of_piW_eq F E σ B a a' G X om om' hT B.v₁ hT.chars.good B.τ₁ _ (hLmem _) _ hh
        (by rw [hLt, GlobalTheory.LocalUnitSubgroupClosure.cmpGL_val])
    have h1 := hS (GlobalTheory.LocalUnitSubgroupClosure.cmpGL B.τ₁ h) _ hvac.1
    rw [hL] at h1
    rw [← hcχ]
    exact uniq _ d (hd _ hvac.1 _ h1.1 h1.2)

end GlobalTheory.WFamilyBar
