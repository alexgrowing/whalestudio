import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodingerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelHeisenbergOperatorsTranslationCharStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulOfCommuteHeisenbergLinearModelSchwartzBruhStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlCharacterFactorsThroughDetOfTwoNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsWeilCharacterDetEqAbsDetPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergPreservesSchwartzBStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergInnerPreservingStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem GlobalTheory.LinModelLocal.exists_omB_of_linBar : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' →
    ∀ (K : GL (Fin a') (Fv F Bs.v₁) →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.V'.J),
    (∀ g, K g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.V' (evFin F Bs.v₁) ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = g.val ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp σ)) =
        (Γ.V'.J.map Bs.τ₁)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * Γ.V'.J.map Bs.τ₁) →
    ∀ (S : GL (Fin a') (Fv F Bs.v₁) → ((Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ) → (Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ),
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _) →
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _, ∀ c : ℂ, S g (c • φ + φ') = c • S g φ + S g φ') →
    (∀ g g', ∀ φ ∈ GlobalTheory.WeilM.SB _, S (g * g') φ = S g (S g' φ)) →
    (∀ φ ∈ GlobalTheory.WeilM.SB _, S 1 φ = φ) →
    (∀ g (γ : Matrix (Fin a') (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F Bs.v₁) γ →
      ∀ φ ∈ GlobalTheory.WeilM.SB _,
        S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ) =
          GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁)
            (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (K g, (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.W.J)) γ)) (S g φ)) →
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ μ : @Measure (Fin a' × Fin (a + a') → Fv F Bs.v₁) (borel _),
      @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∃ ν α : (Fv F Bs.v₁)ˣ →* ℂˣ, (∀ x, ‖(ν x : ℂ)‖ = 1) ∧
      ∀ ι, Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι → ∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g φ) = omB ν α g 1 (ι φ) := by
  intro F E _ _ _ _ _ σ a a' Bs Γ X om om' hTr K hK S h1 hlin h2 h3 h4 h5
  obtain ⟨hψc, hψ1, wT, wM, hA⟩ := GlobalTheory.T.linearModel_heisenbergOperators_translation_char Bs Γ X om om' hTr K hK S h1 h4
  by_cases hex : ∃ ι, Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι
  swap
  · exact ⟨1, 1, fun x => by simp, fun ι hι => absurd ⟨ι, hι⟩ hex⟩
  obtain ⟨ι₀, hι₀⟩ := hex
  obtain ⟨hT0, hM0, hST0, hSM0⟩ := hA ι₀ hι₀
  have hbij0 := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLin.bij hι₀
  have hU0 : ∀ (w : (Fin a' × Fin (a + a') → Fv F Bs.v₁) × (Fin a' × Fin (a + a') → Fv F Bs.v₁)),
      ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F Bs.v₁), GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) w φ ∈ GlobalTheory.WeilM.SB _ :=
    fun w => GlobalTheory.T.schroedingerOperatorHeisenberg_preserves_schwartzBruhat (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) hψc w
  have key1 : ∀ (h : GL (Fin a') (Fv F Bs.v₁)) (Y : Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁)),
      h.valᵀ * (((h⁻¹ : GL (Fin a') (Fv F Bs.v₁)).val)ᵀ * Y) = Y := by
    intro h Y
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one, Matrix.one_mul]
  have key2 : ∀ (h : GL (Fin a') (Fv F Bs.v₁)) (Y : Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁)),
      ((h⁻¹ : GL (Fin a') (Fv F Bs.v₁)).val)ᵀ * (h.valᵀ * Y) = Y := by
    intro h Y
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.one_mul]
  have hc : ∀ g : GL (Fin a') (Fv F Bs.v₁), ∃ c : ℂ, ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F Bs.v₁),
      (fun Y => ι₀ (S g φ) (((g⁻¹ : GL (Fin a') (Fv F Bs.v₁)).val)ᵀ * Y)) = c • ι₀ φ := by
    intro g
    refine GlobalTheory.T.eq_smul_of_commute_heisenberg_linearModel_schwartzBruhat (GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F Bs.v₁)) (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) hψc hψ1 ι₀
      (fun φ Y => ι₀ (S g φ) (((g⁻¹ : GL (Fin a') (Fv F Bs.v₁)).val)ᵀ * Y)) hbij0 ?_
      (fun C => GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wT C))
      (fun l => GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wM l)) ?_ ?_
    · intro x hx y hy c
      funext Y
      simp only [hlin g x hx y hy c, map_add, map_smul, Pi.add_apply, Pi.smul_apply]
    · intro C x hx
      refine ⟨hU0 _ x hx, hT0 C x hx, ?_⟩
      funext Y
      simp only [hST0 g C x hx, Matrix.mul_add]
    · intro l x hx
      refine ⟨hU0 _ x hx, hM0 l x hx, ?_⟩
      funext Y
      simp only [hSM0 g l x hx, key1]
  choose c hc using hc
  have hrel : ∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F Bs.v₁),
      ι₀ (S g φ) = fun Y => c g * ι₀ φ (g.valᵀ * Y) := by
    intro g φ hφ
    funext Y
    have := congrFun (hc g φ hφ) (g.valᵀ * Y)
    simp only [key2, Pi.smul_apply, smul_eq_mul] at this
    exact this
  have hvac := (hTr.geo.hM'.vac Bs.v₁)
  set φv := Γ.M'.vac Bs.v₁
  have hφv : φv ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F Bs.v₁) := hvac.1
  have hιv : ι₀ φv ≠ 0 := by
    intro h0
    exact hvac.2.1 (hbij0.injOn hφv (Submodule.zero_mem _) (by rw [h0, map_zero]))
  obtain ⟨Y₀, hY₀⟩ := Function.ne_iff.mp hιv
  have hmul : ∀ g g', c (g * g') = c g * c g' := by
    intro g g'
    have e := congrFun (congrArg ι₀ (h2 g g' φv hφv)) ((((g * g')⁻¹ : GL (Fin a') (Fv F Bs.v₁)).val)ᵀ * Y₀)
    rw [hrel (g * g') φv hφv, hrel g (S g' φv) (h1 g' φv hφv), hrel g' φv hφv] at e
    beta_reduce at e
    have e2 : (g'.val)ᵀ * ((g.val)ᵀ * ((((g * g')⁻¹ : GL (Fin a') (Fv F Bs.v₁)).val)ᵀ * Y₀)) = Y₀ := by
      rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, key1]
    rw [key1 (g * g') Y₀, e2] at e
    exact mul_right_cancel₀ hY₀ (e.trans (mul_assoc _ _ _).symm)
  have hone : c 1 = 1 := by
    have e := congrFun (congrArg ι₀ (h3 φv hφv)) Y₀
    rw [hrel _ _ hφv] at e
    simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul] at e
    exact (mul_eq_right₀ hY₀).mp e
  let cH : GL (Fin a') (Fv F Bs.v₁) →* ℂ := ⟨⟨c, hone⟩, hmul⟩
  have h2ne : (2 : Fv F Bs.v₁) ≠ 0 := (isUnit_of_invertible (2 : Fv F Bs.v₁)).ne_zero
  obtain ⟨χ, hχ⟩ := GlobalTheory.T.glCharacter_factors_through_det_of_two_ne_zero h2ne cH.toHomUnits
  have hcχ : ∀ g, c g = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) := fun g => by
    rw [← hχ g]; rfl
  obtain ⟨ν, hν1, hν⟩ := GlobalTheory.T.abs_weilCharacter_det_eq_abs_det_pow (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) hψc hψ1 ι₀ hbij0
    (fun C => GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wT C))
    (fun l => GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wM l))
    (fun C φ hφ => ⟨hU0 _ φ hφ, hT0 C φ hφ⟩) (fun l φ hφ => ⟨hU0 _ φ hφ, hM0 l φ hφ⟩)
    (fun μ hμ C φ _ φ' _ => GlobalTheory.T.schroedingerOperatorHeisenberg_inner_preserving _ hψc μ hμ _ φ φ') (fun μ hμ l φ _ φ' _ => GlobalTheory.T.schroedingerOperatorHeisenberg_inner_preserving _ hψc μ hμ _ φ φ')
    S h1 h5 χ (fun g φ hφ => by rw [hrel g φ hφ, hcχ g])
  refine ⟨ν, 1, hν1, ?_⟩
  intro ι hι g φ hφ
  obtain ⟨hT, hM, -, -⟩ := hA ι hι
  obtain ⟨c', hc'⟩ := GlobalTheory.T.eq_smul_of_commute_heisenberg_linearModel_schwartzBruhat (GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F Bs.v₁)) (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) hψc hψ1 ι₀
    ι hbij0 (fun x _ y _ c => by rw [map_add, map_smul])
    (fun C => GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wT C))
    (fun l => GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wM l))
    (fun C x hx => ⟨hU0 _ x hx, hT0 C x hx, hT C x hx⟩) (fun l x hx => ⟨hU0 _ x hx, hM0 l x hx, hM l x hx⟩)
  rw [hc' _ (h1 g φ hφ), hc' φ hφ, hrel g φ hφ, hcχ g, hν g]
  funext Y
  simp only [omB, Pi.smul_apply, smul_eq_mul, map_one, Units.val_one, Matrix.mul_one, Fintype.card_fin, gdet,
    MonoidHom.one_apply, apow_one]
  push_cast
  ring
