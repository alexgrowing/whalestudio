import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSubAug

import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalTranslationEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryGroupSurjectsGeneralLinearRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryDeterminedBySplitImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfCartan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftVOneMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterSmoothUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenKerOfContinuous
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearFunctionalGoodPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LagrangianDecompositionWeilStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalWeilLinearModelActionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalWeilLinearModelUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalWeilLinearModelInvariantStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalWeilLinearModelMeasureStatement

open NumberField IsDedekindDomain

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SplitTransport

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

section Lin

open GlobalTheory.LinWAt
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny

theorem exists_isLinW (hP : GlobalTheory.FunPr.Hypotheses₂) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (hTr : IsTriple B G X om om') (v : Pl F) (t : E →ₐ[F] Fv F v) :
    ∃ ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ),
      G.M.IsLinW B.ψ t 1 1 ι := by
  obtain ⟨uT, uM, hT, hM, hspan, hsymp⟩ := (GlobalTheory.T.local_unipotent_embeddings_exist) F E σ B a a' G X om om' hTr v t
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := GlobalTheory.VacAny.continuous_psiV hTr.base.std.1 v
  have hψ1 : GlobalTheory.LatVac.psiAt B.ψ v ≠ 1 := GlobalTheory.PsiNontriv.psiAt_ne_one _ hTr.base.std v
  have hcoT : ∀ Y, coW G t (uT Y) = 0 := fun Y => coW_eq_zero G t _ (hT Y).2.1
  haveI : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F _).injective
  obtain ⟨ι, hbij, htr, hmu⟩ := GlobalTheory.T.lagrangian_decomposition_weil (GlobalTheory.LatVac.psiAt B.ψ v) hψc hψ1
    ((GlobalTheory.LatVac.locCo G.M.co v).comp uT) ((GlobalTheory.LatVac.locCo G.M.co v).comp uM)
    (fun Y Y' => by
      simp only [AddMonoidHom.comp_apply]
      rw [locCo_form, hsymp _ _ (hT Y).1 (hT Y').1, hcoT, hcoT]
      simp)
    (fun z z' => by
      simp only [AddMonoidHom.comp_apply]
      rw [locCo_form, hsymp _ _ (hM z).1 (hM z').1, (hM z).2.1, (hM z').2.1]
      simp)
    (fun Y z => by
      simp only [AddMonoidHom.comp_apply]
      rw [locCo_form, hsymp _ _ (hT Y).1 (hM z).1, (hT Y).2.2, (hM z).2.2, hcoT, (hM z).2.1]
      simp)
    (fun w => by
      obtain ⟨u, hu, rfl⟩ := locCo_surj G.M.co v w
      obtain ⟨Y, z, rfl⟩ := hspan u hu
      exact ⟨Y, z, by simp only [AddMonoidHom.comp_apply, map_add]⟩)
  have hφ₁ : ∀ (u : Matrix (Fin a) (Fin (a + a')) (AE F E)), At (evFin F v) u →
      ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ₁, Acts (evFin F v) (G.M.co.rho B.ψ u) φ φ₁ →
        φ₁ = GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v u) φ :=
    fun u hu φ hφ φ₁ hact => GlobalTheory.TensUniq.eq_of_tens_eq v φ φ₁ _ hφ fun r hr =>
      (hact r hr).symm.trans (GlobalTheory.VacBridge.rho_acts_locCo G.M.co B.ψ v u hu φ r hr)
  refine ⟨ι, hbij, ?_, ?_⟩
  · intro u hu hu0 φ hφ φ₁ _ hact Y
    have e1 := hφ₁ u hu φ hφ φ₁ hact
    obtain ⟨Y₀, z, rfl⟩ := hspan u hu
    have hz : z = 0 := by
      have h := hu0
      rw [Matrix.map_add _ (map_add _), (hT Y₀).2.1, zero_add] at h
      rw [← (hM z).2.2]
      exact coW_eq_zero G t _ h
    subst hz
    rw [map_zero, add_zero] at e1 ⊢
    rw [co_one, (hT Y₀).2.2, e1]
    exact congrFun (htr Y₀ φ hφ) Y
  · intro u hu hu1 φ hφ φ₁ _ hact x hx hx0
    have e1 := hφ₁ u hu φ hφ φ₁ hact
    obtain ⟨Y₀, z, rfl⟩ := hspan u hu
    have hY : Y₀ = 0 := by
      have h := hu1
      rw [Matrix.map_add _ (map_add _), (hM z).2.1, add_zero] at h
      rw [← (hT Y₀).2.2]
      exact h
    subst hY
    rw [map_zero, zero_add] at e1 ⊢
    rw [co_one, e1, GlobalTheory.VacIndic.psi_of_at B.ψ (at_symp _ _ _ x (uM z) hx), hsymp x (uM z) hx (hM z).1,
      coW_eq_zero G t x hx0, (hM z).2.1, (hM z).2.2]
    have h2 := congrFun (hmu z φ hφ) (x.map (piW t))
    simp only [AddMonoidHom.comp_apply] at h2
    rw [h2, ← GlobalTheory.LatVac.psiAt_apply]
    congr 2
    simp

end Lin

section Points

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem surjV (hTr : IsTriple B G X om om') (v : Pl F) (t : E →ₐ[F] Fv F v) (g' : GL (Fin a) (Fv F v)) :
    ∃ g ∈ UAt σ G.V (evFin F v), (mat g).map (piW t) = g'.1 := by
  have hcm := hTr.base.cm
  have herm : ∀ i j, σ (G.V.J j i) = algebraMap F E 1 * G.V.J i j := fun i j => by
    rw [map_one, one_mul]; exact hTr.geo.hV.herm i j
  have hJ : IsUnit (G.V.J.map t).det := by
    have w := Classical.arbitrary (InfinitePlace F)
    exact GlobalTheory.SplitUnitLift.isUnit_det_of_cartan G.V.J t (B.emb w).1 1 one_ne_zero (G.V.θ w)
      (by rw [one_smul]; exact hTr.geo.hV.cartan w)
  exact ⟨_, GlobalTheory.SplitUnitLift.liftU_mem_UAt hcm t G.V 1 herm hJ g', GlobalTheory.SplitUnitLift.liftU_piW hcm t G.V.J 1 herm hJ g'⟩

theorem isUnit_det_map_J_of_isTriple (hTr : IsTriple B G X om om') (v : Pl F) (t : E →ₐ[F] Fv F v) : IsUnit (G.W.J.map t).det := by
  have w := Classical.arbitrary (InfinitePlace F)
  exact GlobalTheory.SplitUnitLift.isUnit_det_of_cartan G.W.J t (B.emb w).1 Complex.I Complex.I_ne_zero (G.W.θ w)
    (hTr.geo.hW.cartan w)

theorem surjW (hTr : IsTriple B G X om om') (v : Pl F) (t : E →ₐ[F] Fv F v) (h' : GL (Fin (a + a')) (Fv F v)) :
    ∃ h ∈ UAt σ G.W (evFin F v), (mat h).map (piW t) = h'.1 := by
  have hcm := hTr.base.cm
  have herm : ∀ i j, σ (G.W.J j i) = algebraMap F E (-1) * G.W.J i j := fun i j => by
    rw [map_neg, map_one, neg_one_mul]; exact hTr.geo.hW.skew i j
  exact ⟨_, GlobalTheory.SplitUnitLift.liftU_mem_UAt hcm t G.W (-1) herm (isUnit_det_map_J_of_isTriple hTr v t) h',
    GlobalTheory.SplitUnitLift.liftU_piW hcm t G.W.J (-1) herm (isUnit_det_map_J_of_isTriple hTr v t) h'⟩

open GlobalTheory.EmbChart GlobalTheory.LeviAtPlace GlobalTheory.UnitaryInjAtPlace in

theorem injW (hTr : IsTriple B G X om om') (v : Pl F) (t : E →ₐ[F] Fv F v) :
    ∀ h₁ ∈ UAt σ G.W (evFin F v), ∀ h₂ ∈ UAt σ G.W (evFin F v),
      (mat h₁).map (piW t) = (mat h₂).map (piW t) → h₁ = h₂ := by
  intro h₁ hh₁ h₂ hh₂ heq
  have hcm := hTr.base.cm
  have hJ := isUnit_det_map_J_of_isTriple hTr v t
  have u₁ := unitary_at_components v t h₁
  have u₂ := unitary_at_components v t h₂
  rw [heq] at u₁
  set A := ((mat h₂).map (piW t))ᵀ * G.W.J.map t with hA
  have hAu : IsUnit A.det := by
    have hd := congrArg Matrix.det u₂
    rw [Matrix.det_mul] at hd
    exact isUnit_of_mul_isUnit_left (hd ▸ hJ)
  have hQ : (mat h₁).map (piW (t.comp σ)) = (mat h₂).map (piW (t.comp σ)) := by
    rw [← Matrix.nonsing_inv_mul_cancel_left _ ((mat h₁).map (piW (t.comp σ))) hAu,
      ← Matrix.nonsing_inv_mul_cancel_left _ ((mat h₂).map (piW (t.comp σ))) hAu, u₁, u₂]
  have hpi : ∀ (h : UA σ G.W.J) (τ : E →ₐ[F] Fv F v),
      (mat h).map (piW τ) = ((mat h).map (compFin F E v)).map (splitProj τ) := by
    intro h τ; rw [Matrix.map_map]; rfl
  have hY : (mat h₁).map (compFin F E v) = (mat h₂).map (compFin F E v) := by
    refine mat_split_ext hcm t ?_ ?_
    · rw [← hpi, ← hpi, heq]
    · rw [← hpi, ← hpi, hQ]
  have hz : At (evFin F v) (mat h₁ - mat h₂) := by
    intro u hu
    have e : mat h₁ - mat h₂ = (mat h₁ - 1) - (mat h₂ - 1) := by abel
    rw [e, smul_sub, hh₁ u hu, hh₂ u hu, sub_zero]
  have h0 : (mat h₁ - mat h₂).map (compFin F E v) = 0 := by
    rw [Matrix.map_sub _ (fun x y => map_sub _ x y), hY, sub_self]
  have hm := mat_eq_zero_of_at v _ hz h0
  exact Subtype.ext (Units.ext (sub_eq_zero.1 hm))

end Points

end GlobalTheory.SplitTransport

namespace GlobalTheory.SplitTransport

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

section Scalars

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n m : ℕ}

theorem omA_left (ν : kˣ →* ℂˣ) (g : GL (Fin n) k) (Φ : Matrix (Fin n) (Fin m) k → ℂ) :
    GlobalTheory.SplitFlip.omA ν 1 g 1 Φ = (((ν (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) •
      GlobalTheory.SplitWeil.om 1 (1 : GL (Fin m) k) g Φ := by
  funext X
  simp only [GlobalTheory.SplitFlip.omA, GlobalTheory.SplitWeil.om, GlobalTheory.SplitFlip.apow, Pi.smul_apply, smul_eq_mul, map_one,
    Units.val_one, one_mul, mul_one, inv_one, GlobalTheory.SplitFlip.invT_val, Matrix.transpose_one, Fintype.card_fin,
    MonoidHom.one_apply, GlobalTheory.SplitFlip.gdet]
  simp [GlobalTheory.SplitWeil.nabs]
  rw [Complex.ofReal_cpow (NNReal.coe_nonneg _)]
  push_cast
  ring

theorem om_right (β : kˣ →* ℂˣ) (g : GL (Fin m) k) (Φ : Matrix (Fin n) (Fin m) k → ℂ) :
    ∃ s : ℂ, GlobalTheory.SplitWeil.om 1 g (1 : GL (Fin n) k) Φ = s • GlobalTheory.SplitFlip.omA 1 β 1 (GlobalTheory.SplitFlip.invT g) Φ := by
  have h1 : (β (GlobalTheory.SplitFlip.gdet (GlobalTheory.SplitFlip.invT g)) : ℂ) ≠ 0 := Units.ne_zero _
  have h2 := GlobalTheory.SplitFlip.apow_ne_zero (GlobalTheory.SplitFlip.gdet (GlobalTheory.SplitFlip.invT g)) (-(Fintype.card (Fin n) : ℂ) / 2)
  refine ⟨((GlobalTheory.SplitWeil.nabs k (Matrix.GeneralLinearGroup.det g) ^ ((Fintype.card (Fin n) : ℝ) / 2) : ℝ) : ℂ) /
    ((β (GlobalTheory.SplitFlip.gdet (GlobalTheory.SplitFlip.invT g)) : ℂ) *
      GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet (GlobalTheory.SplitFlip.invT g)) (-(Fintype.card (Fin n) : ℂ) / 2)), ?_⟩
  funext X
  simp only [GlobalTheory.SplitFlip.omA, GlobalTheory.SplitWeil.om, Pi.smul_apply, smul_eq_mul, GlobalTheory.SplitFlip.invT_invT, inv_one,
    Units.val_one, map_one, MonoidHom.one_apply, one_mul, Matrix.one_mul, GlobalTheory.SplitFlip.apow_one, mul_one]
  simp [GlobalTheory.SplitWeil.nabs] at h1 h2 ⊢
  field_simp
  rw [mul_div_assoc, div_self (GlobalTheory.SplitFlip.apow_ne_zero _ _), mul_one]

theorem omA_right (β : kˣ →* ℂˣ) (h' : GL (Fin m) k) (Φ : Matrix (Fin n) (Fin m) k → ℂ) :
    ∃ s : ℂ, GlobalTheory.SplitFlip.omA 1 β 1 h' Φ = s • GlobalTheory.SplitWeil.om 1 (GlobalTheory.SplitFlip.invT h') (1 : GL (Fin n) k) Φ := by
  have h2 : ((GlobalTheory.SplitWeil.nabs k (Matrix.GeneralLinearGroup.det (GlobalTheory.SplitFlip.invT h')) ^
      ((Fintype.card (Fin n) : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
    have := GlobalTheory.SplitWeil.Model.nabs_pos (Matrix.GeneralLinearGroup.det (GlobalTheory.SplitFlip.invT h'))
    exact_mod_cast (Real.rpow_pos_of_pos this _).ne'
  refine ⟨(β (GlobalTheory.SplitFlip.gdet h') : ℂ) * GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet h') (-(Fintype.card (Fin n) : ℂ) / 2) /
    ((GlobalTheory.SplitWeil.nabs k (Matrix.GeneralLinearGroup.det (GlobalTheory.SplitFlip.invT h')) ^
      ((Fintype.card (Fin n) : ℝ) / 2) : ℝ) : ℂ), ?_⟩
  funext X
  simp only [GlobalTheory.SplitFlip.omA, GlobalTheory.SplitWeil.om, Pi.smul_apply, smul_eq_mul, inv_one,
    Units.val_one, map_one, MonoidHom.one_apply, one_mul, Matrix.one_mul, GlobalTheory.SplitFlip.apow_one, mul_one]
  simp only [ne_eq] at h2
  simp [GlobalTheory.SplitWeil.nabs] at h2 ⊢
  have h3 : ((↑((MeasureTheory.distribHaarChar k) (Matrix.GeneralLinearGroup.det (GlobalTheory.SplitFlip.invT h'))) ^ ((n : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h2
  field_simp

end Scalars

end GlobalTheory.SplitTransport

namespace GlobalTheory.SplitTransport

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

theorem transport : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs G Xc om om' →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, Nonempty (E →ₐ[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) →
      ∃ (χ : GL (Fin a) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) →* ℂˣ)
        (ι : ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) →ₗ[ℂ]
          (Matrix (Fin a) (Fin (a + a')) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ)),
        IsOpen {g | χ g = 1} ∧
        Set.BijOn ι (GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) : Set _)
          (GlobalTheory.SplitWeil.SB (Matrix (Fin a) (Fin (a + a')) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) : Set _) ∧
        ∀ N : Submodule ℂ ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
          N ≤ GlobalTheory.WeilM.SB _ → (GlobalTheory.Published.ThetaSub om v N ↔ GlobalTheory.ThetaGLSub.IsSub χ (N.map ι)) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hTr v ⟨t⟩
  obtain ⟨ι, hι⟩ := exists_isLinW hP hTr v t
  obtain ⟨ν₀, hV⟩ := GlobalTheory.T.local_weil_linear_model_invariant hP F E σ B a a' G X om om' hTr v t ι hι (GlobalTheory.T.local_weil_linear_model_action hP F E σ B a a' G X om om' hTr v t ι hι)
  obtain ⟨t', ht'⟩ := GlobalTheory.T.local_weil_linear_model_measure hP F E σ B a a' G X om om' hTr v t ι hι ν₀ hV
  have hloc := ((GlobalTheory.T.theta_action_exists hP) F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _
    (GlobalTheory.ThK.Check.isPair_of_isTriple hTr).1 v).1
  obtain ⟨β₀, hW⟩ := GlobalTheory.LocalUnitSubgroupClosure.core hTr v t ι (hloc 1 (GlobalTheory.LocalUnitSubgroupClosure.one_mem_UAt _ _)) (surjW hTr v t) (injW hTr v t)
    (GlobalTheory.T.local_weil_linear_model_unitary hP F E σ B a a' G X om om' hTr v t ι hι)

  have hνc : Continuous X.ν := by
    show Continuous fun x => X.α x / X.β x
    exact hTr.chars.heckeα.1.div' hTr.chars.heckeβ.1
  have hs0 : GlobalTheory.SmGL.IsSmoothChar (chrW X.ν t') :=
    GlobalTheory.RootEx.UniformLattices.isOpen_ker_of_continuous _ (GlobalTheory.ChrWSmooth.continuous_chrW hνc t')
  have hνs : GlobalTheory.SmGL.IsSmoothChar ν₀ := by
    rcases ht' with h | h
    · rw [h]; exact hs0
    · rw [h]; exact hs0.inv
  set χ : GL (Fin a) (Fv F v) →* ℂˣ := GlobalTheory.SmGL.detChar (Fin a) ν₀ with hχ
  have hχv : ∀ g, χ g = ν₀ (Matrix.GeneralLinearGroup.det g) := fun g => rfl
  have hbij := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLin.bij hι
  have hinj := hbij.injOn
  have hmaps : ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ι φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin a) (Fin (a + a')) (Fv F v)) :=
    fun φ hφ => hbij.mapsTo hφ
  refine ⟨χ, ι, ?_, hbij, ?_⟩
  · have := hνs.detChar (n := Fin a)
    exact this
  intro N hN

  have hAugSB : augAt om v ≤ SB (Fin a × Fin (a + a') → Fv F v) := by
    rw [augAt, Submodule.span_le]
    rintro _ ⟨g, hg, φ, hφ, φ₁, hφ₁, -, rfl⟩
    exact Submodule.sub_mem _ hφ₁ hφ
  have hVsc : ∀ g ∈ UAt σ G.V (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ →
      ∃ g' : GL (Fin a) (Fv F v), (mat g).map (piW t) = g'.1 ∧
        ι (φ₁ - φ) = (((χ g')⁻¹ : ℂˣ) : ℂ) • (GlobalTheory.SplitWeil.om 1 1 g' (ι φ) - (χ g' : ℂ) • ι φ) := by
    intro g hg φ hφ φ₁ hφ₁ hA
    obtain ⟨g', hg', hact⟩ := hV g hg
    refine ⟨g', hg', ?_⟩
    rw [map_sub, hact φ hφ φ₁ hφ₁ hA, omA_left, smul_sub, smul_smul, hχv]
    simp
  have hmapAug : (augAt om v).map ι = GlobalTheory.ThetaGLSub.aug (a + a') χ := by
    apply le_antisymm
    · rw [augAt, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨g, hg, φ, hφ, φ₁, hφ₁, hA, rfl⟩, rfl⟩
      obtain ⟨g', -, e⟩ := hVsc g hg φ hφ φ₁ hφ₁ hA
      rw [SetLike.mem_coe, e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g', ι φ, hmaps φ hφ, rfl⟩)
    · rw [GlobalTheory.ThetaGLSub.aug, Submodule.span_le]
      rintro _ ⟨h, Φ, hΦ, rfl⟩
      obtain ⟨φ, hφ, rfl⟩ := hbij.surjOn hΦ
      obtain ⟨g, hg, hgt⟩ := surjV hTr v t h
      obtain ⟨φ₁, ⟨hφ₁, hA⟩, -⟩ := hloc g hg 1 (GlobalTheory.LocalUnitSubgroupClosure.one_mem_UAt _ _) φ hφ
      obtain ⟨g', hg', e⟩ := hVsc g hg φ hφ φ₁ hφ₁ hA
      have : g' = h := Units.ext (hg'.symm.trans hgt)
      subst this
      refine ⟨(χ g' : ℂ) • (φ₁ - φ), Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, hg, φ, hφ, φ₁, hφ₁, hA, rfl⟩), ?_⟩
      rw [map_smul, e, smul_smul]
      simp
  have hiffAug : augAt om v ≤ N ↔ GlobalTheory.ThetaGLSub.aug (a + a') χ ≤ N.map ι := by
    rw [← hmapAug]
    refine ⟨Submodule.map_mono, fun h x hx => ?_⟩
    obtain ⟨y, hy, e⟩ := Submodule.mem_map.1 (h (Submodule.mem_map_of_mem hx))
    rwa [hinj (hN hy) (hAugSB hx) e] at hy

  have hiffW : (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ N, ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → φ₁ ∈ N) ↔
      ∀ g : GL (Fin (a + a')) (Fv F v), ∀ Φ ∈ N.map ι, GlobalTheory.SplitWeil.om 1 g (1 : GL (Fin a) (Fv F v)) Φ ∈ N.map ι := by
    constructor
    · intro H g Φ hΦ
      obtain ⟨φ, hφN, rfl⟩ := Submodule.mem_map.1 hΦ
      obtain ⟨h, hh, hht⟩ := surjW hTr v t (GlobalTheory.SplitFlip.invT g)
      obtain ⟨φ₁, ⟨hφ₁, hA⟩, -⟩ := hloc 1 (GlobalTheory.LocalUnitSubgroupClosure.one_mem_UAt _ _) h hh φ (hN hφN)
      obtain ⟨h', hh', hact⟩ := hW h hh
      have : h' = GlobalTheory.SplitFlip.invT g := Units.ext (hh'.symm.trans hht)
      subst this
      obtain ⟨s, hs⟩ := om_right β₀ g (ι φ)
      rw [hs, ← hact φ (hN hφN) φ₁ hφ₁ hA, ← map_smul]
      exact Submodule.mem_map_of_mem (N.smul_mem s (H h hh φ hφN φ₁ hφ₁ hA))
    · intro H h hh φ hφN φ₁ hφ₁ hA
      obtain ⟨h', -, hact⟩ := hW h hh
      obtain ⟨s, hs⟩ := omA_right β₀ h' (ι φ)
      have h1 : ι φ₁ ∈ N.map ι := by
        rw [hact φ (hN hφN) φ₁ hφ₁ hA, hs]
        exact Submodule.smul_mem _ _ (H _ _ (Submodule.mem_map_of_mem hφN))
      obtain ⟨y, hy, e⟩ := Submodule.mem_map.1 h1
      rwa [hinj (hN hy) hφ₁ e] at hy
  constructor
  · rintro ⟨h1, -, h3⟩
    refine ⟨hiffAug.1 h1, ?_, hiffW.1 h3⟩
    rintro _ ⟨φ, hφ, rfl⟩
    exact hmaps φ (hN hφ)
  · rintro ⟨h1, -, h3⟩
    exact ⟨hiffAug.2 h1, hN, hiffW.2 h3⟩

end GlobalTheory.SplitTransport
