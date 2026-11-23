import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalTranslationEquivariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEmbeddingAtEveryPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlCharacterFactorsThroughDetOfTwoNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarFunctionalGoodPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryDeterminedBySplitImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulOfCommuteHeisenbergLinearModelSchwartzBruhStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix

noncomputable section

theorem GlobalTheory.WeilTransferW.exists_char_right_scalar : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ ι, G.M'.IsLinBar B.ψ B.τ₁ 1 1 ι → ∃ χ : (Fv F B.v₁)ˣ →* ℂˣ, ∀ h ∈ UAt σ G.W (evFin F B.v₁),
      (∃ c : ℂ, ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁), ∀ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁),
        Acts (evFin F B.v₁) (om' (1, h)) φ φ₁ → ι φ₁ = c • fun Y => ι φ (Y * (mat h).map (piW B.τ₁))) ∧
      ∀ c : ℂ, (∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁), ∀ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁),
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
  set L := GlobalTheory.SplitUnitLift.liftU hcm B.τ₁ G.W.J (-1) skew hdetW with hLdef
  have hLmem : ∀ x, L x ∈ UAt σ G.W (evFin F B.v₁) := fun x =>
    GlobalTheory.SplitUnitLift.liftU_mem_UAt hcm B.τ₁ G.W (-1) skew hdetW x
  have hLt : ∀ x, (mat (L x)).map (piW B.τ₁) = x.val := fun x =>
    GlobalTheory.SplitUnitLift.liftU_piW hcm B.τ₁ G.W.J (-1) skew hdetW x
  have hone : (1 : UA σ G.V'.J) ∈ UAt σ G.V' (evFin F B.v₁) := fun u _ => by simp [mat]
  obtain ⟨hEx, -, -⟩ := GlobalTheory.T.theta_action_exists hP F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' G.q (a' - G.q)
    (a + a' - (G.p + G.q)) (G.p + G.q) (GlobalTheory.ThK.Inhab.pairV' hT) B.v₁
  have hpres := (GlobalTheory.WeilM.IsUWeilPair.isUSplitting hT.weil').pres
  have hex : ∀ x : GL (Fin (a + a')) (Fv F B.v₁), ∃ c : ℂ,
      ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁), ∀ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁),
        Acts (evFin F B.v₁) (om' (1, L x)) φ φ₁ → ∀ Y, ι φ₁ Y = c * ι φ (Y * x.val) := by
    intro x
    obtain ⟨S, hS, hlin, hcov, -⟩ := GlobalTheory.WeilTransferW.local_weil_operator_second_space hP F E σ B a a' G X om om' hT B.v₁ (L x) (hLmem x)
    obtain ⟨c, hc⟩ := GlobalTheory.WeilTransferW.linBar_right_mul F E σ B a a' G X om om' hT B.v₁ B.τ₁ (L x) x (hLmem x)
      (hLt x) (GlobalTheory.SplitUnitLift.liftU_piW_comp hcm B.τ₁ G.W.J (-1) skew hdetW x) S (fun φ hφ => (hS φ hφ).1)
      hlin hcov ι hι
    refine ⟨c, fun φ hφ φ₁ hφ₁ hA Y => ?_⟩
    have e : φ₁ = S φ := (hEx 1 hone (L x) (hLmem x) φ hφ).unique ⟨hφ₁, hA⟩ (hS φ hφ)
    rw [e, hc φ hφ]
    rfl
  choose c hrel using hex
  have hvac := hT.geo.hM'.vac B.v₁
  set φv := G.M'.vac B.v₁
  have hφv : φv ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁) := hvac.1
  have hιv : ι φv ≠ 0 := fun h0 => hvac.2.1 (hι.bij.injOn hφv (Submodule.zero_mem _) (by rw [h0, map_zero]))
  obtain ⟨Y₀, hY₀⟩ := Function.ne_iff.mp hιv
  have hmul : ∀ x y, c (x * y) = c x * c y := by
    intro x y
    obtain ⟨φ₂, ⟨hφ₂, hA₂⟩, -⟩ := hEx 1 hone (L y) (hLmem y) φv hφv
    obtain ⟨φ₃, ⟨hφ₃, hA₃⟩, -⟩ := hEx 1 hone (L x) (hLmem x) φ₂ hφ₂
    have hA : Acts (evFin F B.v₁) (om' (1, L (x * y))) φv φ₃ := by
      have e : ((1, L (x * y)) : UA σ G.V'.J × UA σ G.W.J) = (1, L x) * (1, L y) := by
        rw [Prod.mk_mul_mk, map_mul, one_mul]
      rw [e, map_mul]
      intro r hr
      have h2 : Rest (evFin F B.v₁) φ₂ r := ⟨hr.1, by rw [← hA₂ r hr]; exact hpres _ _ hr.2⟩
      rw [Module.End.mul_apply, hA₂ r hr, hA₃ r h2]
    have e1 := hrel (x * y) φv hφv φ₃ hφ₃ hA (Y₀ * ((x * y)⁻¹).val)
    have e2 := hrel x φ₂ hφ₂ φ₃ hφ₃ hA₃ (Y₀ * ((x * y)⁻¹).val)
    have e3 := hrel y φv hφv φ₂ hφ₂ hA₂ (Y₀ * (y⁻¹).val)
    have k1 : Y₀ * ((x * y)⁻¹).val * (x * y).val = Y₀ := by
      rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
    have k2 : Y₀ * ((x * y)⁻¹).val * x.val = Y₀ * (y⁻¹).val := by
      rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_rev, inv_mul_cancel_right]
    have k3 : Y₀ * (y⁻¹).val * y.val = Y₀ := by
      rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
    rw [k1] at e1
    rw [k2] at e2
    rw [k3] at e3
    rw [e2, e3] at e1
    exact mul_right_cancel₀ hY₀ (e1.symm.trans (mul_assoc _ _ _).symm)
  have hc1 : c 1 = 1 := by
    have hA : Acts (evFin F B.v₁) (om' (1, L 1)) φv φv := by
      rw [map_one, show ((1 : UA σ G.V'.J), (1 : UA σ G.W.J)) = 1 from rfl, map_one]
      intro r _
      rfl
    have e := hrel 1 φv hφv φv hφv hA Y₀
    rw [Units.val_one, Matrix.mul_one] at e
    exact (mul_eq_right₀ hY₀).mp e.symm
  let cH : GL (Fin (a + a')) (Fv F B.v₁) →* ℂ := ⟨⟨c, hc1⟩, hmul⟩
  obtain ⟨χ, hχ⟩ := GlobalTheory.T.glCharacter_factors_through_det_of_two_ne_zero (GlobalTheory.LocalUnitSubgroupClosure.two_ne_zero_Fv B.v₁) cH.toHomUnits
  have hcχ : ∀ x, c x = (χ (Matrix.GeneralLinearGroup.det x) : ℂ) := fun x => by rw [← hχ x]; rfl
  refine ⟨χ, fun h hh => ?_⟩
  set g := GlobalTheory.LocalUnitSubgroupClosure.cmpGL B.τ₁ h with hg
  have hgv : (mat h).map (piW B.τ₁) = g.val := (GlobalTheory.LocalUnitSubgroupClosure.cmpGL_val B.τ₁ h).symm
  have hLg : L g = h := GlobalTheory.UnitaryInjAtPlace.eq_of_piW_eq F E σ B a a' G X om om' hT B.v₁ hT.chars.good B.τ₁
    _ (hLmem g) _ hh (by rw [hLt, hgv])
  have hr := hrel g
  rw [hLg] at hr
  rw [hgv]
  refine ⟨⟨c g, fun φ hφ φ₁ hφ₁ hA => funext fun Y => hr φ hφ φ₁ hφ₁ hA Y⟩, fun c' hc' => ?_⟩
  obtain ⟨φ₂, ⟨hφ₂, hA₂⟩, -⟩ := hEx 1 hone h hh φv hφv
  have e1 := hr φv hφv φ₂ hφ₂ hA₂ (Y₀ * (g⁻¹).val)
  have e2 := congrFun (hc' φv hφv φ₂ hφ₂ hA₂) (Y₀ * (g⁻¹).val)
  have k : Y₀ * (g⁻¹).val * g.val = Y₀ := by
    rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
  simp only [Pi.smul_apply, smul_eq_mul] at e2
  rw [k] at e1 e2
  rw [← hcχ g]
  exact mul_right_cancel₀ hY₀ (e2.symm.trans e1)
