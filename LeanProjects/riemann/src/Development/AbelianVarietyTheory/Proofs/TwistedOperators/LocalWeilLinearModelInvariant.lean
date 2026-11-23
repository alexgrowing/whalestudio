import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlCharacterFactorsThroughDetOfTwoNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfCartan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticSelfZeroSplitSupported
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftVOneMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalSphericalValue
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open GlobalTheory.SchurCharV in

theorem GlobalTheory.SchurCharV.exists_char_of_schur_any : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι → (∀ g ∈ UAt σ G.V (evFin F v), ∃ c : ℂ, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (g, 1)) φ φ₁ → ∀ Y, ι φ₁ Y = c * ι φ (((mat g).map (piW t))⁻¹ * Y)) →
    ∃ ν₀ : (Fv F v)ˣ →* ℂˣ, (∀ g ∈ UAt σ G.V (evFin F v), ∃ g' : GL (Fin a) (Fv F v), (mat g).map (piW t) = g'.1 ∧
      ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ 1 g' 1 (ι φ)) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v t ι hι H
  have hcm : IsCMExt F E σ := hT.base.cm
  have herm : ∀ i j, σ (G.V.J j i) = algebraMap F E 1 * G.V.J i j := fun i j => by
    rw [map_one, one_mul]; exact hT.geo.hV.herm i j
  have hJ : IsUnit (G.V.J.map t).det := by
    have w := Classical.arbitrary (InfinitePlace F)
    exact GlobalTheory.SplitUnitLift.isUnit_det_of_cartan G.V.J t (B.emb w).1 1 one_ne_zero (G.V.θ w)
      (by rw [one_smul]; exact hT.geo.hV.cartan w)
  set L := GlobalTheory.SplitUnitLift.liftU hcm t G.V.J 1 herm hJ with hLdef
  have hLmem : ∀ x, L x ∈ UAt σ G.V (evFin F v) := fun x => GlobalTheory.SplitUnitLift.liftU_mem_UAt hcm t G.V 1 herm hJ x
  have hLt : ∀ x, (mat (L x)).map (piW t) = x.val := fun x => GlobalTheory.SplitUnitLift.liftU_piW hcm t G.V.J 1 herm hJ x
  have hEx := (GlobalTheory.T.theta_action_exists hP F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _
    (GlobalTheory.ThK.Check.isPair_of_isTriple hT).1 v).1
  have h1mem : (1 : UA σ G.W.J) ∈ UAt σ G.W (evFin F v) := by
    intro u _
    show u • (mat (1 : UA σ G.W.J) - 1) = 0
    rw [show mat (1 : UA σ G.W.J) = 1 from rfl, sub_self, smul_zero]
  have hpres : ∀ p : UA σ G.V.J × UA σ G.W.J, ∀ Φ ∈ schA F (Fin a × Fin (a + a')),
      om p Φ ∈ schA F (Fin a × Fin (a + a')) :=
    fun p Φ hΦ => (GlobalTheory.WeilM.IsUWeilPair.isUSplitting hT.weil).pres p Φ hΦ
  have hvac := hT.geo.hM.vac v
  set φv := G.M.vac v
  have hφv : φv ∈ SB (Fin a × Fin (a + a') → Fv F v) := hvac.1
  have hbij := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLin.bij hι
  have hιv : ι φv ≠ 0 := fun h0 => hvac.2.1 (hbij.injOn hφv (Submodule.zero_mem _) (by rw [h0, map_zero]))
  obtain ⟨Y₀, hY₀⟩ := Function.ne_iff.mp hιv
  choose c hc using fun x : GL (Fin a) (Fv F v) => H (L x) (hLmem x)
  have hrel : ∀ x, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (L x, 1)) φ φ₁ → ∀ Y, ι φ₁ Y = c x * ι φ ((x⁻¹ : GL (Fin a) (Fv F v)).val * Y) := by
    intro x φ hφ φ₁ hφ₁ hA Y
    rw [hc x φ hφ φ₁ hφ₁ hA Y, hLt x, Matrix.coe_units_inv]
  have hmul : ∀ x y, c (x * y) = c x * c y := by
    intro x y
    obtain ⟨φ₂, ⟨hφ₂, hA₂⟩, -⟩ := hEx (L y) (hLmem y) 1 h1mem φv hφv
    obtain ⟨φ₃, ⟨hφ₃, hA₃⟩, -⟩ := hEx (L x) (hLmem x) 1 h1mem φ₂ hφ₂
    have hA : Acts (evFin F v) (om (L (x * y), 1)) φv φ₃ := by
      have e : ((L (x * y), 1) : UA σ G.V.J × UA σ G.W.J) = (L x, 1) * (L y, 1) := by
        rw [Prod.mk_mul_mk, map_mul, one_mul]
      rw [e, map_mul]
      exact GlobalTheory.InertAvgDual.acts_comp v _ _ (hpres _) hA₂ hA₃
    have e1 := hrel (x * y) φv hφv φ₃ hφ₃ hA ((x * y).val * Y₀)
    have e2 := hrel x φ₂ hφ₂ φ₃ hφ₃ hA₃ ((x * y).val * Y₀)
    have e3 := hrel y φv hφv φ₂ hφ₂ hA₂ (y.val * Y₀)
    have k1 : ((x * y)⁻¹ : GL (Fin a) (Fv F v)).val * ((x * y).val * Y₀) = Y₀ := by
      rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    have k2 : (x⁻¹ : GL (Fin a) (Fv F v)).val * ((x * y).val * Y₀) = y.val * Y₀ := by
      rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel_left]
    have k3 : (y⁻¹ : GL (Fin a) (Fv F v)).val * (y.val * Y₀) = Y₀ := by
      rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    rw [k1] at e1
    rw [k2] at e2
    rw [k3] at e3
    rw [e2, e3] at e1
    exact mul_right_cancel₀ hY₀ (e1.symm.trans (mul_assoc _ _ _).symm)
  have hone : c 1 = 1 := by
    have hA : Acts (evFin F v) (om (L 1, 1)) φv φv := by
      rw [map_one, show ((1 : UA σ G.V.J), (1 : UA σ G.W.J)) = 1 from rfl, map_one]
      exact GlobalTheory.InertAvgDual.acts_one v φv
    have e := hrel 1 φv hφv φv hφv hA Y₀
    rw [inv_one, Units.val_one, Matrix.one_mul] at e
    exact (mul_eq_right₀ hY₀).mp e.symm
  let cH : GL (Fin a) (Fv F v) →* ℂ := ⟨⟨c, hone⟩, hmul⟩
  obtain ⟨χ, hχ⟩ := GlobalTheory.ghom_factors_through_det (two_ne_zero_Fv v) cH.toHomUnits
  have hcχ : ∀ x, c x = (χ (Matrix.GeneralLinearGroup.det x) : ℂ) := fun x => by rw [← hχ x]; rfl
  let A : (Fv F v)ˣ →* ℂˣ :=
    { toFun := fun x => Units.mk0 (GlobalTheory.SplitFlip.apow x (((a + a' : ℕ) : ℂ) / 2)) (GlobalTheory.SplitFlip.apow_ne_zero _ _)
      map_one' := Units.ext (GlobalTheory.SplitFlip.apow_one _)
      map_mul' := fun x y => Units.ext (GlobalTheory.SplitFlip.apow_mul x y _) }
  refine ⟨(χ * A)⁻¹, ?_⟩
  intro g hg
  set g' := Matrix.GeneralLinearGroup.map (piW t) g.1 with hg'
  refine ⟨g', rfl, ?_⟩
  intro φ hφ φ₁ hφ₁ hA
  have hgL : g = L g' := eq_liftU_of_UAt hcm t G.V herm hJ g hg
  rw [hgL] at hA
  funext Y
  rw [hrel g' φ hφ φ₁ hφ₁ hA Y, hcχ g']
  have hpow : ∀ d : (Fv F v)ˣ, GlobalTheory.SplitFlip.apow d (((a + a' : ℕ) : ℂ) / 2) *
      GlobalTheory.SplitFlip.apow d (-((a + a' : ℕ) : ℂ) / 2) = 1 := fun d => by
    rw [← GlobalTheory.SplitFlip.apow_add, show ((a + a' : ℕ) : ℂ) / 2 + -((a + a' : ℕ) : ℂ) / 2 = 0 by ring,
      GlobalTheory.SplitFlip.apow_zero]
  simp only [GlobalTheory.SplitFlip.omA, MonoidHom.inv_apply, inv_inv, MonoidHom.mul_apply, Units.val_mul, map_one,
    MonoidHom.one_apply, Units.val_one, GlobalTheory.SplitFlip.apow_one, Matrix.mul_one, mul_one, Fintype.card_fin]
  have hAv : ∀ d, ((A d : ℂˣ) : ℂ) = GlobalTheory.SplitFlip.apow d (((a + a' : ℕ) : ℂ) / 2) := fun d => rfl
  rw [hAv]
  linear_combination (-(χ (GlobalTheory.SplitFlip.gdet g') : ℂ) * ι φ ((g'⁻¹ : GL (Fin a) (Fv F v)).val * Y)) * hpow (GlobalTheory.SplitFlip.gdet g')
