import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

noncomputable section
namespace GlobalTheory.FlipMatch.ZMat

section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

omit [MeasurableSpace k] [BorelSpace k] in

theorem preimage_shellSet {A : Type} [Fintype A] [DecidableEq A] (ϖ : kˣ) (n : A → ℤ) {g₀ : GL A k}
    (hg : g₀ ∈ KO k A) : (fun g => g₀ * g) ⁻¹' shellSet ϖ n = shellSet ϖ n := by
  ext g
  simp only [Set.mem_preimage, mem_shellSet]
  constructor
  · rintro ⟨x, hx, y, hy, h⟩
    refine ⟨g₀⁻¹ * x, (KO k A).mul_mem ((KO k A).inv_mem hg) hx, y, hy, ?_⟩
    calc g = g₀⁻¹ * (g₀ * g) := (inv_mul_cancel_left g₀ g).symm
      _ = _ := by rw [h]; simp only [mul_assoc]
  · rintro ⟨x, hx, y, hy, h⟩
    exact ⟨g₀ * x, (KO k A).mul_mem hg hx, y, hy, by rw [h]; simp only [mul_assoc]⟩

theorem shellSum_mul_left {a : ℕ} (μ : Measure (GL (Fin a) k)) [μ.IsHaarMeasure] (ϖ : kˣ) (ν : kˣ →* ℂˣ) (z : ℂ)
    (φ : Matrix (Fin a) (Fin a) k → ℂ) {g₀ : GL (Fin a) k} (hg : g₀ ∈ KO k (Fin a)) :
    (ν (gdet g₀) : ℂ) * shellSum μ ϖ ν z (fun g => φ (g₀.val * g)) = shellSum μ ϖ ν z φ := by
  have hz : apow (gdet g₀) z = 1 := apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hg) z
  have hν : (ν (gdet g₀) : ℂ) ≠ 0 := Units.ne_zero _
  have key : ∀ n : Fin a → ℤ, shell μ ϖ ν z (fun g => φ (g₀.val * g)) n =
      shell μ ϖ ν z (fun g => ((ν (gdet g₀) : ℂ))⁻¹ * φ g) n := by
    intro n
    set F : GL (Fin a) k → ℂ := fun g => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z with hF
    have hL : ∀ g : GL (Fin a) k, φ (g₀.val * g.val) * (ν (gdet g) : ℂ) * apow (gdet g) z =
        ((ν (gdet g₀) : ℂ))⁻¹ * F (g₀ * g) := by
      intro g
      simp only [hF, gdet_mul, apow_mul, hz, map_mul, Units.val_mul, one_mul]
      field_simp
    have hR : ∀ g : GL (Fin a) k, ((ν (gdet g₀) : ℂ))⁻¹ * φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z =
        ((ν (gdet g₀) : ℂ))⁻¹ * F g := by
      intro g
      simp only [hF]
      ring
    have hI : ∫ g in shellSet ϖ n, F (g₀ * g) ∂μ = ∫ g in shellSet ϖ n, F g ∂μ := by
      have h1 := setIntegral_map_equiv (μ := μ) (MeasurableEquiv.mulLeft g₀) F (shellSet ϖ n)
      rw [MeasurableEquiv.coe_mulLeft, map_mul_left_eq_self, preimage_shellSet ϖ n hg] at h1
      exact h1.symm
    unfold shell
    simp only [hL, hR]
    rw [integral_const_mul, integral_const_mul, hI]
  have hsum : shellSum μ ϖ ν z (fun g => φ (g₀.val * g)) =
      shellSum μ ϖ ν z (fun g => ((ν (gdet g₀) : ℂ))⁻¹ * φ g) := by
    simp only [shellSum, key]
  rw [hsum, shellSum_smul, ← mul_assoc, mul_inv_cancel₀ hν, one_mul]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] in

def renum {A A₁ : Type} [Fintype A] [DecidableEq A] [Fintype A₁] [DecidableEq A₁] (e : A ≃ A₁) :
    GL A k ≃ₜ* GL A₁ k where
  toMulEquiv := Units.mapEquiv (reindexAlgEquiv k k e).toMulEquiv
  continuous_toFun := Units.continuous_iff.2
    ⟨Units.continuous_val.matrix_reindex e e, Units.continuous_coe_inv.matrix_reindex e e⟩
  continuous_invFun := Units.continuous_iff.2
    ⟨Units.continuous_val.matrix_reindex e.symm e.symm, Units.continuous_coe_inv.matrix_reindex e.symm e.symm⟩

theorem exists_integral_renum {A A₁ : Type} [Fintype A] [DecidableEq A] [Fintype A₁] [DecidableEq A₁] (e : A ≃ A₁)
    (μ : Measure (GL A k)) [μ.IsHaarMeasure] (μ₁ : Measure (GL A₁ k)) [μ₁.IsHaarMeasure] :
    ∃ r : ℂ, r ≠ 0 ∧ ∀ f : GL A₁ k → ℂ, ∫ g, f (renum e g) ∂μ = r * ∫ g, f g ∂μ₁ := by
  have hme : MeasurableEmbedding (renum e : GL A k → GL A₁ k) :=
    (renum e).toHomeomorph.toMeasurableEquiv.measurableEmbedding
  haveI : (μ.map (renum e)).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ (renum e)
  obtain ⟨c, hpos, hmap⟩ : ∃ c : NNReal, 0 < c ∧ μ.map (renum e) = c • μ₁ :=
    ⟨_, Measure.haarScalarFactor_pos_of_isHaarMeasure _ _, Measure.isMulLeftInvariant_eq_smul _ _⟩
  refine ⟨((c : ℝ) : ℂ), ?_, fun f => ?_⟩
  · exact_mod_cast hpos.ne'
  · rw [← hme.integral_map f, hmap, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

private theorem reindex_mul {K A A₁ C C₁ : Type} [Field K] [Fintype A] [Fintype A₁]
    (e : A ≃ A₁) (eC : C ≃ C₁) (M : Matrix A A K) (N : Matrix A C K) :
    reindex e eC (M * N) = reindex e e M * reindex e eC N := by
  simp only [reindex_apply]
  exact submatrix_mul M N e.symm e.symm eC.symm e.symm.bijective

private theorem renum_mul_reindex {A A₁ C C₁ : Type} [Fintype A] [DecidableEq A] [Fintype A₁] [DecidableEq A₁]
    (e : A ≃ A₁) (eC : C ≃ C₁) (g : GL A k) (N : Matrix A C k) :
    (renum e g).val * reindex e eC N = reindex e eC (g.val * N) := by
  have h1 : (renum e g).val = reindex e e g.val := rfl
  rw [h1, reindex_mul]

private theorem gdet_renum {A A₁ : Type} [Fintype A] [DecidableEq A] [Fintype A₁] [DecidableEq A₁]
    (e : A ≃ A₁) (g : GL A k) : gdet (renum e g) = gdet g := by
  ext
  have h1 : (renum e g).val = reindex e e g.val := rfl
  simp only [gdet, Matrix.GeneralLinearGroup.val_det_apply, h1, det_reindex_self]

theorem exists_smallF_rows {A A₁ C C₁ : Type} [Fintype A] [DecidableEq A] [Fintype A₁] [DecidableEq A₁]
    [Fintype C] [DecidableEq C] [Fintype C₁] [DecidableEq C₁] (e : A ≃ A₁) (eC : C ≃ C₁)
    (μ : Measure (GL A k)) [μ.IsHaarMeasure] (μ₁ : Measure (GL A₁ k)) [μ₁.IsHaarMeasure] (ν : kˣ →* ℂˣ)
    (g₀ : GL A k) (c : Matrix C C k) :
    ∃ r : ℂ, r ≠ 0 ∧ ∀ (lam : ℂ) (Ψ : Matrix A₁ C₁ k → ℂ) (Y : Matrix A C k),
      smallF μ ν (fun Y => lam * Ψ (reindex e eC (g₀.val * Y * c))) Y =
        lam * r * smallF μ₁ ν Ψ (reindex e eC (Y * c)) := by
  obtain ⟨r₀, hr₀, hint⟩ := exists_integral_renum e μ μ₁
  have hCC : (Fintype.card C₁ : ℂ) = Fintype.card C := by rw [Fintype.card_congr eC]
  have hp := apow_ne_zero (gdet g₀) ((Fintype.card C : ℂ) / 2)
  have hν : (ν (gdet g₀) : ℂ) ≠ 0 := Units.ne_zero _
  refine ⟨((ν (gdet g₀) : ℂ))⁻¹ * (apow (gdet g₀) ((Fintype.card C : ℂ) / 2))⁻¹ * r₀,
    by simp [hp, hν, hr₀], fun lam Ψ Y => ?_⟩
  set F : GL A₁ k → ℂ := fun g => Ψ (g.val * reindex e eC (Y * c)) * (ν (gdet g) : ℂ) *
    apow (gdet g) ((Fintype.card C₁ : ℂ) / 2) with hF
  have hpt : ∀ g : GL A k, lam * Ψ (reindex e eC (g₀.val * (g.val * Y) * c)) * (ν (gdet g) : ℂ) *
      apow (gdet g) ((Fintype.card C : ℂ) / 2) = (lam * ((ν (gdet g₀) : ℂ))⁻¹ *
        (apow (gdet g₀) ((Fintype.card C : ℂ) / 2))⁻¹) * F (renum e (g₀ * g)) := by
    intro g
    simp only [hF, renum_mul_reindex, gdet_renum, gdet_mul, map_mul, Units.val_mul, apow_mul, hCC,
      Matrix.mul_assoc]
    field_simp
  have h2 := hint F
  unfold smallF
  simp only [hpt]
  rw [integral_const_mul, integral_mul_left_eq_self (fun g => F (renum e g)) g₀, h2]
  ring

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] in

theorem exists_reindex_unit {C C₁ : Type} [Fintype C] [DecidableEq C] [Fintype C₁] [DecidableEq C₁] (τ eC : C ≃ C₁) :
    ∃ s : kˣ, ∀ u : GL C k, ∃ u₁ : GL C₁ k, u₁.val = reindex τ eC u.val ∧
      (invT u₁).val = reindex τ eC (invT u).val ∧ gdet u₁ = s * gdet u := by
  refine ⟨Units.map (Int.castRingHom k).toMonoidHom (Equiv.Perm.sign (τ.symm.trans eC)), fun u => ?_⟩
  refine ⟨⟨reindex τ eC u.val, reindex eC τ (u⁻¹).val, ?_, ?_⟩, rfl, ?_, ?_⟩
  · rw [reindex_apply, reindex_apply, ← submatrix_mul _ _ _ _ _ eC.symm.bijective, Units.mul_inv,
      submatrix_one_equiv]
  · rw [reindex_apply, reindex_apply, ← submatrix_mul _ _ _ _ _ τ.symm.bijective, Units.inv_mul,
      submatrix_one_equiv]
  · rw [invT_val, invT_val]
    rfl
  · have hsub : reindex τ eC u.val =
        (u.val.submatrix eC.symm eC.symm).submatrix (τ.symm.trans eC) id := by
      ext i j
      simp [reindex_apply]
    ext
    simp only [gdet, Matrix.GeneralLinearGroup.val_det_apply, Units.val_mul]
    change det (reindex τ eC u.val) = _
    rw [hsub, det_permute, det_submatrix_equiv_self]
    simp

private theorem X0_mul_reindex {K A' A₁ C C₁ : Type} [Field K] [Fintype A'] [DecidableEq A'] [Fintype A₁]
    [DecidableEq A₁] [Fintype C] [DecidableEq C] [Fintype C₁] [DecidableEq C₁] {a : ℕ}
    (eB : A' ≃ A₁) (eC : C ≃ C₁) (σ : Fin a ⊕ A' ≃ C) (σ₁ : Fin a ⊕ A₁ ≃ C₁) (N : Matrix C C K) :
    X0 K σ₁ * reindex ((σ₁.symm.trans ((Equiv.sumCongr (Equiv.refl (Fin a)) eB).symm.trans
      (σ.trans eC))).trans eC.symm).symm eC N = reindex (Equiv.refl (Fin a)) eC (X0 K σ * N) := by
  ext i j
  simp [reindex_apply, frameMatrixFirstColumnBlock_mul_apply]

private theorem Y0_mul_reindex {K A' A₁ C C₁ : Type} [Field K] [Fintype A'] [DecidableEq A'] [Fintype A₁]
    [DecidableEq A₁] [Fintype C] [DecidableEq C] [Fintype C₁] [DecidableEq C₁] {a : ℕ}
    (eB : A' ≃ A₁) (eC : C ≃ C₁) (σ : Fin a ⊕ A' ≃ C) (σ₁ : Fin a ⊕ A₁ ≃ C₁) (N : Matrix C C K) :
    Y0 K σ₁ * reindex ((σ₁.symm.trans ((Equiv.sumCongr (Equiv.refl (Fin a)) eB).symm.trans
      (σ.trans eC))).trans eC.symm).symm eC N = reindex eB eC (Y0 K σ * N) := by
  ext i j
  simp [reindex_apply, frameMatrixSecondColumnBlock_mul_apply]

end

theorem bigZeta_eq_smallZeta_change : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a a₁ : ℕ) (ha : a = a₁) (A' : Type) [Fintype A'] [DecidableEq A'] (A₁ : Type) [Fintype A₁] [DecidableEq A₁] (C : Type) [Fintype C] [DecidableEq C] (C₁ : Type) [Fintype C₁] [DecidableEq C₁] (eB : A' ≃ A₁) (eC : C ≃ C₁)
    (σ : Fin a ⊕ A' ≃ C) (σ₁ : Fin a₁ ⊕ A₁ ≃ C₁) (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (μ₁ : Measure (GL A₁ k)) [μ₁.IsHaarMeasure]
    (ϖ : kˣ) (ν β : kˣ →* ℂˣ) (gA : GL (Fin a) k) (gB : GL A' k) (c : GL C k), gA ∈ KO k (Fin a) →
    ∃ lam : ℂ, lam ≠ 0 ∧ ∀ (Ξ : Matrix (Fin a₁) C₁ k → ℂ) (Ψ : Matrix A₁ C₁ k → ℂ),
      bigP (haarVol (KO k (Fin a₁))) ϖ σ₁ ν β Ξ = smallP μ₁ σ₁ ν (ν * β) Ψ →
      bigP (haarVol (KO k (Fin a))) ϖ σ ν β (fun X => Ξ (reindex (finCongr ha) eC (gA.val * X * (invT c).val))) =
        smallP μ σ ν (ν * β) fun Y => lam * Ψ (reindex eB eC (gB.val * Y * c.val)) := by
  intro k _ _ _ _ _ _ a a₁ ha A' _ _ A₁ _ _ C _ _ C₁ _ _ eB eC σ σ₁ μ _ μ₁ _ ϖ ν β gA gB c hgA
  subst a₁
  obtain ⟨s, hs⟩ := exists_reindex_unit (k := k)
    ((σ₁.symm.trans ((Equiv.sumCongr (Equiv.refl (Fin a)) eB).symm.trans (σ.trans eC))).trans eC.symm).symm eC
  obtain ⟨r, hr0, hr⟩ := exists_smallF_rows eB eC μ μ₁ ν gB c.val
  have hCC : (Fintype.card C₁ : ℂ) = Fintype.card C := by rw [Fintype.card_congr eC]
  have hAA : (Fintype.card A₁ : ℂ) = Fintype.card A' := by rw [Fintype.card_congr eB]
  have q1 := apow_ne_zero s ((Fintype.card A' : ℂ) / 2)
  have q2 := apow_ne_zero (gdet c) ((Fintype.card A' : ℂ) / 2)
  have q3 := apow_ne_zero s (-(a : ℂ) / 2)
  have q4 := apow_ne_zero (gdet c) (-(a : ℂ) / 2)
  refine ⟨((ν (gdet gA) : ℂ))⁻¹ * (ν s : ℂ) * (ν (gdet c) : ℂ) * apow s ((Fintype.card A' : ℂ) / 2) *
      apow (gdet c) ((Fintype.card A' : ℂ) / 2) / (apow s (-(a : ℂ) / 2) * apow (gdet c) (-(a : ℂ) / 2)) / r,
    by simp [q1, q2, q3, q4, hr0], fun Ξ Ψ H => ?_⟩
  funext h
  obtain ⟨u₁, hu₁, hiu₁, hdu₁⟩ := hs (h * c)
  have hfc : finCongr (rfl : a = a) = Equiv.refl (Fin a) := by
    ext i
    simp
  have hpt : ∀ M : Matrix (Fin a) (Fin a) k,
      reindex (finCongr (rfl : a = a)) eC (gA.val * (M * (X0 k σ * (invT h).val)) * (invT c).val) =
        gA.val * M * (X0 k σ₁ * (invT u₁).val) := by
    intro M
    rw [hiu₁, show invT (h * c) = invT h * invT c from map_mul invT h c, Units.val_mul, X0_mul_reindex, hfc,
      show gA.val * (M * (X0 k σ * (invT h).val)) * (invT c).val =
        (gA.val * M) * (X0 k σ * ((invT h).val * (invT c).val)) by simp only [Matrix.mul_assoc],
      reindex_mul, reindex_refl_refl]
  have hY : reindex eB eC (Y0 k σ * h.val * c.val) = Y0 k σ₁ * u₁.val := by
    rw [hu₁, Y0_mul_reindex, Units.val_mul, Matrix.mul_assoc]
  have hsh := shellSum_mul_left (haarVol (KO k (Fin a))) ϖ ν ((Fintype.card C : ℂ) / 2)
    (fun N => Ξ (N * (X0 k σ₁ * (invT u₁).val))) hgA
  have hνA : (ν (gdet gA) : ℂ) ≠ 0 := Units.ne_zero _
  have H1 := congrFun H u₁
  rw [bigZetaIntegral_eq, smallP] at H1
  unfold bigF at H1
  rw [hCC, hAA] at H1
  rw [bigZetaIntegral_eq, smallP]
  unfold bigF
  simp only [hpt]
  rw [hr _ Ψ (Y0 k σ * h.val), hY]
  have hS0 : shellSum (haarVol (KO k (Fin a))) ϖ ν ((Fintype.card C : ℂ) / 2)
      (fun M => Ξ (gA.val * M * (X0 k σ₁ * (invT u₁).val))) =
      ((ν (gdet gA) : ℂ))⁻¹ * shellSum (haarVol (KO k (Fin a))) ϖ ν ((Fintype.card C : ℂ) / 2)
        (fun N => Ξ (N * (X0 k σ₁ * (invT u₁).val))) := by
    rw [← hsh, ← mul_assoc, inv_mul_cancel₀ hνA, one_mul]
  rw [hS0]
  set S := shellSum (haarVol (KO k (Fin a))) ϖ ν ((Fintype.card C : ℂ) / 2)
    (fun N => Ξ (N * (X0 k σ₁ * (invT u₁).val))) with hSdef
  set I := smallF μ₁ ν Ψ (Y0 k σ₁ * u₁.val) with hIdef
  have hden : (β (gdet u₁) : ℂ) * apow (gdet u₁) (-(a : ℂ) / 2) ≠ 0 :=
    mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)
  have hS : S = ((ν * β) (gdet u₁) : ℂ) * apow (gdet u₁) ((Fintype.card A' : ℂ) / 2) * I /
      ((β (gdet u₁) : ℂ) * apow (gdet u₁) (-(a : ℂ) / 2)) := by
    rw [eq_div_iff hden, ← H1]
    ring
  rw [hS, hdu₁, gdet_mul]
  have q5 := apow_ne_zero (gdet h) ((Fintype.card A' : ℂ) / 2)
  have q6 := apow_ne_zero (gdet h) (-(a : ℂ) / 2)
  have q7 : (ν s : ℂ) ≠ 0 := Units.ne_zero _
  have q8 : (ν (gdet h) : ℂ) ≠ 0 := Units.ne_zero _
  have q9 : (ν (gdet c) : ℂ) ≠ 0 := Units.ne_zero _
  have q10 : (β s : ℂ) ≠ 0 := Units.ne_zero _
  have q11 : (β (gdet h) : ℂ) ≠ 0 := Units.ne_zero _
  have q12 : (β (gdet c) : ℂ) ≠ 0 := Units.ne_zero _
  simp only [map_mul, MonoidHom.mul_apply, Units.val_mul, apow_mul]
  clear * - q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 hνA hr0
  generalize apow s ((Fintype.card A' : ℂ) / 2) = x1 at q1 ⊢
  generalize apow (gdet c) ((Fintype.card A' : ℂ) / 2) = x2 at q2 ⊢
  generalize apow s (-(a : ℂ) / 2) = x3 at q3 ⊢
  generalize apow (gdet c) (-(a : ℂ) / 2) = x4 at q4 ⊢
  generalize apow (gdet h) ((Fintype.card A' : ℂ) / 2) = x5 at q5 ⊢
  generalize apow (gdet h) (-(a : ℂ) / 2) = x6 at q6 ⊢
  generalize (ν s : ℂ) = x7 at q7 ⊢
  generalize (ν (gdet h) : ℂ) = x8 at q8 ⊢
  generalize (ν (gdet c) : ℂ) = x9 at q9 ⊢
  generalize (β s : ℂ) = x10 at q10 ⊢
  generalize (β (gdet h) : ℂ) = x11 at q11 ⊢
  generalize (β (gdet c) : ℂ) = x12 at q12 ⊢
  generalize (ν (gdet gA) : ℂ) = x13 at hνA ⊢
  field_simp

end GlobalTheory.FlipMatch.ZMat
