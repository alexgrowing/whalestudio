import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZetaIdentityPersistsRowColumnChanges
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOperatorIsotropicTranslationCharSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterAndTranslationCoordsSurjectivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulOfCommuteHeisenbergLinearModelSchwartzBruhStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelUnitaryConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedFiniteMapsRestriction

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ReBase

section Local

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL Formalism.DoubleCosetMeasures.instMeasMat

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {A' D : Type} [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D] {a : ℕ}

theorem bigZetaIntegral_equivariant (μ : Measure (GL (Fin a) k)) [μ.IsHaarMeasure] (ϖ : kˣ) (σ : Fin a ⊕ A' ≃ D) (ν β : kˣ →* ℂˣ)
    {g : GL (Fin a) k} (hg : g ∈ KO k (Fin a)) {c : GL D k} (hc : c ∈ KO k D) (Φ : Matrix (Fin a) D k → ℂ) (h : GL D k) :
    (ν (gdet g) : ℂ) * bigP μ ϖ σ ν β (fun X => Φ (g.val * X * c.valᵀ)) h =
      β (gdet c) * bigP μ ϖ σ ν β Φ (h * c⁻¹) := by
  have e1 : (invT (h * c⁻¹)).val = (invT h).val * c.valᵀ := by rw [map_mul, map_inv, Units.val_mul, invT_inv_val]
  have e2 : gdet h = gdet (h * c⁻¹) * gdet c := by rw [← gdet_mul, inv_mul_cancel_right]
  rw [bigZetaIntegral_eq, bigZetaIntegral_eq, e1, e2, apow_mul, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hc), map_mul, Units.val_mul]
  unfold bigF
  rw [← GlobalTheory.FlipMatch.ZMat.shellSum_mul_left μ ϖ ν _ (fun x => Φ (x * (X0 k σ * ((invT h).val * c.valᵀ)))) hg]
  simp only [Matrix.mul_assoc]
  ring

theorem smallP_change {A : Type} (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ : A ⊕ A' ≃ D) (ν α : kˣ →* ℂˣ)
    {g : GL A' k} (hg : g ∈ KO k A') {c : GL D k} (hc : c ∈ KO k D) (Ψ : Matrix A' D k → ℂ) (h : GL D k) :
    smallP μ σ ν α (fun Y => Ψ ((invT g).val * Y * (c⁻¹).val)) h =
      ν (gdet g) * α (gdet c) * smallP μ σ ν α Ψ (h * c⁻¹) := by
  have e2 : gdet h = gdet (h * c⁻¹) * gdet c := by rw [← gdet_mul, inv_mul_cancel_right]
  have e3 : ∀ Y : Matrix A' D k, smallF μ ν (fun Y => Ψ ((invT g).val * Y * (c⁻¹).val)) Y =
      ν (gdet g) * smallF μ ν Ψ (Y * (c⁻¹).val) := fun Y => by
    unfold smallF
    rw [← integral_mul_left_eq_self (fun x : GL A' k => Ψ (x.val * (Y * (c⁻¹).val)) * (ν (gdet x) : ℂ) *
      apow (gdet x) ((Fintype.card D : ℂ) / 2)) (invT g), ← integral_const_mul]
    congr 1
    funext x
    have h4 : (ν (gdet g) : ℂ) ≠ 0 := Units.ne_zero _
    rw [gdet_mul, apow_mul, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO (invT_mem_KO hg)), gdet_invT, map_mul,
      map_inv, Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val]
    simp only [Matrix.mul_assoc]
    field_simp
  unfold smallP
  rw [e3, e2, apow_mul, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hc), map_mul, Units.val_mul, Units.val_mul,
    Matrix.mul_assoc]
  ring

theorem bigZetaIntegral_smul (μ : Measure (GL (Fin a) k)) (ϖ : kˣ) (σ : Fin a ⊕ A' ≃ D) (ν β : kˣ →* ℂˣ) (z : ℂ)
    (Φ : Matrix (Fin a) D k → ℂ) (h : GL D k) : bigP μ ϖ σ ν β (z • Φ) h = z * bigP μ ϖ σ ν β Φ h := by
  simp only [bigZetaIntegral_eq, bigF, Pi.smul_apply, smul_eq_mul, shellSum_smul]
  ring

theorem zeta_change (μ : Measure (GL (Fin a) k)) [μ.IsHaarMeasure] (μ' : Measure (GL A' k)) [μ'.IsHaarMeasure] (ϖ : kˣ)
    (σ : Fin a ⊕ A' ≃ D) (ν α β : kˣ →* ℂˣ) (hν : ∀ x, α x = ν x * β x) {g : GL (Fin a) k} (hg : g ∈ KO k (Fin a))
    {g' : GL A' k} (hg' : g' ∈ KO k A') {c : GL D k} (hc : c ∈ KO k D) (Φ : Matrix (Fin a) D k → ℂ)
    (Ψ : Matrix A' D k → ℂ) (H : bigP μ ϖ σ ν β Φ = smallP μ' σ ν α Ψ) :
    bigP μ ϖ σ ν β (fun X => ((ν (gdet g * gdet g' * gdet c) : ℂ) • Φ) (g.val * X * c.valᵀ)) =
      smallP μ' σ ν α fun Y => Ψ ((invT g').val * Y * (c⁻¹).val) := by
  funext h
  have h1 := bigZetaIntegral_equivariant μ ϖ σ ν β hg hc ((ν (gdet g * gdet g' * gdet c) : ℂ) • Φ) h
  rw [bigZetaIntegral_smul, H] at h1
  rw [smallP_change μ' σ ν α hg' hc, hν]
  refine mul_left_cancel₀ (Units.ne_zero (ν (gdet g))) ?_
  rw [h1]
  simp only [map_mul, Units.val_mul]
  ring

end Local

section Lin

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.FlipMatch (coX coY pairM)
open scoped GlobalTheory.VacAny ValuativeRel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d r s r' s' : ℕ} {X : Spc F E n} {W : Spc F E d} {B : Base F E} {v : Pl F}

theorem psiLoc_zero' (ψ : AddChar (AF F) ℂ) (v : Pl F) : psiLoc ψ v 0 = 1 := by
  rw [psiLoc, map_zero, map_zero]
  exact AddChar.map_zero_eq_one ψ

theorem coX_mul (t : E →ₐ[F] Fv F v) (b g : GL (Fin n) (Fv F v)) (c k : GL (Fin d) (Fv F v))
    (u : Matrix (Fin n) (Fin d) (AE F E)) : coX t b c u = g.val * coX t (b * g) (c * k) u * k.valᵀ := by
  simp only [coX, mul_inv_rev, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [← Matrix.transpose_mul k.val, Units.mul_inv, Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc g.val,
    Units.mul_inv, Matrix.one_mul]

theorem coY_mul (t : E →ₐ[F] Fv F v) (b g : GL (Fin n) (Fv F v)) (c k : GL (Fin d) (Fv F v))
    (u : Matrix (Fin n) (Fin d) (AE F E)) : coY σ X W t (b * g) (c * k) u = g.valᵀ * coY σ X W t b c u * k.val := by
  simp only [coY, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul]

theorem pairM_mul {K : Type} [CommRing K] {m n : Type} [Fintype m] [Fintype n]
    (A : Matrix m m K) (Y : Matrix m n K) (C : Matrix n n K) (P : Matrix m n K) :
    pairM (A * Y * C) P = pairM Y (Aᵀ * P * Cᵀ) := GlobalTheory.LinWShape.frob_mul A Y C P

theorem pairM_lin {K : Type} [Field K] {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (l : Matrix m n K →ₗ[K] K) (Y : Matrix m n K) : pairM Y (Matrix.of fun i j => l (Matrix.single i j 1)) = l Y :=
  (GlobalTheory.LinWShape.linForm_eq l Y).symm

theorem pairM_neg {K : Type} [CommRing K] {m n : Type} [Fintype m] [Fintype n] (Y P : Matrix m n K) :
    pairM Y (-P) = -pairM Y P := by simp [pairM]

theorem linW_change (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (M : Model σ X W)
    (t : E →ₐ[F] Fv F v) (b g : GL (Fin n) (Fv F v)) (c k : GL (Fin d) (Fv F v)) {ι ι₂} (hι : M.IsLinW B.ψ t b c ι)
    (hι₂ : M.IsLinW B.ψ t (b * g) (c * k) ι₂) :
    ∃ z : ℂ, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), (fun Y => ι φ (g.val * Y * k.valᵀ)) = z • ι₂ φ := by
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := GlobalTheory.SchrSB.continuous_psiAt _ hB.std.1 v
  have hψ1 : GlobalTheory.LatVac.psiAt B.ψ v ≠ 1 := GlobalTheory.PsiNontriv.psiAt_ne_one _ hB.std v
  have hsb := fun (u : Matrix (Fin n) (Fin d) (AE F E)) φ hφ =>
    GlobalTheory.SchrSB.schr_mem_SB B.ψ hB.std.1 v (GlobalTheory.LatVac.locCo M.co v u) φ hφ
  have act := fun b c u hu hp φ hφ => (GlobalTheory.T.heisenbergOperator_isotropic_translation_char_split hB.cm X W hX.herm hW.skew (GlobalTheory.FinUniq.det_ne_zero_herm hX)
    (GlobalTheory.FinUniq.det_ne_zero_skew hW) M B.ψ hB.std t b c u hu hp φ hφ _ (hsb u φ hφ)
    (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v u hu φ)).1
  choose zX hzX hzX0 hzXe using fun Z => (GlobalTheory.T.splitPlace_characterAndTranslationCoords_surjective F E σ B hB n d _ _ _ _ X W hX hW v t (b * g) (c * k) Z).1
  choose zY hzY hzY0 hzYe using fun Z => (GlobalTheory.T.splitPlace_characterAndTranslationCoords_surjective F E σ B hB n d _ _ _ _ X W hX hW v t (b * g) (c * k) Z).2
  have y0 : ∀ b c Z, coY σ X W t b c (zX Z) = 0 := fun b c Z => by simp [coY, hzX0]
  have x0 : ∀ b c Z, coX t b c (zY Z) = 0 := fun b c Z => by simp [coX, hzY0]
  have p0 : ∀ Y : Matrix (Fin n) (Fin d) (Fv F v), pairM Y 0 = 0 := fun Y => by simp [pairM]
  have p0' : ∀ Y : Matrix (Fin n) (Fin d) (Fv F v), pairM 0 Y = 0 := fun Y => by simp [pairM]
  refine GlobalTheory.T.eq_smul_of_commute_heisenberg_linearModel_schwartzBruhat (SB (Fin n × Fin d → Fv F v)) (GlobalTheory.LatVac.psiAt B.ψ v) hψc hψ1 ι₂
    (fun φ Y => ι φ (g.val * Y * k.valᵀ)) (Model.IsLin.bij hι₂) (fun x _ y _ a => by rw [map_add, map_smul]; rfl)
    (fun C φ => schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v (zX C)) φ)
    (fun l φ => schr (GlobalTheory.LatVac.psiAt B.ψ v)
      (GlobalTheory.LatVac.locCo M.co v (zY (Matrix.of fun i j => l (Matrix.single i j 1)))) φ)
    (fun C x hx => ⟨hsb _ x hx, funext fun Y => ?_, funext fun Y => ?_⟩)
    (fun l x hx => ⟨hsb _ x hx, funext fun Y => ?_, funext fun Y => ?_⟩)
  · rw [act _ _ _ (hzX C) (by rw [y0, p0]) x hx ι₂ hι₂, y0, p0, psiLoc_zero', one_mul, hzXe]
  · rw [act _ _ _ (hzX C) (by rw [y0, p0]) x hx ι hι, y0, p0, psiLoc_zero', one_mul, coX_mul t b g c k, hzXe,
      Matrix.mul_add, Matrix.add_mul]
  · rw [act _ _ _ (hzY _) (by rw [x0, p0']) x hx ι₂ hι₂, x0, add_zero, hzYe, pairM_lin]
    rfl
  · rw [act _ _ _ (hzY _) (by rw [x0, p0']) x hx ι hι, x0, add_zero, pairM_mul, Matrix.transpose_transpose, ← coY_mul,
      hzYe, pairM_lin]
    rfl

theorem linBar_change (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (M : Model σ X W)
    (t : E →ₐ[F] Fv F v) (b g : GL (Fin n) (Fv F v)) (c k : GL (Fin d) (Fv F v)) {ι ι₂} (hι : M.IsLinBar B.ψ t b c ι)
    (hι₂ : M.IsLinBar B.ψ t (b * g) (c * k) ι₂) :
    ∃ z : ℂ, ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      (fun Y => ι φ ((GlobalTheory.SplitFlip.invT g).val * Y * (k⁻¹).val)) = z • ι₂ φ := by
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := GlobalTheory.SchrSB.continuous_psiAt _ hB.std.1 v
  have hψ1 : GlobalTheory.LatVac.psiAt B.ψ v ≠ 1 := GlobalTheory.PsiNontriv.psiAt_ne_one _ hB.std v
  have hsb := fun (u : Matrix (Fin n) (Fin d) (AE F E)) φ hφ =>
    GlobalTheory.SchrSB.schr_mem_SB B.ψ hB.std.1 v (GlobalTheory.LatVac.locCo M.co v u) φ hφ
  have act := fun b c u hu hp φ hφ => (GlobalTheory.T.heisenbergOperator_isotropic_translation_char_split hB.cm X W hX.herm hW.skew (GlobalTheory.FinUniq.det_ne_zero_herm hX)
    (GlobalTheory.FinUniq.det_ne_zero_skew hW) M B.ψ hB.std t b c u hu hp φ hφ _ (hsb u φ hφ)
    (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v u hu φ)).2
  choose zX hzX hzX0 hzXe using fun Z => (GlobalTheory.T.splitPlace_characterAndTranslationCoords_surjective F E σ B hB n d _ _ _ _ X W hX hW v t (b * g) (c * k) Z).1
  choose zY hzY hzY0 hzYe using fun Z => (GlobalTheory.T.splitPlace_characterAndTranslationCoords_surjective F E σ B hB n d _ _ _ _ X W hX hW v t (b * g) (c * k) Z).2
  have y0 : ∀ b c Z, coY σ X W t b c (zX Z) = 0 := fun b c Z => by simp [coY, hzX0]
  have x0 : ∀ b c Z, coX t b c (zY Z) = 0 := fun b c Z => by simp [coX, hzY0]
  have p0 : ∀ Y : Matrix (Fin n) (Fin d) (Fv F v), pairM Y 0 = 0 := fun Y => by simp [pairM]
  have p0' : ∀ Y : Matrix (Fin n) (Fin d) (Fv F v), pairM 0 Y = 0 := fun Y => by simp [pairM]
  have eY : ∀ u, coY σ X W t b c u = (GlobalTheory.SplitFlip.invT g).val * coY σ X W t (b * g) (c * k) u * (k⁻¹).val := fun u => by
    have := coY_mul (σ := σ) (X := X) (W := W) t (b * g) g⁻¹ (c * k) k⁻¹ u
    rwa [mul_inv_cancel_right, mul_inv_cancel_right] at this
  have eX : ∀ u, coX t (b * g) (c * k) u = (GlobalTheory.SplitFlip.invT g).valᵀ * coX t b c u * (k⁻¹).valᵀ := fun u => by
    have := coX_mul t (b * g) g⁻¹ (c * k) k⁻¹ u
    rwa [mul_inv_cancel_right, mul_inv_cancel_right] at this
  refine GlobalTheory.T.eq_smul_of_commute_heisenberg_linearModel_schwartzBruhat (SB (Fin n × Fin d → Fv F v)) (GlobalTheory.LatVac.psiAt B.ψ v) hψc hψ1 ι₂
    (fun φ Y => ι φ ((GlobalTheory.SplitFlip.invT g).val * Y * (k⁻¹).val)) (Model.IsLin.bij hι₂)
    (fun x _ y _ a => by rw [map_add, map_smul]; rfl)
    (fun C φ => schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v (zY C)) φ)
    (fun l φ => schr (GlobalTheory.LatVac.psiAt B.ψ v)
      (GlobalTheory.LatVac.locCo M.co v (zX (-Matrix.of fun i j => l (Matrix.single i j 1)))) φ)
    (fun C x hx => ⟨hsb _ x hx, funext fun Y => ?_, funext fun Y => ?_⟩)
    (fun l x hx => ⟨hsb _ x hx, funext fun Y => ?_, funext fun Y => ?_⟩)
  · rw [act _ _ _ (hzY C) (by rw [x0, p0']) x hx ι₂ hι₂, x0, p0, neg_zero, psiLoc_zero', one_mul, hzYe]
  · rw [act _ _ _ (hzY C) (by rw [x0, p0']) x hx ι hι, x0, p0, neg_zero, psiLoc_zero', one_mul, eY, hzYe,
      Matrix.mul_add, Matrix.add_mul]
  · rw [act _ _ _ (hzX _) (by rw [y0, p0]) x hx ι₂ hι₂, y0, add_zero, hzXe, pairM_neg, neg_neg, pairM_lin]
    rfl
  · rw [act _ _ _ (hzX _) (by rw [y0, p0]) x hx ι hι, y0, add_zero, pairM_mul, ← eX, hzXe, pairM_neg, neg_neg, pairM_lin]
    rfl

theorem mem_O_iff (v : Pl F) (a : Fv F v) : a ∈ 𝒪[Fv F v] ↔ a ∈ v.adicCompletionIntegers F := by
  rw [Valuation.mem_integer_iff, ← map_one (ValuativeRel.valuation (Fv F v)), ← Valuation.Compatible.vle_iff_le,
    IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
    ← map_one (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))]
  exact Iff.rfl

theorem mem_KO_of_bases {t : E →ₐ[F] Fv F v} {L : Submodule (𝓞 E) (Fin n → E)} {b b₂ : GL (Fin n) (Fv F v)}
    (h : IsSplitBasis t L b) (h₂ : IsSplitBasis t L b₂) : b⁻¹ * b₂ ∈ GlobalTheory.SplitWeil.KO (Fv F v) (Fin n) := by
  have := mem_GLint_iff.1 (h.iff_mem_GLint.1 h₂)
  rw [GlobalTheory.SplitFlip.mem_KO_iff]
  exact ⟨fun i j => (mem_O_iff v _).2 (this.1 i j), fun i j => (mem_O_iff v _).2 (this.2 i j)⟩

variable {a a' : ℕ}

def kap (G : Geo σ a a') (V : Spc F E a) (V' : Spc F E a') (Z : Spc F E (a + a')) (v : Pl F) : (Fv F v)ˣ :=
  GlobalTheory.SplitFlip.gdet ((G.V.bas v)⁻¹ * V.bas v) * GlobalTheory.SplitFlip.gdet ((G.V'.bas v)⁻¹ * V'.bas v) *
    GlobalTheory.SplitFlip.gdet ((G.W.bas v)⁻¹ * Z.bas v)

variable {G : Geo σ a a'} {V : Spc F E a} {V' : Spc F E a'} {Z : Spc F E (a + a')}

theorem valuation_kap (hG : G.IsGood B) (hG₂ : (reG G V V' Z).IsGood B) (v : B.P) :
    ValuativeRel.valuation (Fv F v.1) (kap G V V' Z v.1 : Fv F v.1) = 1 := by
  rw [kap, Units.val_mul, Units.val_mul, map_mul, map_mul,
    GlobalTheory.SplitFlip.valuation_gdet_of_mem_KO (mem_KO_of_bases (b₂ := V.bas v) (hG.hV.bas v) (hG₂.hV.bas v)),
    GlobalTheory.SplitFlip.valuation_gdet_of_mem_KO (mem_KO_of_bases (b₂ := V'.bas v) (hG.hV'.bas v) (hG₂.hV'.bas v)),
    GlobalTheory.SplitFlip.valuation_gdet_of_mem_KO (mem_KO_of_bases (b₂ := Z.bas v) (hG.hW.bas v) (hG₂.hW.bas v)), one_mul, one_mul]

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL Formalism.DoubleCosetMeasures.instMeasMat in

theorem zeta_rel (hB : B.IsGood σ) (hG : G.IsGood B) (hG₂ : (reG G V V' Z).IsGood B) {X : Chars F E}
    {Rf S : FinMaps F a a'} {v : B.P} (h : IsZetaAt B G X Rf v) (h₂ : IsZetaAt B (reG G V V' Z) X S v)
    {φ φ'} (hφ : φ ∈ SB (Fin a × Fin (a + a') → Fv F v.1)) (hφ' : φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v.1))
    (e : Rf.p v φ = Rf.p' v φ') : S.p v ((chrW X.ν (B.τ v) (kap G V V' Z v.1) : ℂ) • φ) = S.p' v φ' := by
  obtain ⟨ι, ι', hι, hι', hv, hv', H⟩ := h
  obtain ⟨ι₂, ι₂', hι₂, hι₂', hv₂, hv₂', H₂⟩ := h₂
  have j₂ : G.M.IsLinW B.ψ (B.τ v) (G.V.bas v * ((G.V.bas v)⁻¹ * V.bas v)) (G.W.bas v * ((G.W.bas v)⁻¹ * Z.bas v)) ι₂ := by
    rw [mul_inv_cancel_left, mul_inv_cancel_left]
    exact ⟨hι₂.1, hι₂.2, hι₂.3⟩
  have j₂' : G.M'.IsLinBar B.ψ (B.τ v) (G.V'.bas v * ((G.V'.bas v)⁻¹ * V'.bas v))
      (G.W.bas v * ((G.W.bas v)⁻¹ * Z.bas v)) ι₂' := by
    rw [mul_inv_cancel_left, mul_inv_cancel_left]
    exact ⟨hι₂'.1, hι₂'.2, hι₂'.3⟩
  obtain ⟨z, hz⟩ := linW_change hB hG.hV hG.hW G.M (B.τ v) _ _ _ _ hι j₂
  obtain ⟨z', hz'⟩ := linBar_change hB hG.hV' hG.hW G.M' (B.τ v) _ _ _ _ hι' j₂'
  have z1 : z = 1 := by
    have := congrFun (hz _ (hG.hM.vac v).1) 0
    rw [show ι₂ (G.M.vac v) = _ from hv₂, hv, Matrix.mul_zero, Matrix.zero_mul, Pi.smul_apply,
      Set.indicator_of_mem (by intro i j; exact zero_mem _)] at this
    simpa using this.symm
  have z1' : z' = 1 := by
    have := congrFun (hz' _ (hG.hM'.vac v).1) 0
    rw [show ι₂' (G.M'.vac v) = _ from hv₂', hv', Matrix.mul_zero, Matrix.zero_mul, Pi.smul_apply,
      Set.indicator_of_mem (by intro i j; exact zero_mem _)] at this
    simpa using this.symm
  subst z1 z1'
  have hs := (SB _).smul_mem (chrW X.ν (B.τ v) (kap G V V' Z v.1) : ℂ) hφ
  rw [H₂ _ hs _ hφ', ← one_smul ℂ (ι₂ _), ← one_smul ℂ (ι₂' _), ← hz _ hs, ← hz' _ hφ', map_smul]
  letI : MeasurableSpace (Fv F v.1) := borel _
  haveI : BorelSpace (Fv F v.1) := ⟨rfl⟩
  exact zeta_change _ _ _ _ _ _ _ (fun x => by
      simp only [Chars.ν, chrW, locChar, MonoidHom.comp_apply, MonoidHom.div_apply, map_div, div_mul_cancel])
    (mem_KO_of_bases (hG.hV.bas v) (hG₂.hV.bas v)) (mem_KO_of_bases (hG.hV'.bas v) (hG₂.hV'.bas v))
    (mem_KO_of_bases (hG.hW.bas v) (hG₂.hW.bas v)) _ _ ((H _ hφ _ hφ').1 e)

end Lin

end GlobalTheory.ReBase

end
