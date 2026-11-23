import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlCharacterFactorsThroughDetOfTwoNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryGroupSurjectsGeneralLinearRightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryDeterminedBySplitImageStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocalUnitSubgroupClosure

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem one_mem_UAt {n : ℕ} (Y : Spc F E n) {R : Type} [Zero R] (ev : AF F → R) : (1 : UA σ Y.J) ∈ UAt σ Y ev := by
  intro u _
  simp [mat]

theorem mul_mem_UAt {n : ℕ} {Y : Spc F E n} {R : Type} [Zero R] {ev : AF F → R} {g h : UA σ Y.J}
    (hg : g ∈ UAt σ Y ev) (hh : h ∈ UAt σ Y ev) : g * h ∈ UAt σ Y ev := by
  intro u hu
  have e : mat (g * h) - 1 = (mat g - 1) * mat h + (mat h - 1) := by
    simp only [mat, Subgroup.coe_mul, Units.val_mul]; noncomm_ring
  rw [e, smul_add, ← Matrix.smul_mul, hg u hu, hh u hu, Matrix.zero_mul, add_zero]

theorem mat_mul {n : ℕ} {Y : Spc F E n} (g h : UA σ Y.J) : mat (g * h) = mat g * mat h := rfl

theorem mat_one {n : ℕ} {Y : Spc F E n} : mat (1 : UA σ Y.J) = 1 := rfl

end GlobalTheory.LocalUnitSubgroupClosure

namespace GlobalTheory.LocalUnitSubgroupClosure

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem pres (hT : IsTriple B G X om om') (p : UA σ G.V.J × UA σ G.W.J) {Φ : (Fin a × Fin (a + a') → AF F) → ℂ}
    (hΦ : Φ ∈ schA F (Fin a × Fin (a + a'))) : om p Φ ∈ schA F (Fin a × Fin (a + a')) :=
  (IsUWeilPair.isUSplitting hT.weil).pres p Φ hΦ

theorem acts_comp (hT : IsTriple B G X om om') {v : Pl F} {h₁ h₂ : UA σ G.W.J}
    {φ φ₂ φ₃ : (Fin a × Fin (a + a') → Fv F v) → ℂ}
    (h2 : Acts (evFin F v) (om (1, h₂)) φ φ₂) (h1 : Acts (evFin F v) (om (1, h₁)) φ₂ φ₃) :
    Acts (evFin F v) (om (1, h₁ * h₂)) φ φ₃ := by
  intro r hr
  have hr2 : Rest (evFin F v) φ₂ r := ⟨hr.1, by rw [← h2 r hr]; exact pres hT _ hr.2⟩
  have e : om (1, h₁ * h₂) = om (1, h₁) * om (1, h₂) := by rw [← map_mul]; simp
  rw [e, Module.End.mul_apply, h2 r hr, h1 r hr2]

theorem acts_one {v : Pl F} (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) :
    Acts (evFin F v) (om (1, 1)) φ φ := by
  intro r _
  rw [show ((1, 1) : UA σ G.V.J × UA σ G.W.J) = 1 from rfl, map_one, Module.End.one_apply]

noncomputable section

def cmpGL {n : ℕ} {Y : Spc F E n} {v : Pl F} (t : E →ₐ[F] Fv F v) (h : UA σ Y.J) : GL (Fin n) (Fv F v) :=
  Units.map (piW t).mapMatrix.toMonoidHom h.1

theorem cmpGL_val {n : ℕ} {Y : Spc F E n} {v : Pl F} (t : E →ₐ[F] Fv F v) (h : UA σ Y.J) :
    (cmpGL t h).1 = (mat h).map (piW t) := rfl

def apowHom {v : Pl F} (z : ℂ) : (Fv F v)ˣ →* ℂˣ where
  toFun x := Units.mk0 (GlobalTheory.SplitFlip.apow x z) (GlobalTheory.SplitFlip.apow_ne_zero x z)
  map_one' := Units.ext (by simp)
  map_mul' x y := Units.ext (by simp [GlobalTheory.SplitFlip.apow_mul])

end

end GlobalTheory.LocalUnitSubgroupClosure

namespace GlobalTheory.LocalUnitSubgroupClosure

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem isUnit_det_cmp {n : ℕ} {Y : Spc F E n} {v : Pl F} (t : E →ₐ[F] Fv F v) (h : UA σ Y.J) :
    IsUnit ((mat h).map (piW t)).det := by
  rw [← cmpGL_val]; exact (Matrix.isUnit_iff_isUnit_det _).1 (cmpGL t h).isUnit

theorem two_ne_zero_Fv (v : Pl F) : (2 : Fv F v) ≠ 0 := by
  have := (algebraMap F (Fv F v)).injective.ne (two_ne_zero (α := F))
  rwa [map_ofNat, map_zero] at this

theorem core (hT : IsTriple B G X om om') (v : Pl F) (t : E →ₐ[F] Fv F v)
    (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ))
    (hEx : ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      ∃! φ₁, φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v) ∧ Acts (evFin F v) (om (1, h)) φ φ₁)
    (hsurj : ∀ h' : GL (Fin (a + a')) (Fv F v), ∃ h ∈ UAt σ G.W (evFin F v), (mat h).map (piW t) = h'.1)
    (hinj : ∀ h₁ ∈ UAt σ G.W (evFin F v), ∀ h₂ ∈ UAt σ G.W (evFin F v),
      (mat h₁).map (piW t) = (mat h₂).map (piW t) → h₁ = h₂)
    (hS : ∀ h ∈ UAt σ G.W (evFin F v), ∃ c : ℂ, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → ∀ Y, ι φ₁ Y = c * ι φ (Y * (((mat h).map (piW t))⁻¹)ᵀ)) :
    ∃ β₀ : (Fv F v)ˣ →* ℂˣ, (∀ h ∈ UAt σ G.W (evFin F v), ∃ h' : GL (Fin (a + a')) (Fv F v), (mat h).map (piW t) = h'.1 ∧
      ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om (1, h)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omA 1 β₀ 1 h' (ι φ)) := by
  classical
  by_cases h0 : ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ι φ = 0
  · refine ⟨1, fun h _ => ⟨cmpGL t h, rfl, fun φ hφ φ₁ hφ₁ _ => ?_⟩⟩
    rw [h0 φ₁ hφ₁, h0 φ hφ]
    funext Y
    simp [GlobalTheory.SplitFlip.omA]
  push Not at h0
  obtain ⟨φ₀, hφ₀, hne⟩ := h0
  obtain ⟨Y₀, hY₀⟩ := Function.ne_iff.1 hne
  set P : UA σ G.W.J → ℂ → Prop := fun h c => ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → ∀ Y, ι φ₁ Y = c * ι φ (Y * (((mat h).map (piW t))⁻¹)ᵀ) with hP
  have uniq : ∀ h ∈ UAt σ G.W (evFin F v), ∀ c c', P h c → P h c' → c = c' := by
    intro h hh c c' hc hc'
    obtain ⟨φ₁, ⟨hφ₁, hA⟩, -⟩ := hEx h hh φ₀ hφ₀
    set M := (mat h).map (piW t)
    have key : Y₀ * Mᵀ * M⁻¹ᵀ = Y₀ := by
      rw [Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ (isUnit_det_cmp t h),
        Matrix.transpose_one, Matrix.mul_one]
    have e1 := hc φ₀ hφ₀ φ₁ hφ₁ hA (Y₀ * Mᵀ)
    have e2 := hc' φ₀ hφ₀ φ₁ hφ₁ hA (Y₀ * Mᵀ)
    rw [key] at e1 e2
    exact mul_right_cancel₀ hY₀ (e1.symm.trans e2)
  let c : UA σ G.W.J → ℂ := fun h => if hh : h ∈ UAt σ G.W (evFin F v) then (hS h hh).choose else 0
  have hc : ∀ h (hh : h ∈ UAt σ G.W (evFin F v)), P h (c h) := by
    intro h hh
    simp only [c, dif_pos hh]
    exact (hS h hh).choose_spec
  have P1 : P 1 1 := by
    intro φ hφ φ₁ hφ₁ hA Y
    have : φ₁ = φ := (hEx 1 (one_mem_UAt _ _) φ hφ).unique ⟨hφ₁, hA⟩ ⟨hφ, acts_one φ⟩
    subst this
    rw [mat_one, Matrix.map_one (piW t) (map_zero _) (map_one _), inv_one, Matrix.transpose_one, Matrix.mul_one,
      one_mul]
  have c1 : c 1 = 1 := uniq 1 (one_mem_UAt _ _) _ _ (hc 1 (one_mem_UAt _ _)) P1
  have Pmul : ∀ h₁ (hh₁ : h₁ ∈ UAt σ G.W (evFin F v)) h₂ (hh₂ : h₂ ∈ UAt σ G.W (evFin F v)),
      P (h₁ * h₂) (c h₁ * c h₂) := by
    intro h₁ hh₁ h₂ hh₂ φ hφ φ₁₂ hφ₁₂ hA Y
    obtain ⟨φ₂, ⟨hφ₂, hA2⟩, -⟩ := hEx h₂ hh₂ φ hφ
    obtain ⟨φ₃, ⟨hφ₃, hA3⟩, -⟩ := hEx h₁ hh₁ φ₂ hφ₂
    have : φ₁₂ = φ₃ := (hEx (h₁ * h₂) (mul_mem_UAt hh₁ hh₂) φ hφ).unique ⟨hφ₁₂, hA⟩ ⟨hφ₃, acts_comp hT hA2 hA3⟩
    subst this
    rw [hc h₁ hh₁ φ₂ hφ₂ φ₁₂ hφ₁₂ hA3, hc h₂ hh₂ φ hφ φ₂ hφ₂ hA2, mat_mul, Matrix.map_mul, Matrix.mul_inv_rev,
      Matrix.transpose_mul, Matrix.mul_assoc, mul_assoc]
  have cmul : ∀ h₁ (hh₁ : h₁ ∈ UAt σ G.W (evFin F v)) h₂ (hh₂ : h₂ ∈ UAt σ G.W (evFin F v)),
      c (h₁ * h₂) = c h₁ * c h₂ := fun h₁ hh₁ h₂ hh₂ =>
    uniq _ (mul_mem_UAt hh₁ hh₂) _ _ (hc _ (mul_mem_UAt hh₁ hh₂)) (Pmul h₁ hh₁ h₂ hh₂)
  choose sec hsec hsecv using hsurj
  have secmul : ∀ g₁ g₂, sec (g₁ * g₂) = sec g₁ * sec g₂ := fun g₁ g₂ =>
    hinj _ (hsec _) _ (mul_mem_UAt (hsec g₁) (hsec g₂)) (by
      rw [hsecv, mat_mul, Matrix.map_mul, hsecv, hsecv, Units.val_mul])
  have sec1 : sec 1 = 1 := hinj _ (hsec _) _ (one_mem_UAt _ _) (by
      rw [hsecv, mat_one, Matrix.map_one (piW t) (map_zero _) (map_one _), Units.val_one])
  let κ : GL (Fin (a + a')) (Fv F v) →* ℂ :=
    { toFun := fun g => c (sec g)
      map_one' := by simp only [sec1, c1]
      map_mul' := fun g₁ g₂ => by simp only [secmul, cmul _ (hsec g₁) _ (hsec g₂)] }
  obtain ⟨χ, hχ⟩ := GlobalTheory.ghom_factors_through_det (two_ne_zero_Fv v) κ.toHomUnits
  refine ⟨χ * apowHom ((a : ℂ) / 2), fun h hh => ⟨cmpGL t h, rfl, fun φ hφ φ₁ hφ₁ hA => ?_⟩⟩
  have hsh : sec (cmpGL t h) = h := hinj _ (hsec _) _ hh (by rw [hsecv, cmpGL_val])
  have hch : c h = (χ (Matrix.GeneralLinearGroup.det (cmpGL t h)) : ℂ) := by
    have := congrArg Units.val (hχ (cmpGL t h))
    rw [MonoidHom.coe_toHomUnits] at this
    rw [← this]
    show c h = c (sec (cmpGL t h))
    rw [hsh]
  funext Y
  rw [hc h hh φ hφ φ₁ hφ₁ hA Y, hch]
  simp only [GlobalTheory.SplitFlip.omA, GlobalTheory.SplitFlip.invT_val, map_one, inv_one, Units.val_one, MonoidHom.mul_apply,
    Units.val_mul, Fintype.card_fin, GlobalTheory.SplitFlip.apow_one, one_mul, Matrix.one_mul, Matrix.coe_units_inv, cmpGL_val]
  have hv : ((apowHom (v := v) ((a : ℂ) / 2) (GlobalTheory.SplitFlip.gdet (cmpGL t h)) : ℂˣ) : ℂ) *
      GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet (cmpGL t h)) (-(a : ℂ) / 2) = 1 := by
    show GlobalTheory.SplitFlip.apow _ _ * GlobalTheory.SplitFlip.apow _ _ = 1
    rw [← GlobalTheory.SplitFlip.apow_add, show (a : ℂ) / 2 + -(a : ℂ) / 2 = 0 by ring, GlobalTheory.SplitFlip.apow_zero]
  rw [mul_one, mul_assoc (χ _ : ℂ), hv, mul_one]

end GlobalTheory.LocalUnitSubgroupClosure

namespace GlobalTheory.LocalUnitSubgroupClosure

theorem linear_weil_functional_character_weight_zero : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι → (∀ h ∈ UAt σ G.W (evFin F v), ∃ c : ℂ, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → ∀ Y, ι φ₁ Y = c * ι φ (Y * (((mat h).map (piW t))⁻¹)ᵀ)) →
    ∃ β₀ : (Fv F v)ˣ →* ℂˣ, (∀ h ∈ UAt σ G.W (evFin F v), ∃ h' : GL (Fin (a + a')) (Fv F v), (mat h).map (piW t) = h'.1 ∧
      ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omA 1 β₀ 1 h' (ι φ)) := by
  intro hPr F E _ _ _ _ _ σ B a a' G X om om' hT v hv t ι _ hS
  have hEx := (GlobalTheory.T.theta_action_exists hPr F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _
    (GlobalTheory.ThK.Check.isPair_of_isTriple hT).1 v).1 1 (one_mem_UAt _ _)
  exact core hT v t ι hEx (GlobalTheory.T.local_unitary_group_surjects_general_linear_right hPr F E σ B a a' G X om om' hT v hv t)
    (GlobalTheory.T.local_unitary_determined_by_split_image F E σ B a a' G X om om' hT v hv t) hS

end GlobalTheory.LocalUnitSubgroupClosure
