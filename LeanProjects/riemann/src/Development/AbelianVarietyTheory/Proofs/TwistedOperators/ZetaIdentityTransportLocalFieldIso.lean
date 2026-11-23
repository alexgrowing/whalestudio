import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedAbsValueLocalFieldUnitMapHomeomorph

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

noncomputable section
namespace GlobalTheory.FlipMatch.FieldTransport
open ValuativeRel

section
variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'}
  {n : Type} [Fintype n] [DecidableEq n]

omit [IsNonarchimedeanLocalField k] [IsNonarchimedeanLocalField k'] in

theorem val_le_iff (hj : IsLocIso j) (x y : k) :
    valuation k' (j x) ≤ valuation k' (j y) ↔ valuation k x ≤ valuation k y := by
  by_cases hy : y = 0
  · subst hy; simp
  have h := hj.2.2 (x / y)
  have h0 : 0 < valuation k y := zero_lt_iff.2 (by simpa using hy)
  have h1 : 0 < valuation k' (j y) := zero_lt_iff.2 (by simpa using hy)
  rwa [Valuation.mem_integer_iff, Valuation.mem_integer_iff, map_div₀, map_div₀, map_div₀, div_le_one₀ h0,
    div_le_one₀ h1] at h

theorem isUnif_map (hj : IsLocIso j) {ϖ : kˣ} (h : IsUnif ϖ) : IsUnif (Units.map (j : k →* k') ϖ) := by
  have hlt : ∀ x, valuation k' (j x) < 1 ↔ valuation k x < 1 := fun x => by
    have := (val_le_iff hj 1 x).not
    simpa only [map_one, not_le] using this
  obtain ⟨ϖ', h'⟩ := exists_isUnif (k := k')
  show valuation k' (j ϖ) = uniformizer k'
  refine le_antisymm (le_uniformizer_iff.2 ((hlt _).2 (h ▸ uniformizer_lt_one))) ?_
  obtain ⟨y, hy⟩ := j.surjective ϖ'
  rw [← show valuation k' (ϖ' : k') = uniformizer k' from h', ← hy, val_le_iff hj,
    show valuation k (ϖ : k) = uniformizer k from h, le_uniformizer_iff, ← hlt, hy]
  exact h' ▸ uniformizer_lt_one

theorem shellSet_subset {ϖ ϖ' : kˣ} (h : IsUnif ϖ) (h' : IsUnif ϖ') (m : n → ℤ) :
    shellSet ϖ m ⊆ shellSet ϖ' m := by
  intro g hg
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_shellSet.1 hg
  have hu : ∀ r : ℤ, valuation k (((ϖ / ϖ') ^ r : kˣ) : k) = 1 := fun r => by
    have h1 : valuation k ((ϖ : k) / ϖ') = 1 := by
      rw [map_div₀, show valuation k (ϖ : k) = _ from h, show valuation k (ϖ' : k) = _ from h']
      exact div_self uniformizer_ne_zero
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, Units.val_div_eq_div_val, h1, _root_.one_zpow]
  have hd : ∀ c : n → kˣ, (∀ i, valuation k (c i : k) = 1) → ∀ i l, (diagGL c).val i l ∈ 𝒪[k] := fun c hc i l => by
    rw [diagGL_val, diagonal_apply]
    split_ifs
    · exact (hc i).le
    · exact zero_mem _
  have hK : (diagGL fun i => (ϖ / ϖ') ^ m i) ∈ KO k n := (mem_KO_iff _).2 ⟨hd _ fun i => hu _,
    hd (fun i => ((ϖ / ϖ') ^ m i)⁻¹) fun i => by rw [← _root_.zpow_neg]; exact hu _⟩
  refine mem_shellSet.2 ⟨_, mul_mem hx hK, y, hy, ?_⟩
  congr 1
  rw [mul_assoc]
  congr 1
  have := diagHom.map_mul (fun i => (ϖ / ϖ') ^ m i) (fun i => ϖ' ^ m i)
  refine Eq.trans ?_ this
  show SplitFlip.diagGL _ = SplitFlip.diagGL _
  congr 1
  funext i
  simp [← mul_zpow]

def glEquiv (j : k ≃+* k') (n : Type) [Fintype n] [DecidableEq n] : GL n k ≃* GL n k' :=
  Units.mapEquiv (j.mapMatrix (m := n)).toMulEquiv

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [ValuativeRel k'] [TopologicalSpace k']
  [IsNonarchimedeanLocalField k'] in

theorem glEquiv_val (g : GL n k) : (glEquiv j n g).val = g.val.map j := rfl

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [ValuativeRel k'] [TopologicalSpace k']
  [IsNonarchimedeanLocalField k'] in

theorem gdet_glEquiv (g : GL n k) : gdet (glEquiv j n g) = Units.map (j : k →* k') (gdet g) :=
  Units.ext ((j : k →+* k').map_det g.val).symm

def glHomeo (hj : IsLocIso j) (n : Type) [Fintype n] [DecidableEq n] : GL n k ≃ₜ* GL n k' :=
  { glEquiv j n with
    continuous_toFun := isEmbedding_val_GL.continuous_iff.2 (Units.continuous_val.matrix_map hj.1)
    continuous_invFun := isEmbedding_val_GL.continuous_iff.2 (Units.continuous_val.matrix_map hj.2.1) }

theorem glEquiv_mem_KO (hj : IsLocIso j) (g : GL n k) : glEquiv j n g ∈ KO k' n ↔ g ∈ KO k n := by
  rw [mem_KO_iff, mem_KO_iff, ← map_inv]
  simp only [glEquiv_val, map_apply, hj.2.2]

theorem preimage_shellSet (hj : IsLocIso j) {ϖ : kˣ} {ϖ' : k'ˣ} (h : IsUnif ϖ) (h' : IsUnif ϖ') (m : n → ℤ) :
    glEquiv j n ⁻¹' shellSet ϖ' m = shellSet ϖ m := by
  rw [(shellSet_subset h' (isUnif_map hj h) m).antisymm (shellSet_subset (isUnif_map hj h) h' m)]
  have hd : glEquiv j n (diagGL fun i => ϖ ^ m i) = diagGL fun i => (Units.map (j : k →* k') ϖ) ^ m i :=
    Units.ext (by rw [glEquiv_val, diagGL_val, diagGL_val, diagonal_map (map_zero _)]; simp)
  ext g
  rw [Set.mem_preimage, mem_shellSet, mem_shellSet, ← hd]
  constructor
  · rintro ⟨x, hx, y, hy, H⟩
    obtain ⟨x, rfl⟩ := (glEquiv j n).surjective x
    obtain ⟨y, rfl⟩ := (glEquiv j n).surjective y
    rw [← map_mul, ← map_mul] at H
    exact ⟨x, (glEquiv_mem_KO hj _).1 hx, y, (glEquiv_mem_KO hj _).1 hy, (glEquiv j n).injective H⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨_, (glEquiv_mem_KO hj _).2 hx, _, (glEquiv_mem_KO hj _).2 hy, by rw [map_mul, map_mul]⟩

theorem apow_map (hj : IsLocIso j) (x : kˣ) (z : ℂ) : apow (Units.map (j : k →* k') x) z = apow x z := by
  have := GlobalTheory.SplitWeil.nabs_map_of_homeomorph j hj.1 hj.2.1 x
  unfold apow
  congr 2

variable [MeasurableSpace k] [BorelSpace k] [MeasurableSpace k'] [BorelSpace k']

def glMeas (hj : IsLocIso j) (n : Type) [Fintype n] [DecidableEq n] : GL n k ≃ᵐ GL n k' :=
  (glHomeo hj n).toHomeomorph.toMeasurableEquiv

theorem isHaar_map (hj : IsLocIso j) (μ : Measure (GL n k)) [μ.IsHaarMeasure] : (μ.map (glMeas hj n)).IsHaarMeasure :=
  (glHomeo hj n).isHaarMeasure_map μ

theorem map_haarVol (hj : IsLocIso j) : (haarVol (KO k n)).map (glMeas hj n) = haarVol (KO k' n) := by
  have := isHaar_map hj (haarVol (KO k n))
  refine eq_haarVol _ isOpen_KO le_rfl ?_
  rw [MeasurableEquiv.map_apply, show glMeas hj n ⁻¹' (KO k' n : Set (GL n k')) = KO k n from
    Set.ext fun g => glEquiv_mem_KO hj g]
  exact haarVol_self isOpen_KO le_rfl

variable {C : Type} [Fintype C] [DecidableEq C] {ν : kˣ →* ℂˣ} {ν' : k'ˣ →* ℂˣ}

theorem shell_map (hj : IsLocIso j) {ϖ : kˣ} {ϖ' : k'ˣ} (h : IsUnif ϖ) (h' : IsUnif ϖ')
    (hν : ∀ x, ν x = ν' (Units.map (j : k →* k') x)) (z : ℂ) (φ : Matrix n n k' → ℂ) (m : n → ℤ) :
    shell (haarVol (KO k n)) ϖ ν z (fun X => φ (X.map j)) m = shell (haarVol (KO k' n)) ϖ' ν' z φ m := by
  unfold shell
  rw [← map_haarVol hj, setIntegral_map_equiv, ← preimage_shellSet hj h h']
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  show _ = φ (glEquiv j _ g).val * ν' (gdet (glEquiv j _ g)) * apow (gdet (glEquiv j _ g)) _
  rw [gdet_glEquiv, apow_map hj, ← hν, glEquiv_val]

omit [DecidableEq C] in

theorem bigF_map (hj : IsLocIso j) {a : ℕ} {ϖ : kˣ} {ϖ' : k'ˣ} (h : IsUnif ϖ) (h' : IsUnif ϖ')
    (hν : ∀ x, ν x = ν' (Units.map (j : k →* k') x)) (Ξ : Matrix (Fin a) C k' → ℂ) (X : Matrix (Fin a) C k) :
    bigF (haarVol (KO k (Fin a))) ϖ ν (fun X => Ξ (X.map j)) X = bigF (haarVol (KO k' (Fin a))) ϖ' ν' Ξ (X.map j) := by
  unfold bigF shellSum
  refine finsum_congr fun m => ?_
  rw [← shell_map hj h h' hν]
  simp only [Matrix.map_mul]

omit [DecidableEq C] in

theorem smallF_map (hj : IsLocIso j) (μ : Measure (GL n k))
    (hν : ∀ x, ν x = ν' (Units.map (j : k →* k') x)) (Ψ : Matrix n C k' → ℂ) (Y : Matrix n C k) :
    smallF μ ν (fun Y => Ψ (Y.map j)) Y = smallF (μ.map (glMeas hj n)) ν' Ψ (Y.map j) := by
  unfold smallF
  rw [integral_map_equiv]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  show _ = Ψ ((glEquiv j _ g).val * Y.map j) * ν' (gdet (glEquiv j _ g)) * apow (gdet (glEquiv j _ g)) _
  rw [gdet_glEquiv, apow_map hj, ← hν, glEquiv_val, ← Matrix.map_mul]

end

theorem zeta_identity_transport : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (k' : Type) [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [MeasurableSpace k'] [BorelSpace k'] (j : k ≃+* k'), IsLocIso j → ∀ (a : ℕ) (A' : Type) [Fintype A'] [DecidableEq A'] (C : Type) [Fintype C] [DecidableEq C] (σ : Fin a ⊕ A' ≃ C)
    (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (μ' : Measure (GL A' k')) [μ'.IsHaarMeasure] (ϖ : kˣ) (ϖ' : k'ˣ), IsUnif ϖ → IsUnif ϖ' →
    ∀ (ν β : kˣ →* ℂˣ) (ν' β' : k'ˣ →* ℂˣ), (∀ x, ν x = ν' (Units.map (j : k →* k') x)) →
    ∃ lam : ℂ, lam ≠ 0 ∧ ∀ (Ξ : Matrix (Fin a) C k' → ℂ) (Ψ : Matrix A' C k' → ℂ),
      bigP (haarVol (KO k' (Fin a))) ϖ' σ ν' β' Ξ = smallP μ' σ ν' (ν' * β') Ψ →
      bigP (haarVol (KO k (Fin a))) ϖ σ ν β (fun X => Ξ (X.map j)) = smallP μ σ ν (ν * β) fun Y => lam * Ψ (Y.map j) := by
  intro k _ _ _ _ _ _ k' _ _ _ _ _ _ j hj a A' _ _ C _ _ σ μ _ μ' _ ϖ ϖ' h h' ν β ν' β' hν
  have := isHaar_map hj μ
  have hc := Measure.isMulLeftInvariant_eq_smul (μ.map (glMeas hj A')) μ'
  have hc0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure (μ.map (glMeas hj A')) μ').ne'
  generalize Measure.haarScalarFactor (μ.map (glMeas hj A')) μ' = c at hc hc0
  have hc1 : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc0
  refine ⟨((c : ℝ) : ℂ)⁻¹, inv_ne_zero hc1, fun Ξ Ψ H => funext fun g => ?_⟩
  have H1 := congrFun H (glEquiv j C g)
  have hX : (X0 k σ * (invT g).val).map j = X0 k' σ * (invT (glEquiv j C g)).val := by
    ext i l
    rw [map_apply, frameMatrixFirstColumnBlock_mul_apply, frameMatrixFirstColumnBlock_mul_apply]; rfl
  have hY : (Y0 k σ * g.val).map j = Y0 k' σ * (glEquiv j C g).val := by
    ext i l
    rw [map_apply, frameMatrixSecondColumnBlock_mul_apply, frameMatrixSecondColumnBlock_mul_apply]; rfl
  have hS : smallF μ ν (fun Y => ((c : ℝ) : ℂ)⁻¹ * Ψ (Y.map j)) (Y0 k σ * g.val) =
      smallF μ' ν' Ψ (Y0 k' σ * (glEquiv j C g).val) := by
    rw [smallF_map hj μ hν (fun Y => ((c : ℝ) : ℂ)⁻¹ * Ψ Y), hc, hY]
    simp only [smallF, integral_smul_nnreal_measure, mul_assoc, integral_const_mul, NNReal.smul_def,
      Complex.real_smul]
    rw [inv_mul_cancel_left₀ hc1]
  rw [bigZetaIntegral_eq, smallP, gdet_glEquiv, apow_map hj, apow_map hj, MonoidHom.mul_apply, ← hν, Units.val_mul] at H1
  rw [bigZetaIntegral_eq, smallP, bigF_map hj h h' hν, hS, hX, MonoidHom.mul_apply, Units.val_mul]
  have hb : ((β' (Units.map (j : k →* k') (gdet g)) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  apply mul_left_cancel₀ hb
  linear_combination (β (gdet g) : ℂ) * H1

end GlobalTheory.FlipMatch.FieldTransport
