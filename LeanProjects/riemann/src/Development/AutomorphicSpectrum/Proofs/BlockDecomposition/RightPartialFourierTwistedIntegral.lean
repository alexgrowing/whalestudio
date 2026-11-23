import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Lpart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialFourierInversion

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2DualWhittakerPair.FlR

section Iter

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]

theorem int4 (f : X × X × X × X → ℂ) (hf : Integrable f (μ.prod (μ.prod (μ.prod μ)))) :
    ∫ q, f q ∂(μ.prod (μ.prod (μ.prod μ))) = ∫ x, ∫ y, ∫ z, ∫ w, f (x, y, z, w) ∂μ ∂μ ∂μ ∂μ := by
  rw [integral_prod _ hf]
  refine integral_congr_ae ?_
  filter_upwards [hf.prod_right_ae] with x hx
  rw [integral_prod _ hx]
  refine integral_congr_ae ?_
  filter_upwards [hx.prod_right_ae] with y hy
  exact integral_prod _ hy

end Iter

section D

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def ent (a b d c : F) : Fin 2 × Fin 2 → F :=
  fun ij => (!![a, b; d, c] : Matrix (Fin 2) (Fin 2) F) ij.1 ij.2

@[simp] theorem ent_00 (a b d c : F) : ent a b d c (0, 0) = a := by simp [ent]
@[simp] theorem ent_01 (a b d c : F) : ent a b d c (0, 1) = b := by simp [ent]
@[simp] theorem ent_10 (a b d c : F) : ent a b d c (1, 0) = d := by simp [ent]
@[simp] theorem ent_11 (a b d c : F) : ent a b d c (1, 1) = c := by simp [ent]

theorem toM_ent (a b d c : F) : toM (ent a b d c) = !![a, b; d, c] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toM]

theorem ent_eta (X : Fin 2 × Fin 2 → F) : ent (X (0, 0)) (X (0, 1)) (X (1, 0)) (X (1, 1)) = X := by
  funext ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> simp

theorem measurable_ent : Measurable fun q : F × F × F × F => ent q.1 q.2.1 q.2.2.1 q.2.2.2 := by
  refine measurable_pi_iff.mpr fun ij => ?_
  obtain ⟨i, j⟩ := ij
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, ent_00, ent_01, ent_10, ent_11] <;> fun_prop

def eqA : (F × F × F × F) ≃ᵐ (Fin 2 × Fin 2 → F) where
  toFun q := ent q.2.1 q.2.2.1 q.2.2.2 q.1
  invFun X := (X (1, 1), X (0, 0), X (0, 1), X (1, 0))
  left_inv q := by simp
  right_inv X := ent_eta X
  measurable_toFun := measurable_ent.comp
    (f := fun q : F × F × F × F => (q.2.1, q.2.2.1, q.2.2.2, q.1)) (by fun_prop)
  measurable_invFun := by
    change Measurable fun X : Fin 2 × Fin 2 → F => (X (1, 1), X (0, 0), X (0, 1), X (1, 0))
    fun_prop

def eqB : (F × F × F × F) ≃ᵐ (Fin 2 × Fin 2 → F) where
  toFun q := ent q.2.2.2 q.2.2.1 q.2.1 q.1
  invFun X := (X (1, 1), X (1, 0), X (0, 1), X (0, 0))
  left_inv q := by simp
  right_inv X := ent_eta X
  measurable_toFun := measurable_ent.comp
    (f := fun q : F × F × F × F => (q.2.2.2, q.2.2.1, q.2.1, q.1)) (by fun_prop)
  measurable_invFun := by
    change Measurable fun X : Fin 2 × Fin 2 → F => (X (1, 1), X (1, 0), X (0, 1), X (0, 0))
    fun_prop

theorem mpA (ψ : AddChar F Circle) : MeasurePreserving (eqA (F := F))
    (selfDualMeasure ψ |>.prod (selfDualMeasure ψ |>.prod (selfDualMeasure ψ |>.prod (selfDualMeasure ψ)))) (mM ψ) := by
  refine ⟨eqA.measurable, ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [eqA.map_apply]
  have : (eqA (F := F)) ⁻¹' Set.univ.pi s = s (1, 1) ×ˢ s (0, 0) ×ˢ s (0, 1) ×ˢ s (1, 0) := by
    ext ⟨c, a, b, d⟩
    simp [eqA, Set.mem_pi, Prod.forall, Fin.forall_fin_two]
    tauto
  rw [this]
  simp only [Measure.prod_prod]
  rw [Fintype.prod_prod_type]
  simp only [Fin.prod_univ_two]
  ring

theorem mpB (ψ : AddChar F Circle) : MeasurePreserving (eqB (F := F))
    (selfDualMeasure ψ |>.prod (selfDualMeasure ψ |>.prod (selfDualMeasure ψ |>.prod (selfDualMeasure ψ)))) (mM ψ) := by
  refine ⟨eqB.measurable, ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [eqB.map_apply]
  have : (eqB (F := F)) ⁻¹' Set.univ.pi s = s (1, 1) ×ˢ s (1, 0) ×ˢ s (0, 1) ×ˢ s (0, 0) := by
    ext ⟨c, d, b, a⟩
    simp [eqB, Set.mem_pi, Prod.forall, Fin.forall_fin_two]
    tauto
  rw [this]
  simp only [Measure.prod_prod]
  rw [Fintype.prod_prod_type]
  simp only [Fin.prod_univ_two]
  ring

theorem iterA (ψ : AddChar F Circle) (g : (Fin 2 × Fin 2 → F) → ℂ) (hg : Integrable g (mM ψ)) :
    ∫ X, g X ∂mM ψ = ∫ c, ∫ a, ∫ b, ∫ d, g (ent a b d c)
      ∂selfDualMeasure ψ ∂selfDualMeasure ψ ∂selfDualMeasure ψ ∂selfDualMeasure ψ := by
  rw [← (mpA ψ).integral_comp' g]
  exact int4 _ _ (((mpA ψ).integrable_comp_emb eqA.measurableEmbedding).mpr hg)

theorem iterB (ψ : AddChar F Circle) (g : (Fin 2 × Fin 2 → F) → ℂ) (hg : Integrable g (mM ψ)) :
    ∫ X, g X ∂mM ψ = ∫ c, ∫ d, ∫ b, ∫ a, g (ent a b d c)
      ∂selfDualMeasure ψ ∂selfDualMeasure ψ ∂selfDualMeasure ψ ∂selfDualMeasure ψ := by
  rw [← (mpB ψ).integral_comp' g]
  exact int4 _ _ (((mpB ψ).integrable_comp_emb eqB.measurableEmbedding).mpr hg)

def toMH : (Fin 2 × Fin 2 → F) ≃ₜ Matrix (Fin 2) (Fin 2) F where
  toFun := toM
  invFun M := fun ij => M ij.1 ij.2
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_matrix fun i j => continuous_apply (i, j)
  continuous_invFun := continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1)

def nH (t : F) : Matrix (Fin 2) (Fin 2) F ≃ₜ Matrix (Fin 2) (Fin 2) F where
  toFun M := (uni2 (-t)).val * M
  invFun M := ((uni2 (-t))⁻¹ : GL (Fin 2) F).val * M
  left_inv M := Units.inv_mul_cancel_left _ M
  right_inv M := Units.mul_inv_cancel_left _ M
  continuous_toFun := continuous_const.matrix_mul continuous_id
  continuous_invFun := continuous_const.matrix_mul continuous_id

theorem schwartz_bruhat_unipotent_shift {p : Matrix (Fin 2) (Fin 2) F → ℂ} (hp : SB2 p) (t : F) :
    SB2 fun M => p ((uni2 (-t)).val * M) :=
  ⟨hp.1.comp_continuous (nH t).continuous, hp.2.comp_homeomorph (nH t)⟩

theorem integrable_sb (ψ : AddChar F Circle) {p : Matrix (Fin 2) (Fin 2) F → ℂ} (hp : SB2 p)
    {χ : (Fin 2 × Fin 2 → F) → ℂ} (hχ : Continuous χ) :
    Integrable (fun X => p (toM X) * χ X) (mM ψ) := by
  have hc : Continuous fun X : Fin 2 × Fin 2 → F => p (toM X) :=
    hp.1.continuous.comp (toMH (F := F)).continuous
  have hs : HasCompactSupport fun X : Fin 2 × Fin 2 → F => p (toM X) :=
    hp.2.comp_homeomorph (toMH (F := F))
  haveI : IsFiniteMeasureOnCompacts (mM ψ) := by
    unfold mM
    infer_instance
  exact (hc.mul hχ).integrable_of_hasCompactSupport hs.mul_right

theorem rr_mem (ψ : AddChar F Circle) {p : Matrix (Fin 2) (Fin 2) F → ℂ} (hp : SB2 p) :
    rr ψ p ∈ schwartzBruhat F := by
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun c₀ => ?_, ?_⟩
  · have hinv := GlobalTheory.LocFlat.PartialFourier.eventually_add_invariant
      (X := Matrix (Fin 2) (Fin 2) F) (f := p) ⟨hp.1, hp.2⟩
    have hcont : Continuous fun c : F => (!![0, 0; 0, c - c₀] : Matrix (Fin 2) (Fin 2) F) := by
      refine continuous_matrix fun i j => ?_
      fin_cases i <;> fin_cases j <;> simp <;> fun_prop
    have h2 : Filter.Tendsto (fun c : F => (!![0, 0; 0, c - c₀] : Matrix (Fin 2) (Fin 2) F))
        (𝓝 c₀) (𝓝 0) := by
      have h0 : (!![0, 0; 0, c₀ - c₀] : Matrix (Fin 2) (Fin 2) F) = 0 := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      simpa only [h0] using hcont.tendsto c₀
    filter_upwards [h2.eventually hinv] with c hc
    have key : ∀ a b d, p !![a, b; d, c] = p !![a, b; d, c₀] := fun a b d => by
      rw [← hc !![a, b; d, c₀]]
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    simp only [rr, key]
  · refine HasCompactSupport.intro (K := (fun M : Matrix (Fin 2) (Fin 2) F => M 1 1) '' tsupport p)
      (hp.2.image (by fun_prop)) fun c hc => ?_
    have h0 : ∀ a b d, p !![a, b; d, c] = 0 := fun a b d =>
      image_eq_zero_of_notMem_tsupport fun h => hc ⟨_, h, by simp⟩
    simp [rr, h0]

theorem uni2_mul_uni2_eq_uni2_add (t a b d c : F) :
    (uni2 (-t)).val * !![a, b; d, c] = !![a - t * d, b - t * c; d, c] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uni2, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem Rpart_shift (ψ : AddChar F Circle) (hψ : Continuous ψ) {p : Matrix (Fin 2) (Fin 2) F → ℂ}
    (hp : SB2 p) (t : F) :
    Rpart ψ (fun M => p ((uni2 (-t)).val * M)) =
      localFourier (selfDualMeasure ψ) ψ (rr ψ p) (-t) := by
  have hψc : Continuous fun x : F => (ψ x : ℂ) := continuous_subtype_val.comp hψ
  have hχ₀ : Continuous fun X : Fin 2 × Fin 2 → F => (ψ (-(X (0, 1) + X (1, 0))) : ℂ) :=
    hψc.comp (by fun_prop)
  have hχ₁ : Continuous fun X : Fin 2 × Fin 2 → F => (ψ (X (1, 1) * -t) : ℂ) :=
    hψc.comp (by fun_prop)
  have h₀ := integrable_sb ψ (schwartz_bruhat_unipotent_shift hp t) hχ₀
  have hχ₂ : Continuous fun X : Fin 2 × Fin 2 → F =>
      (ψ (-(X (0, 1) + X (1, 0))) : ℂ) * (ψ (X (1, 1) * -t) : ℂ) := hχ₀.mul hχ₁
  have h₁ := integrable_sb ψ hp hχ₂
  have e₀ : Rpart ψ (fun M => p ((uni2 (-t)).val * M)) =
      ∫ X, p (toM X) * ((ψ (-(X (0, 1) + X (1, 0))) : ℂ) * (ψ (X (1, 1) * -t) : ℂ)) ∂mM ψ := by
    rw [Rpart, iterB ψ _ h₀, iterB ψ _ h₁]
    refine integral_congr_ae (.of_forall fun c => ?_)
    refine integral_congr_ae (.of_forall fun d => ?_)
    simp only [ent_01, ent_10, ent_11, toM_ent, uni2_mul_uni2_eq_uni2_add]
    have s₁ : ∀ b, ∫ a, p !![a - t * d, b - t * c; d, c] * (ψ (-(b + d)) : ℂ) ∂selfDualMeasure ψ =
        ∫ a, p !![a, b - t * c; d, c] * (ψ (-(b + d)) : ℂ) ∂selfDualMeasure ψ := fun b =>
      integral_sub_right_eq_self (fun a => p !![a, b - t * c; d, c] * (ψ (-(b + d)) : ℂ)) (t * d)
    simp only [s₁]
    rw [← integral_sub_right_eq_self (μ := selfDualMeasure ψ)
      (fun b => ∫ a, p !![a, b; d, c] * ((ψ (-(b + d)) : ℂ) * (ψ (c * -t) : ℂ)) ∂selfDualMeasure ψ) (t * c)]
    refine integral_congr_ae (.of_forall fun b => ?_)
    refine integral_congr_ae (.of_forall fun a => ?_)
    have hk : (ψ (-(b + d)) : ℂ) = (ψ (-(b - t * c + d)) : ℂ) * (ψ (c * -t) : ℂ) := by
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    dsimp only
    rw [hk]
  rw [e₀, iterA ψ _ h₁]
  simp only [ent_01, ent_10, ent_11, toM_ent, localFourier, rr, ← integral_mul_const, mul_assoc]

end D

theorem integral_Rpart_shift : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ p : Matrix (Fin 2) (Fin 2) F → ℂ, SB2 p → ∫ t, (ψ t : ℂ) * Rpart ψ (fun M => p ((uni2 (-t)).val * M)) ∂selfDualMeasure ψ = rr ψ p 1 := by
  intro F _ _ _ _ _ _ ψ hs p hp
  obtain ⟨hc, h1, -⟩ := hs
  have hinv := localFourier_localFourier_selfDual hc h1 (rr_mem ψ hp) (-1)
  rw [neg_neg] at hinv
  rw [← hinv]
  simp only [Rpart_shift ψ hc hp]
  have := integral_neg_eq_self (fun t => localFourier (selfDualMeasure ψ) ψ (rr ψ p) t * (ψ (t * -1) : ℂ)) (selfDualMeasure ψ)
  rw [show localFourier (selfDualMeasure ψ) ψ (localFourier (selfDualMeasure ψ) ψ (rr ψ p)) (-1) =
    ∫ t, localFourier (selfDualMeasure ψ) ψ (rr ψ p) t * (ψ (t * -1) : ℂ) ∂selfDualMeasure ψ from rfl, ← this]
  refine integral_congr_ae (.of_forall fun t => ?_)
  simp [mul_comm]

end GlobalTheory.CompanionTheory.GL2DualWhittakerPair.FlR
