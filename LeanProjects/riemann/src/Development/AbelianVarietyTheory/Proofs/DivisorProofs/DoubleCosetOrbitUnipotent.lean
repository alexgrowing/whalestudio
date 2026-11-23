import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegFamConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelEisensteinDoubled
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelWeilAnisotropicHermitian
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling

noncomputable section

namespace GlobalTheory.UnipSpNorm

open GlobalTheory.ThKLiftCusp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem mat_mul' {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

theorem mat_mul_inv {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g * mat g⁻¹ = 1 :=
  g.1.mul_inv

theorem mat_inv_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g⁻¹ * mat g = 1 :=
  g.1.inv_mul

theorem formA_col {d j : ℕ} (J : Matrix (Fin d) (Fin d) E) (Y : Matrix (Fin d) (Fin j) E) (z : Fin d → AE F E) (k : Fin j) :
    formA σ J z (incV F fun i => Y i k) = (z ᵥ* (incM F J * (incM F Y).map (cA σ))) k := by
  unfold formA
  rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_vecMul]
  rfl

theorem perp_map {d j : ℕ} {J : Matrix (Fin d) (Fin d) E} (Y : Matrix (Fin d) (Fin j) E) (h : UA σ J)
    (C : Matrix (Fin j) (Fin j) (AE F E)) (hC : mat h⁻¹ * incM F Y = incM F Y * C) (v : Fin d → AE F E)
    (hv : v ᵥ* (incM F J * (incM F Y).map (cA σ)) = 0) :
    (mat h *ᵥ v) ᵥ* (incM F J * (incM F Y).map (cA σ)) = 0 := by
  have hiso : (mat h)ᵀ * incM F J * (mat h).map (cA σ) = incM F J := h.2
  have hmap : ∀ M N : Matrix (Fin d) (Fin d) (AE F E), (M * N).map (cA σ) = M.map (cA σ) * N.map (cA σ) :=
    fun M N => Matrix.map_mul (f := (cA σ).toRingHom)
  have hmap' : ((mat h⁻¹) * incM F Y).map (cA σ) = (mat h⁻¹).map (cA σ) * (incM F Y).map (cA σ) :=
    Matrix.map_mul (f := (cA σ).toRingHom)
  have hmap'' : (incM F Y * C).map (cA σ) = (incM F Y).map (cA σ) * C.map (cA σ) :=
    Matrix.map_mul (f := (cA σ).toRingHom)
  have h1 : (mat h).map (cA σ) * (mat h⁻¹).map (cA σ) = 1 := by
    rw [← hmap, mat_mul_inv]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have h2 : (mat h)ᵀ * incM F J = incM F J * (mat h⁻¹).map (cA σ) := by
    calc (mat h)ᵀ * incM F J = (mat h)ᵀ * incM F J * ((mat h).map (cA σ) * (mat h⁻¹).map (cA σ)) := by
          rw [h1, Matrix.mul_one]
      _ = incM F J * (mat h⁻¹).map (cA σ) := by rw [← Matrix.mul_assoc, hiso]
  rw [← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, h2, Matrix.mul_assoc, ← hmap', hC,
    hmap'', ← Matrix.mul_assoc, ← Matrix.vecMul_vecMul, hv, Matrix.zero_vecMul]

theorem perp_iff {d j : ℕ} (J : Matrix (Fin d) (Fin d) E) (Y : Matrix (Fin d) (Fin j) E) (z : Fin d → AE F E) :
    (∀ k, formA σ J z (incV F fun i => Y i k) = 0) ↔ z ᵥ* (incM F J * (incM F Y).map (cA σ)) = 0 := by
  simp only [formA_col, funext_iff, Pi.zero_apply]

theorem conj_gen {d j : ℕ} (W : Spc F E d) (Y : Matrix (Fin d) (Fin j) E) (g : UA σ W.J)
    (C C' : Matrix (Fin j) (Fin j) (AE F E)) (hC : mat g * incM F Y = incM F Y * C)
    (hC' : mat g⁻¹ * incM F Y = incM F Y * C') (u : UA σ W.J)
    (hu : u ∈ {u : UA σ W.J | mat u * incM F Y = incM F Y ∧
      (∀ z, (∀ k, formA σ W.J z (incV F fun i => Y i k) = 0) → ∃ a, mat u *ᵥ z = z + incM F Y *ᵥ a) ∧
      ∀ z k, formA σ W.J (mat u *ᵥ z - z) (incV F fun i => Y i k) = 0}) :
    g * u * g⁻¹ ∈ {u : UA σ W.J | mat u * incM F Y = incM F Y ∧
      (∀ z, (∀ k, formA σ W.J z (incV F fun i => Y i k) = 0) → ∃ a, mat u *ᵥ z = z + incM F Y *ᵥ a) ∧
      ∀ z k, formA σ W.J (mat u *ᵥ z - z) (incV F fun i => Y i k) = 0} := by
  obtain ⟨hu1, hu2, hu3⟩ := hu
  have hm : mat (g * u * g⁻¹) = mat g * mat u * mat g⁻¹ := rfl
  have hCi : mat g⁻¹⁻¹ * incM F Y = incM F Y * C := by rw [inv_inv]; exact hC
  have hback : ∀ z, mat g *ᵥ (mat g⁻¹ *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, mat_mul_inv, Matrix.one_mulVec]
  refine ⟨?_, fun z hz => ?_, fun z k => ?_⟩
  · rw [hm, Matrix.mul_assoc, hC', ← Matrix.mul_assoc, Matrix.mul_assoc (mat g), hu1, Matrix.mul_assoc, ← hC',
      ← Matrix.mul_assoc, mat_mul_inv, Matrix.one_mul]
  · have hw := perp_map (J := W.J) Y g⁻¹ C hCi z ((perp_iff W.J Y z).1 hz)
    obtain ⟨a, ha⟩ := hu2 _ ((perp_iff W.J Y _).2 hw)
    refine ⟨C *ᵥ a, ?_⟩
    rw [hm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_add, hback, Matrix.mulVec_mulVec, hC,
      ← Matrix.mulVec_mulVec]
  · have h3 : mat (g * u * g⁻¹) *ᵥ z - z = mat g *ᵥ (mat u *ᵥ (mat g⁻¹ *ᵥ z) - mat g⁻¹ *ᵥ z) := by
      rw [Matrix.mulVec_sub, hback, hm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have h4 := (perp_iff W.J Y _).1 fun k => hu3 (mat g⁻¹ *ᵥ z) k
    rw [h3]
    exact (perp_iff W.J Y _).2 (perp_map (J := W.J) Y g C' hC' _ h4) k

theorem span_stable {d j : ℕ} (W : Spc F E d) (W₂ : Spc F E (d + d))
    (i : UA σ W.J × UA σ W.J →* UA σ W₂.J) (hi : ∀ h h', mat (i (h, h')) = blkMat finSumFinEquiv (mat h) (mat h'))
    (γ : UA σ W₂.J) (Y : Matrix (Fin d) (Fin j) E)
    (hiff : ∀ y : Fin d → E, (mat γ *ᵥ pairVec finSumFinEquiv 0 (incV F y) ∈ diagSub (AE F E) finSumFinEquiv ↔
        ∃ a : Fin j → E, y = Y *ᵥ a))
    (g : UA σ W.J) (hg : g ∈ ratU σ W.J)
    (hP : γ * i (1, g) * γ⁻¹ ∈ siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) :
    ∃ C : Matrix (Fin j) (Fin j) (AE F E), mat g * incM F Y = incM F Y * C := by
  obtain ⟨g₀, hg₀⟩ := MonoidHom.mem_range.1 (Subgroup.mem_subgroupOf.1 hg)
  have hm : mat g = (g₀ : Matrix (Fin d) (Fin d) E).map (inclR (F := F) (AF F)) := by
    show g.1.val = _
    rw [← hg₀]; rfl
  have hv : ∀ y, mat g *ᵥ incV F y = incV F ((g₀ : Matrix (Fin d) (Fin d) E) *ᵥ y) := fun y => by
    rw [hm]; funext k
    simp [incV, Matrix.mulVec, dotProduct, map_sum, map_mul]
  have hP' : ∀ x, x ∈ diagSub (AE F E) finSumFinEquiv ↔ mat (γ * i (1, g) * γ⁻¹) *ᵥ x ∈ diagSub (AE F E) finSumFinEquiv :=
    fun x => hP x
  have key : ∀ a : Fin j → E, ∃ b, (g₀ : Matrix (Fin d) (Fin d) E) *ᵥ (Y *ᵥ a) = Y *ᵥ b := by
    intro a
    have h2 := (hP' _).1 ((hiff (Y *ᵥ a)).2 ⟨a, rfl⟩)
    have h3 : mat (γ * i (1, g) * γ⁻¹) *ᵥ (mat γ *ᵥ pairVec finSumFinEquiv 0 (incV F (Y *ᵥ a))) =
        mat γ *ᵥ pairVec finSumFinEquiv 0 (incV F ((g₀ : Matrix (Fin d) (Fin d) E) *ᵥ (Y *ᵥ a))) := by
      rw [mat_mul', mat_mul', Matrix.mulVec_mulVec, Matrix.mul_assoc, mat_inv_mul, Matrix.mul_one,
        ← Matrix.mulVec_mulVec, hi, blkMat_mulVec, ← hv, Matrix.mulVec_zero]
    rw [h3] at h2
    exact (hiff _).1 h2
  choose b hb using key
  refine ⟨incM F (Matrix.of fun l k => b (Pi.single k 1) l), ?_⟩
  have hA : (g₀ : Matrix (Fin d) (Fin d) E) * Y = Y * Matrix.of fun l k => b (Pi.single k 1) l := by
    ext i' k
    have := congrFun (hb (Pi.single k 1)) i'
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.col_apply] at this
    rw [this, Matrix.mul_apply]
    simp [Matrix.mulVec, dotProduct]
  rw [hm]
  show _ * Y.map _ = Y.map _ * _
  rw [← Matrix.map_mul, hA, Matrix.map_mul]
  rfl

theorem conj_mem_unipSp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (B : Base F E) (d r s : ℕ) (W : Spc F E d), W.IsSkew σ B r s →
    ∀ W₂ : Spc F E (d + d), W₂.J = dblGram finSumFinEquiv W.J →
    ∀ i : UA σ W.J × UA σ W.J →* UA σ W₂.J, (∀ h h', mat (i (h, h')) = blkMat finSumFinEquiv (mat h) (mat h')) →
    ∀ γ ∈ ratU σ W₂.J, ∀ (j : ℕ) (Y : Matrix (Fin d) (Fin j) E), Function.Injective Y.mulVec →
      (∀ k l, form σ W.J (fun a => Y a k) (fun a => Y a l) = 0) →
      (∀ y : Fin d → E, (mat γ *ᵥ pairVec finSumFinEquiv 0 (incV F y) ∈ diagSub (AE F E) finSumFinEquiv ↔
        ∃ a : Fin j → E, y = Y *ᵥ a)) →
    ∀ g ∈ ratU σ W.J, γ * i (1, g) * γ⁻¹ ∈ siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype →
      ∀ n ∈ GlobalTheory.ThKLiftCusp.unipSp σ W Y, g * n * g⁻¹ ∈ GlobalTheory.ThKLiftCusp.unipSp σ W Y := by
  intro F E _ _ _ _ _ σ _hcm B d r s W _hW W₂ _hW₂ i hi γ _hγ j Y _hY _hiso hiff g hg hP n hn
  obtain ⟨C, hC⟩ := span_stable W W₂ i hi γ Y hiff g hg hP
  have hP2 : γ * i (1, g⁻¹) * γ⁻¹ ∈ siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype := by
    have e : γ * i (1, g⁻¹) * γ⁻¹ = (γ * i (1, g) * γ⁻¹)⁻¹ := by
      rw [show ((1 : UA σ W.J), g⁻¹) = ((1 : UA σ W.J), g)⁻¹ by simp, map_inv]
      group
    rw [e]; exact inv_mem hP
  obtain ⟨C', hC'⟩ := span_stable W W₂ i hi γ Y hiff g⁻¹ (inv_mem hg) hP2
  unfold GlobalTheory.ThKLiftCusp.unipSp at hn ⊢
  induction hn using Subgroup.closure_induction with
  | mem x hx => exact Subgroup.subset_closure (conj_gen W Y g C C' hC hC' x hx)
  | one => simp
  | mul x y _ _ hx hy =>
    have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [e]; exact mul_mem hx hy
  | inv x _ hx =>
    have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [e]; exact inv_mem hx

end GlobalTheory.UnipSpNorm
