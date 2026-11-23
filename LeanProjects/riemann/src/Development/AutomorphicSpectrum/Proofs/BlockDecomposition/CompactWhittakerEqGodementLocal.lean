import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedBoundGL2
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PureTensorDecompositionLocal
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol

noncomputable section

namespace GlobalTheory.CompanionTheory.WcSplit

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def phiW (χ : AddChar F Circle) (Φ : F × F → ℂ) (x : Fin 2 → F) : ℂ :=
  ∫ r, Φ (x 0, r) * (χ (r * x 1) : ℂ) ∂selfDualMeasure χ

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in
theorem norm_pair (z : F × F) : Algebra.norm F z = z.1 * z.2 := by
  rw [Algebra.norm_eq_matrix_det (Module.Basis.finTwoProd F), Matrix.det_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, Module.Basis.finTwoProd_zero, Module.Basis.finTwoProd_one, Module.Basis.coe_finTwoProd_repr]
  simp

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in
theorem trace_pair (z : F × F) : Algebra.trace F (F × F) z = z.1 + z.2 := by
  rw [Algebra.trace_eq_matrix_trace (Module.Basis.finTwoProd F), Matrix.trace_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, Module.Basis.finTwoProd_zero, Module.Basis.finTwoProd_one, Module.Basis.coe_finTwoProd_repr]
  simp

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in
theorem nsg_pair {a : F} (ha : a ≠ 0) : GL2LocalData.nsg (F × F) a = 1 := by
  classical
  unfold GL2LocalData.nsg
  rw [if_pos]
  refine ⟨⟨(a, 1), (a⁻¹, 1), by ext <;> simp [ha], by ext <;> simp [ha]⟩, ?_⟩
  simp [norm_pair]

omit [MeasurableSpace F] [BorelSpace F] in
theorem slice_mem {Φ : F × F → ℂ} (hl : IsLocallyConstant Φ) (hc : HasCompactSupport Φ) (p : F) :
    (fun r => Φ (p, r)) ∈ schwartzBruhat F := by
  obtain ⟨n, f, g, -, hg, hfg⟩ := GlobalTheory.CompanionTheory.PureTensor.exists_pure_sum hl hc
  have : (fun r => Φ (p, r)) = ∑ i, f i p • g i := by
    funext r
    simp [hfg]
  rw [this]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hg i)

theorem phiW_pair (χ : AddChar F Circle) (Φ : F × F → ℂ) (p y : F) :
    phiW χ Φ ![p, y] = localFourier (selfDualMeasure χ) χ (fun r => Φ (p, r)) y := rfl

theorem integral_phiW {χ : AddChar F Circle} (hχ : IsStd χ) {Φ : F × F → ℂ}
    (hl : IsLocallyConstant Φ) (hc : HasCompactSupport Φ) (p r : F) :
    ∫ y, phiW χ Φ ![p, y] * (χ (-(y * r)) : ℂ) ∂selfDualMeasure χ = Φ (p, r) := by
  have h := localFourier_localFourier_selfDual hχ.1 hχ.2.1 (slice_mem hl hc p) (-r)
  rw [neg_neg] at h
  rw [← h]
  simp only [localFourier, phiW_pair, mul_neg]

theorem phiW_mem {χ : AddChar F Circle} (hχ : IsStd χ) {Φ : F × F → ℂ}
    (hl : IsLocallyConstant Φ) (hc : HasCompactSupport Φ) :
    phiW χ Φ ∈ GodementSectionLocal.schwartzBruhat2 F := by
  obtain ⟨n, f, g, hf, hg, hfg⟩ := GlobalTheory.CompanionTheory.PureTensor.exists_pure_sum hl hc
  have e : phiW χ Φ = ∑ i, fun x : Fin 2 → F =>
      f i (x 0) * localFourier (selfDualMeasure χ) χ (g i) (x 1) := by
    funext x
    simp only [phiW, hfg, Finset.sum_mul, Finset.sum_apply]
    rw [integral_finset_sum _ fun i _ => ?_]
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [localFourier, mul_assoc]
      exact integral_const_mul _ _
    · simp only [mul_assoc]
      exact (integrable_mul_char_of_mem_schwartzBruhat _ hχ.1 (hg i) (x 1)).const_mul _
  rw [e]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hb : localFourier (selfDualMeasure χ) χ (g i) ∈ schwartzBruhat F :=
    localFourier_mem_schwartzBruhat _ hχ.1 hχ.2.1 (hg i)
  refine GodementSectionLocal.mem_schwartzBruhat2.2
    ⟨((hf i).1.comp_continuous (continuous_apply 0)).mul (hb.1.comp_continuous (continuous_apply 1)), ?_⟩
  refine HasCompactSupport.intro
    (((hf i).2.isCompact.prod hb.2.isCompact).image (Homeomorph.finTwoArrow (X := F)).symm.continuous) fun x hx => ?_
  by_contra hne
  refine hx ⟨(x 0, x 1), ⟨subset_tsupport _ fun h => hne ?_, subset_tsupport _ fun h => hne ?_⟩, ?_⟩
  · simp [h]
  · simp [h]
  · ext j
    fin_cases j <;> simp

theorem integral_affine (ν : Measure F) [ν.IsAddHaarMeasure] {a : F} (ha : a ≠ 0) (b : F) (f : F → ℂ) :
    ∫ x, f (b + a * x) ∂ν = (((modulus a : ℝ)⁻¹ : ℝ) : ℂ) * ∫ x, f x ∂ν := by
  rw [integral_comp_mul_left ν ha (fun y => f (b + y)), integral_add_left_eq_self f b, Complex.real_smul]

end GlobalTheory.CompanionTheory.WcSplit

namespace GlobalTheory.CompanionTheory.WcSplit

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem rW_upper {χ : AddChar F Circle} (hχ : IsStd χ) {Φ : F × F → ℂ}
    (hl : IsLocallyConstant Φ) (hc : HasCompactSupport Φ) {α β δ : F} (hα : α ≠ 0) (hδ : δ ≠ 0) (u : Fˣ) :
    GL2LocalData.rW χ GL2LocalData.swapE ((selfDualMeasure χ).prod (selfDualMeasure χ)) 1 (α / (α * δ)) β (0 / (α * δ)) δ
                 (fun x => Φ (x * (α * δ, 1))) ((u : F), ((u⁻¹ : Fˣ) : F)) =
      mp u 1 * ∫ x, phiW χ Φ ![u * α, u * β + u * x * δ] * (χ (-x) : ℂ) ∂selfDualMeasure χ := by
  have hu : (u : F) ≠ 0 := u.ne_zero
  set r : F := ((u : F) * δ)⁻¹ with hr
  have key : ∀ x : F, phiW χ Φ ![u * α, u * β + u * x * δ] * (χ (-x) : ℂ) =
      (χ (β / δ) : ℂ) * (fun y => phiW χ Φ ![u * α, y] * (χ (-(y * r)) : ℂ)) (u * β + (u * δ) * x) := by
    intro x
    have e : -x = β / δ + -((u * β + (u * δ) * x) * r) := by
      rw [hr]; field_simp; ring
    simp only
    rw [show (u : F) * β + u * x * δ = u * β + (u * δ) * x by ring]
    conv_lhs => rw [e, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  simp only [key]
  have hI := integral_affine (selfDualMeasure χ) (mul_ne_zero hu hδ) (u * β)
    (fun y => phiW χ Φ ![u * α, y] * (χ (-(y * r)) : ℂ))
  rw [integral_const_mul, hI, integral_phiW hχ hl hc]
  have e0 : (0 : F) / (α * δ) = 0 := by simp
  have e1 : α / (α * δ) = δ⁻¹ := by field_simp
  have e2 : (u : F) * ((u⁻¹ : Fˣ) : F) = 1 := by simp
  unfold GL2LocalData.rW
  rw [if_pos e0, e1, nsg_pair (inv_ne_zero hδ), norm_pair]
  simp only [e2]
  have e3 : (algebraMap F (F × F) δ⁻¹ * ((u : F), ((u⁻¹ : Fˣ) : F))) * (α * δ, 1) = ((u : F) * α, r) := by
    ext
    · simp <;> field_simp
    · simp [hr] <;> field_simp
  rw [e3, show δ⁻¹ * β * 1 = β / δ by field_simp]
  simp only [mp, Complex.cpow_one, modulus_mul, modulus_inv]
  have hm : ((modulus (u : F) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast modulus_ne_zero hu
  push_cast
  field_simp

theorem rW_lower {χ : AddChar F Circle} (hχ : IsStd χ) {Φ : F × F → ℂ}
    (hl : IsLocallyConstant Φ) (hc : HasCompactSupport Φ) {α β γ δ Δ : F} (hγ : γ ≠ 0)
    (hΔ : Δ = α * δ - β * γ) (hΔ0 : Δ ≠ 0) (u : Fˣ) :
    GL2LocalData.rW χ GL2LocalData.swapE ((selfDualMeasure χ).prod (selfDualMeasure χ)) 1 (α / Δ) β (γ / Δ) δ
                 (fun x => Φ (x * (Δ, 1))) ((u : F), ((u⁻¹ : Fˣ) : F)) =
      mp u 1 * ∫ x, phiW χ Φ ![u * α + u * x * γ, u * β + u * x * δ] * (χ (-x) : ℂ) ∂selfDualMeasure χ := by
  have hu : (u : F) ≠ 0 := u.ne_zero
  have hχc : Continuous fun x => (χ x : ℂ) := continuous_subtype_val.comp hχ.1
  set T : F → F → F := fun p r => α / γ + (δ / γ) * (p * r) + (-((u : F) * γ)⁻¹) * p + (-(u * Δ / γ)) * r with hT
  set Kf : F → F → ℂ := fun p r => (χ (T p r) : ℂ) * Φ (p, r) with hKf
  have hΦe : HasCompactSupport (fun U : F × F => Φ (Δ * U.1, U.2)) :=
    hc.comp_homeomorph ((Homeomorph.mulLeft₀ Δ hΔ0).prodCongr (Homeomorph.refl F))
  have hint : Integrable (fun U : F × F => Kf (Δ * U.1) U.2)
      ((selfDualMeasure χ).prod (selfDualMeasure χ)) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ hΦe.mul_left
    refine (hχc.comp ?_).mul (hl.continuous.comp ?_)
    · simp only [hT]; fun_prop
    · fun_prop

  have hL : ∫ U : F × F, (χ ((α / Δ * Algebra.norm F (((u : F), ((u⁻¹ : Fˣ) : F)) : F × F) +
        δ * Algebra.norm F U - Algebra.trace F (F × F) (GL2LocalData.swapE (((u : F), ((u⁻¹ : Fˣ) : F)) : F × F) * U)) /
        (γ / Δ)) : ℂ) * Φ (U * (Δ, 1)) ∂((selfDualMeasure χ).prod (selfDualMeasure χ)) =
      (((modulus Δ : ℝ)⁻¹ : ℝ) : ℂ) * ∫ p, ∫ r, Kf p r ∂selfDualMeasure χ ∂selfDualMeasure χ := by
    have e : ∀ U : F × F, (χ ((α / Δ * Algebra.norm F (((u : F), ((u⁻¹ : Fˣ) : F)) : F × F) +
        δ * Algebra.norm F U - Algebra.trace F (F × F) (GL2LocalData.swapE (((u : F), ((u⁻¹ : Fˣ) : F)) : F × F) * U)) /
        (γ / Δ)) : ℂ) * Φ (U * (Δ, 1)) = Kf (Δ * U.1) U.2 := by
      rintro ⟨a, b⟩
      have hs : GL2LocalData.swapE (((u : F), ((u⁻¹ : Fˣ) : F)) : F × F) = (((u⁻¹ : Fˣ) : F), (u : F)) := rfl
      have e1 : (α / Δ * Algebra.norm F (((u : F), ((u⁻¹ : Fˣ) : F)) : F × F) +
          δ * Algebra.norm F ((a, b) : F × F) - Algebra.trace F (F × F)
            (GL2LocalData.swapE (((u : F), ((u⁻¹ : Fˣ) : F)) : F × F) * (a, b))) / (γ / Δ) = T (Δ * a) b := by
        rw [hs, norm_pair, norm_pair, trace_pair]
        simp only [hT, Prod.mk_mul_mk, Units.val_inv_eq_inv_val]
        field_simp
        ring
      rw [e1]
      simp only [hKf, Prod.mk_mul_mk, mul_one, mul_comm a Δ]
    simp only [e]
    rw [integral_prod _ hint]
    have := integral_comp_mul_left (selfDualMeasure χ) hΔ0 (fun p => ∫ r, Kf p r ∂selfDualMeasure χ)
    rw [this, Complex.real_smul]

  have key : ∀ x : F, phiW χ Φ ![u * α + u * x * γ, u * β + u * x * δ] * (χ (-x) : ℂ) =
      (fun p => ∫ r, Kf p r ∂selfDualMeasure χ) (u * α + (u * γ) * x) := by
    intro x
    simp only [phiW, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
    have e : T (u * α + (u * γ) * x) r = r * (u * β + u * x * δ) + -x := by
      simp only [hT, hΔ]
      field_simp
      ring
    simp only [hKf, e, AddChar.map_add_eq_mul, Circle.coe_mul]
    rw [show (u : F) * α + u * x * γ = u * α + (u * γ) * x by ring]
    ring
  simp only [key]
  have hI := integral_affine (selfDualMeasure χ) (mul_ne_zero hu hγ) (u * α)
    (fun p => ∫ r, Kf p r ∂selfDualMeasure χ)
  rw [hI]
  unfold GL2LocalData.rW
  rw [if_neg (div_ne_zero hγ hΔ0), nsg_pair (neg_ne_zero.2 (div_ne_zero hγ hΔ0)), hL]
  simp only [mp, Complex.cpow_one, modulus_mul, modulus_inv, div_eq_mul_inv]
  have hm : ((modulus (u : F) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast modulus_ne_zero hu
  have hm2 : ((modulus Δ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast modulus_ne_zero hΔ0
  have hm3 : ((modulus γ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast modulus_ne_zero hγ
  push_cast
  field_simp

theorem rW_eq {χ : AddChar F Circle} (hχ : IsStd χ) {Φ : F × F → ℂ}
    (hl : IsLocallyConstant Φ) (hc : HasCompactSupport Φ) (g : GL (Fin 2) F) (u : Fˣ) :
    GL2LocalData.rW χ GL2LocalData.swapE ((selfDualMeasure χ).prod (selfDualMeasure χ)) 1 (g.val 0 0 / (g.val).det) (g.val 0 1)
                 (g.val 1 0 / (g.val).det) (g.val 1 1) (fun x => Φ (x * ((g.val).det, 1))) ((u : F), ((u⁻¹ : Fˣ) : F)) =
      mp u 1 * ∫ x, phiW χ Φ (Matrix.vecMul ![(u : F), u * x] (g : Matrix (Fin 2) (Fin 2) F)) * (χ (-x) : ℂ)
        ∂selfDualMeasure χ := by
  have hd0 : (g.val).det ≠ 0 := (Matrix.isUnits_det_units g).ne_zero
  have hv : ∀ x : F, Matrix.vecMul ![(u : F), u * x] (g : Matrix (Fin 2) (Fin 2) F) =
      ![u * g.val 0 0 + u * x * g.val 1 0, u * g.val 0 1 + u * x * g.val 1 1] := by
    intro x
    ext j
    fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  simp only [hv]
  have hdet : (g.val).det = g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0 := Matrix.det_fin_two _
  by_cases hγ : g.val 1 0 = 0
  · have hd : (g.val).det = g.val 0 0 * g.val 1 1 := by rw [hdet, hγ]; ring
    have hα : g.val 0 0 ≠ 0 := fun h => hd0 (by rw [hd, h, zero_mul])
    have hδ : g.val 1 1 ≠ 0 := fun h => hd0 (by rw [hd, h, mul_zero])
    rw [hd, hγ]
    have := rW_upper hχ hl hc (β := g.val 0 1) hα hδ u
    simpa using this
  · exact rW_lower hχ hl hc hγ hdet hd0 u

end GlobalTheory.CompanionTheory.WcSplit

open GlobalTheory.CompanionTheory.WcSplit in

theorem GlobalTheory.CompanionTheory.WcSplit.compact_whittaker_eq_godement : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle), IsStd χ → ∀ c₁ c₂ : Fˣ →* ℂˣ, IsUnit1 c₁ → IsUnit1 c₂ → ∀ Φ : F × F → ℂ, IsLocallyConstant Φ → HasCompactSupport Φ → ∃ φ ∈ GodementSectionLocal.schwartzBruhat2 F, GL2LocalData.WcS χ c₁ c₂ Φ = W2 χ c₂ c₁ φ := by
  intro F _ _ _ _ _ _ χ hχ c₁ c₂ _ _ Φ hl hc
  refine ⟨phiW χ Φ, phiW_mem hχ hl hc, ?_⟩
  funext g
  simp only [GL2LocalData.WcS, W2]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [rW_eq hχ hl hc g u, Units.val_mul]
  ring
