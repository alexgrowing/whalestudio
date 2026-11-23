import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ThetaSpanAdjoint
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CanonicalThetaExponentSymplecticInvariant
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EqOfSiegelThetaSeriesRationalEq
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsWeilOfSymplectic
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledRowTestFunctionPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ComplexPhaseCalculusRootOfUnity
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HeisenbergVacuumProjectionRootOfUnityPhasesStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsRationalSymplecticUnitaryColumnsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RootOfUnityPhaseVacuumSiegelThetaTransformStatement

section Siegel

open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real

namespace GlobalTheory.Phase.Mult

theorem thS_smul' {κ ι : Type} [Fintype κ] [Fintype ι] (c : ℂ) (φ : Matrix κ ι ℚ → ℂ) (τ : Matrix ι ι ℂ)
    (ζ : κ → ι → ℂ) : thS (c • φ) τ ζ = c * thS φ τ ζ := by
  unfold thS
  rw [← tsum_mul_left]
  congr 1
  funext x
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem isSB_smul' {κ ι : Type} [Fintype κ] [Fintype ι] (c : ℂ) {φ : Matrix κ ι ℚ → ℂ} (h : IsSB φ) :
    IsSB (c • φ) := by
  obtain ⟨R, hR, h1, h2⟩ := h
  refine ⟨R, hR, fun x hx => h1 x ?_, fun x y hy => ?_⟩
  · intro h0
    apply hx
    simp [h0]
  · simp only [Pi.smul_apply, smul_eq_mul]
    rw [h2 x y hy]

theorem quad_blk {n g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (ζ : Fin n × Fin g → ℂ) :
    ζ ⬝ᵥ blk n M *ᵥ ζ = ∑ k, (fun i => ζ (k, i)) ⬝ᵥ M *ᵥ fun i => ζ (k, i) := by
  simp only [dotProduct, mulVec, blk, Matrix.of_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem isMu_of_fixed {n g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ Siegel (Fin g))
    {s : Matrix ((Fin n × Fin g) ⊕ (Fin n × Fin g)) ((Fin n × Fin g) ⊕ (Fin n × Fin g)) ℚ}
    (hs : s ∈ Matrix.symplecticGroup (Fin n × Fin g) ℚ) (hfix : spAct s (blk n τ) = blk n τ)
    {d t : ℂ} (hd : (spDen s (blk n τ)).det * d = 1) (hd1 : ‖d‖ = 1) (ht : ‖t‖ = 1)
    {φ φ' : Matrix (Fin n) (Fin g) ℚ → ℂ} (hφ : PV φ) (hφ' : PV φ') (h0 : φ' ≠ 0)
    (H : ∀ ζ ζ' : Fin n × Fin g → ℂ, ζ' = ζ ᵥ* (spDen s (blk n τ))⁻¹ →
      cexp (π / 2 * ∑ k, (fun i => ζ' (k, i)) ⬝ᵥ (τ.map fun z => (z.im : ℂ))⁻¹ *ᵥ fun i => ζ' (k, i)) *
        thS φ' τ (fun k i => ζ' (k, i)) =
      t * (cexp (π / 2 * ∑ k, (fun i => ζ (k, i)) ⬝ᵥ (τ.map fun z => (z.im : ℂ))⁻¹ *ᵥ fun i => ζ (k, i)) *
        thS φ τ (fun k i => ζ (k, i)))) : IsMu (t ^ 2 * d) := by
  classical
  set B := blk n τ with hB
  set D := spDen s B with hD
  have hDu : IsUnit D.det := isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul_eq_one hd)
  have hsb : IsSB φ := by
    obtain ⟨A, ε, hv⟩ := hφ.1
    exact hv.sb
  have hsb' : IsSB φ' := by
    obtain ⟨A, ε, hv⟩ := hφ'.1
    exact hv.sb
  obtain ⟨hpvd, -, hsbd, -, hτB⟩ := GlobalTheory.T.doubledRowTestFunction_properties n g φ
  obtain ⟨hpvd', hned', hsbd', -, hτB'⟩ := GlobalTheory.T.doubledRowTestFunction_properties n g φ'
  obtain ⟨hBs, hthS, hImB⟩ := hτB τ hτ
  obtain ⟨-, hthS', -⟩ := hτB' τ hτ

  have hrel : ∀ ζ : Fin n × Fin g → ℂ, thS φ' τ (fun k i => (ζ ᵥ* D⁻¹) (k, i)) =
      t * cexp (π * I * (ζ ⬝ᵥ (D⁻¹ * qm s.toBlocks₂₁) *ᵥ ζ)) * thS φ τ (fun k i => ζ (k, i)) := by
    intro ζ
    have h1 := H ζ (ζ ᵥ* D⁻¹) rfl
    have hq : ∀ v : Fin n × Fin g → ℂ,
        ∑ k, (fun i => v (k, i)) ⬝ᵥ (τ.map fun z => (z.im : ℂ))⁻¹ *ᵥ (fun i => v (k, i)) =
          v ⬝ᵥ (B.map fun z => (z.im : ℂ))⁻¹ *ᵥ v := by
      intro v
      rw [hImB, quad_blk]
    rw [hq ζ, hq (ζ ᵥ* D⁻¹)] at h1
    have hc := canon_exponent_invariant (Fin n × Fin g) s hs B hBs ζ
    rw [hfix] at hc
    set a := ζ ⬝ᵥ (B.map fun z => (z.im : ℂ))⁻¹ *ᵥ ζ
    set a' := (ζ ᵥ* D⁻¹) ⬝ᵥ (B.map fun z => (z.im : ℂ))⁻¹ *ᵥ (ζ ᵥ* D⁻¹)
    set e := ζ ⬝ᵥ (D⁻¹ * qm s.toBlocks₂₁) *ᵥ ζ
    have ha' : a' = a - 2 * I * e := by rw [← hc]; ring
    have hexp : cexp (π / 2 * a') = cexp (π / 2 * a) * cexp (-(π * I * e)) := by
      rw [← Complex.exp_add, ha']
      congr 1
      ring
    rw [hexp] at h1
    have hne : cexp (π / 2 * a) ≠ 0 := Complex.exp_ne_zero _
    have h2 : cexp (-(π * I * e)) * thS φ' τ (fun k i => (ζ ᵥ* D⁻¹) (k, i)) =
        t * thS φ τ (fun k i => ζ (k, i)) := by
      apply mul_left_cancel₀ hne
      rw [← mul_assoc, h1]
      ring
    calc thS φ' τ (fun k i => (ζ ᵥ* D⁻¹) (k, i))
        = cexp (π * I * e) * (cexp (-(π * I * e)) * thS φ' τ (fun k i => (ζ ᵥ* D⁻¹) (k, i))) := by
          rw [← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
      _ = t * cexp (π * I * e) * thS φ τ (fun k i => ζ (k, i)) := by
          rw [h2]
          ring

  have hdup : ∀ Z : Fin 2 → Fin n × Fin g → ℂ, thS (dup φ') B (fun k => Z k ᵥ* D⁻¹) =
      t ^ 2 * cexp (π * I * ∑ k, Z k ⬝ᵥ (D⁻¹ * qm s.toBlocks₂₁) *ᵥ Z k) * thS (dup φ) B Z := by
    intro Z
    rw [hthS' hsb', hthS hsb, hrel (Z 0), hrel (Z 1), Fin.sum_univ_two, mul_add, Complex.exp_add]
    ring
  have heven : Even (Fintype.card (Fin 2)) := by
    rw [Fintype.card_fin]
    exact even_two
  obtain ⟨ω, hω⟩ := exists_weil_of_symplectic (Fin 2) (Fin n × Fin g) s heven hs
  obtain ⟨hsbω, hTω, -⟩ := hω (dup φ) (hsbd hsb)
  have hT : ∀ Z : Fin 2 → Fin n × Fin g → ℂ,
      cexp (π * I * ∑ k, Z k ⬝ᵥ (D⁻¹ * qm s.toBlocks₂₁) *ᵥ Z k) * thS (dup φ) B Z =
        d * thS (ω (dup φ)) B (fun k => Z k ᵥ* D⁻¹) := by
    intro Z
    have h1 := hTω B hBs Z
    rw [hfix, Fintype.card_fin] at h1
    rw [h1]
    calc cexp (π * I * ∑ k, Z k ⬝ᵥ (D⁻¹ * qm s.toBlocks₂₁) *ᵥ Z k) * thS (dup φ) B Z
        = (D.det * d) * (cexp (π * I * ∑ k, Z k ⬝ᵥ (D⁻¹ * qm s.toBlocks₂₁) *ᵥ Z k) *
            thS (dup φ) B Z) := by rw [hd, one_mul]
      _ = _ := by ring
  have hall : ∀ W : Fin 2 → Fin n × Fin g → ℂ,
      thS (dup φ') B W = thS ((t ^ 2 * d) • ω (dup φ)) B W := by
    intro W
    have hW : W = fun k => (W k ᵥ* D) ᵥ* D⁻¹ := by
      funext k
      rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hDu, Matrix.vecMul_one]
    rw [thS_smul', hW, hdup, mul_assoc, hT, ← hW]
    ring
  have heq := eq_of_thS_eq (Fin 2) (Fin n × Fin g) (dup φ') ((t ^ 2 * d) • ω (dup φ))
    (hsbd' hsb') (isSB_smul' _ hsbω) B hBs hall
  have hpvω : PV (ω (dup φ)) :=
    GlobalTheory.T.rootOfUnityPhaseVacuum_siegelThetaTransform (Fin 2) (Fin n × Fin g) heven s hs (dup φ) (ω (dup φ)) hsbω hTω (hpvd hφ)
  obtain ⟨x, hx⟩ := Function.ne_iff.mp (hned' h0)
  have hxe : dup φ' x = (t ^ 2 * d) * ω (dup φ) x := by
    rw [heq]
    rfl
  have hb0 : ω (dup φ) x ≠ 0 := by
    intro hz
    apply hx
    rw [hxe, hz, mul_zero]
    rfl
  have hph : Ph (t ^ 2 * d) :=
    GlobalTheory.Phase.Calc.ph_cancel hb0 (hpvω.2 x) (hxe ▸ (hpvd' hφ').2 x)
  refine GlobalTheory.Phase.Calc.isMu_of_ph hph ?_
  rw [norm_mul, norm_pow, ht, hd1]
  norm_num

end GlobalTheory.Phase.Mult

end Siegel

section Frames

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

namespace GlobalTheory.Phase.Mult

theorem isUnit_hMat_of_siegel {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (X : Data E r)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r)
    (h : tauMat X bas idx x ∈ Siegel (Fin g)) : IsUnit (ThFr.hMat X bas idx x).det := by
  by_cases hP : IsUnit (perMat X bas idx Sum.inl x).det
  · exact Matrix.isUnit_nonsing_inv_det _ hP
  · have h0 : ThFr.hMat X bas idx x = 0 := Matrix.nonsing_inv_apply_not_isUnit _ hP
    have ht : tauMat X bas idx x = 0 := by
      rw [ThFr.tauMat, h0, Matrix.zero_mul]
    rw [ht] at h
    rcases Nat.eq_zero_or_pos g with rfl | hg
    · rw [Matrix.det_fin_zero]
      exact isUnit_one
    · exfalso
      have hx : Finsupp.single (⟨0, hg⟩ : Fin g) (1 : ℝ) ≠ 0 := Finsupp.single_ne_zero.mpr one_ne_zero
      have := h.2.2 hx
      simp at this

theorem norm_det_unitary {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    {h : Matrix (Fin n) (Fin n) E} (hu : ccT h * h = 1) (σ : E →+* ℂ) : ‖σ h.det‖ = 1 := by
  have h1 : cc h.det * h.det = 1 := by
    have := congrArg Matrix.det hu
    rw [Matrix.det_mul, Matrix.det_one, ccT, Matrix.det_transpose] at this
    have hm : (h.map cc).det = cc h.det := by
      have := (IsCMField.complexConj E).toRingHom.map_det h
      rw [RingHom.mapMatrix_apply] at this
      exact this.symm
    rwa [hm] at this
  have h2 : conj (σ h.det) * σ h.det = 1 := by
    rw [← IsCMField.complexEmbedding_complexConj, ← map_mul]
    have : IsCMField.complexConj E h.det * h.det = 1 := h1
    rw [this, map_one]
  have h3 := congrArg (‖·‖) h2
  simp only [norm_mul, Complex.norm_conj, norm_one] at h3
  nlinarith [norm_nonneg (σ h.det)]

theorem isMu_multiplier_sq_mul_det : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ h : Matrix (Fin n) (Fin n) E, ccT h * h = 1 → ∀ Λ ∈ Vset E n 1, ∀ Λ' ∈ Vset E n 1, ∀ L : Lt E r, SelfD X L → ∀ v : TF n g, IsVac X bas w (tens (stdL E n) L) v → ∀ x ∈ X.dom, ∀ t : ℂ, ‖t‖ = 1 → (∀ z : Fin n → Fin g → ℂ, thA X bas idx (unitv (projA X bas w (tens Λ' L) v)) x (Dict.hAct X idx h z) = t * thA X bas idx (unitv (projA X bas w (tens Λ L) v)) x z) → IsMu (t ^ 2 * ∏ i : Fin g, rowType X (idx i) h.det) := by
  intro E _ _ _ r X g bas idx n hS hn w hw hwc h hu Λ hΛ Λ' hΛ' L hL v hv x hx t ht H
  obtain ⟨u, hu1, hU⟩ := GlobalTheory.T.heisenbergVacuum_projection_rootOfUnity_phases E r X g bas idx n hS hn w hw hwc L hL v hv
  obtain ⟨s, hs, hsx⟩ := GlobalTheory.T.exists_rational_symplectic_unitary_columns E r X g bas idx n hS hn h hu
  obtain ⟨hτ, hfix, hdet, hvec⟩ := hsx x hx
  obtain ⟨-, hpv, -⟩ := hU Λ hΛ
  obtain ⟨hvac', hpv', -⟩ := hU Λ' hΛ'
  have hMu : IsUnit (hMat X bas idx x).det := isUnit_hMat_of_siegel X bas idx x hτ
  have hd1 : ‖∏ i : Fin g, rowType X (idx i) h.det‖ = 1 := by
    rw [norm_prod]
    exact Finset.prod_eq_one fun i _ => norm_det_unitary hu _
  have hψ'0 : u • unitv (projA X bas w (tens Λ' L) v) ≠ 0 := by
    intro h0
    have hu0 : u ≠ 0 := by
      intro h
      rw [h, norm_zero] at hu1
      exact zero_ne_one hu1
    have hz : unitv (projA X bas w (tens Λ' L) v) = 0 := by
      funext y
      have := congrFun h0 y
      simpa [hu0] using this
    have h1 : ip (unitv (projA X bas w (tens Λ' L) v)) (unitv (projA X bas w (tens Λ' L) v)) = 1 :=
      hvac'.2.1
    rw [hz] at h1
    simp [GlobalTheory.SW.ip, GlobalTheory.SW.haar, GlobalTheory.SW.haarAt] at h1
  refine isMu_of_fixed hτ hs hfix hdet hd1 ht hpv hpv' hψ'0 ?_
  intro ζ ζ' hζ'
  obtain ⟨z, hz⟩ : ∃ z : Fin n → Fin g → ℂ, ∀ k, hMat X bas idx x *ᵥ z k = fun i => ζ (k, i) :=
    ⟨fun k => (hMat X bas idx x)⁻¹ *ᵥ fun i => ζ (k, i), fun k => by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hMu, Matrix.one_mulVec]⟩
  have hζ : (fun p : Fin n × Fin g => (hMat X bas idx x *ᵥ z p.1) p.2) = ζ := by
    funext p
    rw [hz p.1]
  have hz' : ∀ k, hMat X bas idx x *ᵥ Dict.hAct X idx h z k = fun i => ζ' (k, i) := by
    intro k
    funext i
    have := congrFun (hvec z) (k, i)
    rw [hζ, ← hζ'] at this
    exact this.symm
  have H1 := H z
  simp only [GlobalTheory.SW.thA, hz, hz', imInv_eq] at H1
  rw [thS_smul', thS_smul']
  have hne := pow_ne_zero (n / 2) hMu.ne_zero
  have H2 := mul_left_cancel₀ hne (by rw [← _root_.mul_assoc, H1]; ring :
    (hMat X bas idx x).det ^ (n / 2) *
      (cexp (Real.pi / 2 * ∑ k, (fun i => ζ' (k, i)) ⬝ᵥ ((tauMat X bas idx x).map fun z => (z.im : ℂ))⁻¹ *ᵥ
          (fun i => ζ' (k, i))) * thS (unitv (projA X bas w (tens Λ' L) v)) (tauMat X bas idx x)
          (fun k i => ζ' (k, i))) =
    (hMat X bas idx x).det ^ (n / 2) *
      (t * (cexp (Real.pi / 2 * ∑ k, (fun i => ζ (k, i)) ⬝ᵥ ((tauMat X bas idx x).map fun z => (z.im : ℂ))⁻¹ *ᵥ
          (fun i => ζ (k, i))) * thS (unitv (projA X bas w (tens Λ L) v)) (tauMat X bas idx x)
          (fun k i => ζ (k, i)))))
  linear_combination u * H2

end GlobalTheory.Phase.Mult

end Frames
