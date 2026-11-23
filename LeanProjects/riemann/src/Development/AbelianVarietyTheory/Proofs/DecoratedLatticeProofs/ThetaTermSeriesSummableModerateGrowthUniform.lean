import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateAbsSumWeilTranslateModerateGrowthStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedThetaSeriesTermsLawsUnipotentRationalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf.SigConv

variable {D : D7}

theorem mt_jX_eq {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {n : GA D V} (hn : n ∈ flagN d) :
    mt V n ⬝ d.jX = d.jX ⬝ blockX d n := by
  obtain ⟨T, b, -, h1, -⟩ := exists_blocks d hn
  have e3 : blockX d n = 1 + T := by
    rw [blockX, h1, Matrix.mul_add, d.pX_jX, cancel₂ d.pX_jX, Matrix.one_mul]
  rw [e3, h1, Matrix.mul_add, Matrix.mul_one]

theorem blockX_mul_inv {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {n : GA D V} (hn : n ∈ flagN d) :
    blockX d n ⬝ blockX d n⁻¹ = 1 := by
  have h1 := mt_jX_eq d (inv_mem hn)
  have h2 := mt_jX_eq d hn
  have h3 : d.jX ⬝ (blockX d n ⬝ blockX d n⁻¹) = d.jX := by
    rw [← Matrix.mul_assoc, ← h2, Matrix.mul_assoc, ← h1, ← Matrix.mul_assoc, ← mt_mul, mul_inv_cancel, mt_one,
      Matrix.one_mul]
  have h4 : d.pX ⬝ (d.jX ⬝ (blockX d n ⬝ blockX d n⁻¹)) = d.pX ⬝ d.jX := by rw [h3]
  rwa [← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul] at h4

theorem blockX_rat {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {γ : GA D V} (hγ : γ ∈ GQ V) :
    ∃ B : Matrix (Fin ρ) (Fin ρ) D.host.E, rat B = blockX d γ :=
  mem_ratMx.1 (ratMx_mul (rat_mem d.qX) (ratMx_mul ((mem_GQ_iff V γ).1 hγ) (rat_mem d.e)))

def sumAbs (ψ : AddChar (AF D.host.F) ℂ) {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (W : HSp D)
    (vS : VolM D W.rank ρ) (Ψ : WO V W → ℂ) : ENNReal :=
  ∑' x : Matrix (Fin W.rank) (Fin ρ) D.host.E, ‖term ψ d W vS Ψ x‖ₑ

end GlobalTheory.Unf.SigConv

open GlobalTheory.Unf.SigConv in

theorem GlobalTheory.Unf.sum_term_bound : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (Φ : WO V W → ℂ), IsThetaFunO ψ V W Φ → ∃ (C : ℝ) (A : ℕ), ∀ g h, ∀ n ∈ flagN d, ∑' x : Matrix (Fin W.rank) (Fin ρ) D.host.E, ‖term ψ d W vS (om (n * g, h) Φ) x‖ₑ ≤ ENNReal.ofReal (C * (height V g * quotHeight W h) ^ A) := by
  intro D ψ V V₀ W ρ d χV χW om om' hW hW' vS Φ hΦ
  obtain ⟨C, A, hC⟩ := GlobalTheory.T.mixedCoordinate_absSum_weilTranslate_moderateGrowth D ψ V W χV χW om hW V₀ ρ d vS Φ hΦ
  have hT := fun Ψ (hΨ : IsThetaFunO ψ V W Ψ) => GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hW hW' vS Ψ hΨ

  have hA : ∀ g h, sumAbs ψ d W vS (om (g, h) Φ) ≤ ENNReal.ofReal (C * (height V g * height W h) ^ A) := by
    intro g h
    refine le_trans ?_ (hC g h 0)
    exact ENNReal.tsum_comp_le_tsum_of_injective (f := fun x : Matrix (Fin W.rank) (Fin ρ) D.host.E =>
        (⟨rat x, rat_mem x⟩ : ratMx D W.rank ρ))
      (fun x y hxy => rat_injective (congrArg Subtype.val hxy))
      (fun y : ratMx D W.rank ρ => ‖d.mixS W ψ vS.μ vS.𝓕 (om (g, h) Φ) y 0‖ₑ)

  have hB : ∀ Ψ, IsThetaFunO ψ V W Ψ → ∀ γ ∈ GQ V, γ ∈ flagN d →
      sumAbs ψ d W vS (om (γ, 1) Ψ) ≤ sumAbs ψ d W vS Ψ := by
    intro Ψ hΨ γ hQ hN
    obtain ⟨B, hB⟩ := blockX_rat d hQ
    have key : ∀ x, term ψ d W vS (om (γ, 1) Ψ) x = term ψ d W vS Ψ (x * B) :=
      fun x => (hT Ψ hΨ).2.1 γ hQ hN x (x * B) (by rw [rat_mul, hB])
    unfold sumAbs
    simp only [key]
    refine ENNReal.tsum_comp_le_tsum_of_injective (f := fun x => x * B) ?_ (fun y => ‖term ψ d W vS Ψ y‖ₑ)
    intro x y hxy
    apply rat_injective
    have hxy' : x * B = y * B := hxy
    have h5 := congrArg (fun z : Matrix (Fin W.rank) (Fin ρ) D.host.E => (rat z : Mx D W.rank ρ) ⬝ blockX d γ⁻¹) hxy'
    simp only [rat_mul, hB, Matrix.mul_assoc, blockX_mul_inv d hN, Matrix.mul_one] at h5
    exact h5

  have hD : ∀ Ψ, IsThetaFunO ψ V W Ψ → ∀ δ ∈ GQ W,
      sumAbs ψ d W vS (om (1, δ⁻¹) Ψ) ≤ sumAbs ψ d W vS Ψ := by
    intro Ψ hΨ δ hQ
    obtain ⟨M, hM⟩ := mem_ratMx.1 ((mem_GQ_iff W δ).1 hQ)
    have key : ∀ x, term ψ d W vS (om (1, δ⁻¹) Ψ) x = term ψ d W vS Ψ (M * x) :=
      fun x => (hT Ψ hΨ).2.2.1 δ⁻¹ (inv_mem hQ) x (M * x)
        (by rw [rat_mul, hM, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul])
    unfold sumAbs
    simp only [key]
    refine ENNReal.tsum_comp_le_tsum_of_injective (f := fun x => M * x) ?_ (fun y => ‖term ψ d W vS Ψ y‖ₑ)
    intro x y hxy
    apply rat_injective
    have hxy' : M * x = M * y := hxy
    have h5 := congrArg (fun z : Matrix (Fin W.rank) (Fin ρ) D.host.E => mt W δ⁻¹ ⬝ (rat z : Mx D W.rank ρ)) hxy'
    simp only [rat_mul, hM, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul] at h5
    exact h5

  obtain ⟨K, hK, hcov⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D V ρ d.e (isIsoSub_e d)).1
  obtain ⟨c, hc⟩ := exists_height_le_of_isCompact V (hK.image continuous_subtype_val)
  set c' := max c 1 with hc'
  set C₀ := max C 0 with hC₀
  have hc'1 : 1 ≤ c' := le_max_right _ _
  have hC₀0 : 0 ≤ C₀ := le_max_right _ _
  set C' := C₀ * c' ^ A with hC'
  have hC'0 : 0 ≤ C' := mul_nonneg hC₀0 (pow_nonneg (zero_le_one.trans hc'1) _)

  have hN : ∀ g h, ∀ n ∈ flagN d, sumAbs ψ d W vS (om (n * g, h) Φ) ≤
      ENNReal.ofReal (C' * (height V g * height W h) ^ A) := by
    intro g h n hn
    obtain ⟨γ, hγ, k, hk, hnk⟩ := hcov ⟨n, hn⟩
    have hγQ : γ.1 ∈ GQ V := Subgroup.mem_subgroupOf.1 hγ
    have hn' : n = γ.1 * k.1 := congrArg Subtype.val hnk
    have hp : ((n * g, h) : GA D V × GA D W) = (γ.1, 1) * (k.1 * g, h) := by
      rw [hn']; ext <;> simp [mul_assoc]
    have hom : om (n * g, h) Φ = om (γ.1, 1) (om (k.1 * g, h) Φ) := by
      rw [hp, map_mul, Module.End.mul_apply]
    rw [hom]
    refine (hB _ (hW.om_pres _ _ hΦ) γ.1 hγQ γ.2).trans ((hA _ _).trans (ENNReal.ofReal_le_ofReal ?_))
    have hk' : height V k.1 ≤ c' := (hc _ ⟨k, hk, rfl⟩).trans (le_max_left _ _)
    have hkg : height V (k.1 * g) ≤ c' * height V g :=
      (height_mul_le V _ _).trans (mul_le_mul_of_nonneg_right hk' (height_pos V g).le)
    have hx0 : 0 ≤ height V (k.1 * g) * height W h := mul_nonneg (height_pos V _).le (height_pos W h).le
    have hx : height V (k.1 * g) * height W h ≤ c' * (height V g * height W h) := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hkg (height_pos W h).le
    calc C * (height V (k.1 * g) * height W h) ^ A ≤ C₀ * (height V (k.1 * g) * height W h) ^ A :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hx0 _)
      _ ≤ C₀ * (c' * (height V g * height W h)) ^ A :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0 hx _) hC₀0
      _ = C' * (height V g * height W h) ^ A := by rw [mul_pow, hC', mul_assoc]
  refine ⟨C', A, fun g h n hn => ?_⟩

  have hδ : ∀ δ : GQ W, sumAbs ψ d W vS (om (n * g, h) Φ) ≤
      ENNReal.ofReal (C' * (height V g * max (height W (δ.1 * h)) 0) ^ A) := by
    intro δ
    rw [max_eq_left (height_pos W _).le]
    have hp : ((n * g, h) : GA D V × GA D W) = (1, δ.1⁻¹) * (n * g, δ.1 * h) := by
      ext <;> simp [← mul_assoc]
    have hom : om (n * g, h) Φ = om (1, δ.1⁻¹) (om (n * g, δ.1 * h) Φ) := by
      rw [hp, map_mul, Module.End.mul_apply]
    rw [hom]
    exact (hD _ (hW.om_pres _ _ hΦ) δ.1 δ.2).trans (hN g _ n hn)
  let φ : ℝ → ENNReal := fun t => ENNReal.ofReal (C' * (height V g * max t 0) ^ A)
  have hmono : Monotone φ := by
    intro a b hab
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hC'0
    apply pow_le_pow_left₀ (mul_nonneg (height_pos V g).le (le_max_right _ _))
    exact mul_le_mul_of_nonneg_left (max_le_max hab le_rfl) (height_pos V g).le
  have hcont : Continuous φ := by
    refine ENNReal.continuous_ofReal.comp ?_
    fun_prop
  have hinf := hmono.map_ciInf_of_continuousAt (g := fun δ : GQ W => height W (δ.1 * h)) hcont.continuousAt
    ⟨1, by rintro _ ⟨_, rfl⟩; exact one_le_height W _⟩
  have hq : ENNReal.ofReal (C' * (height V g * quotHeight W h) ^ A) = φ (quotHeight W h) := by
    simp only [φ, max_eq_left (quotHeight_pos W h).le]
  change sumAbs ψ d W vS (om (n * g, h) Φ) ≤ _
  rw [hq, quotHeight, hinf]
  exact le_iInf hδ
