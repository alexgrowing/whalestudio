import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.XLastLin
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiToBesselFlatMapEquivariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralLeOfTsum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorThetaFunSupModerateGrowth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightWittEmbeddingLeConstMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightOrthogonalEmbeddingLePow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section
namespace GlobalTheory.PairKerBound

theorem kernel_bound : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (χ χz : (AE D)ˣ →* Circle) (omz : Om J.W₀ B.L), IsWeilDatumO ψ J.W₀ B.L χ χz omz → ∀ (Φ₀ : WO J.W₀ B.L → ℂ) (Φ : WO J.W B.V → ℂ), IsThetaFunO ψ J.W₀ B.L Φ₀ → IsThetaFunO ψ J.W B.V Φ → ∃ (C : ℝ) (a : ℕ), ∀ h h₀ h₁, ‖contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb (h₁, 1)) (flFB s (s.om (1, h) Φ))) (omz (h₀, 1) Φ₀) 0‖ ≤ C * (height J.W₀ h₀ * height B.A h₁ * height B.V h) ^ a := by
  intro D ψ σ J B s vL χ χz omz homz Φ₀ Φ hΦ₀ hΦ
  obtain ⟨x, hx, hxe⟩ := GlobalTheory.JacMean.xLast_lin B.d B.o B.line
  obtain ⟨C₁, A₁, hC₁⟩ := GlobalTheory.FlatSup.flat_sup_growth D ψ J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d s x hx Φ hΦ
  obtain ⟨C₂, A₂, hC₂⟩ := GlobalTheory.SupThetaGrowth.om_sup_growth D ψ J.W₀ B.L χ χz omz homz Φ₀ hΦ₀
  obtain ⟨C₃, hC₃⟩ := GlobalTheory.EmbHeight.unitaryAdelicHeight_wittEmbedding_le D J.W J.W₀ (σ + 1) J.d
  obtain ⟨C₄, hC₄⟩ := GlobalTheory.EmbHeight.unitaryAdelicHeight_wittEmbedding_le D B.V B.V₀ σ B.d
  obtain ⟨C₅, a₅, hC₅⟩ := GlobalTheory.EmbHeight.height_emb_le D B.V₀ B.A B.L B.o
  have key : ∀ h h₀ h₁ w, s.om₀ (h₀, B.o.emb (h₁, 1)) (flFB s (s.om (1, h) Φ)) w =
      flatS J.d B.d s (rat x) 0 (s.om (J.d.emb0 h₀, embA B.d B.o h₁ * h) Φ) w := by
    intro h h₀ h₁ w
    have e := GlobalTheory.AscFlatEquiFB.flFB_equivariant D ψ σ J B s (s.om (1, h) Φ) (s.weil.om_pres _ _ hΦ) h₀ 1 (one_mem _) h₁
    have hp : psiBes ψ B.d 1 (vecB B.o B.ζ) 1 = 1 :=
      (GlobalTheory.MixPer.charLaws D ψ s.weil.std.1 B.V B.V₀ B.A B.L σ B.d B.o B.ζ 1).2.1 _ 1 (one_mem _)
    rw [hp, star_one, one_smul, one_mul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one] at e
    rw [← e]
    show flatS J.d B.d s (xLast B.d (vecB B.o B.ζ)) 0 _ w = _
    rw [hxe]
  have hC₃1 : 1 ≤ C₃ := by simpa using (GlobalTheory.Grow.one_le_height J.W (J.d.emb0 1)).trans (hC₃ 1)
  have hC₄1 : 1 ≤ C₄ := by simpa using (GlobalTheory.Grow.one_le_height B.V (B.d.emb0 1)).trans (hC₄ 1)
  have hC₅1 : 1 ≤ C₅ := by simpa using (GlobalTheory.Grow.one_le_height B.V₀ (B.o.emb (1, 1))).trans (hC₅ 1)
  have hM₁ : 0 ≤ max C₁ 0 := le_max_right _ _
  have hM₂ : 0 ≤ max C₂ 0 := le_max_right _ _
  have hK : 0 ≤ C₃ * C₄ * C₅ := by positivity
  refine ⟨max C₁ 0 * (C₃ * C₄ * C₅) ^ A₁ * max C₂ 0, (a₅ + 2) * A₁ + A₂, fun h h₀ h₁ => ?_⟩
  have p0 : 1 ≤ height J.W₀ h₀ := GlobalTheory.Grow.one_le_height _ _
  have p1 : 1 ≤ height B.A h₁ := GlobalTheory.Grow.one_le_height _ _
  have p2 : 1 ≤ height B.V h := GlobalTheory.Grow.one_le_height _ _
  generalize hX : height J.W₀ h₀ * height B.A h₁ * height B.V h = X
  have n01 : 0 ≤ height J.W₀ h₀ * height B.A h₁ := mul_nonneg (by linarith) (by linarith)
  have q0 : height J.W₀ h₀ ≤ X := by
    rw [← hX]; exact (le_mul_of_one_le_right (by linarith) p1).trans (le_mul_of_one_le_right n01 p2)
  have q1 : height B.A h₁ ≤ X := by
    rw [← hX]; exact (le_mul_of_one_le_left (by linarith) p0).trans (le_mul_of_one_le_right n01 p2)
  have q2 : height B.V h ≤ X := by
    rw [← hX]; exact le_mul_of_one_le_left (by linarith) (one_le_mul_of_one_le_of_one_le p0 p1)
  have hX1 : 1 ≤ X := p2.trans q2
  have hX0 : 0 ≤ X := by linarith
  have e1 : height J.W (J.d.emb0 h₀) ≤ C₃ * X := (hC₃ h₀).trans (mul_le_mul_of_nonneg_left q0 (by linarith))
  have e2 : height B.V (embA B.d B.o h₁ * h) ≤ C₄ * C₅ * X ^ (a₅ + 1) := by
    have f1 : height B.V (embA B.d B.o h₁) ≤ C₄ * (C₅ * X ^ a₅) := by
      rw [embA_apply]
      refine (hC₄ _).trans (mul_le_mul_of_nonneg_left ((hC₅ h₁).trans ?_) (by linarith))
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) q1 _) (by linarith)
    calc _ ≤ height B.V (embA B.d B.o h₁) * height B.V h := GlobalTheory.Grow.height_mul_le _ _ _
      _ ≤ (C₄ * (C₅ * X ^ a₅)) * X := mul_le_mul f1 q2 (by linarith) (by positivity)
      _ = C₄ * C₅ * X ^ (a₅ + 1) := by ring
  have hP : height J.W (J.d.emb0 h₀) * height B.V (embA B.d B.o h₁ * h) ≤ C₃ * C₄ * C₅ * X ^ (a₅ + 2) := by
    calc _ ≤ (C₃ * X) * (C₄ * C₅ * X ^ (a₅ + 1)) :=
          mul_le_mul e1 e2 (zero_le_one.trans (GlobalTheory.Grow.one_le_height _ _)) (by positivity)
      _ = _ := by ring
  have hf : ∀ w, ‖flatS J.d B.d s (rat x) 0 (s.om (J.d.emb0 h₀, embA B.d B.o h₁ * h) Φ) w‖ ≤
      max C₁ 0 * (C₃ * C₄ * C₅) ^ A₁ * X ^ ((a₅ + 2) * A₁) := by
    intro w
    have hP0 : 0 ≤ height J.W (J.d.emb0 h₀) * height B.V (embA B.d B.o h₁ * h) :=
      mul_nonneg (zero_le_one.trans (GlobalTheory.Grow.one_le_height _ _)) (zero_le_one.trans (GlobalTheory.Grow.one_le_height _ _))
    calc _ ≤ C₁ * (height J.W (J.d.emb0 h₀) * height B.V (embA B.d B.o h₁ * h)) ^ A₁ := hC₁ _ _ 0 w
      _ ≤ max C₁ 0 * (height J.W (J.d.emb0 h₀) * height B.V (embA B.d B.o h₁ * h)) ^ A₁ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hP0 _)
      _ ≤ max C₁ 0 * (C₃ * C₄ * C₅ * X ^ (a₅ + 2)) ^ A₁ :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hP0 hP _) hM₁
      _ = _ := by rw [mul_pow, ← pow_mul]; ring
  have hg : ∀ v, ‖omz (h₀, 1) Φ₀ v‖ ≤ max C₂ 0 * X ^ A₂ := by
    intro v
    have := hC₂ h₀ 1 v
    rw [GlobalTheory.Grow.height_one, mul_one] at this
    refine this.trans ?_
    calc C₂ * height J.W₀ h₀ ^ A₂ ≤ max C₂ 0 * height J.W₀ h₀ ^ A₂ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (by linarith) _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) q0 _) hM₂
  unfold contractT thPair
  have hvol := vL.covol.2.2
  refine (norm_setIntegral_le_of_norm_le_const (C := max C₁ 0 * (C₃ * C₄ * C₅) ^ A₁ * X ^ ((a₅ + 2) * A₁) *
    (max C₂ 0 * X ^ A₂)) (by rw [hvol]; exact ENNReal.one_lt_top) fun v _ => ?_).trans ?_
  · beta_reduce
    rw [norm_mul, norm_star, key]
    exact mul_le_mul (hf _) (hg _) (norm_nonneg _) (by positivity)
  · rw [measureReal_def, hvol, ENNReal.toReal_one, mul_one, pow_add]
    exact le_of_eq (by ring)

end GlobalTheory.PairKerBound
