import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ImportsFurther
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PowLeSqrtDetGram
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.LinearIndependentReal
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PFirstMinPos
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

namespace FullerData

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {Em : Type} [Field Em] [NumberField Em] [IsCMField Em]
  (D : FullerData II Ψ K ι Ω E Em)

def embHom : (Fin D.N → Em) →+ ((Ψ × Fin D.N) → ℂ) where
  toFun v p := D.herm.emb p.1 (v p.2)
  map_zero' := by
    funext p
    simp
  map_add' v w := by
    funext p
    simp

def hodgeFrame (z : (Σ k, ι k) → ℂ) : ((Ψ × Fin D.N) → ℂ) →ₗ[ℝ] EuclideanSpace ℂ (Ψ × Fin D.N) where
  toFun y := WithLp.toLp 2 fun p =>
    (Real.sqrt (2 * ‖D.herm.emb p.1 D.herm.ξ‖) : ℂ) * ((D.per z p.1)⁻¹ *ᵥ fun a => y (p.1, a)) p.2
  map_add' y y' := by
    ext p
    simp only [PiLp.add_apply, Pi.add_apply]
    rw [show (fun a => y (p.1, a) + y' (p.1, a)) = (fun a => y (p.1, a)) + fun a => y' (p.1, a) from rfl,
      Matrix.mulVec_add, Pi.add_apply, mul_add]
  map_smul' r y := by
    ext p
    simp only [PiLp.smul_apply, Pi.smul_apply, RingHom.id_apply]
    rw [show (fun a => r • y (p.1, a)) = r • fun a => y (p.1, a) from rfl, Matrix.mulVec_smul,
      Pi.smul_apply, Complex.real_smul, Complex.real_smul]
    ring

theorem inner_hodgeFrame (z : (Σ k, ι k) → ℂ) (v w : Fin D.N → Em) :
    inner ℝ (D.hodgeFrame z (D.embHom v)) (D.hodgeFrame z (D.embHom w)) = D.hodgeInner z v w := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type, hodgeInner]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [hodgeFrame, embHom, LinearMap.coe_mk, AddHom.coe_mk, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, WithLp.ofLp_toLp, Complex.inner, map_mul, Complex.conj_ofReal]
  have hs : Real.sqrt (2 * ‖D.herm.emb τ D.herm.ξ‖) * Real.sqrt (2 * ‖D.herm.emb τ D.herm.ξ‖) =
      2 * ‖D.herm.emb τ D.herm.ξ‖ := Real.mul_self_sqrt (by positivity)
  rw [show ∀ (s : ℝ) (u x : ℂ), (s * x * ((s : ℂ) * starRingEnd ℂ u)).re = (s * s) * (starRingEnd ℂ u * x).re by
    intro s u x
    rw [show (s : ℂ) * x * ((s : ℂ) * starRingEnd ℂ u) = ((s * s : ℝ) : ℂ) * (starRingEnd ℂ u * x) by
      push_cast
      ring, Complex.re_ofReal_mul], hs]

theorem hodgeFrame_injective {z : (Σ k, ι k) → ℂ} (hz : z ∈ D.Xo) : Function.Injective (D.hodgeFrame z) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  funext p
  obtain ⟨τ, a⟩ := p
  have hP : IsUnit (D.per z τ).det := FirstMinPos.isUnit_det_of_eq_signMat (D.per_witt z hz τ)
  have hs : (Real.sqrt (2 * ‖D.herm.emb τ D.herm.ξ‖) : ℂ) ≠ 0 := by
    have : D.herm.emb τ D.herm.ξ ≠ 0 := (map_ne_zero _).2 D.herm.ξ_ne
    exact_mod_cast (Real.sqrt_pos.2 (by positivity)).ne'
  have h0 : (D.per z τ)⁻¹ *ᵥ (fun b => y (τ, b)) = 0 := by
    funext b
    have := congrArg (fun x : EuclideanSpace ℂ (Ψ × Fin D.N) => x (τ, b)) hy
    simp only [hodgeFrame, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp, PiLp.zero_apply] at this
    exact (mul_eq_zero.1 this).resolve_left hs
  have h1 : (fun b => y (τ, b)) = 0 := by
    rw [← Matrix.one_mulVec (fun b => y (τ, b)), ← Matrix.mul_nonsing_inv _ hP, ← Matrix.mulVec_mulVec, h0,
      Matrix.mulVec_zero]
  exact congr_fun h1 a

end FullerData

theorem UnitaryMinkowskiBound.proof : UnitaryMinkowskiBound.Statement := by
  intro II Ψ _ K _ ι _ Ω _ _ E _ _ Em _ _ _ D z hz I hI ρ v hv
  classical
  have hex := D.herm.exists_isZBasis hI
  have hcov : D.covolZ z I = Real.sqrt (Matrix.of fun k l =>
      D.hodgeInner z (hex.choose_spec.choose k) (hex.choose_spec.choose l)).det := by
    unfold FullerData.covolZ
    rw [dif_pos hex]
  have hb : IsZBasis I hex.choose_spec.choose := hex.choose_spec.choose_spec
  have hm : hex.choose = 2 * D.f * ρ := by
    rw [card_eq_of_isZBasis hv hb, D.herm.finrank_eq]
    rfl
  set b := hex.choose_spec.choose
  let u : Fin hex.choose → EuclideanSpace ℂ (Ψ × Fin D.N) := fun k => D.hodgeFrame z (D.embHom (b k))
  have hbQ : LinearIndependent ℚ b := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hb.1
  have hu_li : LinearIndependent ℝ u :=
    (D.herm.linearIndependent_real hbQ).map' (D.hodgeFrame z)
      (LinearMap.ker_eq_bot.2 (D.hodgeFrame_injective hz))
  have hgram : Matrix.gram ℝ u = Matrix.of fun k l => D.hodgeInner z (b k) (b l) := by
    ext k l
    exact D.inner_hodgeFrame z _ _
  have hlam0 : 0 ≤ D.lam1 z :=
    Real.sInf_nonneg (by rintro x ⟨w, -, -, rfl⟩; exact Real.sqrt_nonneg _)
  have hmin : ∀ x ∈ Submodule.span ℤ (Set.range u), x ≠ 0 → D.lam1 z ≤ ‖x‖ := by
    intro x hx hx0
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hx
    have hw : ∑ k, c k • u k = D.hodgeFrame z (D.embHom (∑ k, c k • b k)) := by
      simp only [u, map_sum, map_zsmul]
    have hwI : ∑ k, c k • b k ∈ I := (hb.2 _).2 ((Submodule.mem_span_range_iff_exists_fun ℤ).2 ⟨c, rfl⟩)
    have hw0 : ∑ k, c k • b k ≠ 0 := by
      intro h
      apply hx0
      rw [hw, h, map_zero, map_zero]
    rw [hw, norm_eq_sqrt_real_inner, D.inner_hodgeFrame, D.hodgeInner_self]
    exact D.firstMinimum_le_period_norm z (hI hwI) hw0
  have key := pow_le_sqrt_det_gram u hu_li hlam0 hmin
  rw [hgram, ← hcov, hm] at key
  push_cast at key
  exact key

end GroundTheory.Heights₂.Heights.NineStatements
