import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.MapsToUpToSign
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.LamCont

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.Vac

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n} {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0}
  {sec I : PX m n →ₗ[ℂ] (G → ℂ)} {Λ : Set ((G → ℂ) → ℂ)}

theorem top_theta [MeasurableSpace (KR n)] [BorelSpace (KR n)] [CompactSpace (KR n)] (μ : Measure (KR n))
    [IsFiniteMeasure μ] (hD : CayleyBlocksInvertible) (hιc : Continuous ι) {a b : GR n} {nb : (Fin n → Fin n → ℝ) → GR n}
    (hnbc : Continuous nb) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) {cz : ℂ → ℂ}
    (hceig : ∀ (w : ℂ) (y : GR n), ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * (∫ x, ((hLoc (y * (k : GR n) * a * nb x * b) : ℂ) ^ w *
        F0 p q e (y * (k : GR n) * a * nb x * b)) * ψ x) ∂μ = cz w * ((hLoc y : ℂ) ^ w * F0 p q e y))
    (I1 : G → ℂ) (hIc : Continuous I1)
    (hTS : ∀ (g : G) (y : GR n), ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * I1 (g * ι ((k : GR n) * y)) ∂μ =
      I1 g * ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * F0 p q e ((k : GR n) * y) ∂μ) (g : G) :
    Top μ ι p q e a b nb ψ I1 g = cz 0 * I1 g := by
  have hswap : ∀ Φ : GR n → ℂ, Continuous Φ →
      ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * (∫ x, Φ ((k : GR n) * a * nb x * b) * ψ x) ∂μ =
      ∫ x, (∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * Φ ((k : GR n) * (a * nb x * b)) ∂μ) * ψ x := by
    intro Φ hΦ
    have hcont : Continuous (fun z : KR n × (Fin n → Fin n → ℝ) =>
        (F0 p q e (z.1 : GR n))⁻¹ * (Φ ((z.1 : GR n) * a * nb z.2 * b) * ψ z.2)) := by
      refine Continuous.mul ?_ (Continuous.mul ?_ (hψc.comp continuous_snd))
      · exact ((continuous_weight_factor hD p q e).comp (continuous_subtype_val.comp continuous_fst)).inv₀
          (fun z => spherical_section_ne_zero hD p q e _)
      · exact hΦ.comp ((((continuous_subtype_val.comp continuous_fst).mul continuous_const).mul
          (hnbc.comp continuous_snd)).mul continuous_const)
    have hsupp : HasCompactSupport (fun z : KR n × (Fin n → Fin n → ℝ) =>
        (F0 p q e (z.1 : GR n))⁻¹ * (Φ ((z.1 : GR n) * a * nb z.2 * b) * ψ z.2)) := by
      refine HasCompactSupport.intro' (K := univ ×ˢ tsupport ψ) (isCompact_univ.prod hψs)
        (isClosed_univ.prod (isClosed_tsupport ψ)) ?_
      intro z hz
      have hz2 : z.2 ∉ tsupport ψ := fun h => hz ⟨mem_univ _, h⟩
      simp [image_eq_zero_of_notMem_tsupport hz2]
    have hint := hcont.integrable_of_hasCompactSupport (μ := μ.prod volume) hsupp
    calc _ = ∫ k : KR n, (∫ x, (F0 p q e (k : GR n))⁻¹ * (Φ ((k : GR n) * a * nb x * b) * ψ x)) ∂μ := by
          congr 1
          funext k
          exact (integral_const_mul _ _).symm
      _ = ∫ x, (∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * (Φ ((k : GR n) * a * nb x * b) * ψ x) ∂μ) :=
          integral_integral_swap
            (f := fun (k : KR n) (x : Fin n → Fin n → ℝ) =>
              (F0 p q e (k : GR n))⁻¹ * (Φ ((k : GR n) * a * nb x * b) * ψ x)) hint
      _ = _ := by
          congr 1
          funext x
          rw [← integral_mul_const]
          congr 1
          funext k
          simp only [mul_assoc]
  have h1 := hswap (fun y => I1 (g * ι y)) (hIc.comp (continuous_const.mul hιc))
  have h2 := hswap (F0 p q e) (continuous_weight_factor hD p q e)
  have hc := hceig 0 1
  simp only [Complex.cpow_zero, one_mul, mul_one, weight_factor_one] at hc
  unfold Top
  rw [h1]
  simp_rw [hTS g]
  have hpull : ∫ x, (I1 g * ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * F0 p q e ((k : GR n) * (a * nb x * b)) ∂μ) * ψ x =
      I1 g * ∫ x, (∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * F0 p q e ((k : GR n) * (a * nb x * b)) ∂μ) * ψ x := by
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [hpull, ← h2, hc, mul_comm]

end PositivityTheory.Rg.Sw.AbsSt.Vac
