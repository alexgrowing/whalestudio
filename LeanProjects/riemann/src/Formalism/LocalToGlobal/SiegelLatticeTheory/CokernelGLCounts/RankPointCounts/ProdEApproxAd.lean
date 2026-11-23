import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StrongApproximation.LocalIntegralOfSubstitution
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StrongApproximation.ExistsLatticeAutomorphismApprox
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StrongApproximation.DedekindLFunctions

noncomputable section

open IsDedekindDomain NumberField ValuativeRel

namespace Formalism.L2.SG.Pf.ProdEApprox

section Ball

variable {K : Type*} [Field K] [ValuativeRel K]

def InBall (c x : K) : Prop := ValuativeRel.valuation K x ≤ ValuativeRel.valuation K c

def ballS (c : K) : AddSubgroup K where
  carrier := {x | InBall c x}
  zero_mem' := by simp [InBall]
  add_mem' := fun {x y} hx hy => by
    simp only [Set.mem_setOf_eq, InBall] at hx hy ⊢
    exact Valuation.map_add_le _ hx hy
  neg_mem' := fun {x} hx => by
    simp only [Set.mem_setOf_eq, InBall] at hx ⊢
    simpa [Valuation.map_neg] using hx

theorem mem_ballS {c x : K} : x ∈ ballS c ↔ valuation K x ≤ valuation K c := by
  show InBall c x ↔ _
  rfl

theorem ballS_isOpen [TopologicalSpace K] [IsValuativeTopology K] {c : K} (hc : c ≠ 0) :
    IsOpen (ballS c : Set K) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hv : valuation K c ≠ 0 := by simpa using hc
  refine IsValuativeTopology.mem_nhds_iff'.mpr ⟨Units.mk0 _ hv, fun y hy => ?_⟩
  have hy' : valuation K (y - x) < valuation K c := by simpa using hy
  rw [SetLike.mem_coe, mem_ballS]
  have e : y = (y - x) + x := by ring
  rw [e]
  exact Valuation.map_add_le _ hy'.le hx

theorem ballS_mul {c x : K} (hc : c ≠ 0) (hx : x ∈ ballS c) : ∃ β ∈ 𝒪[K], x = c * β := by
  refine ⟨x / c, ?_, by field_simp⟩
  rw [Valuation.mem_integer_iff, map_div₀]
  exact div_le_one_of_le₀ (mem_ballS.1 hx) zero_le'

end Ball

section Ad

open Formalism.MainNotions.S.Loc PI.StrongApproxE

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  (L : ∀ p : HeightOneSpectrum (𝓞 F), LocAt F E sig p)

theorem sa_lat (T : Finset (HeightOneSpectrum (𝓞 F))) (x : ∀ p, (L p).Ep) (c : ∀ p, (L p).Fp)
    (hc : ∀ p ∈ T, c p ≠ 0) :
    ∃ t : E, (∀ p ∈ T, ∃ y ∈ (L p).O, (L p).ιE t - x p = algebraMap (L p).Fp (L p).Ep (c p) * y) ∧
      ∀ p, p ∉ T → (L p).ιE t ∈ (L p).O := by
  classical
  obtain ⟨n, b, hbint, hbspan⟩ := intSpan' F E
  choose α hα using fun p => local_span_holds F E sig p (L p) n b hbspan (x p)
  set c' : ∀ p, (L p).Fp := fun p => if p ∈ T then c p else 1 with hc'
  have hc'0 : ∀ p, c' p ≠ 0 := by
    intro p
    by_cases hp : p ∈ T
    · simp only [hc', if_pos hp]; exact hc p hp
    · simp only [hc', if_neg hp]; exact one_ne_zero
  have hVo : ∀ p, IsOpen (ballS (c' p) : Set (L p).Fp) := by
    intro p
    have := (L p).lf
    exact ballS_isOpen (hc'0 p)
  choose a ha using fun p (i : Fin n) => local_dense_embedding F E sig p (L p) (ballS (c' p)) (hVo p) (α p i)
  choose d hd0 hd using fun p => local_neighbourhood_small F E sig p (L p) (ballS (c' p)) (hVo p)
  choose t ht1 ht2 using fun i : Fin n => strong_approximation_finite_places F T (fun p => a p i) d (fun p _ => hd0 p)
  refine ⟨∑ i, t i • b i, fun p hp => ?_, fun p hp => ?_⟩
  · have hιE : (L p).ιE (∑ i, t i • b i) = ∑ i, (L p).ιF (t i) • (L p).ιE (b i) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => existsLatticeAutomorphismApprox F E sig p (L p) (t i) (b i)
    have h1 : (L p).ιE (∑ i, t i • b i) - x p = ∑ i, ((L p).ιF (t i) - α p i) • (L p).ιE (b i) := by
      rw [hιE]
      conv_lhs => rw [hα p]
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => (sub_smul _ _ _).symm
    have hmem : ∀ i, (L p).ιF (t i) - α p i ∈ ballS (c' p) := by
      intro i
      have h2 : (L p).ιF (t i) - α p i = (L p).ιF (t i - a p i) + ((L p).ιF (a p i) - α p i) := by
        rw [map_sub]; ring
      rw [h2]
      exact (ballS (c' p)).add_mem (hd p _ (ht1 i p hp)) (ha p i)
    have hcp : c' p = c p := by simp only [hc', if_pos hp]
    choose β hβO hβ using fun i => ballS_mul (hc'0 p) (hmem i)
    have hbO : ∀ i, (L p).ιE (b i) ∈ (L p).O := by
      intro i
      have := local_integral_of_substitution F E sig p (L p) 1 (b i) (by simp) (hbint i)
      simpa using this
    have hβE : ∀ i, algebraMap (L p).Fp (L p).Ep (β i) * (L p).ιE (b i) ∈ (L p).O := by
      intro i
      have := (L p).lf
      have hA : IsIntegral 𝒪[(L p).Fp] (algebraMap (L p).Fp (L p).Ep (β i)) :=
        isIntegral_algebraMap (R := 𝒪[(L p).Fp]) (A := (L p).Ep) (x := ⟨β i, hβO i⟩)
      exact (L p).O.mul_mem (((L p).O_def _).mpr hA) (hbO i)
    refine ⟨∑ i, algebraMap (L p).Fp (L p).Ep (β i) * (L p).ιE (b i), (L p).O.sum_mem fun i _ => hβE i, ?_⟩
    rw [h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hβ i, ← hcp, Algebra.smul_def, map_mul, mul_assoc]
  · rw [map_sum]
    refine (L p).O.sum_mem fun i _ => ?_
    rw [existsLatticeAutomorphismApprox F E sig p (L p) (t i) (b i)]
    exact local_integral_of_substitution F E sig p (L p) (t i) (b i) (ht2 i p hp) (hbint i)

end Ad

end Formalism.L2.SG.Pf.ProdEApprox
