import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsVeryAmpleZFinite
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PAmpleAffineGen
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

namespace VeryAmpleZChartRing

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem exists_pow_mul_mem_ampleRing (H : LineBundle S x) {m : ℕ} {h : Ω}
    (hh : ∀ I, h ∈ (H.pow m).sub I) {c : Ω} (hc : c ∈ ampleRing H.toSubSystem m h) (K : Chart x)
    (hrat : ∀ I : Chart x, ∃ e : ℕ,
      c ^ e * (xProd I ^ K.1.card / xProd K ^ I.1.card) ∈ ampleChart H.toSubSystem m h I)
    {y : Ω} (hy : y ∈ ampleChart H.toSubSystem m h K) : ∃ M : ℕ, c ^ M * y ∈ ampleRing H.toSubSystem m h := by
  classical
  have hI : ∀ I : Chart x, ∃ M, c ^ M * y ∈ ampleChart H.toSubSystem m h I := by
    intro I
    have h1 : y ∈ ampleChart H.toSubSystem m h (AmpleAffineGen.unionChart I K) :=
      AmpleAffineGen.ampleChart_mono (AmpleAffineGen.subset_unionChart_right I K) hy
    obtain ⟨D, hD⟩ := AmpleAffineGen.ampleChart_loc H I K h1
    obtain ⟨e, he⟩ := hrat I
    refine ⟨e * D, ?_⟩
    have := mul_mem
      (pow_mem (show _ ∈ AmpleAffineGen.ampleSubalg H.toSubSystem m h I (hh I) from he) D)
      (show _ ∈ AmpleAffineGen.ampleSubalg H.toSubSystem m h I (hh I) from hD)
    rwa [show c ^ e * (xProd I ^ K.1.card / xProd K ^ I.1.card) =
        c ^ e * AmpleAffineGen.chartRatio K I from rfl,
      AmpleAffineGen.pow_mul_cancel (AmpleAffineGen.chartRatio_mul_chartRatio I K)] at this
  choose M hM using hI
  refine ⟨Finset.univ.sup M, Set.mem_iInter.mpr fun I => ?_⟩
  have hle : M I ≤ Finset.univ.sup M := Finset.le_sup (Finset.mem_univ I)
  have e1 : c ^ Finset.univ.sup M * y = c ^ (Finset.univ.sup M - M I) * (c ^ M I * y) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  rw [e1]
  exact mul_mem
    (pow_mem (show c ∈ AmpleAffineGen.ampleSubalg H.toSubSystem m h I (hh I) from
      Set.mem_iInter.mp hc I) _)
    (show _ ∈ AmpleAffineGen.ampleSubalg H.toSubSystem m h I (hh I) from hM I)

theorem ampleBase_le_chartRing {r : ℕ} {h : Fin (r + 1) → Ω} (J : Chart h) {j : Fin (r + 1)} (hj : j ∈ J.1) :
    ampleBase (S := S) h j ≤ chartRing S h J :=
  Algebra.adjoin_le (by
    rintro _ ⟨l, rfl⟩
    exact ⟨X l, X j, 1, X_mem_monos hj, isHomogeneous_X S l, isHomogeneous_X S j, by simp⟩)

theorem pow_div_xProd_mem {r : ℕ} {h : Fin (r + 1) → Ω} (J : Chart h) (j : Fin (r + 1)) :
    h j ^ J.1.card / xProd J ∈ chartRing S h J :=
  ⟨X j ^ J.1.card, AmpleAffineGen.monoProd J.1, J.1.card, AmpleAffineGen.monoProd_mem_monos subset_rfl,
    by simpa using (isHomogeneous_X S j).pow J.1.card, AmpleAffineGen.monoProd_isHomogeneous J.1,
    by rw [map_pow, aeval_X, AmpleAffineGen.aeval_monoProd, xProd]⟩

end VeryAmpleZChartRing

open VeryAmpleZChartRing in

theorem VeryAmpleZChartRing.proof : VeryAmpleZChartRing.Statement.{u, w} := by
  intro S _ Ω _ _ N x H r h hv J j hjJ c hc K hrat α hα
  have hj0 : h j ≠ 0 := (mem_support h).mp (J.2.2 hjJ)
  have hh : ∀ I : Chart x, h j ∈ (H.pow 1).sub I := fun I => by
    rw [SubSystem.pow_sub, pow_one]
    exact (Submodule.mem_iInf _).mp (hv.mem_secs j) I
  have hJ0 : xProd J ≠ 0 := AmpleAffineGen.xProd_ne_zero J
  obtain ⟨n, hn⟩ := hα
  set g : Ω := xProd J / h j ^ J.1.card with hg
  have hy : α * g ^ n ∈ ampleChart H.toSubSystem 1 (h j) K := by
    refine ⟨J.1.card * n, ?_⟩
    have e1 : α * g ^ n * h j ^ (J.1.card * n) = α * xProd J ^ n := by
      rw [hg, div_pow, pow_mul, ← pow_mul, mul_comm J.1.card n, pow_mul, mul_assoc,
        div_mul_cancel₀ _ (pow_ne_zero _ (pow_ne_zero _ hj0))]
    rw [e1, one_mul]
    exact hn
  obtain ⟨M₀, hM₀⟩ := exists_pow_mul_mem_ampleRing H hh hc K hrat hy
  have hbase := ampleBase_le_chartRing (S := S) J hjJ
  have h1 : c ^ M₀ * (α * g ^ n) ∈ chartRing S h J := hbase (hv.closed j hj0 hM₀)
  have hcJ : c ∈ chartRing S h J := hbase (hv.closed j hj0 hc)
  have h2 : c ^ M₀ * α ∈ chartRing S h J := by
    have e2 : c ^ M₀ * α = c ^ M₀ * (α * g ^ n) * (h j ^ J.1.card / xProd J) ^ n := by
      rw [hg, mul_assoc (c ^ M₀), mul_assoc α, ← mul_pow, div_mul_div_cancel₀ (pow_ne_zero _ hj0),
        div_self hJ0, one_pow, mul_one]
    rw [e2]
    exact mul_mem h1 (pow_mem (pow_div_xProd_mem J j) n)
  refine eventually_atTop.mpr ⟨M₀, fun M hM => ?_⟩
  have e3 : c ^ M * α = c ^ (M - M₀) * (c ^ M₀ * α) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hM]
  rw [e3]
  exact mul_mem (pow_mem hcJ _) h2

end

end GroundTheory.Heights₂.Heights.Kleiman
