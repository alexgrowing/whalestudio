import Mathlib
import Formalism.LocalToGlobal.InertKernelTheory.StatementCc
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.HalfTorsionNotMemCmLattice
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.Homothety
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.InertPrime
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticInvariants.QuadPolyIrreducible
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticDedekindZeta.GenBase

noncomputable section
open NumberField Formalism.BasicNotions
open scoped Pointwise

namespace Formalism.L2.KerInert.CcGen

variable {K : Type} [Field K] [NumberField K]

theorem coprime_absNorm_of_not_le {p : ℕ} (hp : p.Prime) (hP : (Ideal.span {(p : 𝓞 K)}).IsMaximal)
    {I : Ideal (𝓞 K)} (hI : ¬ I ≤ Ideal.span {(p : 𝓞 K)}) : Nat.Coprime (Ideal.absNorm I) p := by
  have hsup : I ⊔ Ideal.span {(p : 𝓞 K)} = ⊤ := by
    by_contra h
    exact hI (le_sup_left.trans (hP.eq_of_le h le_sup_right).ge)
  have h1 : (1 : 𝓞 K) ∈ I ⊔ Ideal.span {(p : 𝓞 K)} := hsup ▸ Submodule.mem_top
  obtain ⟨i, hi, z, hz, hiz⟩ := Submodule.mem_sup.mp h1
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hz
  have hunit : Ideal.Quotient.mk I y * (p : 𝓞 K ⧸ I) = 1 := by
    have := congrArg (Ideal.Quotient.mk I) hiz
    rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hi, zero_add, map_mul, map_one, map_natCast] at this
    exact this
  have hI0 : I ≠ ⊥ := fun h => hI (h ▸ bot_le)
  have hc : Nat.card (𝓞 K ⧸ I) = Ideal.absNorm I := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 K ⧸ I) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact Ideal.absNorm_eq_zero_iff.not.mpr hI0)
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := 𝓞 K ⧸ I) p (hc ▸ hdvd)
  have hpx : (p : 𝓞 K ⧸ I) * x = 0 := by
    rw [← nsmul_eq_mul, ← hx, addOrderOf_nsmul_eq_zero]
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, addOrderOf_zero] at hx
    exact hp.one_lt.ne hx
  apply hx0
  calc x = (Ideal.Quotient.mk I y * (p : 𝓞 K ⧸ I)) * x := by rw [hunit, one_mul]
    _ = Ideal.Quotient.mk I y * ((p : 𝓞 K ⧸ I) * x) := mul_assoc _ _ _
    _ = 0 := by rw [hpx, mul_zero]

theorem factor_inert {p : ℕ} (hp : p.Prime) (hP : (Ideal.span {(p : 𝓞 K)}).IsPrime)
    (hP0 : Ideal.span {(p : 𝓞 K)} ≠ ⊥) {cc : Ideal (𝓞 K)} (hcc : cc ≠ ⊥) :
    ∃ (k : ℕ) (cc' : Ideal (𝓞 K)), cc = Ideal.span {(p : 𝓞 K) ^ k} * cc' ∧
      Nat.Coprime (Ideal.absNorm cc') p := by
  have hpr : Prime (Ideal.span {(p : 𝓞 K)}) := Ideal.prime_of_isPrime hP0 hP
  obtain ⟨k, cc', hnd, heq⟩ :=
    WfDvdMonoid.max_power_factor (by rwa [Ideal.zero_eq_bot]) hpr.irreducible (a₀ := cc)
  refine ⟨k, cc', by rw [heq, Ideal.span_singleton_pow], ?_⟩
  exact coprime_absNorm_of_not_le hp (hP.isMaximal hP0) (fun h => hnd (Ideal.dvd_iff_le.mpr h))

end Formalism.L2.KerInert.CcGen

namespace Formalism.L2.KerInert

open Formalism.MainNotions

theorem lamOf_span_mul (D : D7) (cc : Ideal (𝓞 D.host.K)) (a : 𝓞 D.host.K) (δ : ℂ) :
    TaylorLogMetric.lamOf D (Ideal.span {a} * cc) δ = TaylorLogMetric.lamOf D cc (δ * D.host.φ₀ ((a : D.host.K) : D.host.E)) := by
  unfold TaylorLogMetric.lamOf
  congr 1
  ext w
  simp only [Set.mem_setOf_eq, Ideal.mem_span_singleton_mul]
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, by simp only [map_mul, MulMemClass.coe_mul]; ring⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨a * z, ⟨z, hz, rfl⟩, by simp only [map_mul, MulMemClass.coe_mul]; ring⟩

theorem lamOf_smul (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) :
    TaylorLogMetric.lamOf D cc δ = δ • TaylorLogMetric.lamOf D cc 1 := by
  unfold TaylorLogMetric.lamOf
  change _ = AddSubgroup.map (DistribSMul.toAddMonoidHom ℂ δ) _
  rw [AddMonoidHom.map_closure]
  congr 1
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_image, one_mul]
  constructor
  · rintro ⟨c, hc, rfl⟩; exact ⟨_, ⟨c, hc, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩; exact ⟨c, hc, rfl⟩

theorem discr_smul_eq_inv_pow_twelve_mul (Λ : AddSubgroup ℂ) (c : ℂ) (hc : c ≠ 0) :
    TaylorLogMetric.discr (c • Λ) = (c ^ 12)⁻¹ * TaylorLogMetric.discr Λ :=
  Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.discr_smul Λ c hc

theorem curve_ideal_prime : CcPrime := by
  intro D cc δ hcc hδ p hpF hj
  have hp := hpF.out
  have hq := quadK D.host
  have hK2 := PI.UnitaryGroupMassFormula.ClassNumImQInv.finrank_two hq
  have hP : (Ideal.span {(p : 𝓞 D.host.K)}).IsPrime :=
    isPrime_span_of_jacobi_neg_one _ hK2 _ D.host.d p hq.2.2.2.1 hp hj
  have hP0 : Ideal.span {(p : 𝓞 D.host.K)} ≠ ⊥ :=
    PI.ClassNumImQ.ZetaNonvanishing₂.ne_bot_of_absNorm (PI.ClassNumImQ.ZetaNonvanishing₂.absNorm_span_two hK2 p)
      (pow_ne_zero 2 hp.ne_zero)
  obtain ⟨k, cc', heq, hcop⟩ := CcGen.factor_inert hp hP hP0 hcc.1
  have hpk : D.host.φ₀ ((((p : 𝓞 D.host.K) ^ k : 𝓞 D.host.K) : D.host.K) : D.host.E) = (p : ℂ) ^ k := by
    simp
  have hlam : ∀ e : ℂ, TaylorLogMetric.lamOf D cc e = TaylorLogMetric.lamOf D cc' (e * (p : ℂ) ^ k) := by
    intro e; rw [heq, lamOf_span_mul, hpk]
  have hne : cc' ≠ ⊥ := by
    rintro rfl; apply hcc.1; rw [heq, Ideal.mul_bot]
  have hnorm : Ideal.absNorm cc' ∣ Ideal.absNorm cc := by
    rw [heq, map_mul]; exact dvd_mul_left _ _
  refine ⟨cc', δ * (p : ℂ) ^ k, ⟨hne, Nat.Coprime.coprime_dvd_left hnorm hcc.2⟩, ?_, hcop, hlam δ⟩
  have hp0 : ((p : ℂ) ^ k) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero)
  unfold TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice at hδ ⊢
  rw [hlam 1, one_mul, lamOf_smul D cc' ((p : ℂ) ^ k), discr_smul_eq_inv_pow_twelve_mul _ _ hp0] at hδ
  rw [mul_pow, hδ]
  field_simp

end Formalism.L2.KerInert
