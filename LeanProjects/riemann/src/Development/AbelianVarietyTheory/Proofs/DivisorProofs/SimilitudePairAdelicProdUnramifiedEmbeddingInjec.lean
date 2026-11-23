import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

theorem finiteAdeleRingAway_nontrivial (p : ℕ) [Fact p.Prime] : Nontrivial (AfP p) := by
  obtain ⟨q, hqp, hq⟩ := Nat.exists_infinite_primes (p + 1)
  have hqi : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  let v0 : IsDedekindDomain.HeightOneSpectrum ℤ :=
    { asIdeal := Ideal.span {(q : ℤ)}
      isPrime := (Ideal.span_singleton_prime hqi.ne_zero).mpr hqi
      ne_bot := by simpa using hqi.ne_zero }
  have hne : v0.asIdeal ≠ Ideal.span {(p : ℤ)} := by
    intro h
    change Ideal.span {(q : ℤ)} = Ideal.span {(p : ℤ)} at h
    rw [Ideal.span_singleton_eq_span_singleton, Int.associated_iff_natAbs] at h
    simp at h
    omega
  exact (AfP.eval (p := p) ⟨v0, hne⟩).toRingHom.domain_nontrivial

theorem pair_toAf_injective {p : ℕ} [Fact p.Prime] {G : HTGroup p} (P : Pair G) (x : (AfP p ⊗[ℚ] G.C)ˣ)
    (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) : Function.Injective (P.toAf x t hx) := by
  haveI := finiteAdeleRingAway_nontrivial p
  intro a b h
  have h0 := congrArg Subtype.val h
  have h1 := congrArg Prod.fst h0
  have h2 := congrArg Prod.snd h0
  simp only [Pair.toAf, MonoidHom.codRestrict_apply, MonoidHom.comp_apply, MonoidHom.prodMap, MonoidHom.prod_apply, Prod.map_fst, Prod.map_snd,
    Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_left_inj, mul_right_inj] at h1 h2
  have e1 : (a : G.Cˣ × ℚˣ).1 = (b : G.Cˣ × ℚˣ).1 := by
    apply Units.ext
    have := congrArg Units.val h1
    simp only [Units.coe_map, MonoidHom.coe_coe] at this
    exact Algebra.TensorProduct.includeRight_injective (algebraMap ℚ (AfP p)).injective this
  have e2 : (a : G.Cˣ × ℚˣ).2 = (b : G.Cˣ × ℚˣ).2 := by
    apply Units.ext
    have := congrArg Units.val h2
    simp only [Units.coe_map, MonoidHom.coe_coe] at this
    exact (algebraMap ℚ (AfP p)).injective this
  exact Subtype.ext (Prod.ext e1 e2)

theorem pair_embedding_injective : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (r : ℕ) (z : Gr G r), Function.Injective ((P.toAf x t hx).prod (P.toQr r z)) := by
  intro p _ G P x t hx r z a b h
  exact pair_toAf_injective P x t hx (congrArg Prod.fst h)

end GlobalTheory.LKMid
