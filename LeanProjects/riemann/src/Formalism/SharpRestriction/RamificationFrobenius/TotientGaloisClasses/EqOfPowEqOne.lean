import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ArtinMapSecondEqJacobiSym
import Formalism.GL3MeanSquares.HookFormulaTorsion.DifferentIdealConditions

open NumberField IntermediateField Ideal
open scoped Pointwise

noncomputable section

namespace Formalism.HC.D7

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

variable {e q d : ℕ} (hH : HostHyp q d) {L : Type} [Field L] [NumberField L] {ζ a b : L}
  (h : IsLayer (e + 2) q d ζ a b)

theorem exists_prime_mem (M : Type) [Field M] [NumberField M] (p : ℕ) (hp : p.Prime) :
    ∃ P : Ideal (𝓞 M), P.IsPrime ∧ P.LiesOver (span {(p : ℤ)}) ∧ ((p : ℤ) : 𝓞 M) ∈ P := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨P, h1, h2⟩⟩ : Nonempty ((span {(p : ℤ)}).primesOver (𝓞 M)) := inferInstance
  exact ⟨P, h1, h2, (odd_intCast_mem_iff p P _).mpr dvd_rfl⟩

theorem eq_of_pow_eq_one {S : Type*} [CommRing S] [IsDomain S] (P : Ideal S) [hP : P.IsPrime] {m : ℕ} (hm : (m : S) ∉ P)
    {x y : S} (hx : x ^ m = 1) (hy : y ^ m = 1) (hxy : x - y ∈ P) : x = y := by
  by_contra hne
  have h1 := geom_sum₂_mul x y m
  rw [hx, hy, sub_self, mul_eq_zero, sub_eq_zero] at h1
  have h2 := congrArg (Ideal.Quotient.mk P) (h1.resolve_right hne)
  have h3 : Ideal.Quotient.mk P x = Ideal.Quotient.mk P y := Ideal.Quotient.eq.mpr hxy
  rw [RingHom.map_geom_sum₂, h3, geom_sum₂_self, map_zero, ← map_pow, ← map_natCast (Ideal.Quotient.mk P), ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem] at h2
  rcases hP.mem_or_mem h2 with h4 | h4
  · exact hm h4
  · have h5 : y ∈ P := hP.mem_of_pow_mem _ h4
    have hm0 : m ≠ 0 := by rintro rfl; exact hm (by simp)
    have h6 := P.pow_mem_of_mem h5 m (Nat.pos_of_ne_zero hm0)
    rw [hy] at h6
    exact hP.ne_top ((Ideal.eq_top_iff_one P).mpr h6)

include hH h

theorem no_root_d (η : L) (hη : IsPrimitiveRoot η d) : False := by
  have : Fact d.Prime := ⟨hH.2.1⟩
  obtain ⟨Q, hQp, hQl, -⟩ := exists_prime_mem L d hH.2.1
  have hge := Mu.mu_le_ram d Q (d - 1) (Mu.mu_mem_pow d Q η hη)
  have hd := hH.2.2.2.1
  have hle := (Mu.mu_ram_bound hH.toHypOdd h d (by omega) Q).1
  omega

theorem iod_fix (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (hσ : galE e ζ a b σ = ((1, -1), 1)) (x : hostE ζ a b)
    (hx : ∃ m : ℕ, 0 < m ∧ x ^ m = 1) : σ x = x := by
  obtain ⟨n, hn, hxn⟩ := hx
  have hfin : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, hxn⟩
  have hmpos : 0 < orderOf x := orderOf_pos_iff.2 hfin
  have hprim : IsPrimitiveRoot x (orderOf x) := IsPrimitiveRoot.orderOf x
  have hd : ¬ d ∣ orderOf x := by
    rintro ⟨k, hk⟩
    have hη : IsPrimitiveRoot (x ^ k) d := hprim.pow hmpos (by rw [hk, mul_comm])
    exact no_root_d hH h _ (hη.map_of_injective (algebraMap (hostE ζ a b) L).injective)
  have : Fact d.Prime := ⟨hH.2.1⟩
  obtain ⟨P, hPp, hPl, -⟩ := exists_prime_mem (hostE ζ a b) d hH.2.1
  have hin := ((hostInertia e q d hH L ζ a b h σ).2.2 P).mpr (Or.inr hσ)
  have hint : IsIntegral ℤ x := hprim.isIntegral hmpos
  let X : 𝓞 (hostE ζ a b) := ⟨x, hint⟩
  have hX : X ^ orderOf x = 1 := by
    apply RingOfIntegers.ext
    have : ((X ^ orderOf x : 𝓞 (hostE ζ a b)) : hostE ζ a b) = (X : hostE ζ a b) ^ orderOf x := by push_cast; rfl
    rw [this]
    exact hprim.pow_eq_one
  have hX' : (σ • X) ^ orderOf x = 1 := by rw [← smul_pow', hX, smul_one]
  have hm : ((orderOf x : ℕ) : 𝓞 (hostE ζ a b)) ∉ P := by
    intro h0
    have h1 := (odd_intCast_mem_iff d P ((orderOf x : ℕ) : ℤ)).mp (by exact_mod_cast h0)
    exact hd (by exact_mod_cast h1)
  have := eq_of_pow_eq_one P hm hX' hX (hin X)
  exact congrArg (fun y : 𝓞 (hostE ζ a b) => (y : hostE ζ a b)) this

theorem conj_mul_self (x : hostE ζ a b) (hx : ∃ m : ℕ, 0 < m ∧ x ^ m = 1) : x * conjE hH.toHypOdd h x = 1 := by
  obtain ⟨n, hn, hxn⟩ := hx
  let ψ : hostE ζ a b →+* ℂ := Classical.choice inferInstance
  apply ψ.injective
  have h1 : ‖ψ x‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hxn, map_one]) hn.ne'
  rw [map_mul, conjE_apply, Complex.mul_conj', h1, map_one]
  simp

theorem norm_mu (x : hostE ζ a b) (hx : ∃ m : ℕ, 0 < m ∧ x ^ m = 1) : Algebra.norm (KinE ζ a b) x = 1 := by
  classical
  have hqd := hH.toHypOdd
  have := hostE_isGalois hqd h
  have : IsGalois (KinE ζ a b) (hostE ζ a b) := IsGalois.tower_top_of_isGalois ℚ _ _
  obtain ⟨ι, hι⟩ := exists_galE_eq hqd h (((1, -1), 1) : FrobeniusOrbits.GG e)
  set s₀ := conjE hqd h * ι with hs₀
  have hg : galE e ζ a b s₀ = sg e := by
    rw [hs₀, galE_mul hqd h, galE_conjE, hι]
    exact Prod.ext (show c0 * ((1, -1) : G0) = (-1, 1) by decide) (mul_one _)
  have hΨ : galE e ζ a b s₀ ∈ Psi e := by rw [hg]; rfl
  let s : hostE ζ a b ≃ₐ[KinE ζ a b] hostE ζ a b :=
    AlgEquiv.ofRingEquiv (f := s₀.toRingEquiv) (fun y => Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN.fixK s₀ hΨ y)
  have hs : ∀ y, s y = s₀ y := fun _ => rfl
  have hsx : x * s x = 1 := by
    rw [hs, hs₀, AlgEquiv.mul_apply, iod_fix hH h ι hι x hx]
    exact conj_mul_self hH h x hx
  have hss0 : s₀ * s₀ = 1 := by
    apply galE_injective (e := e) hqd h
    rw [galE_mul hqd h, hg, galE_one hqd h]
    exact Prod.ext (show ((-1, 1) : G0) * (-1, 1) = 1 by decide) (mul_one _)
  have hss : s * s = 1 := AlgEquiv.ext fun y => DFunLike.congr_fun hss0 y
  have hs1 : s ≠ 1 := by
    intro h1
    have h2 : s₀ = 1 := AlgEquiv.ext fun y => DFunLike.congr_fun h1 y
    rw [h2, galE_one hqd h] at hg
    exact absurd (congrArg (fun g : FrobeniusOrbits.GG e => g.1) hg) (show ¬ (1 : G0) = (-1, 1) by decide)
  apply (algebraMap (KinE ζ a b) (hostE ζ a b)).injective
  rw [Algebra.norm_eq_prod_automorphisms, map_one]
  refine Finset.prod_involution (fun σ _ => σ * s) (fun σ _ => ?_) (fun σ _ _ => ?_) (fun _ _ => Finset.mem_univ _)
    (fun σ _ => ?_)
  · rw [AlgEquiv.mul_apply, ← map_mul, hsx, map_one]
  · exact fun h1 => hs1 (mul_eq_left.mp h1)
  · rw [mul_assoc, hss, mul_one]

theorem principal_stable (c : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (hc : galE e ζ a b c = cc e) :
    ∃ 𝔟 : Ideal (𝓞 (hostE ζ a b)),
      differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) = 𝔟 * (c • 𝔟) ∧ 𝔟 ⊔ c • 𝔟 = ⊤ ∧
      ∀ σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, galE e ζ a b σ ∈ Psi e → σ • 𝔟 = 𝔟 := by
  obtain ⟨P2, h2, -, m2⟩ := exists_prime_mem (KinE ζ a b) 2 Nat.prime_two
  obtain ⟨Pq, hq, -, mq⟩ := exists_prime_mem (KinE ζ a b) q hH.1
  obtain ⟨B, h1, -, h3, h4, -⟩ := Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN.principalStable e q d hH L ζ a b h c hc P2 Pq h2 hq
    (by exact_mod_cast m2) mq
  exact ⟨B, h1, h3, h4⟩

end Formalism.HC.D7

end
