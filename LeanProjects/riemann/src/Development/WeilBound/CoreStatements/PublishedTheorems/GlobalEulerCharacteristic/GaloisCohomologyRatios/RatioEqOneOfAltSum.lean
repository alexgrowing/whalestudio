import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.NormalOfGsOpenSubgroupNormal
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.RealHerbrand
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.Coprime

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.X

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K : FiniteSubfield} {S : Set (HeightOneSpectrum (𝓞 K.1))} {ℓ : ℕ} [Fact ℓ.Prime]

theorem pow_ratio_eq_one {ι : Type*} [Fintype ι] (ℓ : ℕ) (hl0 : (ℓ : ℚ) ≠ 0) (a0 a1 a2 m c : ℕ) (b : ι → ℕ)
    (h : (a0 : ℤ) - a1 + a2 = ∑ v, (b v : ℤ) - c * m) :
    ((ℓ ^ a0 : ℕ) : ℚ) * ((ℓ ^ a2 : ℕ) : ℚ) / ((ℓ ^ a1 : ℕ) : ℚ) * ((ℓ ^ m : ℕ) : ℚ) ^ c /
      ∏ v, ((ℓ ^ b v : ℕ) : ℚ) = 1 := by
  push_cast
  rw [Finset.prod_pow_eq_pow_sum, ← pow_mul, div_eq_one_iff_eq (pow_ne_zero _ hl0),
    div_mul_eq_mul_div, div_eq_iff (pow_ne_zero _ hl0), ← pow_add, ← pow_add, ← pow_add]
  congr 1
  have h' : ((a0 + a2 + m * c : ℕ) : ℤ) = ((∑ v, b v + a1 : ℕ) : ℤ) := by
    push_cast
    linarith
  exact_mod_cast h'

open scoped Classical in

theorem ratio_eq_one_of_altSum [Finite S] (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal)
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
    (hMl : ∀ m : M, ℓ • m = 0)
    (h : (Module.finrank (ZMod ℓ) (cohomology (zmodRepOfTorsion ℓ M hMl) 0) : ℤ) - Module.finrank (ZMod ℓ) (cohomology (zmodRepOfTorsion ℓ M hMl) 1) +
        Module.finrank (ZMod ℓ) (cohomology (zmodRepOfTorsion ℓ M hMl) 2) =
      ∑ v : {v : InfinitePlace K.1 // v.IsReal},
          (Module.finrank (ZMod ℓ) (cohomology (Rep.res (gsRealFamily S ιr v).toMonoidHom (zmodRepOfTorsion ℓ M hMl)) 0) : ℤ) -
        Fintype.card (InfinitePlace K.1) * Module.finrank (ZMod ℓ) (zmodRepOfTorsion ℓ M hMl)) :
    gsEulerRatio S M ιr = 1 := by
  have hlp : ℓ.Prime := Fact.out
  have : Finite (zmodRepOfTorsion ℓ M hMl) := ‹Finite M›
  have : Module.Finite (ZMod ℓ) (zmodRepOfTorsion ℓ M hMl) := Module.Finite.of_finite
  have hcardM : Nat.card M = ℓ ^ Module.finrank (ZMod ℓ) (zmodRepOfTorsion ℓ M hMl) :=
    natCard_eq_pow_finrank_zmod ℓ (zmodRepOfTorsion ℓ M hMl)
  have hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((Nat.card M : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S := by
    intro v hv
    by_contra hvS
    apply hℓS v hvS
    rw [hcardM, Nat.cast_pow] at hv
    exact v.isPrime.mem_of_pow_mem _ hv
  have hcard : ∀ i ≤ 2, Nat.card (cohomology M i) =
      ℓ ^ Module.finrank (ZMod ℓ) (cohomology (zmodRepOfTorsion ℓ M hMl) i) := fun i hi => by
    have := finite_cohomology_gs K S M hS i hi
    have : Finite (cohomology (zmodRepOfTorsion ℓ M hMl) i) :=
      Finite.of_equiv _ (cohomologyZModEquiv ℓ M hMl i).toEquiv
    rw [Nat.card_congr (cohomologyZModEquiv ℓ M hMl i).toEquiv, natCard_eq_pow_finrank_zmod ℓ]
  have hreal : ∀ v, gsRealH0Card S M ιr v = ℓ ^ Module.finrank (ZMod ℓ)
      (cohomology (Rep.res (gsRealFamily S ιr v).toMonoidHom (zmodRepOfTorsion ℓ M hMl)) 0) := fun v => by
    have := gsReal_finite_cohomology S ιr M v 0 (by norm_num)
    let e := cohomologyAddEquivOfEquiv (A := Rep.res (gsRealFamily S ιr v).toMonoidHom M)
      (A' := Rep.res (gsRealFamily S ιr v).toMonoidHom (zmodRepOfTorsion ℓ M hMl))
      (zmodRepOfTorsionEquiv ℓ M hMl) (fun _ _ => rfl) 0
    have : Finite (cohomology (Rep.res (gsRealFamily S ιr v).toMonoidHom (zmodRepOfTorsion ℓ M hMl)) 0) :=
      Finite.of_equiv _ e.toEquiv
    exact (Nat.card_congr e.toEquiv).trans (natCard_eq_pow_finrank_zmod ℓ _)
  have hl0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hlp.ne_zero
  unfold gsEulerRatio
  rw [eulerChar_eq, hcard 0 (by norm_num), hcard 1 (by norm_num), hcard 2 (by norm_num), hcardM,
    Finset.prod_congr rfl (fun v _ => by rw [hreal v])]
  exact pow_ratio_eq_one ℓ hl0 _ _ _ _ _ _ h

end PositivityTheory.Lit1.GEN.X
