import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CyclotomicConjugation.QuadConjAlt
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.UnipotentFundamentalDomain

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)
open UpperTheory.Gal.CertificateRingHomMap UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂

private theorem val_two (K : Type) [Field K] [NumberField K] (hK : Module.finrank ℚ K ≤ 2)
    (P Q : HeightOneSpectrum (𝓞 K)) (hne : P ≠ Q) (h : P.asIdeal.under ℤ = Q.asIdeal.under ℤ) :
    Valued.v ((Ideal.absNorm P.asIdeal : ℕ) : P.adicCompletion K) = WithZero.exp (-1 : ℤ) :=
  _root_.UpperTheory.Reformulated.B.UnipotentFundamentalDomain.val_two K hK P Q hne h

private theorem finrank_Kx_le {E : Type} [Field E] [NumberField E] (d : ℕ) (x : E)
    (hx : x ^ 2 = -(d : E)) : Module.finrank ℚ (Kx x) ≤ 2 := by
  have hi : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  have e : Module.finrank ℚ (Kx x) = (minpoly ℚ x).natDegree := IntermediateField.adjoin.finrank hi
  rw [e]
  have hm : (Polynomial.X ^ 2 + Polynomial.C (d : ℚ)).Monic :=
    Polynomial.monic_X_pow_add_C _ two_ne_zero
  have hz : Polynomial.aeval x (Polynomial.X ^ 2 + Polynomial.C (d : ℚ)) = 0 := by
    simp [hx]
  have hd := minpoly.min ℚ x hm hz
  have := Polynomial.natDegree_le_natDegree hd
  rwa [Polynomial.natDegree_X_pow_add_C] at this

private theorem sameK_iff {E : Type} [Field E] [NumberField E] (x : E) (w w' : Plc E) :
    SameK x w w' ↔ w.under (𝓞 (Kx x)) = w'.under (𝓞 (Kx x)) := by
  constructor
  · intro h
    refine HeightOneSpectrum.ext (Ideal.ext fun a => ?_)
    exact h (algebraMap (𝓞 (Kx x)) (𝓞 E) a) ((a : Kx x)).2
  · intro h y hy
    have hk : IsIntegral ℤ (⟨y, hy⟩ : Kx x) := by
      have h1 : IsIntegral ℤ (algebraMap (Kx x) E ⟨y, hy⟩) := y.isIntegral_coe
      exact (isIntegral_algebraMap_iff (algebraMap (Kx x) E).injective).1 h1
    obtain ⟨a, ha⟩ : ∃ a : 𝓞 (Kx x), algebraMap (𝓞 (Kx x)) (𝓞 E) a = y :=
      ⟨⟨⟨y, hy⟩, hk⟩, RingOfIntegers.ext rfl⟩
    have hm : ∀ u : Plc E, a ∈ (u.under (𝓞 (Kx x))).asIdeal ↔ y ∈ u.asIdeal := by
      intro u
      rw [← ha]
      rfl
    rw [← hm w, ← hm w', h]

private theorem under_int_cj {E : Type} [Field E] [NumberField E] [IsCMField E] (K : Type) [Field K]
    [NumberField K] [Algebra K E] (w : Plc E) :
    (w.under (𝓞 K)).asIdeal.under ℤ = ((cj w).under (𝓞 K)).asIdeal.under ℤ := by
  have key : (cj w).asIdeal = Ideal.comap (RingOfIntegers.mapRingEquiv (conjE E)) w.asIdeal :=
    (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (GlobalTheory.CuspRep.conjPl_conjSrc (conjE E) w)
  have hm : ∀ (u : Plc E) (n : ℤ), n ∈ (u.under (𝓞 K)).asIdeal.under ℤ ↔ (n : 𝓞 E) ∈ u.asIdeal := by
    intro u n
    have e : algebraMap (𝓞 K) (𝓞 E) (algebraMap ℤ (𝓞 K) n) = (n : 𝓞 E) := by simp
    rw [← e]
    rfl
  refine Ideal.ext fun n => ?_
  rw [hm, hm, key, Ideal.mem_comap, map_intCast]

theorem UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.kPlace :
    UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.KPlace := by
  intro E _ _ _ d x _ hx
  refine ⟨sameK_iff x, fun w hw => ?_⟩
  rw [sameK_iff] at hw
  exact val_two (Kx x) (finrank_Kx_le d x hx) _ _ (Ne.symm hw) (under_int_cj (Kx x) w)
