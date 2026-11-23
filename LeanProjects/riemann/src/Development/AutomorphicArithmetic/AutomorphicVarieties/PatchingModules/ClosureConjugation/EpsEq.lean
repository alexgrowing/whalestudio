import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrAlg
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

theorem UpperTheory.V.Pa.eps_eq :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K] {r : Resid G.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} (P : OoPt h x u), ∀ g : G.G₀, P.f (G.frame.eps O B g : Bˣ) = ((G0.frame.eps ℤ_[l] x.A (h.p₀ g) : x.Aˣ) : x.A) ∧ h.p₀ (G.frame.conj g) = G0.frame.conj (h.p₀ g) := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P g
  have hl : (l : x.K) = 0 := by
    by_contra hn
    obtain ⟨p, hp⟩ := CharP.exists x.K
    have hpp : p.Prime := CharP.char_is_prime x.K p
    have hne : p ≠ l := by rintro rfl; exact hn (CharP.cast_eq_zero _ _)
    have h6 : IsUnit ((p : ℤ) : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff]
      refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun hlt => hne ?_)
      rw [PadicInt.norm_int_lt_one_iff_dvd] at hlt
      exact ((Nat.prime_dvd_prime_iff_eq Fact.out hpp).1 (by exact_mod_cast hlt)).symm
    have h8 := h6.map (algebraMap ℤ_[l] x.K)
    rw [map_intCast, Int.cast_natCast, CharP.cast_eq_zero] at h8
    exact not_isUnit_zero h8
  have hA : (l : x.A) = 0 := by rw [← map_natCast (PowerSeries.C (R := x.K)), hl, map_zero]
  have key : ∀ φ : ℤ_[l] →+* x.A, ∀ a, φ a = (a.zmodRepr : x.A) := fun φ a => by
    have h1 := PadicInt.sub_zmodRepr_mem a
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h1
    obtain ⟨c, hc⟩ := h1
    have h2 := congrArg φ hc
    rw [map_mul, map_natCast, hA, mul_zero, map_sub, map_natCast] at h2
    exact sub_eq_zero.1 h2.symm
  refine ⟨?_, Subtype.ext ?_⟩
  · have e1 := key (P.f.toRingHom.comp ((algebraMap O B).comp (algebraMap ℤ_[l] O))) (G.ε g : ℤ_[l])
    have e2 := key ((algebraMap ℤ_[l] x.A).comp (algebraMap ℤ_[l] ℤ_[l])) (G0.ε (h.p g) : ℤ_[l])
    rw [h.ε] at e2
    refine e1.trans (e2.symm.trans ?_)
    rw [← h.ε]; rfl
  · show h.p (G.c * g * G.c⁻¹) = G0.c * h.p g * G0.c⁻¹
    rw [map_mul, map_mul, map_inv, h.c]
