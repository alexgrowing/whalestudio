import Development.EtaleCohomology.EtaleSheaves.CompCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.CoverCut LateralTheory.E.BuildCut LateralTheory.E.CompCut

namespace LateralTheory.E.LocACPf

variable {W : Type} [CommRing W]

lemma idem_split {e : W} (he : IsIdempotentElem e) : e * (1 - e) = 0 := by
  rw [mul_sub, mul_one, he.eq, sub_self]

lemma map_zero_of_mem (hW : ProdACF W) (p : Ideal W) [p.IsPrime] {a : W} (ha : a ∈ p) :
    algebraMap W (Localization.AtPrime p) a = 0 := by
  obtain ⟨e, u, he, hu, rfl⟩ := hW.2 a
  have heq : e ∈ p := by
    rcases (inferInstance : p.IsPrime).mem_or_mem ha with h | h
    · exact h
    · exact absurd (p.eq_top_of_isUnit_mem h hu) (inferInstance : p.IsPrime).ne_top
  have h1 : (1 - e) ∈ p.primeCompl := by
    intro h
    have : (1 : W) ∈ p := by simpa using p.add_mem heq h
    exact (inferInstance : p.IsPrime).ne_top ((Ideal.eq_top_iff_one _).2 this)
  rw [IsLocalization.map_eq_zero_iff p.primeCompl]
  refine ⟨⟨1 - e, h1⟩, ?_⟩
  show (1 - e) * (e * u) = 0
  rw [← mul_assoc, mul_comm (1 - e), idem_split he, zero_mul]

lemma map_idem_one (hW : ProdACF W) (p : Ideal W) [p.IsPrime] {e : W} (he : IsIdempotentElem e) (hne : e ∉ p) :
    algebraMap W (Localization.AtPrime p) e = 1 := by
  have h1 : (1 - e) ∈ p := by
    rcases (inferInstance : p.IsPrime).mem_or_mem (show e * (1 - e) ∈ p by rw [idem_split he]; exact p.zero_mem) with h | h
    · exact absurd h hne
    · exact h
  have := map_zero_of_mem hW p h1
  rw [map_sub, map_one, sub_eq_zero] at this
  exact this.symm

lemma surj (hW : ProdACF W) (p : Ideal W) [p.IsPrime] :
    Function.Surjective (algebraMap W (Localization.AtPrime p)) := by
  intro x
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl x
  obtain ⟨e, u, he, hu, hs⟩ := hW.2 (s : W)
  have hne : e ∉ p := fun h => s.2 (hs ▸ p.mul_mem_right u h)
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  refine ⟨a * e * v, ?_⟩
  rw [eq_comm, IsLocalization.mk'_eq_iff_eq_mul, ← map_mul, hs]
  have : a * e * v * (e * u) = a * e * e * (v * u) := by ring
  rw [this, hv, mul_one, mul_assoc, he.eq, map_mul, map_idem_one hW p he hne, mul_one]

theorem LocAC_of : LocAC := by
  intro W _ hW q
  have := q.isPrime
  set p := q.asIdeal
  constructor
  · rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← Localization.AtPrime.map_eq_maximalIdeal,
      Ideal.map_eq_bot_iff_le_ker]
    intro a ha
    exact map_zero_of_mem hW p ha
  · intro P hP hdeg
    have hl : P ∈ Polynomial.lifts (algebraMap W (Localization.AtPrime p)) := by
      obtain ⟨Q, hQ⟩ := Polynomial.map_surjective _ (surj hW p) P
      exact Polynomial.mem_lifts _ |>.2 ⟨Q, hQ⟩
    obtain ⟨Q, hQ, hdQ, hmQ⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hP
    obtain ⟨r, hr⟩ := hW.1 Q hmQ (hdQ ▸ hdeg)
    refine ⟨algebraMap W _ r, ?_⟩
    rw [← hQ, Polynomial.eval_map, Polynomial.eval₂_at_apply, hr, map_zero]

end LateralTheory.E.LocACPf
