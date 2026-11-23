import Mathlib

namespace GlobalTheory.CompanionTheory.PerfClos

theorem exists_perfect_radical (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] (I : Ideal S)
    (hp : (p : S) = 0) :
    ∃ (T : Type) (_ : CommRing T) (i : S →+* T), (p : T) = 0 ∧
      Function.Bijective (fun t : T => t ^ p) ∧
      (∀ t : T, ∃ (k : ℕ) (x : S), t ^ p ^ k = i x) ∧
      ∀ x : S, i x = 0 ↔ x ∈ I.radical := by
  by_cases htop : I.radical = ⊤
  · haveI : Subsingleton (S ⧸ I.radical) := Ideal.Quotient.subsingleton_iff.mpr htop
    refine ⟨S ⧸ I.radical, inferInstance, Ideal.Quotient.mk I.radical, Subsingleton.elim _ _,
      ⟨fun a b _ => Subsingleton.elim a b, fun b => ⟨b, Subsingleton.elim _ _⟩⟩, fun t => ?_,
      fun x => Ideal.Quotient.eq_zero_iff_mem⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective t
    exact ⟨0, x, by simp⟩
  · haveI : Nontrivial (S ⧸ I.radical) := Ideal.Quotient.nontrivial_iff.mpr htop
    have hpQ : ((p : ℕ) : S ⧸ I.radical) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk I.radical), hp, map_zero]
    haveI : CharP (S ⧸ I.radical) p := by
      first
        | exact (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hpQ
        | exact ringChar.of_eq (CharP.ringChar_of_prime_eq_zero (Fact.out : p.Prime) hpQ)
    haveI : ExpChar (S ⧸ I.radical) p := ExpChar.prime (Fact.out : p.Prime)
    haveI : IsReduced (S ⧸ I.radical) :=
      (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical I)
    refine ⟨PerfectClosure (S ⧸ I.radical) p, inferInstance,
      (PerfectClosure.of (S ⧸ I.radical) p).comp (Ideal.Quotient.mk I.radical), ?_, ?_, ?_, ?_⟩
    · exact CharP.cast_eq_zero _ p
    · first
        | exact PerfectRing.bijective_frobenius (R := PerfectClosure (S ⧸ I.radical) p) (p := p)
        | (convert PerfectRing.bijective_frobenius (R := PerfectClosure (S ⧸ I.radical) p) (p := p) using 1
           funext t
           exact (frobenius_def _ _ t).symm)
    · intro t
      obtain ⟨n, y, hy⟩ := IsPRadical.pow_mem (i := PerfectClosure.of (S ⧸ I.radical) p) (p := p) t
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨n, x, hy.symm⟩
    · intro x
      constructor
      · intro h
        have hk : Ideal.Quotient.mk I.radical x ∈ RingHom.ker (PerfectClosure.of (S ⧸ I.radical) p) := h
        obtain ⟨n, hn⟩ := mem_pNilradical.mp
          (IsPRadical.ker_le (i := PerfectClosure.of (S ⧸ I.radical) p) (p := p) hk)
        exact Ideal.Quotient.eq_zero_iff_mem.mp (IsReduced.eq_zero _ ⟨_, hn⟩)
      · intro h
        simp [Ideal.Quotient.eq_zero_iff_mem.mpr h]

end GlobalTheory.CompanionTheory.PerfClos
