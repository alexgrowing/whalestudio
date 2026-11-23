import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain

namespace GlobalTheory

theorem exists_int_sub_eq_mul_of_integral_over {E : Type} [Field E] [NumberField E]
    (g : ℕ) (hg : g ≠ 0) (m : E)
    (hm : ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal →
      ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ o : 𝓞 E, (s : E) * m = o) :
    ∃ ξ c : 𝓞 E, m - (ξ : E) = (g : E) * (c : E) * m := by
  let D : Ideal (𝓞 E) := Submodule.comap (LinearMap.toSpanSingleton (𝓞 E) E m) 1
  have hD : ∀ s : 𝓞 E, s ∈ D ↔ ∃ o : 𝓞 E, (s : E) * m = o := by
    intro s
    simp only [D, Submodule.mem_comap, LinearMap.toSpanSingleton_apply, Submodule.mem_one]
    constructor
    · rintro ⟨y, hy⟩; exact ⟨y, by rw [Algebra.smul_def] at hy; exact hy.symm⟩
    · rintro ⟨o, ho⟩; exact ⟨o, by rw [Algebra.smul_def]; exact ho.symm⟩
  have htop : D ⊔ Ideal.span {(g : 𝓞 E)} = ⊤ := by
    by_contra hne
    obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_le_maximal _ hne
    have hgQ : (g : 𝓞 E) ∈ Q := hQ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hg0 : (g : 𝓞 E) ≠ 0 := by exact_mod_cast hg
    have hQbot : Q ≠ ⊥ := fun h => hg0 (by rw [h] at hgQ; simpa using hgQ)
    obtain ⟨s, hs, o, ho⟩ := hm ⟨Q, hQmax.isPrime, hQbot⟩ hgQ
    exact hs (hQ (Ideal.mem_sup_left ((hD s).2 ⟨o, ho⟩)))
  have h1 : (1 : 𝓞 E) ∈ D ⊔ Ideal.span {(g : 𝓞 E)} := by rw [htop]; trivial
  obtain ⟨d, hd, y, hy, hdy⟩ := Submodule.mem_sup.1 h1
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  obtain ⟨o, ho⟩ := (hD d).1 hd
  refine ⟨o, c, ?_⟩
  have e := congrArg (fun x : 𝓞 E => (x : E)) hdy
  push_cast at e
  rw [← ho]
  linear_combination (-m) * e

theorem admissible_of_congr_unitriangular {E : Type} [Field E] [NumberField E] [StarRing E]
    {S : HSpace E} {r : ℕ} (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (hg : g ≠ 0) {T T' : E}
    (F : LFlag S r T) (F' : LFlag S r T') (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hlow : ∀ a b, b < a → M a b = 0) (hdiag : ∀ a, M a a = 1)
    (hint : ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∀ a b,
      ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ o : 𝓞 E, (s : E) * M a b = o)
    (hloc : ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∀ a,
      frame F a ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ))
    (hmod : ∀ b, ModG S Λ g (frame F' b - ∑ a, M a b • frame F a)) :
    IsAdmissible Λ g F F' := by
  classical
  have key : ∀ a b, ∃ ξ c : 𝓞 E, M a b - (ξ : E) = (g : E) * (c : E) * M a b :=
    fun a b => exists_int_sub_eq_mul_of_integral_over g hg (M a b) (fun P hP => hint P hP a b)
  let ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E) := fun a b =>
    if b < a then 0 else if a = b then 1 else (key a b).choose
  have hξ : ∀ a b, ∃ c : 𝓞 E, M a b - ((ξ a b : 𝓞 E) : E) = (g : E) * (c : E) * M a b := by
    intro a b
    by_cases h1 : b < a
    · exact ⟨0, by simp [ξ, h1, hlow a b h1]⟩
    · by_cases h2 : a = b
      · subst h2; exact ⟨0, by simp [ξ, hdiag]⟩
      · obtain ⟨c, hc⟩ := (key a b).choose_spec
        exact ⟨c, by simpa [ξ, h1, h2] using hc⟩
  refine ⟨ξ, fun a b hab => by simp [ξ, hab], fun a => by simp [ξ], ?_⟩
  intro b P hP
  haveI := P.isPrime
  have hsplit : frame F' b - frameAct (frame F) ξ b =
      (frame F' b - ∑ a, M a b • frame F a) + ∑ a, (M a b - (ξ a b : E)) • frame F a := by
    simp only [frameAct, sub_smul, Finset.sum_sub_distrib]; abel
  rw [hsplit]
  refine Submodule.add_mem _ (hmod b P hP) (Submodule.sum_mem _ fun a _ => ?_)
  obtain ⟨c, hc⟩ := hξ a b
  obtain ⟨t, ht, htf⟩ := hloc P hP a
  obtain ⟨s, hs, o, ho⟩ := hint P hP a b
  refine ⟨s * t, P.asIdeal.primeCompl.mul_mem hs ht, ?_⟩
  rw [hc]
  have e : (s * t) • (((g : E) * (c : E) * M a b) • frame F a) =
      ((g : 𝓞 E) * (c * o)) • (t • frame F a) := by
    rw [← algebraMap_smul E (s * t), ← algebraMap_smul E ((g : 𝓞 E) * (c * o)),
      ← algebraMap_smul E t, smul_smul, smul_smul]
    congr 1
    simp only [map_mul, map_natCast]
    change (s : E) * (t : E) * ((g : E) * (c : E) * M a b) = (g : E) * ((c : E) * (o : E)) * (t : E)
    rw [← ho]; ring
  rw [e]
  exact Submodule.smul_mem_smul (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)) htf

end GlobalTheory
