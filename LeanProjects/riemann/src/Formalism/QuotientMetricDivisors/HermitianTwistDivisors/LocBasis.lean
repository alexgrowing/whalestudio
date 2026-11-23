import Mathlib
import Formalism.QuotientMetricDivisors.ProdFormula

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.DivisionValues

namespace SemilocalBasisHermitianTwistDivisors

variable {K : Type} [Field K] [NumberField K] [StarRing K]

lemma mem_loc_iff' (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (M : Submodule (𝓞 K) (Fin d → K))
    (x : Fin d → K) :
    x ∈ Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal M ↔
      ∃ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal, s • x ∈ M :=
  Iff.rfl

lemma mem_hcompl (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) (h1 : x ∉ w.asIdeal)
    (h2 : x ∉ (conjPl w).asIdeal) : x ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal := by
  apply Submonoid.subset_closure
  refine ⟨h1, fun t ht htw => h2 ?_⟩
  have hct : cO K t = x := by
    apply RingOfIntegers.ext
    change star (t : K) = (x : K)
    have ht' : (t : K) = star (x : K) := ht
    rw [ht', star_star]
  rw [← hct]
  exact Ideal.mem_map_of_mem _ htw

lemma hcompl_le (w : HeightOneSpectrum (𝓞 K)) :
    Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal ≤ nonZeroDivisors (𝓞 K) := by
  apply Submonoid.closure_le.mpr
  intro s hs
  apply mem_nonZeroDivisors_of_ne_zero
  rintro rfl
  exact hs.1 w.asIdeal.zero_mem

abbrev A (w : HeightOneSpectrum (𝓞 K)) : Subalgebra (𝓞 K) K :=
  Localization.subalgebra.ofField K (Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal) (hcompl_le w)

lemma mem_A (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    x ∈ A w ↔ ∃ (a s : 𝓞 K) (_ : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal),
      x = algebraMap (𝓞 K) K a * (algebraMap (𝓞 K) K s)⁻¹ :=
  Iff.rfl

lemma algebraMap_ne_zero (w : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K}
    (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal) : algebraMap (𝓞 K) K s ≠ 0 :=
  IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hcompl_le w hs)

lemma primes_finite (w : HeightOneSpectrum (𝓞 K)) :
    {P : Ideal (A w) | P.IsPrime}.Finite := by
  apply ((({⊥, w.asIdeal, (conjPl w).asIdeal} : Set (Ideal (𝓞 K))).toFinite.image
    (Ideal.map (algebraMap (𝓞 K) (A w))))).subset
  intro P hP
  have hP' : P.IsPrime := hP
  obtain ⟨hQ, hdisj⟩ :=
    (IsLocalization.isPrime_iff_isPrime_disjoint (Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal) (A w) P).mp hP'
  refine ⟨P.comap (algebraMap (𝓞 K) (A w)), ?_,
    IsLocalization.map_under (Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal) (A w) P⟩
  set Q := P.comap (algebraMap (𝓞 K) (A w))
  have hsub : (Q : Set (𝓞 K)) ⊆ (w.asIdeal : Set (𝓞 K)) ∪ ((conjPl w).asIdeal : Set (𝓞 K)) := by
    intro x hx
    by_contra hn
    simp only [Set.mem_union, SetLike.mem_coe, not_or] at hn
    exact Set.disjoint_left.mp hdisj (mem_hcompl w x hn.1 hn.2) hx
  by_cases hb : Q = ⊥
  · exact Or.inl hb
  have hmax : Q.IsMaximal := hQ.isMaximal hb
  rcases Ideal.subset_union.mp hsub with h | h
  · exact Or.inr (Or.inl (hmax.eq_of_le w.isPrime.ne_top h))
  · exact Or.inr (Or.inr (hmax.eq_of_le (conjPl w).isPrime.ne_top h))

lemma mem_loc_iff_span (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (M : Submodule (𝓞 K) (Fin d → K))
    (x : Fin d → K) :
    x ∈ Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal M ↔ x ∈ Submodule.span (A w) (M : Set (Fin d → K)) := by
  constructor
  · rintro ⟨s, hs, hsx⟩
    have hs0 := algebraMap_ne_zero w hs
    have hu : (algebraMap (𝓞 K) K s)⁻¹ ∈ A w := (mem_A w _).mpr ⟨1, s, hs, by simp⟩
    have hx : x = (⟨_, hu⟩ : A w) • (s • x) := by
      rw [Subalgebra.smul_def, ← algebraMap_smul K s x, smul_smul]
      simp [hs0]
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hsx)
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact (mem_loc_iff' w M y).mpr ⟨1, one_mem _, by simpa using hy⟩
    | zero => exact Submodule.zero_mem _
    | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
    | smul a y _ hy =>
      obtain ⟨s, hs, hsy⟩ := (mem_loc_iff' w M y).mp hy
      obtain ⟨r, t, ht, hat⟩ := (mem_A w a).mp a.2
      refine (mem_loc_iff' w M _).mpr ⟨t * s, mul_mem ht hs, ?_⟩
      have ht0 := algebraMap_ne_zero w ht
      have he : (t * s) • (a • y) = r • (s • y) := by
        rw [Subalgebra.smul_def, hat, ← algebraMap_smul K (t * s), ← algebraMap_smul K r,
          ← algebraMap_smul K s, smul_smul, smul_smul]
        congr 1
        rw [map_mul]
        field_simp
      rw [he]
      exact M.smul_mem r hsy

end SemilocalBasisHermitianTwistDivisors

open SemilocalBasisHermitianTwistDivisors in

theorem semilocal_basis_exists : LocBasisEx := by
  intro K _ _ _ d L hL w
  have : IsDedekindDomain (A w) :=
    IsLocalization.isDedekindDomain (𝓞 K) (hcompl_le w) (A w)
  have : IsPrincipalIdealRing (A w) := IsPrincipalIdealRing.of_finite_primes (primes_finite w)
  set N : Submodule (A w) (Fin d → K) := Submodule.span (A w) (L : Set (Fin d → K)) with hN
  have : Module.Finite (A w) N := by
    obtain ⟨s, hs⟩ := hL.fg
    rw [Module.Finite.iff_fg]
    refine ⟨s, ?_⟩
    rw [hN, ← hs, Submodule.span_span_of_tower]
  have : Module.IsTorsionFree (A w) N := inferInstance
  let b := Module.Free.chooseBasis (A w) N
  let v : Module.Free.ChooseBasisIndex (A w) N → Fin d → K := fun i => (b i : Fin d → K)
  have hliA : LinearIndependent (A w) v := b.linearIndependent.map' N.subtype N.ker_subtype
  have hli : LinearIndependent K v := (LinearIndependent.iff_fractionRing (A w) K).mp hliA
  have hspanA : Submodule.span (A w) (Set.range v) = N := by
    have : Set.range v = N.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hspan : ⊤ ≤ Submodule.span K (Set.range v) := by
    rw [← hL.span_eq_top, Submodule.span_le]
    intro x hx
    have hxN : x ∈ Submodule.span (A w) (Set.range v) := by
      rw [hspanA]; exact Submodule.subset_span hx
    exact Submodule.span_le_restrictScalars (A w) K _ hxN
  let bK : Basis _ K (Fin d → K) := Basis.mk hli hspan
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex (A w) N) = d := by
    rw [← Module.finrank_eq_card_basis bK, Module.finrank_fin_fun]
  let e := Fintype.equivFinOfCardEq hcard
  refine ⟨v ∘ e.symm, hli.comp _ e.symm.injective, ?_⟩
  ext x
  rw [mem_loc_iff_span, mem_loc_iff_span, Submodule.span_span_of_tower, EquivLike.range_comp,
    hspanA]

end Formalism.DivisionValues
