import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.LFun GlobalTheory.CuspRep GlobalTheory.HeckeGal.Model

namespace GlobalTheory.Published.JacquetShalikaModel

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

open NumberField IsDedekindDomain in
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] in
omit [IsTotallyComplex E] in

theorem _root_.GlobalTheory.Published.JacquetShalikaModel.infinite_places : Infinite (HeightOneSpectrum (𝓞 E)) := by
  classical
  by_contra h
  rw [not_infinite_iff_finite] at h
  have hfin : (Set.range fun P : HeightOneSpectrum (𝓞 E) =>
      Ideal.comap (algebraMap ℤ (𝓞 E)) P.asIdeal).Finite := Set.finite_range _
  apply Nat.infinite_setOf_prime
  have hinj : Set.InjOn (fun p : ℕ => Ideal.span {(p : ℤ)}) {p | p.Prime} := by
    intro p _ q _ hpq
    have := Ideal.span_singleton_eq_span_singleton.mp hpq
    rw [Int.associated_iff_natAbs] at this
    simpa using this
  refine Set.Finite.of_finite_image (hfin.subset ?_) hinj
  rintro _ ⟨p, hp, rfl⟩
  haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  obtain ⟨Q, hQ, hlies⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) (Ideal.span {(p : ℤ)})
  have hcomap : Ideal.comap (algebraMap ℤ (𝓞 E)) Q = Ideal.span {(p : ℤ)} :=
    (hlies.over).symm
  have hne : Q ≠ ⊥ := by
    rintro rfl
    have hmem : (p : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 E)) (⊥ : Ideal (𝓞 E)) :=
      hcomap ▸ Ideal.subset_span rfl
    rw [Ideal.mem_comap, Ideal.mem_bot, map_natCast, Nat.cast_eq_zero] at hmem
    exact hp.ne_zero hmem
  exact ⟨⟨Q, hQ.isPrime, hne⟩, hcomap⟩

theorem bound_ofChar {χ : HChar E} (h : χ.IsUnitary) {w : HeightOneSpectrum (𝓞 E)} (hw : χ.UnrAt w) (B : Multiset ℂˣ)
    (hB : (CG.ofChar χ).HasSat w B) : ∀ α ∈ B,
      (Ideal.absNorm w.asIdeal : ℝ) ^ (-(1 / 2) : ℝ) < ‖(α : ℂ)‖ ∧ ‖(α : ℂ)‖ < (Ideal.absNorm w.asIdeal : ℝ) ^ (1 / 2 : ℝ) := by
  obtain rfl := hB.unique (CG.hasSat_ofChar hw)
  intro α hα
  obtain rfl := Multiset.mem_singleton.1 hα
  have e : ‖((χ.val w : ℂˣ) : ℂ)‖ = 1 := h _
  have hq : (1 : ℝ) < Ideal.absNorm w.asIdeal := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm w
  rw [e]
  exact ⟨Real.rpow_lt_one_of_one_lt_of_neg hq (by norm_num), Real.one_lt_rpow hq (by norm_num)⟩

theorem bound_fails_absPow (w : HeightOneSpectrum (𝓞 E)) :
    ∃ B, (CG.ofChar (absPow E (1 / 2))).HasSat w B ∧
      ¬ ∀ α ∈ B, (Ideal.absNorm w.asIdeal : ℝ) ^ (-(1 / 2) : ℝ) < ‖(α : ℂ)‖ := by
  have h := absPow_isAbsPow E (1 / 2)
  refine ⟨_, CG.hasSat_ofChar (h.1 w), fun hh => ?_⟩
  have h1 := hh _ (Multiset.mem_singleton_self _)
  have hq : 1 < Ideal.absNorm w.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm w
  rw [h.2.1 w, Complex.norm_natCast_cpow_of_pos (zero_lt_one.trans hq), Complex.neg_re, Complex.ofReal_re] at h1
  exact lt_irrefl _ h1

theorem not_isUnitary_absPow {s : ℝ} (hs : s ≠ 0) : ¬ (CG.ofChar (absPow E s)).IsUnitary := fun h => by
  have h1 : (CG.ofChar (1 : HChar E)).IsUnitary := CG.isUnitary_ofChar fun x => by simp
  have h0 : (1 : HChar E).IsAbsPow 0 := ⟨fun v x _ => rfl, fun v => by simp [HChar.val, HChar.locK, HChar.loc],
    fun k => by simp [HChar.inf]⟩
  exact hs (CG.exponent_unique le_rfl h1 h (absPow_isAbsPow E s) h0 (by rw [CG.twist_ofChar, one_mul, CG.twist_one]))

theorem rigidity_empty {κ : Type} [Fintype κ] (m' : κ → ℕ) (π' : ∀ j, CG E (m' j)) (hm : ∀ j, 1 ≤ m' j)
    (hw : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ (B : Empty → Multiset ℂˣ) (B' : κ → Multiset ℂˣ),
      (∀ j, (π' j).HasSat w (B' j)) ∧ ∑ i, B i = ∑ j, B' j) : IsEmpty κ := by
  have := infinite_places (E := E)
  obtain ⟨w, B, B', h1, h2⟩ := hw.exists
  refine ⟨fun j => ?_⟩
  have h3 := congrArg Multiset.card h2
  simp only [Finset.univ_eq_empty, Finset.sum_empty, Multiset.card_zero, Multiset.card_sum] at h3
  have h4 := (Finset.sum_eq_zero_iff.1 h3.symm) j (Finset.mem_univ j)
  have := (h1 j).card
  have := hm j
  omega

theorem hyp_fails : ¬ ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite,
    ∃ B, (CG.ofChar (1 : HChar E)).HasSat w B ∧ (CG.ofChar (absPow E 1)).HasSat w B := fun hw => by
  have := infinite_places (E := E)
  obtain ⟨w, B, h1, h2⟩ := hw.exists
  have h := absPow_isAbsPow E 1
  have e := (h1.unique (CG.hasSat_ofChar (χ := 1) fun x _ => rfl)).symm.trans (h2.unique (CG.hasSat_ofChar (h.1 w)))
  have e2 := congrArg (fun u : ℂˣ => ‖(u : ℂ)‖) (Multiset.singleton_inj.1 e)
  have hq : 1 < Ideal.absNorm w.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm w
  simp only [h.2.1 w, Complex.norm_natCast_cpow_of_pos (zero_lt_one.trans hq), Complex.neg_re, Complex.ofReal_re] at e2
  have e3 : ‖(((1 : HChar E).val w : ℂˣ) : ℂ)‖ = 1 := by simp [HChar.val, HChar.locK, HChar.loc]
  rw [e3] at e2
  exact (Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hq) (by norm_num)).ne' e2

end GlobalTheory.Published.JacquetShalikaModel
