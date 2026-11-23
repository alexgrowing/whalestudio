import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
open GlobalTheory.CompanionTheory.Ar.Num

namespace PositivityTheory.Xgn.LatticeSectionAlgebra

theorem denom {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (Q : Type)
    (reg : Q → Subring Ω)
    (h3 : ∀ P : Ideal R, P.IsPrime → ∃ q, ∀ s : R, s ∉ P ↔ ((s : Ω) ≠ 0 ∧ (s : Ω)⁻¹ ∈ reg q))
    (h4 : ∀ q, ∀ a ∈ reg q, ∃ s ∈ R, s ≠ 0 ∧ s⁻¹ ∈ reg q ∧ s * a ∈ R)
    (g : Ω) (hg : g ∈ R) (a : Ω) (ha : ∀ q, g ≠ 0 → g⁻¹ ∈ reg q → a ∈ reg q) :
    ∃ n : ℕ, g ^ n * a ∈ R := by
  let I : Ideal R :=
    { carrier := {s | (s : Ω) * a ∈ R}
      add_mem' := by
        intro x y hx hy
        have := R.add_mem hx hy
        simpa [add_mul] using this
      zero_mem' := by simp
      smul_mem' := by
        intro c x hx
        have := R.mul_mem c.2 hx
        simpa [mul_assoc] using this }
  have hI : ∀ s : R, s ∈ I ↔ (s : Ω) * a ∈ R := fun s => Iff.rfl
  have hrad : (⟨g, hg⟩ : R) ∈ I.radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨hIP, hP⟩
    by_contra hgP
    obtain ⟨q, hq⟩ := h3 P hP
    obtain ⟨h0, hu⟩ := (hq _).1 hgP
    obtain ⟨s, hsR, hs0, hsu, hsa⟩ := h4 q a (ha q h0 hu)
    exact (hq ⟨s, hsR⟩).2 ⟨hs0, hsu⟩ (hIP ((hI ⟨s, hsR⟩).2 hsa))
  obtain ⟨n, hn⟩ := hrad
  refine ⟨n, ?_⟩
  have := (hI _).1 hn
  simpa using this

theorem unif {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω)
    {ι : Type} [Fintype ι] (g a : ι → Ω) (hg : ∀ i, g i ∈ R)
    (h : ∀ i, ∃ n : ℕ, g i ^ n * a i ∈ R) : ∃ n : ℕ, ∀ i, g i ^ n * a i ∈ R := by
  choose n hn using h
  refine ⟨Finset.univ.sup n, fun i => ?_⟩
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := n) (Finset.mem_univ i))
  rw [hd, add_comm, pow_add, mul_assoc]
  exact R.mul_mem (R.pow_mem (hg i) d) (hn i)

theorem some_unit {Ω : Type} [Field Ω] (A : Subring Ω) [IsLocalRing A] {k : ℕ} (c g : Fin k → Ω)
    (hc : ∀ l, c l ∈ A) (hg : ∀ l, g l ∈ A) (h : ∑ l, c l * g l = 1) :
    ∃ l, (g l)⁻¹ ∈ A ∧ g l ≠ 0 := by
  by_contra hne
  have hm : ∀ l, (⟨g l, hg l⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
    intro l
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨b, hb⟩ := hu.exists_right_inv
    have hb' : g l * (b : Ω) = 1 := by simpa using congrArg Subtype.val hb
    refine hne ⟨l, ?_, left_ne_zero_of_mul_eq_one hb'⟩
    rw [inv_eq_of_mul_eq_one_right hb']
    exact b.2
  have h1 : (∑ l, (⟨c l, hc l⟩ : A) * ⟨g l, hg l⟩) ∈ IsLocalRing.maximalIdeal A :=
    Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hm l)
  have h2 : (∑ l, (⟨c l, hc l⟩ : A) * ⟨g l, hg l⟩) = 1 := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finset_sum]
    simpa using h
  rw [h2] at h1
  exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem span_top {Ω : Type} [Field Ω] {r : ℕ} (f : Fin r → (Fin r → Ω))
    (hf : LinearIndependent Ω f) : Submodule.span Ω (Set.range f) = ⊤ :=
  hf.span_eq_top_of_card_eq_finrank' (by simp)

theorem coords {Ω : Type} [Field Ω] {r : ℕ} (f : Fin r → (Fin r → Ω))
    (hf : LinearIndependent Ω f) (e : Fin r → Ω) : ∃ a : Fin r → Ω, e = ∑ i, a i • f i := by
  have : e ∈ Submodule.span Ω (Set.range f) := by rw [span_top f hf]; trivial
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 this
  exact ⟨a, ha.symm⟩

end PositivityTheory.Xgn.LatticeSectionAlgebra

open PositivityTheory.Xgn.LatticeSectionAlgebra in
theorem PositivityTheory.Xgn.lattice_section_algebra : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (Q : Type) (reg : Q → Subring Ω) (r : ℕ) (Λ : Q → AddSubgroup (Fin r → Ω)), (∀ q, IsLocalRing (reg q)) → (∀ q, ∀ a ∈ R, a ∈ reg q) → (∀ P : Ideal R, P.IsPrime → ∃ q, ∀ s : R, s ∉ P ↔ ((s : Ω) ≠ 0 ∧ (s : Ω)⁻¹ ∈ reg q)) → (∀ q, ∀ a ∈ reg q, ∃ s ∈ R, s ≠ 0 ∧ s⁻¹ ∈ reg q ∧ s * a ∈ R) → (∀ q, ∃ g ∈ R, g ≠ 0 ∧ g⁻¹ ∈ reg q ∧ ∃ f : Fin r → (Fin r → Ω), LinearIndependent Ω f ∧ ∀ q', g⁻¹ ∈ reg q' → ∀ e, e ∈ Λ q' ↔ ∃ a : Fin r → Ω, (∀ i, a i ∈ reg q') ∧ e = ∑ i, a i • f i) → LocFree R r (⨅ q, Λ q) ∧ ∀ g ∈ R, ∀ e : Fin r → Ω, (∀ q, g ≠ 0 → g⁻¹ ∈ reg q → e ∈ Λ q) → ∃ n : ℕ, g ^ n • e ∈ ⨅ q, Λ q := by
  intro o Ω _ _ _ R Q reg r Λ h1 h2 h3 h4 h5
  choose G hGR hG0 hGu F hF hfr using h5
  have hstab : ∀ q, ∀ a ∈ reg q, ∀ e ∈ Λ q, a • e ∈ Λ q := by
    intro q a ha e he
    obtain ⟨b, hb, rfl⟩ := (hfr q q (hGu q) e).1 he
    refine (hfr q q (hGu q) _).2 ⟨fun i => a * b i, fun i => mul_mem ha (hb i), ?_⟩
    simp only [Finset.smul_sum, smul_smul]
  have hcoord : ∀ q q', (G q)⁻¹ ∈ reg q' → ∀ a : Fin r → Ω, (∑ i, a i • F q i) ∈ Λ q' →
      ∀ i, a i ∈ reg q' := by
    intro q q' hq a ha i
    obtain ⟨b, hb, hab⟩ := (hfr q q' hq _).1 ha
    rw [Fintype.linearIndependent_iffₛ.1 (hF q) a b hab i]
    exact hb i
  have htop : Ideal.span (Set.range fun q => (⟨G q, hGR q⟩ : R)) = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨q, hq⟩ := h3 P hP.isPrime
    exact (hq ⟨G q, hGR q⟩).2 ⟨hG0 q, hGu q⟩ (hle (Ideal.subset_span ⟨q, rfl⟩))
  obtain ⟨k, c, t, hsum⟩ := Submodule.mem_span_set'.1 ((Ideal.eq_top_iff_one _).1 htop)
  choose p hp using fun l => (t l).2
  have hsum' : ∑ l, (c l : Ω) * G (p l) = 1 := by
    have := congrArg Subtype.val hsum
    rw [AddSubmonoidClass.coe_finset_sum] at this
    refine Eq.trans (Finset.sum_congr rfl fun l _ => ?_) this
    rw [← hp l]
    simp
  have hcov : ∀ q, ∃ l, (G (p l))⁻¹ ∈ reg q := by
    intro q
    haveI := h1 q
    obtain ⟨l, hl, -⟩ := some_unit (reg q) (fun l => (c l : Ω)) (fun l => G (p l))
      (fun l => h2 q _ (c l).2) (fun l => h2 q _ (hGR _)) hsum'
    exact ⟨l, hl⟩
  have hsec : ∀ g ∈ R, ∀ e : Fin r → Ω, (∀ q, g ≠ 0 → g⁻¹ ∈ reg q → e ∈ Λ q) →
      ∃ n : ℕ, g ^ n • e ∈ ⨅ q, Λ q := by
    intro g hg e he
    choose a ha using fun l => coords (F (p l)) (hF _) e
    obtain ⟨n, hn⟩ := unif R (ι := Fin k × Fin r) (fun x => g * G (p x.1)) (fun x => a x.1 x.2)
      (fun x => R.mul_mem hg (hGR _)) (by
        rintro ⟨l, i⟩
        refine denom R Q reg h3 h4 _ (R.mul_mem hg (hGR _)) _ ?_
        intro q h0 hu
        have hg0 : g ≠ 0 := left_ne_zero_of_mul h0
        have hl0 := hG0 (p l)
        have e1 : g⁻¹ = G (p l) * (g * G (p l))⁻¹ := by field_simp
        have e2 : (G (p l))⁻¹ = g * (g * G (p l))⁻¹ := by field_simp
        have u1 : g⁻¹ ∈ reg q := by rw [e1]; exact mul_mem (h2 q _ (hGR _)) hu
        have u2 : (G (p l))⁻¹ ∈ reg q := by rw [e2]; exact mul_mem (h2 q _ hg) hu
        exact hcoord (p l) q u2 (a l) (ha l ▸ he q hg0 u1) i)
    refine ⟨n, AddSubgroup.mem_iInf.2 fun q => ?_⟩
    obtain ⟨l, hl⟩ := hcov q
    refine (hfr (p l) q hl _).2 ⟨fun i => g ^ n * a l i, fun i => ?_, ?_⟩
    · have hl0 := hG0 (p l)
      have e1 : g ^ n * a l i = (G (p l))⁻¹ ^ n * ((g * G (p l)) ^ n * a l i) := by
        rw [mul_pow, inv_pow]; field_simp
      show g ^ n * a l i ∈ reg q
      rw [e1]
      exact mul_mem (pow_mem hl n) (h2 q _ (hn (l, i)))
    · conv_lhs => rw [ha l]
      simp only [Finset.smul_sum, smul_smul]
  refine ⟨⟨?_, k, fun l => G (p l), fun l => c l, fun l => hGR _, fun l => (c l).2, hsum', ?_⟩, hsec⟩
  · intro a ha e he
    exact AddSubgroup.mem_iInf.2 fun q => hstab q a (h2 q a ha) e (AddSubgroup.mem_iInf.1 he q)
  · intro l
    have hl0 := hG0 (p l)
    refine ⟨F (p l), hF _, span_top _ (hF _), fun e => ⟨?_, ?_⟩⟩
    · rintro ⟨n, hn⟩
      obtain ⟨a, rfl⟩ := coords (F (p l)) (hF _) e
      refine ⟨a, fun i => denom R Q reg h3 h4 _ (hGR _) _ ?_, rfl⟩
      intro q _ hu
      refine hcoord (p l) q hu a ?_ i
      have := hstab q _ (pow_mem hu n) _ (AddSubgroup.mem_iInf.1 hn q)
      rwa [smul_smul, ← mul_pow, inv_mul_cancel₀ hl0, one_pow, one_smul] at this
    · rintro ⟨a, ha, rfl⟩
      refine hsec _ (hGR _) _ fun q _ hu => (hfr (p l) q hu _).2 ⟨a, fun i => ?_, rfl⟩
      obtain ⟨n, hn⟩ := ha i
      have e1 : a i = (G (p l))⁻¹ ^ n * (G (p l) ^ n * a i) := by
        rw [inv_pow]; field_simp
      rw [e1]
      exact mul_mem (pow_mem hu n) (h2 q _ hn)
