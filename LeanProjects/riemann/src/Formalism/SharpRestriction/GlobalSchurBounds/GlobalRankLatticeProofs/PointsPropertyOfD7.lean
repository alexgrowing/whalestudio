import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.NoThreeConsecutiveThickPlaces
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts

noncomputable section

namespace Formalism.MainNotions.UnusedSlot33

open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.TwoAdicCyclotomicDecomposition Ideal
open scoped Pointwise
open Formalism.MainNotions.UnusedSlot33.SlopeTestRemainingChoices

namespace SlopeTestRemainingChoices

theorem span_prime {p : ℕ} (hp : p.Prime) : (span {(p : ℤ)}).IsPrime := by
  exact (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp)

theorem span_ne_bot {p : ℕ} (hp : p.Prime) : span {(p : ℤ)} ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast hp.ne_zero

private theorem ram_of_unit (D : D7) (p : ℕ) (hp : p.Prime) (hN : p ∣ D.host.condN)
    (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})]
    (u : (ZMod D.host.condN)ˣ) (hu : (u : ZMod D.host.condN).val ≡ 1 [MOD D.host.condN / p])
    (hu1 : D.host.art u ≠ 1) :
    ∃ σ : D.host.E ≃ₐ[ℚ] D.host.E, σ ≠ 1 ∧ ∀ x : 𝓞 D.host.E, σ • x - x ∈ P := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hu' : (u : ZMod D.host.condN).val ≡ 1 [MOD ordCompl[p] D.host.condN] := by
    by_cases hN0 : D.host.condN = 0
    · have h0 : ordCompl[p] D.host.condN = D.host.condN / p := by
        rw [hN0]
        simp
      rw [h0]
      exact hu
    · apply Nat.ModEq.of_dvd _ hu
      apply Nat.dvd_div_of_mul_dvd
      have hk : 1 ≤ D.host.condN.factorization p := hp.factorization_pos_of_dvd hN0 hN
      have hsplit := Nat.ordProj_mul_ordCompl_eq_self D.host.condN p
      conv_rhs => rw [← hsplit]
      exact Nat.mul_dvd_mul_right (dvd_pow_self p (by omega : D.host.condN.factorization p ≠ 0)) _
  refine ⟨D.host.gal.symm (D.host.art u), ?_, ?_⟩
  · intro h1
    apply hu1
    have := congrArg D.host.gal h1
    rwa [MulEquiv.apply_symm_apply, map_one] at this
  · exact (D.host.der.inertia p P _).2 ⟨u, hu', by rw [MulEquiv.apply_symm_apply]⟩

private theorem exists_unit_q (D : D7) : ∃ u : (ZMod D.host.condN)ˣ,
    (u : ZMod D.host.condN).val ≡ 1 [MOD D.host.condN / D.host.q] ∧ D.host.art u ≠ 1 := by
  have hq := D.host.q_prime
  have hq4 := D.host.q_mod_four
  have hco := D.host.coprime_QSd_q
  obtain ⟨x, hx1, hx2⟩ := Nat.chineseRemainder hco 1 (D.host.q - 1)
  have hN : D.host.condN = (D.host.QS * D.host.d) * D.host.q := by
    simp only [Formalism.HC.HostRaw.condN]; ring
  have hq1 : Nat.Coprime (D.host.q - 1) D.host.q := by
    exact (Nat.coprime_self_sub_left hq.one_le).2 (Nat.coprime_one_left _)
  have hcop : Nat.Coprime x D.host.condN := by
    rw [hN]
    refine Nat.Coprime.mul_right ?_ ?_
    · rw [Nat.Coprime, hx1.gcd_eq, Nat.gcd_one_left]
    · rw [Nat.Coprime, hx2.gcd_eq]; exact hq1
  have hval := D.host.val_unitOfCoprime hcop
  refine ⟨ZMod.unitOfCoprime x hcop, ?_, fun h1 => ?_⟩
  · have hd : D.host.condN / D.host.q = D.host.QS * D.host.d := by
      rw [hN, Nat.mul_div_cancel _ hq.pos]
    rw [hd]
    exact (hval.of_dvd (hN ▸ dvd_mul_right _ _)).trans hx1
  · have h := D.host.flPS (ZMod.unitOfCoprime x hcop)
    rw [h1, Formalism.HC.jacobi_congr ((hval.of_dvd D.host.q_dvd_condN).trans hx2)] at h
    have h3 : jacobiSym ((D.host.q - 1 : ℕ) : ℤ) D.host.q = jacobiSym (-1) D.host.q := by
      refine jacobiSym.mod_left' ?_
      rw [Nat.cast_sub hq.one_le, Nat.cast_one, sub_eq_neg_add, Int.add_emod_right]
    rw [h3, jacobiSym.at_neg_one (Nat.odd_iff.2 (by omega)), ZMod.χ₄_nat_three_mod_four hq4] at h
    exact absurd (show (1 : ℤ) = -1 from h) (by decide)

theorem ram_iff (D : D7) (p : ℕ) (hp : p.Prime) :
    1 < (span {(p : ℤ)}).ramificationIdxIn (𝓞 D.host.E) ↔ p ∣ D.host.condN := by
  have hEgal := D.host.galois
  have : IsGaloisGroup Gal(D.host.E/ℚ) ℤ (𝓞 D.host.E) :=
    IsGaloisGroup.of_isFractionRing _ _ _ ℚ D.host.E
  have := span_prime hp
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨P, hPp, hPl⟩⟩ : Nonempty ((span {(p : ℤ)}).primesOver (𝓞 D.host.E)) := inferInstance
  have hram : (∃ σ : D.host.E ≃ₐ[ℚ] D.host.E, σ ≠ 1 ∧ ∀ x : 𝓞 D.host.E, σ • x - x ∈ P) ↔
      p ∣ D.host.condN := by
    constructor
    · rintro ⟨σ, hσ1, hσ⟩
      by_contra hN
      exact hσ1 (((D.host.der.frob p hN P).2.2.2 σ).1 hσ)
    · intro hN
      rcases (D.host.dvd_condN_iff hp).1 hN with h | h | h
      · obtain ⟨u, hu, hu1⟩ := D.host.QS_exact p hp h
        exact ram_of_unit D p hp hN P u hu hu1
      · obtain ⟨u, hu, hu1⟩ := exists_unit_q D
        exact ram_of_unit D p hp hN P u (h ▸ hu) hu1
      · subst h
        refine ⟨D.host.gal.symm D.R.iod, fun h2 => ?_,
          (D.host.der.inertia_d P _).2 (Or.inr (D.host.gal.apply_symm_apply _))⟩
        have h3 : D.R.iod = 1 := by simpa using congrArg D.host.gal h2
        exact absurd (congrArg (fun g => g.1.2) h3) (by simp [Formalism.HC.Frame.iod])
  rw [← card_inertia_eq_ramificationIdxIn (G := Gal(D.host.E/ℚ)) (span {(p : ℤ)}) P, ← hram,
    Finite.one_lt_card_iff_nontrivial]
  constructor
  · intro hnt
    obtain ⟨⟨σ, hσ⟩, hne⟩ := exists_ne (1 : P.inertia Gal(D.host.E/ℚ))
    exact ⟨σ, fun h1 => hne (Subtype.ext h1), AddSubgroup.mem_inertia.1 hσ⟩
  · rintro ⟨σ, hσ1, hσ⟩
    exact ⟨⟨⟨σ, AddSubgroup.mem_inertia.2 hσ⟩, 1, fun h1 => hσ1 (congrArg Subtype.val h1)⟩⟩

theorem inert_iff_mem_zpowers (D : D7) (p : ℕ) (hp : p.Prime)
    (hram : (span {(p : ℤ)}).ramificationIdxIn (𝓞 D.host.E) = 1)
    (𝔭 : Ideal (𝓞 D.host.F)) (h𝔭 : 𝔭.IsPrime) (hlies : 𝔭.LiesOver (span {(p : ℤ)})) :
    Inert D 𝔭 ↔ D.R.cc ∈ Subgroup.zpowers (frob D p) := by
  haveI hpf : Fact p.Prime := ⟨hp⟩
  have hgal : ∀ σ, D.host.galE σ = D.host.gal σ := fun σ => rfl
  have hbot : 𝔭 ≠ ⊥ := by
    rintro rfl
    apply span_ne_bot hp
    rw [hlies.over]
    exact Ideal.comap_bot_of_injective _ (RingHom.injective_int _)
  have heta := D.host.der.eta.1 𝔭 h𝔭 hbot
  have hInert : Inert D 𝔭 ↔ (primesOver 𝔭 (𝓞 D.host.E)).ncard ≠ 2 := by
    unfold Inert
    rcases heta with h2 | ⟨h1, hf⟩
    · rw [h2]
      simp
    · rw [h1]
      simp [hf]
  have hne : (primesOver 𝔭 (𝓞 D.host.E)).Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    rcases heta with h2 | ⟨h1, _⟩
    · rw [h2]; norm_num
    · rw [h1]; norm_num
  obtain ⟨P, hP⟩ := hne
  obtain ⟨hPp, hPl⟩ := hP
  haveI := hPp
  haveI := hPl
  haveI := h𝔭
  haveI := hlies
  haveI hPq : P.LiesOver (span {(p : ℤ)}) := Ideal.LiesOver.trans P 𝔭 (span {(p : ℤ)})
  have hcomap : P.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = 𝔭 := hPl.over.symm
  have hcc1 : D.R.cc ≠ 1 := by
    intro h
    have h' := congrArg (fun g : D.R.GG => g.1.1) h
    change (-1 : ℤˣ) = 1 at h'
    exact absurd h' (by decide)
  by_cases hN : p ∣ D.host.condN
  · have hsplit := D.host.der.eta.2.2 p hN P
    rw [hcomap] at hsplit
    rw [hInert]
    have hc : (primesOver 𝔭 (𝓞 D.host.E)).ncard = 2 := by
      unfold Formalism.HC.HostRaw.etaF at hsplit
      split_ifs at hsplit with hc
      exact hc
    constructor
    · intro h
      exact absurd hc h
    · intro hmem
      exfalso
      unfold frob at hmem
      split_ifs at hmem with hex
      · obtain ⟨hP', hl', hfr⟩ := hex.choose_spec.choose_spec
        haveI := hP'
        haveI := hl'
        obtain ⟨u, hu, hgu⟩ := (D.host.der.frob_any p _ _).1 hfr
        have hst : hex.choose ∈ MulAction.stabilizer _ hex.choose_spec.choose :=
          (D.host.der.decomp p _ _).2 ⟨u, 1, by simpa using hu, hgu⟩
        apply D.host.der.decompConj p hp hN hex.choose_spec.choose
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
        have hconj : D.host.conj = hex.choose ^ k := by
          unfold Formalism.HC.HostRaw.conj
          rw [← hk, hgal, ← map_zpow, MulEquiv.symm_apply_apply]
        rw [hconj]
        exact Subgroup.zpow_mem _ hst k
      · rw [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hmem
        exact hcc1 hmem
  · obtain ⟨σ, hσ⟩ := (D.host.der.frob p hN P).1
    have hcop : Nat.Coprime p D.host.condN := (Nat.Prime.coprime_iff_not_dvd hp).2 hN
    have hu : ((ZMod.unitOfCoprime p hcop : (ZMod D.host.condN)ˣ) : ZMod D.host.condN) = (p : ZMod _) :=
      ZMod.coe_unitOfCoprime p hcop
    have hgs : D.host.gal σ = D.host.art (ZMod.unitOfCoprime p hcop) :=
      ((D.host.der.frob p hN P).2.1 σ _ hu).1 hσ
    have hfrob : frob D p = D.host.gal σ := by
      unfold frob
      split_ifs with hex
      · obtain ⟨hP', hl', hfr⟩ := hex.choose_spec.choose_spec
        haveI := hP'
        haveI := hl'
        rw [hgal, hgs]
        exact ((D.host.der.frob p hN _).2.1 _ _ hu).1 hfr
      · exact absurd ⟨σ, P, hPp, hPq, hσ⟩ hex
    rw [hInert, hfrob, ← D.host.der.eta.2.1 p hN P σ hσ, hcomap]
    unfold Formalism.HC.HostRaw.etaF
    split_ifs with hc
    · simp [hc]
    · simp [hc]

end SlopeTestRemainingChoices

theorem inertPart_holds (D : D7) : InertPart D := by
  intro φ₀ _ h p hp hram hfr 𝔭 h𝔭 hlies
  rw [SlopeTestRemainingChoices.inert_iff_mem_zpowers D p hp hram 𝔭 h𝔭 hlies, hfr]
  exact cc_mem_zpowers_gOf D φ₀ h

theorem points_property_of_d7 (D : D7) : PointsLemma D := lemma_one_three_of_inert D (inertPart_holds D)

end Formalism.MainNotions.UnusedSlot33

end
