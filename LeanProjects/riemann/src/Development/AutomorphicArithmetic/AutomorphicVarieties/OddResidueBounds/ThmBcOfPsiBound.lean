import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.KillPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.LenPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ActEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ActFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ProdVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.AtPrime
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.DegExistsLift
import Mathlib

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

namespace UpperTheory.V.Odd

private theorem stick_of (hK : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (N : ℕ), 0 < N → Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ) → ∀ (l : ℕ) [Fact l.Prime] (D : LData E Ω l), Procyc E Ω l → ∀ e : ℕ, 1 ≤ e → ∃ r : ℕ, (r : ℝ) * Real.log l ≤ C * Module.finrank ℚ E * (e + 1) * Real.log ((e : ℝ) * l * N) ∧ ∀ x ∈ ShaMinus D e, (l : ℤ_[l]) ^ r • x = 0) (hL : ∀ (R X : Type) [CommRing R] [AddCommGroup X] [Module R X] (P : Submodule R X) (a : R) (r : ℕ), (∀ x ∈ P, a ^ r • x = 0) → Module.length R P ≤ r * Module.length R (Submodule.torsionBy R X a)) (hG : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (N : ℕ), 0 < N → Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ) → ∀ (l : ℕ) [Fact l.Prime] (D : LData E Ω l) (e : ℤ), ∃ g : ℕ, Module.length ℤ_[l] (Submodule.torsionBy ℤ_[l] (H1 (qzTw D e)) (l : ℤ_[l])) ≤ g ∧ (g : ℝ) ≤ 8 * l * Module.finrank ℚ E * Real.log ((l : ℝ) * N)) : ∃ C : ℝ, 0 ≤ C ∧ StickBound C := by
  obtain ⟨C, hC, hK⟩ := hK
  refine ⟨8 * C, by positivity, fun E Ω _ _ _ _ _ _ N hN hE l _ D hP e he => ?_⟩
  obtain ⟨r, hr, hk⟩ := hK E Ω N hN hE l D hP e he
  obtain ⟨g, hg, hg'⟩ := hG E Ω N hN hE l D e
  have h1 : minusLen D e ≤ ((r * g : ℕ) : ℕ∞) := by
    push_cast
    exact (hL _ _ (ShaMinus D e) _ r hk).trans (by gcongr)
  have h2 : minusLen D e ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top _) h1
  refine ⟨h2, ?_⟩
  have h3 : ((minusLen D e).toNat : ℝ) ≤ r * g := by exact_mod_cast ENat.toNat_le_of_le_coe h1
  have hl : (1 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).one_le
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have he' : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hlN : (1 : ℝ) ≤ l * N := one_le_mul_of_one_le_of_one_le hl hN'
  have h4 : Real.log ((l : ℝ) * N) ≤ Real.log ((e : ℝ) * l * N) :=
    Real.log_le_log (by positivity) (by rw [mul_assoc]; exact le_mul_of_one_le_left (by positivity) he')
  have h5 : 0 ≤ Real.log ((e : ℝ) * l * N) := (Real.log_nonneg hlN).trans h4
  have h6 : 0 ≤ Real.log l := Real.log_nonneg hl
  calc ((minusLen D e).toNat : ℝ) * Real.log l ≤ (r * g) * Real.log l := by gcongr
    _ = (r * Real.log l) * g := by ring
    _ ≤ (C * Module.finrank ℚ E * (e + 1) * Real.log ((e : ℝ) * l * N)) *
        (8 * l * Module.finrank ℚ E * Real.log ((e : ℝ) * l * N)) := by
      refine mul_le_mul hr (hg'.trans (by gcongr)) (by positivity) (by positivity)
    _ = _ := by ring

private theorem ncard_charSet_le_ker_index {E : Type} [Field E] [NumberField E] {N : ℕ} [NeZero N]
    (ρ : (ZMod N)ˣ →* Gal(E/ℚ)) (k : ℕ) : (charSet ℂ (parE ρ k)).ncard ≤ ρ.ker.index := by
  classical
  have hS : ∀ χ ∈ charSet ℂ (parE ρ k), ρ.ker ≤ (MulChar.toUnitHom χ).ker := by
    intro χ hχ
    simp only [charSet, Set.mem_setOf_eq, parE] at hχ
    exact hχ.1
  let f : charSet ℂ (parE ρ k) → ((ZMod N)ˣ ⧸ ρ.ker →* ℂˣ) :=
    fun χ => QuotientGroup.lift ρ.ker (MulChar.toUnitHom χ.1) (hS χ.1 χ.2)
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply MulChar.ext
    intro u
    have := congrArg (fun g => ((g (QuotientGroup.mk u) : ℂˣ) : ℂ)) hab
    simpa [f] using this
  have hQ : Nat.card ((ZMod N)ˣ ⧸ ρ.ker →* ℂˣ) = ρ.ker.index := by
    rw [CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity]
    rfl
  have hfin : Finite ((ZMod N)ˣ ⧸ ρ.ker →* ℂˣ) :=
    Nat.finite_of_card_ne_zero (by rw [hQ]; exact Subgroup.index_ne_zero_of_finite)
  calc (charSet ℂ (parE ρ k)).ncard = Nat.card (charSet ℂ (parE ρ k)) :=
        (Nat.card_coe_set_eq _).symm
    _ ≤ Nat.card ((ZMod N)ˣ ⧸ ρ.ker →* ℂˣ) := Nat.card_le_card_of_injective f hf
    _ = _ := hQ

private theorem prime_of (hA : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (N : ℕ) [NeZero N], Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ) → ∃ ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E), IsCycAct Ω N ρ) (hF : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (N : ℕ) [NeZero N] (ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E)), IsCycAct Ω N ρ → Function.Surjective ρ ∧ IsAbelianGalois ℚ E ∧ Nat.card (Gq ρ) = Module.finrank ℚ E ∧ ρ.ker.index = Module.finrank ℚ E ∧ ∀ (M : ℕ) [NeZero M] (h : N ∣ M), IsCycAct Ω M (ρ.comp (ZMod.unitsMap h))) (hV : ∀ (N : ℕ) [NeZero N] (k : ℕ) (P : Set (Subgroup (ZMod N)ˣ)), 1 ≤ k → P ⊆ parKer N k → ∃ w : ℕ → ℕ, (∀ T : Finset ℕ, (∀ l ∈ T, l.Prime) → ∑ l ∈ T, (w l : ℝ) * Real.log l ≤ (charSet ℂ P).ncard * Real.log (bnd N k)) ∧ ∀ (l : ℕ) [Fact l.Prime] (T : Finset (DirichletCharacter (PadicAlgCl l) N)), (T : Set _) ⊆ charSet (PadicAlgCl l) P → ∑ χ ∈ T, -Real.log ‖alN k χ‖ ≤ (w l : ℝ) * Real.log l) (hP : PsiBound → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (N : ℕ) [NeZero N] (ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E)), IsCycAct Ω N ρ → ∀ (l : ℕ) [Fact l.Prime] (D : LData E Ω l), l ≠ 2 → ¬ l ∣ Module.finrank ℚ E → ∀ e : ℕ, 1 ≤ e → minusLen D e ≠ ⊤ ∧ ∃ T : Finset (DirichletCharacter (PadicAlgCl l) N), (T : Set _) ⊆ charSet (PadicAlgCl l) (parE ρ (e + 1)) ∧ ((minusLen D e).toNat : ℝ) * Real.log l ≤ ∑ χ ∈ T, -Real.log ‖alN (e + 1) χ‖)
    (h : PsiBound) : PrimeBound := by
  intro E Ω _ _ _ _ _ _ N hN hemb ld e he
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨ρ, hρ⟩ := hA E Ω N hemb
  obtain ⟨-, -, -, hidx, -⟩ := hF E Ω N ρ hρ
  have key : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ¬ p ∣ Module.finrank ℚ E →
      minusLen (ld p) e ≠ ⊤ ∧ ∃ T : Finset (DirichletCharacter (PadicAlgCl p) N),
        (T : Set _) ⊆ charSet (PadicAlgCl p) (parE ρ (e + 1)) ∧
        ((minusLen (ld p) e).toNat : ℝ) * Real.log p ≤ ∑ χ ∈ T, -Real.log ‖alN (e + 1) χ‖ :=
    fun p _ hp2 hpd => hP h E Ω N ρ hρ p (ld p) hp2 hpd e he
  refine ⟨fun p _ hp2 hpd => (key p hp2 hpd).1, ?_⟩
  intro S hS
  obtain ⟨w, hw1, hw2⟩ := hV N (e + 1) (parE ρ (e + 1)) (by omega) (fun H hH => hH.2)
  have hterm : ∀ l ∈ S, Real.log ((l : ℕ) : ℝ) * ((minusLen (ld (l : ℕ)) e).toNat : ℝ) ≤
      (w l : ℝ) * Real.log ((l : ℕ) : ℝ) := by
    intro l hl
    haveI : Fact (l : ℕ).Prime := ⟨l.2⟩
    obtain ⟨-, T, hT, hle⟩ := key l (hS l hl).1 (hS l hl).2
    have h2 := hw2 l T hT
    nlinarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogb : 0 ≤ Real.log (bnd N (e + 1)) := by
    apply Real.log_nonneg
    unfold bnd
    have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (e + 1 + 1) := one_le_pow₀ hN1
    have h2 : (1 : ℝ) ≤ ((e + 1).factorial : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
    nlinarith
  calc ∑ l ∈ S, Real.log ((l : ℕ) : ℝ) * ((minusLen (ld (l : ℕ)) e).toNat : ℝ)
        ≤ ∑ l ∈ S, (w l : ℝ) * Real.log ((l : ℕ) : ℝ) := Finset.sum_le_sum hterm
    _ = ∑ m ∈ S.image (fun p : Nat.Primes => (p : ℕ)), (w m : ℝ) * Real.log (m : ℝ) :=
        (Finset.sum_image (f := fun m : ℕ => (w m : ℝ) * Real.log m) (s := S)
          (g := fun p : Nat.Primes => (p : ℕ)) (fun a _ b _ h => Nat.Primes.coe_nat_injective h)).symm
    _ ≤ (charSet ℂ (parE ρ (e + 1))).ncard * Real.log (bnd N (e + 1)) := by
        apply hw1
        intro m hm
        obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hm
        exact p.2
    _ ≤ (Module.finrank ℚ E : ℝ) * Real.log (bnd N (e + 1)) := by
        apply mul_le_mul_of_nonneg_right _ hlogb
        exact_mod_cast (ncard_charSet_le_ker_index ρ (e + 1)).trans hidx.le

private theorem log_bnd_le_mul_log (F t e : ℕ) (hF : 0 < F) (ht : 2 ≤ t) (he : e + 1 ≤ t) :
    Real.log (bnd F (e + 1)) ≤ (2 * t + 5) * Real.log (t * F) := by
  have htF : 2 ≤ t * F := le_trans ht (Nat.le_mul_of_pos_right t hF)
  have h1 : 16 ≤ (t * F) ^ 4 := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ (t * F) ^ 4 := Nat.pow_le_pow_left htF 4
  have h2 : F ^ (e + 1 + 1) ≤ (t * F) ^ (t + 1) :=
    calc F ^ (e + 1 + 1) ≤ (t * F) ^ (e + 1 + 1) :=
          Nat.pow_le_pow_left (Nat.le_mul_of_pos_left F (by omega)) _
      _ ≤ (t * F) ^ (t + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : (e + 1).factorial ≤ (t * F) ^ t :=
    calc (e + 1).factorial ≤ (e + 1) ^ (e + 1) := Nat.factorial_le_pow _
      _ ≤ t ^ (e + 1) := Nat.pow_le_pow_left he _
      _ ≤ t ^ t := Nat.pow_le_pow_right (by omega) he
      _ ≤ (t * F) ^ t := Nat.pow_le_pow_left (Nat.le_mul_of_pos_right t hF) _
  have hnat : 16 * F ^ (e + 1 + 1) * (e + 1).factorial ≤ (t * F) ^ (2 * t + 5) := by
    calc 16 * F ^ (e + 1 + 1) * (e + 1).factorial
        ≤ (t * F) ^ 4 * (t * F) ^ (t + 1) * (t * F) ^ t :=
          Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
      _ = (t * F) ^ (2 * t + 5) := by
          rw [← pow_add, ← pow_add]
          congr 1
          omega
  have hF' : (0 : ℝ) < F := by exact_mod_cast hF
  have hreal : bnd F (e + 1) ≤ ((t : ℝ) * F) ^ (2 * t + 5) := by
    unfold bnd
    exact_mod_cast hnat
  have hpos : 0 < bnd F (e + 1) := by
    unfold bnd
    positivity
  calc Real.log (bnd F (e + 1)) ≤ Real.log (((t : ℝ) * F) ^ (2 * t + 5)) :=
        Real.log_le_log hpos hreal
    _ = (2 * t + 5) * Real.log (t * F) := by
        rw [Real.log_pow]
        push_cast
        ring

private theorem thmBc_of (hD : ∀ (M : AbF) (e q d : ℕ), PrimePair M.m q d → ∀ (E : Type) [Field E] [NumberField E], IsCompField M e q d E → ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ Module.finrank ℚ E → l ∣ M.deg) (hS : ∃ C : ℝ, 0 ≤ C ∧ StickBound C) (hP : PrimeBound) : ThmBcFree := by
  obtain ⟨C, hC0, hSt⟩ := hS
  refine ⟨C, ?_⟩
  intro M e t q d he ht hpp E _ _ _ hcomp
  have hmem : condF E ∈ {N : ℕ | 0 < N ∧ Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ)} := by
    unfold condF
    apply Nat.sInf_mem
    unfold IsCompField at hcomp
    obtain ⟨N, hN0, j, -⟩ := hcomp
    exact ⟨N, Nat.pos_of_ne_zero hN0.out, ⟨j⟩⟩
  obtain ⟨hFpos, hemb⟩ := hmem
  have hdvd : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ Module.finrank ℚ E → l ∣ M.deg :=
    hD M e q d hpp E hcomp
  haveI : NeZero M.m := NeZero.of_pos M.pos
  have hdeg : M.deg ≠ 0 := by
    unfold AbF.deg
    exact Subgroup.index_ne_zero_of_finite
  unfold VVminusLe minusBound
  intro Ω _ _ _ ld
  set F := condF E with hFdef
  set dE := Module.finrank ℚ E with hdE
  refine ⟨?_, ?_⟩
  · intro p _ e' hp2 he' _
    by_cases hpd : p ∣ dE
    · have hpc : Procyc E Ω p := by
        unfold Procyc
        exact Or.inl hp2
      exact (hSt E Ω F hFpos hemb p (ld p) hpc e' he').1
    · exact (hP E Ω F hFpos hemb ld e' he').1 p hp2 hpd
  · intro S hS2
    rw [← Finset.sum_filter_add_sum_filter_not S (fun l : Nat.Primes => ¬ (l : ℕ) ∣ dE)]
    have hF1 : (1 : ℝ) ≤ F := by exact_mod_cast hFpos
    have ht1 : (2 : ℝ) ≤ t := by exact_mod_cast ht
    have hlogtF : 0 ≤ Real.log ((t : ℝ) * F) := Real.log_nonneg (by nlinarith)
    have hd0 : (0 : ℝ) ≤ dE := Nat.cast_nonneg _
    have hA : ∑ l ∈ S.filter (fun l : Nat.Primes => ¬ (l : ℕ) ∣ dE),
        Real.log ((l : ℕ) : ℝ) * ∑ e' ∈ Finset.Ico 1 t, ((minusLen (ld (l : ℕ)) e').toNat : ℝ) ≤
        3 * dE * t ^ 2 * Real.log (t * F) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      calc ∑ e' ∈ Finset.Ico 1 t, ∑ l ∈ S.filter (fun l : Nat.Primes => ¬ (l : ℕ) ∣ dE),
            Real.log ((l : ℕ) : ℝ) * ((minusLen (ld (l : ℕ)) e').toNat : ℝ)
          ≤ ∑ e' ∈ Finset.Ico 1 t, (dE : ℝ) * ((2 * t + 5) * Real.log (t * F)) := by
            apply Finset.sum_le_sum
            intro e' he'
            rw [Finset.mem_Ico] at he'
            have hb := (hP E Ω F hFpos hemb ld e' he'.1).2
              (S.filter (fun l : Nat.Primes => ¬ (l : ℕ) ∣ dE)) (by
                intro l hl
                rw [Finset.mem_filter] at hl
                exact ⟨hS2 l hl.1, hl.2⟩)
            calc _ ≤ (dE : ℝ) * Real.log (bnd F (e' + 1)) := hb
              _ ≤ _ := mul_le_mul_of_nonneg_left
                  (log_bnd_le_mul_log F t e' hFpos ht (by omega)) hd0
        _ = ((t - 1 : ℕ) : ℝ) * ((dE : ℝ) * ((2 * t + 5) * Real.log (t * F))) := by
            rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        _ ≤ 3 * dE * t ^ 2 * Real.log (t * F) := by
            rw [Nat.cast_sub (by omega : 1 ≤ t)]
            push_cast
            have key : ((t : ℝ) - 1) * (2 * t + 5) ≤ 3 * t ^ 2 := by nlinarith
            have := mul_le_mul_of_nonneg_right key (mul_nonneg hd0 hlogtF)
            nlinarith
    have hB : ∑ l ∈ S.filter (fun l : Nat.Primes => ¬ ¬ (l : ℕ) ∣ dE),
        Real.log ((l : ℕ) : ℝ) * ∑ e' ∈ Finset.Ico 1 t, ((minusLen (ld (l : ℕ)) e').toNat : ℝ) ≤
        C * ∑ l ∈ M.deg.primeFactors.erase 2,
          (l : ℝ) * (dE : ℝ) ^ 2 * (t : ℝ) ^ 2 * Real.log (t * l * F) ^ 2 := by
      have hterm : ∀ l ∈ S.filter (fun l : Nat.Primes => ¬ ¬ (l : ℕ) ∣ dE),
          Real.log ((l : ℕ) : ℝ) * ∑ e' ∈ Finset.Ico 1 t, ((minusLen (ld (l : ℕ)) e').toNat : ℝ) ≤
          C * (((l : ℕ) : ℝ) * (dE : ℝ) ^ 2 * (t : ℝ) ^ 2 *
            Real.log (t * ((l : ℕ) : ℝ) * F) ^ 2) := by
        intro l hl
        rw [Finset.mem_filter, not_not] at hl
        haveI : Fact (l : ℕ).Prime := ⟨l.2⟩
        have hp2 := hS2 l hl.1
        have hpc : Procyc E Ω (l : ℕ) := by
          unfold Procyc
          exact Or.inl hp2
        have hl1 : (1 : ℝ) ≤ ((l : ℕ) : ℝ) := by exact_mod_cast l.2.one_le
        have hK : 0 ≤ C * ((l : ℕ) : ℝ) * (dE : ℝ) ^ 2 := by positivity
        rw [Finset.mul_sum]
        calc ∑ e' ∈ Finset.Ico 1 t, Real.log ((l : ℕ) : ℝ) * ((minusLen (ld (l : ℕ)) e').toNat : ℝ)
            ≤ ∑ e' ∈ Finset.Ico 1 t, C * ((l : ℕ) : ℝ) * (dE : ℝ) ^ 2 * (t : ℝ) *
                Real.log (t * ((l : ℕ) : ℝ) * F) ^ 2 := by
              apply Finset.sum_le_sum
              intro e' he'
              rw [Finset.mem_Ico] at he'
              have h1 := (hSt E Ω F hFpos hemb (l : ℕ) (ld (l : ℕ)) hpc e' he'.1).2
              have he1 : (1 : ℝ) ≤ e' := by exact_mod_cast he'.1
              have het : (e' : ℝ) + 1 ≤ t := by exact_mod_cast he'.2
              have hge1 : (1 : ℝ) ≤ e' * ((l : ℕ) : ℝ) * F :=
                one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le he1 hl1) hF1
              have hlogle : Real.log (e' * ((l : ℕ) : ℝ) * F) ≤ Real.log (t * ((l : ℕ) : ℝ) * F) := by
                apply Real.log_le_log (by linarith)
                have : (e' : ℝ) ≤ t := by linarith
                gcongr
              have hlog0' : 0 ≤ Real.log (e' * ((l : ℕ) : ℝ) * F) := Real.log_nonneg hge1
              have hsq : Real.log (e' * ((l : ℕ) : ℝ) * F) ^ 2 ≤ Real.log (t * ((l : ℕ) : ℝ) * F) ^ 2 :=
                pow_le_pow_left₀ hlog0' hlogle 2
              have hm := mul_le_mul het hsq (sq_nonneg _) (by linarith)
              calc Real.log ((l : ℕ) : ℝ) * ((minusLen (ld (l : ℕ)) e').toNat : ℝ)
                  = ((minusLen (ld (l : ℕ)) e').toNat : ℝ) * Real.log ((l : ℕ) : ℝ) := mul_comm _ _
                _ ≤ _ := h1
                _ = (C * ((l : ℕ) : ℝ) * (dE : ℝ) ^ 2) *
                      (((e' : ℝ) + 1) * Real.log (e' * ((l : ℕ) : ℝ) * F) ^ 2) := by ring
                _ ≤ (C * ((l : ℕ) : ℝ) * (dE : ℝ) ^ 2) *
                      ((t : ℝ) * Real.log (t * ((l : ℕ) : ℝ) * F) ^ 2) :=
                    mul_le_mul_of_nonneg_left hm hK
                _ = _ := by ring
          _ = ((t - 1 : ℕ) : ℝ) * (C * ((l : ℕ) : ℝ) * (dE : ℝ) ^ 2 * (t : ℝ) *
                Real.log (t * ((l : ℕ) : ℝ) * F) ^ 2) := by
              rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
          _ ≤ ∑ e' ∈ Finset.Ico 1 t, 0 + C * (((l : ℕ) : ℝ) * (dE : ℝ) ^ 2 * (t : ℝ) ^ 2 *
                Real.log (t * ((l : ℕ) : ℝ) * F) ^ 2) := by
              rw [Finset.sum_const_zero, zero_add, Nat.cast_sub (by omega : 1 ≤ t)]
              push_cast
              have hK2 : 0 ≤ C * ((l : ℕ) : ℝ) * (dE : ℝ) ^ 2 * (t : ℝ) *
                  Real.log (t * ((l : ℕ) : ℝ) * F) ^ 2 := by positivity
              nlinarith
          _ = _ := by rw [Finset.sum_const_zero, zero_add]
      calc _ ≤ ∑ l ∈ S.filter (fun l : Nat.Primes => ¬ ¬ (l : ℕ) ∣ dE),
            C * (((l : ℕ) : ℝ) * (dE : ℝ) ^ 2 * (t : ℝ) ^ 2 * Real.log (t * ((l : ℕ) : ℝ) * F) ^ 2) :=
            Finset.sum_le_sum hterm
        _ = C * ∑ m ∈ (S.filter (fun l : Nat.Primes => ¬ ¬ (l : ℕ) ∣ dE)).image
              (fun p : Nat.Primes => (p : ℕ)),
              ((m : ℝ) * (dE : ℝ) ^ 2 * (t : ℝ) ^ 2 * Real.log (t * (m : ℝ) * F) ^ 2) := by
            rw [← Finset.mul_sum]
            congr 1
            exact (Finset.sum_image
              (f := fun m : ℕ => (m : ℝ) * (dE : ℝ) ^ 2 * (t : ℝ) ^ 2 * Real.log (t * (m : ℝ) * F) ^ 2)
              (s := S.filter (fun l : Nat.Primes => ¬ ¬ (l : ℕ) ∣ dE))
              (g := fun p : Nat.Primes => (p : ℕ))
              (fun a _ b _ h => Nat.Primes.coe_nat_injective h)).symm
        _ ≤ _ := by
            apply mul_le_mul_of_nonneg_left _ hC0
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro m hm
              obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
              rw [Finset.mem_filter, not_not] at hp
              rw [Finset.mem_erase, Nat.mem_primeFactors]
              exact ⟨hS2 p hp.1, p.2, hdvd p p.2 (hS2 p hp.1) hp.2, hdeg⟩
            · intro m _ _
              positivity
    exact add_le_add hA hB

theorem stickBound : ∃ C : ℝ, 0 ≤ C ∧ StickBound C := stick_of killPow lenPow gen

theorem primeBound_of (h : PsiBound) : PrimeBound := prime_of actEx actFacts prodVal atPrime h

theorem thmBcFree_of (h : PsiBound) : ThmBcFree := thmBc_of deg stickBound (primeBound_of h)

end UpperTheory.V.Odd
