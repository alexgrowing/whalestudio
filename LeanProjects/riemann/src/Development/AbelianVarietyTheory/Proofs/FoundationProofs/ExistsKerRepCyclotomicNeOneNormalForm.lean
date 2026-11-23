import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HomPadicIntTrivialOfIrreducibleCompactRepStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormUnitPowSubOne

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.ImZ

variable {l : ℕ} [Fact l.Prime]

theorem norm_coe_unit (u : ℤ_[l]ˣ) : ‖((u : ℤ_[l]) : ℚ_[l])‖ = 1 := by
  exact PadicInt.norm_def.symm.trans (PadicInt.isUnit_iff.mp u.isUnit)

def logU (u : ℤ_[l]ˣ) : ℤ_[l] :=
  ⟨Formalism.MainNotions.LocalSituation.logZl l ((u : ℤ_[l]) : ℚ_[l]), (GlobalTheory.PadicLogUnits.logZl_hom l).2.2.1 _ (norm_coe_unit u)⟩

theorem coe_logU (u : ℤ_[l]ˣ) : ((logU u : ℤ_[l]) : ℚ_[l]) = Formalism.MainNotions.LocalSituation.logZl l ((u : ℤ_[l]) : ℚ_[l]) := rfl

theorem logU_mul (u w : ℤ_[l]ˣ) : logU (u * w) = logU u + logU w := by
  apply Subtype.ext
  show Formalism.MainNotions.LocalSituation.logZl l (((u * w : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) = Formalism.MainNotions.LocalSituation.logZl l ((u : ℤ_[l]) : ℚ_[l]) + Formalism.MainNotions.LocalSituation.logZl l ((w : ℤ_[l]) : ℚ_[l])
  rw [Units.val_mul, PadicInt.coe_mul]
  exact (GlobalTheory.PadicLogUnits.logZl_hom l).1 _ _ (norm_coe_unit u) (norm_coe_unit w)

theorem logU_one : logU (1 : ℤ_[l]ˣ) = 0 := by
  have h := logU_mul (l := l) 1 1
  rw [mul_one] at h
  linear_combination -h

def logHom : ℤ_[l]ˣ →* Multiplicative ℤ_[l] where
  toFun u := Multiplicative.ofAdd (logU u)
  map_one' := by rw [logU_one]; rfl
  map_mul' u w := by rw [logU_mul]; rfl

theorem continuous_logHom : Continuous (logHom (l := l)) := by
  have h1 : Continuous fun u : ℤ_[l]ˣ => ((u : ℤ_[l]) : ℚ_[l]) :=
    (continuous_subtype_val : Continuous (fun x : ℤ_[l] => (x : ℚ_[l]))).comp (Units.continuous_val (M := ℤ_[l]))
  have h2 : Continuous fun u : ℤ_[l]ˣ => Formalism.MainNotions.LocalSituation.logZl l ((u : ℤ_[l]) : ℚ_[l]) :=
    (GlobalTheory.PadicLogUnits.logZl_hom l).2.1.comp_continuous h1 (fun u => norm_coe_unit u)
  exact continuous_ofAdd.comp (h2.subtype_mk _)

theorem cycZ_eq_one_of_eps {Ω : Type} [Field Ω] [Algebra ℚ Ω] {z : G ℚ Ω} (h : eps l z = 1) :
    cycZ ℚ Ω l z = 1 := by
  have h' : ((cycZ ℚ Ω l z : ℤ_[l]) : ℚ_[l]) = 1 := by
    have h2 := h
    simp [eps, cycBar] at h2
    exact h2
  apply Units.ext
  exact PadicInt.ext (h'.trans PadicInt.coe_one.symm)

theorem isIrr_of_comp {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (H : Subgroup Γ)
    (h : IsIrr (r.comp H.subtype)) : IsIrr r := by
  obtain ⟨h1, _, h3⟩ := h
  exact ⟨h1, fun _ _ _ => Submodule.mem_top, fun W' hW' hinv => h3 W' hW' fun g v hv => hinv g v hv⟩

theorem exists_cycZ_nat (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (hl : l ≠ 2) :
    ∃ (σ : G ℚ Ω) (n : ℕ), 2 ≤ n ∧ ((cycZ ℚ Ω l σ : ℤ_[l]) = n) := by
  haveI : (Ideal.span {((2 : ℕ) : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime 2
  obtain ⟨M, hM, hc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 ℚ) (Ideal.span {((2 : ℕ) : ℤ)})
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 (algebraMap ℤ (𝓞 ℚ)).injective_int]; exact bot_le)
  let v : HeightOneSpectrum (𝓞 ℚ) :=
    ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField ℚ)⟩
  have hlv : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
    intro h
    have h2 : ((l : ℕ) : ℤ) ∈ M.comap (algebraMap ℤ (𝓞 ℚ)) := by
      rw [Ideal.mem_comap, map_natCast]; exact h
    rw [hc, Ideal.mem_span_singleton] at h2
    have h3 : (2 : ℕ) ∣ l := by exact_mod_cast h2
    exact hl ((Nat.prime_dvd_prime_iff_eq Nat.prime_two (Fact.out)).mp h3).symm
  have hσ := cycZ_of_isFrob (l := l) hlv (isPlaceOver_placeOf Ω v) (isFrob_frobOf Ω v)
  refine ⟨frobOf Ω v, normV v, ?_, hσ⟩
  have h0 : normV v ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero] at hσ
    exact (cycZ ℚ Ω l (frobOf Ω v)).ne_zero hσ
  have h1 : normV v ≠ 1 := by
    intro h1
    have : Nat.card (𝓞 ℚ ⧸ v.asIdeal) = 1 := h1
    obtain ⟨hs, _⟩ := Nat.card_eq_one_iff_unique.mp this
    haveI : v.asIdeal.IsMaximal := hM
    haveI : Nontrivial (𝓞 ℚ ⧸ v.asIdeal) := inferInstance
    exact not_subsingleton _ hs
  omega

theorem logHom_ne_one (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (hl : l ≠ 2) :
    ∃ σ : G ℚ Ω, logHom (cycZ ℚ Ω l σ) ≠ 1 := by
  obtain ⟨σ, n, hn, hσ⟩ := exists_cycZ_nat (l := l) Ω hl
  refine ⟨σ ^ (l - 1), fun h => ?_⟩
  have hl1 : 1 ≤ l - 1 := by have := (Fact.out : l.Prime).two_le; omega
  have hval : ((cycZ ℚ Ω l (σ ^ (l - 1)) : ℤ_[l]) : ℚ_[l]) = ((n ^ (l - 1) : ℕ) : ℚ_[l]) := by
    rw [map_pow, Units.val_pow_eq_pow_val, hσ]; push_cast; rfl
  have h0 : logU (cycZ ℚ Ω l (σ ^ (l - 1))) = 0 := by
    have := congrArg Multiplicative.toAdd h
    simpa [logHom] using this
  have h0' : Formalism.MainNotions.LocalSituation.logZl l ((n ^ (l - 1) : ℕ) : ℚ_[l]) = 0 := by
    rw [← hval, ← coe_logU, h0]; rfl

  have hnd : ¬ l ∣ n := by
    rintro ⟨k, rfl⟩
    have hu : IsUnit ((l * k : ℕ) : ℤ_[l]) := by rw [← hσ]; exact Units.isUnit _
    rw [Nat.cast_mul] at hu
    have hlu := PadicInt.isUnit_iff.mp (isUnit_of_mul_isUnit_left hu)
    rw [PadicInt.norm_p] at hlu
    have : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    have : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ this
    linarith

  have hdvd : ((l : ℤ)) ^ 1 ∣ ((n : ℤ) ^ (l - 1) - 1) := by
    rw [pow_one, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hz : ((n : ℤ) : ZMod l) ≠ 0 := by
      rw [Int.cast_natCast, ne_eq, ZMod.natCast_eq_zero_iff]; exact hnd
    push_cast
    rw [ZMod.pow_card_sub_one_eq_one (by simpa using hz), sub_self]
  have hnorm := (Padic.norm_int_le_pow_iff_dvd (p := l) _ 1).mpr hdvd
  have hle : ‖((n ^ (l - 1) : ℕ) : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-((1 : ℕ) : ℤ)) := by
    have : ((((n : ℤ) ^ (l - 1) - 1 : ℤ)) : ℚ_[l]) = ((n ^ (l - 1) : ℕ) : ℚ_[l]) - 1 := by push_cast; ring
    rw [← this]; exact hnorm
  have heq := (GlobalTheory.PadicLogUnits.logZl_hom l).2.2.2 1 le_rfl (fun h2 => absurd h2 hl) _ hle
  rw [h0', norm_zero] at heq
  have hne : ((n ^ (l - 1) : ℕ) : ℚ_[l]) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    have : 2 ≤ n ^ (l - 1) := le_trans hn (Nat.le_self_pow (by omega) n)
    intro he
    have : n ^ (l - 1) = 1 := by exact_mod_cast he
    omega
  exact hne (norm_eq_zero.mp heq.symm)

end GlobalTheory.Ord2.ImZ

namespace GlobalTheory.Ord2

open GlobalTheory.Ord2.ImZ in

theorem exists_ker_eps_ne_one : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ)
    (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∃ z ∈ W.ker, eps l z ≠ 1 := by
  intro l _ Ω _ _ _ e S A W h
  by_contra hne
  push_neg at hne
  obtain ⟨c, hc⟩ := h.int
  let lam : G ℚ Ω →* Multiplicative ℤ_[l] := logHom.comp (cycZ ℚ Ω l)
  have hlamc : Continuous lam := continuous_logHom.comp (continuous_cycZ ℚ Ω l)
  have hdet : ∀ g, ((W g : Matrix (Fin 2) (Fin 2) (Qbar l))).det ^ 2 = 1 := by
    intro g
    have := congrArg (fun u : (Qbar l)ˣ => (u : Qbar l)) (DFunLike.congr_fun h.det2 g)
    simpa [dt] using this
  have hker : W.ker ≤ lam.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    show logHom (cycZ ℚ Ω l z) = 1
    rw [cycZ_eq_one_of_eps (hne z hz), map_one]
  have hlam := GlobalTheory.T.hom_padicInt_trivial_of_irreducible_compact_rep l c (G ℚ Ω) W lam h.cont hc hdet (isIrr_of_comp W _ h.irr) hlamc hker
  obtain ⟨σ, hσ⟩ := logHom_ne_one (l := l) Ω h.l_odd
  exact hσ (DFunLike.congr_fun hlam σ)

end GlobalTheory.Ord2
