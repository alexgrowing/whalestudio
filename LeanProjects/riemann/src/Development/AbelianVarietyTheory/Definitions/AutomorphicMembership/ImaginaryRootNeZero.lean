import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.TrueGeo GlobalTheory.Cartier

namespace GlobalTheory.ShFam.Pad.LineTest

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

theorem expo_add (w w' : Sym E →₀ ℤ) : expo Dw (w + w') = expo Dw w + expo Dw w' := by
  classical
  funext x
  simp only [expo, Pi.add_apply]
  rw [Finsupp.sum_add_index']
  · intro a; simp
  · intro a b c; split_ifs <;> simp

theorem expo_zero : expo Dw 0 = 0 := by
  funext x; simp [expo]

open Classical in
theorem expo_single (a : Sym E) (n : ℤ) (x : Letter Dw) :
    expo Dw (Finsupp.single a n) x = if letterOf Dw a.2.2 = some x then n else 0 := by
  simp only [expo]
  rw [Finsupp.sum_single_index]
  simp

theorem imaginary_root_ne_zero : starRingEnd ℂ H.rt0 ≠ H.rt0 := by
  intro h
  have h1 : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h
  have h2 := congrArg Complex.re H.sqrt_neg_disc_sq
  have h3 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  simp [pow_two, h1] at h2
  nlinarith [mul_self_nonneg H.rt0.re]

theorem mult_of_mem {τ : E →+* ℂ} (h : τ (H.rt : E) = H.rt0) : Dw.mult τ = Dw.p := by
  simp [Datum.mult, h]

theorem mult_conj_of_mem {τ : E →+* ℂ} (h : τ (H.rt : E) = H.rt0) : Dw.mult (conjEmb τ) = Dw.q := by
  have : conjEmb τ (H.rt : E) ≠ H.rt0 := by
    simpa [conjEmb, h] using imaginary_root_ne_zero (H := H)
  simp [Datum.mult, this]

theorem expo_root_first (a : ℕ → Bool) (R : Option ℝ) {τ : E →+* ℂ} (h : τ (H.rt : E) = H.rt0) (i : ℕ) (hi : i < Dw.p) :
    expo Dw (rootSym Dw a R τ i) ⟨τ, ⟨i, by rw [mult_of_mem Dw h]; exact hi⟩⟩ = 1 := by
  have : i < Dw.mult τ := by rw [mult_of_mem Dw h]; exact hi
  simp [rootSym, hi, expo_single, letterOf, this]

theorem expo_root_second (a : ℕ → Bool) (R : Option ℝ) {τ : E →+* ℂ} (h : τ (H.rt : E) = H.rt0) (i : ℕ)
    (hi : Dw.p ≤ i) (hi' : i < Dw.p + Dw.q) :
    expo Dw (rootSym Dw a R τ i)
      ⟨conjEmb τ, ⟨Dw.p + Dw.q - 1 - i, by rw [mult_conj_of_mem Dw h]; omega⟩⟩ = -1 := by
  have : Dw.p + Dw.q - 1 - i < Dw.mult (conjEmb τ) := by rw [mult_conj_of_mem Dw h]; omega
  have h' : ¬ i < Dw.p := by omega
  rw [rootSym, if_neg h', expo_single]
  simp [letterOf, this]

theorem parOf_eq {w : Sym E →₀ ℤ} {R : Option ℝ} (h0 : w ≠ 0) (h : ∀ a ∈ w.support, a.2.1 = R) : parOf w = R := by
  have hne : w.support.Nonempty := Finsupp.support_nonempty_iff.2 h0
  rw [parOf, dif_pos hne]
  exact h _ hne.choose_spec

theorem mem_letters (x : Letter Dw) : x ∈ letters Dw := by
  obtain ⟨τ, i⟩ := x
  obtain ⟨a, rfl⟩ := (Fintype.equivFin (E →+* ℂ)).symm.surjective τ
  simp only [letters, List.mem_flatMap, List.mem_map]
  exact ⟨a, List.mem_finRange a, i, List.mem_finRange i, rfl⟩

theorem length_letters : (letters Dw).length = ∑ τ : E →+* ℂ, Dw.mult τ := by
  simp only [letters, List.length_flatMap, List.length_map, List.length_finRange]
  rw [← Fin.sum_univ_def]
  exact (Fintype.equivFin (E →+* ℂ)).symm.sum_comp (fun τ => Dw.mult τ)

variable {Dw} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

theorem divOf_add (n n' : Letter Dw → ℤ) : divOf Y (n + n') = divOf Y n + divOf Y n' := by
  simp [divOf, add_smul, Finset.sum_add_distrib]

theorem divOf_eq_neg (ex : Ix Dw → ℤ) : divOf Y (fun x => ex (some x)) = -Y.LEx ex := by
  simp [divOf, FlagCpt.LEx]

theorem isEqn_divOf (n : Letter Dw → ℤ) (y : Y.Y.X) :
    (divOf Y n).IsEqn y (∏ x : Letter Dw, (Y.gr_spec y).choose_spec.choose_spec.choose x.1 x.2 ^ n x) := by
  classical
  have h := (Y.gr_spec y).choose_spec.choose_spec.choose_spec.2
  unfold divOf
  induction (Finset.univ : Finset (Letter Dw)) using Finset.induction_on with
  | empty => simpa using CartierDiv.isEqn_zero y
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha]; exact ((h a.1 a.2).zsmul _).add ih

theorem residueCharacteristic_prime (v : HeightOneSpectrum (𝓞 F)) : (resP v).Prime := by
  haveI := v.isMaximal
  letI := Ideal.Quotient.field v.asIdeal
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  exact CharP.char_is_prime (𝓞 F ⧸ v.asIdeal) _

variable {D : D7} {A : Amb D}

theorem mem_setB (κ : Lv A) (B : ℝ) (hB : 0 ≤ B) (p : ℕ) :
    p ∈ setB κ B ↔ p.Prime ∧ ((p : ℝ) ≤ B ∨ p = 2 ∨ p ∣ (discr D.host.E).natAbs ∨ p ∣ κ.l.M') := by
  have h1 : (discr D.host.E).natAbs ≠ 0 := by simpa using discr_ne_zero D.host.E
  have h2 : κ.l.M' ≠ 0 := Nat.lcm_ne_zero (by have := κ.l.three_le; omega) κ.l.A_pos.ne'
  simp only [setB, Finset.mem_union, Finset.mem_filter, Finset.mem_range, Nat.mem_primeFactors, Nat.lt_succ_iff,
    Nat.le_floor_iff hB]
  constructor
  · rintro (⟨a, b⟩ | ⟨a, b, -⟩)
    · exact ⟨b, .inl a⟩
    · refine ⟨a, .inr ?_⟩
      rcases (Nat.Prime.dvd_mul a).1 b with b | b
      · rcases (Nat.Prime.dvd_mul a).1 b with b | b
        · exact .inl ((Nat.prime_dvd_prime_iff_eq a Nat.prime_two).1 b)
        · exact .inr (.inl b)
      · exact .inr (.inr b)
  · rintro ⟨a, b | b | b | b⟩
    · exact .inl ⟨b, a⟩
    · exact .inr ⟨a, b ▸ (dvd_mul_right _ _).mul_right _, by positivity⟩
    · exact .inr ⟨a, (b.mul_left _).mul_right _, by positivity⟩
    · exact .inr ⟨a, b.mul_left _, by positivity⟩

end GlobalTheory.ShFam.Pad.LineTest
