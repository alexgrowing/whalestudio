import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.XiNeZeroOfIsStdGeneric
import Formalism.LocalRingCardinality.ConjSqrtMinusD

noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.NX

namespace Formalism.IndefR.NX

section general

variable {E : Type} [Field E] [NumberField E]

theorem natCast_not_mem_of_coprime_g {P : Ideal (𝓞 E)} (hP : P ≠ ⊤) {g n : ℕ} (hg : ((g : ℕ) : 𝓞 E) ∈ P)
    (hc : Nat.Coprime n g) : ((n : ℕ) : 𝓞 E) ∉ P := by
  intro hn
  apply hP
  rw [Ideal.eq_top_iff_one]
  have h := Nat.gcd_eq_gcd_ab n g
  rw [hc.gcd_eq_one] at h
  have h' : (1 : 𝓞 E) = (n : 𝓞 E) * ((Nat.gcdA n g : ℤ) : 𝓞 E) + (g : 𝓞 E) * ((Nat.gcdB n g : ℤ) : 𝓞 E) := by
    have h2 := congrArg (Int.cast : ℤ → 𝓞 E) h
    push_cast at h2
    exact h2
  rw [h']
  exact P.add_mem (P.mul_mem_right _ hn) (P.mul_mem_right _ hg)

theorem primesOver_eq_places (g : ℕ) [Fact g.Prime] :
    (Ideal.span {(g : ℤ)}).primesOver (𝓞 E) =
      (fun v : HeightOneSpectrum (𝓞 E) => v.asIdeal) '' {v | ((g : ℕ) : 𝓞 E) ∈ v.asIdeal} := by
  have hmax : (Ideal.span {(g : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime g
  have hlo : ∀ (P : Ideal (𝓞 E)) [P.IsPrime], P.LiesOver (Ideal.span {(g : ℤ)}) ↔ ((g : ℕ) : 𝓞 E) ∈ P := by
    intro P hP
    rw [Ideal.liesOver_iff]
    constructor
    · intro h
      have hg : (g : ℤ) ∈ P.under ℤ := h ▸ Ideal.mem_span_singleton_self _
      rw [Ideal.under_def, Ideal.mem_comap, map_natCast] at hg
      exact hg
    · intro h
      have hle : Ideal.span {(g : ℤ)} ≤ P.under ℤ := by
        rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.under_def, Ideal.mem_comap, map_natCast]
        exact h
      exact hmax.eq_of_le (Ideal.comap_ne_top _ hP.ne_top) hle
  have hne0 : ((g : ℕ) : 𝓞 E) ≠ 0 := by
    intro h
    have : ((g : ℕ) : E) = 0 := by
      have := congrArg (fun x : 𝓞 E => (x : E)) h
      simpa using this
    exact (Fact.out : g.Prime).ne_zero (by exact_mod_cast this)
  ext P
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hP, hl⟩
    have hg : ((g : ℕ) : 𝓞 E) ∈ P := (hlo P).mp hl
    have hne : P ≠ ⊥ := fun h => hne0 (by rw [h] at hg; exact hg)
    exact ⟨⟨P, hP, hne⟩, hg, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.isPrime, (hlo v.asIdeal).mpr hv⟩

theorem card_residue_of_split (g : ℕ) (hg : g.Prime) (w : HeightOneSpectrum (𝓞 E))
    (hsplit : ({v : HeightOneSpectrum (𝓞 E) | ((g : ℕ) : 𝓞 E) ∈ v.asIdeal}).ncard = Module.finrank ℚ E)
    (hw : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal) : Nat.card (𝓞 E ⧸ w.asIdeal) = g := by
  classical
  have : Fact g.Prime := ⟨hg⟩
  set p : Ideal ℤ := Ideal.span {(g : ℤ)} with hp_def
  have : p.IsMaximal := Int.ideal_span_isMaximal_of_prime g
  have hfin : ({v : HeightOneSpectrum (𝓞 E) | ((g : ℕ) : 𝓞 E) ∈ v.asIdeal}).Finite := by
    apply Set.finite_of_ncard_pos
    rw [hsplit]; exact Module.finrank_pos
  have hinj : Function.Injective (fun v : HeightOneSpectrum (𝓞 E) => v.asIdeal) :=
    fun a b h => HeightOneSpectrum.ext h
  have hPO := primesOver_eq_places (E := E) g
  have hfin' : (p.primesOver (𝓞 E)).Finite := by rw [hPO]; exact hfin.image _
  let _ : Fintype (p.primesOver (𝓞 E)) := hfin'.fintype
  have hcard : Fintype.card (p.primesOver (𝓞 E)) = Module.finrank ℚ E := by
    rw [← Set.toFinset_card, ← Set.ncard_eq_toFinset_card', hPO, Set.ncard_image_of_injective _ hinj, hsplit]
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 E)
  rw [NumberField.RingOfIntegers.rank] at hsum
  have hle : ∀ q ∈ (Finset.univ : Finset (p.primesOver (𝓞 E))),
      (1 : ℕ) ≤ q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
    intro q _
    have := q.2.1
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (Ideal.ramificationIdx_pos q.1 ℤ).ne' (Ideal.inertiaDeg_pos q.1 ℤ).ne')
  have hones : ∑ q : p.primesOver (𝓞 E), (1 : ℕ) =
      ∑ q : p.primesOver (𝓞 E), q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
    rw [hsum, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, hcard]
  have hall := (Finset.sum_eq_sum_iff_of_le hle).mp hones
  have hwmem : w.asIdeal ∈ p.primesOver (𝓞 E) := by
    rw [hPO]; exact ⟨w, hw, rfl⟩
  have h1 := hall ⟨w.asIdeal, hwmem⟩ (Finset.mem_univ _)
  have hf : w.asIdeal.inertiaDeg ℤ = 1 := Nat.eq_one_of_mul_eq_one_left h1.symm
  have : w.asIdeal.LiesOver p := hwmem.2
  have hpow := Ideal.pow_inertiaDeg g w.asIdeal
  rw [hf, pow_one, Ideal.absNorm_apply, Submodule.cardQuot_apply] at hpow
  exact hpow.symm

private theorem zmod_eq_of_val_sub_mem_prime (g : ℕ) (hg : g.Prime) (w : HeightOneSpectrum (𝓞 E)) (hw : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal)
    {x y : ZMod g} (h : ((x.val : ℕ) : 𝓞 E) - ((y.val : ℕ) : 𝓞 E) ∈ w.asIdeal) : x = y := by
  haveI := Fact.mk hg
  have hwt : w.asIdeal ≠ ⊤ := w.isPrime.ne_top
  by_contra hne
  have hab : x.val ≠ y.val := fun h' => hne (ZMod.val_injective g h')
  have hxg := ZMod.val_lt x
  have hyg := ZMod.val_lt y
  rcases Nat.lt_or_ge x.val y.val with hlt | hle
  · have hmem : (((y.val - x.val : ℕ)) : 𝓞 E) ∈ w.asIdeal := by
      rw [Nat.cast_sub hlt.le, ← neg_sub]
      exact w.asIdeal.neg_mem h
    have hcop : Nat.Coprime (y.val - x.val) g :=
      (Nat.coprime_of_lt_prime (by omega) (by omega) hg).symm
    exact natCast_not_mem_of_coprime_g hwt hw hcop hmem
  · have hmem : (((x.val - y.val : ℕ)) : 𝓞 E) ∈ w.asIdeal := by
      rw [Nat.cast_sub hle]
      exact h
    have hcop : Nat.Coprime (x.val - y.val) g :=
      (Nat.coprime_of_lt_prime (by omega) (by omega) hg).symm
    exact natCast_not_mem_of_coprime_g hwt hw hcop hmem

theorem exists_zmod_residue (g : ℕ) (hg : g.Prime) (w : HeightOneSpectrum (𝓞 E))
    (hsplit : ({v : HeightOneSpectrum (𝓞 E) | ((g : ℕ) : 𝓞 E) ∈ v.asIdeal}).ncard = Module.finrank ℚ E)
    (hw : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal) (y : 𝓞 E ⧸ w.asIdeal) :
    ∃ x : ZMod g, Ideal.Quotient.mk w.asIdeal ((x.val : ℕ) : 𝓞 E) = y := by
  haveI := Fact.mk hg
  have hcard := card_residue_of_split g hg w hsplit hw
  haveI : Finite (𝓞 E ⧸ w.asIdeal) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hg.ne_zero)
  let f : ZMod g → 𝓞 E ⧸ w.asIdeal := fun x => Ideal.Quotient.mk w.asIdeal ((x.val : ℕ) : 𝓞 E)
  have hinj : Function.Injective f := by
    intro x y hxy
    exact zmod_eq_of_val_sub_mem_prime g hg w hw (Ideal.Quotient.eq.1 hxy)
  have hbij := hinj.bijective_of_nat_card_le (by rw [hcard, Nat.card_zmod])
  obtain ⟨x, hx⟩ := hbij.2 y
  exact ⟨x, hx⟩

end general

section record

variable (D : D7)

theorem isIntegral_sqrtMinusD : IsIntegral ℤ D.host.sqrtMinusD := by
  have h : D.host.sqrtMinusD ^ 2 = (((-(D.host.d : ℤ) : ℤ) : 𝓞 D.host.E) : D.host.E) := by
    rw [Host.sqrtMinusD_sq]; push_cast; ring
  exact IsIntegral.of_pow (by norm_num : 0 < 2) (h ▸ RingOfIntegers.isIntegral_coe _)

def sqrtO : 𝓞 D.host.E := ⟨D.host.sqrtMinusD, isIntegral_sqrtMinusD D⟩

@[simp] theorem coe_sqrtO : ((sqrtO D : 𝓞 D.host.E) : D.host.E) = D.host.sqrtMinusD :=
  rfl

theorem sqrtMinusD_ne_zero : D.host.sqrtMinusD ≠ 0 := by
  intro h0
  have hsq := Host.sqrtMinusD_sq D.host
  rw [h0] at hsq
  have hd0 : (D.host.d : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr D.host.hyp.2.1.ne_zero
  apply hd0
  have : -(D.host.d : D.host.E) = 0 := by rw [← hsq]; ring
  simpa using this

def xiDen : 𝓞 D.host.E := ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) * sqrtO D

theorem imaginary_generator_mul_denominator : D.host.xi0 * ((xiDen D : 𝓞 D.host.E) : D.host.E) = -1 := by
  have hN : ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact D.host.ccK_ne_bot
  have hs := sqrtMinusD_ne_zero D
  change D.host.xi0 * (((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) * D.host.sqrtMinusD) = -1
  rw [Host.xi0]
  field_simp

theorem g_mem_pG (kv : Σ k : Fin 2, D.nd.PlG k) : ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (pG D kv).asIdeal :=
  D.naut.plGw_over kv.1 kv.2

theorem coprime_normK_g (k : Fin 2) : Nat.Coprime (Ideal.absNorm D.host.ccK) (D.host.g k) :=
  D.host.ccK_coprime _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
    (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (D.host.g_level k))))))

theorem coprime_d_g (k : Fin 2) : Nat.Coprime D.host.d (D.host.g k) := by
  have h := D.ntypes.g_cond k
  have hdvd : D.host.d ∣ D.host.QS * D.host.q * D.host.d := Dvd.intro_left _ rfl
  have hmod : D.host.g k % D.host.d = 1 % D.host.d := by
    rw [← Nat.mod_mod_of_dvd _ hdvd, h]
  rw [Nat.Coprime, Nat.gcd_rec, hmod, ← Nat.gcd_rec]
  exact Nat.gcd_one_right _

theorem xiDen_not_mem (kv : Σ k : Fin 2, D.nd.PlG k) : xiDen D ∉ (pG D kv).asIdeal := by
  have hP : (pG D kv).asIdeal.IsPrime := (pG D kv).isPrime
  have hg := g_mem_pG D kv
  have hN := natCast_not_mem_of_coprime_g hP.ne_top hg (coprime_normK_g D kv.1)
  have hd := natCast_not_mem_of_coprime_g hP.ne_top hg (coprime_d_g D kv.1)
  have hs : sqrtO D ∉ (pG D kv).asIdeal := by
    intro hs
    apply hd
    have h2 : sqrtO D * sqrtO D ∈ (pG D kv).asIdeal := (pG D kv).asIdeal.mul_mem_left _ hs
    have he : sqrtO D * sqrtO D = -((D.host.d : ℕ) : 𝓞 D.host.E) := by
      apply RingOfIntegers.coe_injective
      push_cast
      change D.host.sqrtMinusD * D.host.sqrtMinusD = -((D.host.d : ℕ) : D.host.E)
      rw [← sq, Host.sqrtMinusD_sq]
    rw [he] at h2
    simpa using (pG D kv).asIdeal.neg_mem_iff.mp h2
  intro hc
  rcases hP.mem_or_mem hc with h | h
  · exact hN h
  · exact hs h

theorem xiRed_cond (kv : Σ k : Fin 2, D.nd.PlG k) :
    ∃ x : ZMod (D.host.g kv.1), ∃ a c : 𝓞 D.host.E, c ∉ (pG D kv).asIdeal ∧ (a : D.host.E) = D.host.xi0 * c ∧
      ((x.val : 𝓞 D.host.E) * c - a) ∈ (pG D kv).asIdeal := by
  classical
  have : (pG D kv).asIdeal.IsMaximal := (pG D kv).isMaximal
  let _ : Field (𝓞 D.host.E ⧸ (pG D kv).asIdeal) := Ideal.Quotient.field _
  have hc := xiDen_not_mem D kv
  have hcq : Ideal.Quotient.mk (pG D kv).asIdeal (xiDen D) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨x, hx⟩ := exists_zmod_residue (D.host.g kv.1) (D.host.g_prime kv.1) (pG D kv) (D.nd.g_split kv.1)
    (g_mem_pG D kv) (Ideal.Quotient.mk (pG D kv).asIdeal (-1) * (Ideal.Quotient.mk (pG D kv).asIdeal (xiDen D))⁻¹)
  refine ⟨x, -1, xiDen D, hc, ?_, ?_⟩
  · have h1 := imaginary_generator_mul_denominator D
    push_cast
    exact h1.symm
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hx, mul_assoc, inv_mul_cancel₀ hcq, mul_one, sub_self]

theorem xiRed_ne_zero (kv : Σ k : Fin 2, D.nd.PlG k) : xiRed D kv ≠ 0 := by
  intro h0
  have hP := xiRed_cond D kv
  have hx : xiRed D kv = hP.choose := by
    unfold Formalism.L2.NX.xiRed
    rw [dif_pos hP]
  obtain ⟨a, c, hc, hac, hmem⟩ := hP.choose_spec
  rw [← hx, h0, ZMod.val_zero, Nat.cast_zero, zero_mul, zero_sub] at hmem
  have ha : a ∈ (pG D kv).asIdeal := by simpa using (pG D kv).asIdeal.neg_mem hmem
  have h1 : a * xiDen D = -c := by
    apply NumberField.RingOfIntegers.ext
    show (a : D.host.E) * ((xiDen D : 𝓞 D.host.E) : D.host.E) = -(c : D.host.E)
    rw [hac, mul_comm D.host.xi0, mul_assoc, imaginary_generator_mul_denominator, mul_neg_one]
  apply hc
  have h2 : -c ∈ (pG D kv).asIdeal := by
    rw [← h1]
    exact (pG D kv).asIdeal.mul_mem_right _ ha
  simpa using (pG D kv).asIdeal.neg_mem h2

def IsXiRes (kv : Σ k : Fin 2, D.nd.PlG k) (x : ZMod (D.host.g kv.1)) : Prop :=
  ∃ a c : 𝓞 D.host.E, c ∉ (pG D kv).asIdeal ∧ (a : D.host.E) = D.host.xi0 * c ∧
    ((x.val : 𝓞 D.host.E) * c - a) ∈ (pG D kv).asIdeal

theorem xiRed_isXiRes (kv : Σ k : Fin 2, D.nd.PlG k) : IsXiRes D kv (xiRed D kv) := by
  have hP := xiRed_cond D kv
  have hx : xiRed D kv = hP.choose := by
    unfold Formalism.L2.NX.xiRed
    rw [dif_pos hP]
  rw [hx]
  exact hP.choose_spec

theorem xiRedNZ (D : D7) : XiRedNZ D :=
  fun kv => xiRed_ne_zero D kv

end record

end Formalism.IndefR.NX
