import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulVecMemConjSmulOfAdjoint
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardPrimesOverEqFinrankOfAbsNormEqOfNotMemSq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntSubMemPow

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.SplitChoice

theorem exists_int_sub_mem_pow {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 E))
    (hP : P.IsMaximal) (hm : (p : 𝓞 E) ∈ P) (hN : Ideal.absNorm P = p) (h2 : (p : 𝓞 E) ∉ P ^ 2) (k : ℕ)
    (a : 𝓞 E) : ∃ m : ℤ, a - m ∈ P ^ k := by
  first
  | exact @_root_.GlobalTheory.IntSubMemPow.exists_int_sub_mem_pow
  | exact _root_.GlobalTheory.IntSubMemPow.exists_int_sub_mem_pow
  | (apply _root_.GlobalTheory.IntSubMemPow.exists_int_sub_mem_pow <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntSubMemPow.exists_int_sub_mem_pow <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntSubMemPow.exists_int_sub_mem_pow <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntSubMemPow.exists_int_sub_mem_pow ..)

theorem not_isConj_self (I : AutInst) {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 I.E))
    (hm : (p : 𝓞 I.E) ∈ v.asIdeal) (hN : Ideal.absNorm v.asIdeal = p) (h2 : (p : 𝓞 I.E) ∉ v.asIdeal ^ 2) :
    ¬ IsConj I v v := by
  intro h
  let st : 𝓞 I.E →+* 𝓞 I.E := RingOfIntegers.mapRingHom (starRingEnd I.E)
  have hst : ∀ a : 𝓞 I.E, (st a : I.E) = star (a : I.E) := fun a => rfl
  have hmap : v.asIdeal.map st ≤ v.asIdeal :=
    Ideal.map_le_iff_le_comap.2 fun a ha => (h a (st a) (hst a)).1 ha
  have hfix : ∀ a, st a = a := fun a => by
    have hall : ∀ k, st a - a ∈ v.asIdeal ^ k := fun k => by
      obtain ⟨m, hm'⟩ := exists_int_sub_mem_pow hp v.asIdeal v.isMaximal hm hN h2 k a
      have h3 : st (a - m) ∈ v.asIdeal ^ k := by
        have := Ideal.mem_map_of_mem st hm'
        rw [Ideal.map_pow] at this
        exact Ideal.pow_right_mono hmap k this
      rw [map_sub, map_intCast] at h3
      simpa using sub_mem h3 hm'
    have := Ideal.iInf_pow_eq_bot_of_isDomain v.asIdeal v.isPrime.ne_top
    have h4 : st a - a ∈ (⊥ : Ideal (𝓞 I.E)) := this ▸ Ideal.mem_iInf.2 hall
    exact sub_eq_zero.1 h4
  have hfixE : ∀ x : I.E, star x = x := fun x => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 I.E) x
    have ha : star (algebraMap (𝓞 I.E) I.E a) = algebraMap (𝓞 I.E) I.E a := by
      rw [← hst a, hfix]
    have hb : star (algebraMap (𝓞 I.E) I.E b) = algebraMap (𝓞 I.E) I.E b := by
      rw [← hst b, hfix]
    rw [star_div₀, ha, hb]
  have hsurj : Function.Surjective (algebraMap I.F I.E) := fun x => (I.cm.fixed x).1 (hfixE x)
  have h1 : Module.finrank I.F I.E = 1 :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.2 ⟨(algebraMap I.F I.E).injective, hsurj⟩
  have := I.cm.deg2
  omega

theorem ncard_places_eq {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) :
    {v : HeightOneSpectrum (𝓞 E) | (p : 𝓞 E) ∈ v.asIdeal}.ncard =
      (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero
  have hpr : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal := hpr.isMaximal hp0
  rw [← Set.ncard_image_of_injective _ (fun _ _ h => HeightOneSpectrum.ext h :
    Function.Injective (HeightOneSpectrum.asIdeal : HeightOneSpectrum (𝓞 E) → _))]
  congr 1
  ext P
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v.isPrime, ⟨hmax.eq_of_le (Ideal.comap_ne_top _ v.isPrime.ne_top) ?_⟩⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
    exact hv
  · rintro ⟨hP, hl⟩
    refine ⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P⟩, ?_, rfl⟩
    have : (p : ℤ) ∈ P.under ℤ := hl.over ▸ Ideal.mem_span_singleton_self _
    rw [Ideal.mem_comap, map_natCast] at this
    exact this

theorem exists_isChoice_and_isChoice_of_card : ∀ (I : AutInst) (g : Fin 2 → ℕ), (∀ k, (g k).Prime) → g 0 ≠ g 1 → (∀ k (P : Ideal (𝓞 I.E)), P.IsMaximal → ((g k : ℕ) : 𝓞 I.E) ∈ P → Ideal.absNorm P = g k ∧ ((g k : ℕ) : 𝓞 I.E) ∉ P ^ 2) → (∃ w : ∀ _ : Fin 2, Fin I.f → HeightOneSpectrum (𝓞 I.E), IsChoice I g (fun _ => Fin I.f) w) ∧ ∀ (Pl : Fin 2 → Type) [∀ k, Fintype (Pl k)] (w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)), (∀ k, Fintype.card (Pl k) = I.f) → (∀ k v, ((g k : ℕ) : 𝓞 I.E) ∈ (w k v).asIdeal) → (∀ k, Function.Injective (w k)) → (∀ k v v', ¬ IsConj I (w k v) (w k v')) → IsChoice I g Pl w := by
  intro I g hg hne h
  have hdeg : Module.finrank ℚ I.E = 2 * I.f := by
    rw [← Module.finrank_mul_finrank ℚ I.F I.E, I.cm.deg2, AutInst.f, mul_comm]
  refine GlobalTheory.Mem.RowsBundle.isChoice_of_card I g hg hne (fun k v hv => ?_) Module.finrank_pos fun k => ?_
  · obtain ⟨h1, h2⟩ := h k v.asIdeal v.isMaximal hv
    exact ⟨h1, h2, not_isConj_self I (hg k) v hv h1 h2⟩
  · rw [ncard_places_eq (hg k),
      GlobalTheory.ncard_primesOver_eq_finrank_of_absNorm_eq_of_not_mem_sq I.E (g k) (hg k) (h k), hdeg]

end GlobalTheory.SplitChoice
