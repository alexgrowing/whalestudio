import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SplitPlaceTypes
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.SplitRowIffOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes
open GlobalTheory.SplitRowProbe

namespace GlobalTheory.SplitType

theorem exists_sqrt (l d : ℕ) [hl : Fact l.Prime] (h2 : l ≠ 2) (hj : jacobiSym (-(d : ℤ)) l = 1) :
    ∃ s : ℤ_[l], s ^ 2 = -(d : ℤ_[l]) ∧ ‖2 * s‖ = 1 := by
  have hd : ¬ (l : ℤ) ∣ (d : ℤ) := by
    intro h
    have : jacobiSym (-(d : ℤ)) l = 0 := by
      rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_zero_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact h.neg_right
    omega
  have h2' : ¬ (l : ℤ) ∣ 2 := fun h =>
    h2 ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 (by exact_mod_cast h))
  have one_of : ∀ k : ℤ, ¬ (l : ℤ) ∣ k → ‖(k : ℤ_[l])‖ = 1 := fun k hk =>
    le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => hk ((PadicInt.norm_int_lt_one_iff_dvd k).1 h))
  obtain ⟨r, hr⟩ := ZMod.isSquare_of_jacobiSym_eq_one hj
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective r
  have ha : (l : ℤ) ∣ a ^ 2 + d := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at hr ⊢
    linear_combination -hr
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl.out
  have ha' : ¬ (l : ℤ) ∣ 2 * a := by
    intro h
    rcases hp.dvd_or_dvd h with h | h
    · exact h2' h
    · exact hd ((dvd_add_right (dvd_pow h two_ne_zero)).1 ha)
  obtain ⟨s, hs⟩ := Misc.isSquare_of_hensel l d a (by
    rw [one_of _ ha', one_pow]
    exact (PadicInt.norm_int_lt_one_iff_dvd _).2 ha)
  have hs2 : s ^ 2 = -(d : ℤ_[l]) := by
    rw [sq, ← hs]; simp
  refine ⟨s, hs2, ?_⟩
  have n2 : ‖(2 : ℤ_[l])‖ = 1 := by simpa using one_of 2 h2'
  have nd : ‖(d : ℤ_[l])‖ = 1 := by simpa using one_of d hd
  have : ‖s‖ ^ 2 = 1 := by rw [← norm_pow, hs2, norm_neg, nd]
  rw [norm_mul, n2, one_mul]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 this

theorem exists_root {l d : ℕ} [Fact l.Prime] {A : Type} [CommRing A] [IsDomain A] (f : ℤ_[l] →+* A)
    {s : ℤ_[l]} (hs : s ^ 2 = -(d : ℤ_[l])) {y : A} (hy : y ^ 2 = -(d : A)) :
    ∃ t : ℤ_[l], (t = s ∨ t = -s) ∧ f t = y := by
  have : y ^ 2 = (f s) ^ 2 := by rw [← map_pow, hs, hy]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 this with h | h
  · exact ⟨s, Or.inl rfl, h.symm⟩
  · exact ⟨-s, Or.inr rfl, by rw [map_neg, h]⟩

section Host
variable {R : Ranks} (H : Host R)

theorem sqrtE_sq : (H.sqd) ^ 2 = -(H.d : H.E) := H.sqd_sq

theorem map_sqrt_sq {A : Type} [CommRing A] (φ : H.E →+* A) : φ (H.sqd) ^ 2 = -(H.d : A) := by
  rw [← map_pow, sqrtE_sq]; simp

theorem conj_sqrtE : H.conj (H.sqd) = -H.sqd := by
  apply H.φ₀.injective
  have h : H.φ₀ (H.sqd) = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem
  rw [conj_sqrt, map_neg, h]
  simp

theorem isIntegral_sqrtE : IsIntegral ℤ (H.sqd) := by
  refine IsIntegral.of_pow two_pos ?_
  rw [sqrtE_sq]
  exact (isIntegral_natCast _).neg

end Host

section Loc
variable (D : D7) (i : D.nd.Loc)

theorem root_of_embIn (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    {s₀ t : ℤ_[D.nd.l i]}
    (h₀ : algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) (algebraMap ℤ_[D.nd.l i] (D.nd.O i) s₀) =
      D.nd.embK i (D.embE (D.host.sqd)))
    (ht : algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i)) (t : ℚ_[D.nd.l i]) =
      (D.nbr i w hw).j (algebraMap D.host.E D.nd.Om (D.host.sqd)))
    (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) :
    (EmbIn (N := D.nd) D.nbr i true w hw τ → t = s₀) ∧
      (EmbIn (N := D.nd) D.nbr i false w hw τ → t = -s₀) := by
  have e1 : τ (Br.cEw D.nbr i w hw (D.host.sqd)) =
      algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (t : ℚ_[D.nd.l i]) := by
    rw [← τ.commutes]
    exact congrArg τ (Subtype.ext ht.symm)
  have e2 : Br.toLLK (D.nbr i w hw) (D.nd.embK i (D.embE (D.host.sqd))) =
      algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (s₀ : ℚ_[D.nd.l i]) := by
    rw [← h₀, Br.toLLK_alg, (D.nbr i w hw).eO_alg]
    rfl
  have e3 : D.what₂.embLL (D.embE (D.host.sqd)) =
      Complex.I * (Real.sqrt D.host.d : ℂ) :=
    (DFunLike.congr_fun D.embE_φ₀ _).trans D.host.φ₀_mem
  have inj := (algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw)).injective
  constructor
  · rintro ⟨h1, φ, hφ, h2⟩
    obtain ⟨y, hy⟩ := h1 (D.host.sqd)
    have hφ' : φ (D.host.sqd) = Complex.I * (Real.sqrt D.host.d : ℂ) := hφ
    have : y = D.embE (D.host.sqd) :=
      D.what₂.embLL.injective ((h2 _ y hy).trans (hφ'.trans e3.symm))
    rw [this, e1, e2] at hy
    exact Subtype.ext (inj hy).symm
  · rintro ⟨h1, φ, hφ, h2⟩
    obtain ⟨y, hy⟩ := h1 (D.host.sqd)
    have hφ' := (mem_halfType_false D.host φ).1 hφ
    have : y = -D.embE (D.host.sqd) :=
      D.what₂.embLL.injective (by rw [h2 _ y hy, hφ', map_neg, e3])
    rw [this, e1, map_neg, map_neg, e2, ← map_neg] at hy
    exact Subtype.ext (inj hy).symm

theorem mem_iff_norm (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (x : 𝓞 D.host.E) (z : ℤ_[D.nd.l i])
    (hz : algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i)) (z : ℚ_[D.nd.l i]) =
      (D.nbr i w hw).j (algebraMap D.host.E D.nd.Om (x : D.host.E))) :
    x ∈ w.asIdeal ↔ ‖z‖ < 1 := by
  rw [bridge_place D i w hw x, ← hz, norm_algebraMap', PadicInt.norm_def]

theorem root_ne (w w' : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (hw' : w' ∈ placesOver D.host.E (D.nd.l i)) (hc : IsConjPl D.host w w') {t : ℤ_[D.nd.l i]}
    (hn : ‖2 * t‖ = 1)
    (ht : algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i)) (t : ℚ_[D.nd.l i]) =
      (D.nbr i w hw).j (algebraMap D.host.E D.nd.Om (D.host.sqd)))
    (ht' : algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i)) (t : ℚ_[D.nd.l i]) =
      (D.nbr i w' hw').j (algebraMap D.host.E D.nd.Om (D.host.sqd))) : False := by
  let β : 𝓞 D.host.E := ⟨D.host.sqd, isIntegral_sqrtE D.host⟩
  have hβ : (β : D.host.E) = D.host.sqd := rfl
  set n : ℕ := t.zmodRepr with hn'
  have h1 : ‖t - n‖ < 1 := PadicInt.mem_nonunits.1 (PadicInt.sub_zmodRepr_mem t)
  have hx : ((β - n : 𝓞 D.host.E) : D.host.E) = D.host.sqd - n := by
    simp [← hβ]
  have hy : ((-β - n : 𝓞 D.host.E) : D.host.E) = -D.host.sqd - n := by
    simp [← hβ]
  have h2 : β - n ∈ w.asIdeal := (mem_iff_norm D i w hw _ (t - n) (by
    rw [hx, map_sub, map_sub, ← ht]; simp)).2 h1
  have h3 : -β - n ∈ w'.asIdeal := (hc (β - n) (-β - n) (by
    rw [hx, hy, map_sub, conj_sqrtE, map_natCast])).1 h2
  have h4 : ‖-t - n‖ < 1 := (mem_iff_norm D i w' hw' _ (-t - n) (by
    rw [hy, map_sub, map_sub, map_neg, map_neg, ← ht']; simp)).1 h3
  have h5 : 2 * t = (t - n) + -(-t - n) := by ring
  have h6 := PadicInt.nonarchimedean (t - (n : ℤ_[D.nd.l i])) (-(-t - (n : ℤ_[D.nd.l i])))
  rw [← h5, hn, norm_neg] at h6
  exact absurd h6 (not_le.2 (max_lt h1 h4))

end Loc

theorem place_type_conj : ∀ (D : D7) (i : D.nd.Loc), SplitRowPrime D.host (D.nd.l i) →
    ∀ (w w' : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (hw' : w' ∈ placesOver D.host.E (D.nd.l i)), IsConjPl D.host w w' →
      (PlIn (N := D.nd) D.nbr i true w hw ∧ PlIn (N := D.nd) D.nbr i false w' hw') ∨
        (PlIn (N := D.nd) D.nbr i false w hw ∧ PlIn (N := D.nd) D.nbr i true w' hw') := by
  intro D i hl w w' hw hw' hc
  obtain ⟨-, h5, hq, hd, -, hcls⟩ := hl
  have h2 : D.nd.l i ≠ 2 := by omega
  have hj : jacobiSym (-(D.host.d : ℤ)) (D.nd.l i) = 1 := by
    by_contra hj
    simp only [Host.cls, primeClass, if_neg h2, if_neg hq, if_neg hd, if_neg hj] at hcls
    split_ifs at hcls
  obtain ⟨s, hs, hn⟩ := exists_sqrt (D.nd.l i) D.host.d h2 hj
  obtain ⟨s₀, hs₀, h₀⟩ := exists_root
    ((algebraMap (D.nd.O i) (FractionRing (D.nd.O i))).comp (algebraMap ℤ_[D.nd.l i] (D.nd.O i))) hs
    (map_sqrt_sq D.host ((D.nd.embK i).comp D.embE))
  have hs0 : s₀ ^ 2 = -(D.host.d : ℤ_[D.nd.l i]) := by rcases hs₀ with rfl | rfl <;> simp [hs]
  have hn0 : ‖2 * s₀‖ = 1 := by rcases hs₀ with rfl | rfl <;> simpa using hn
  have hne : s₀ ≠ -s₀ := fun e => by
    rw [show 2 * s₀ = 0 by linear_combination e] at hn0
    simp at hn0
  have key : ∀ (v : HeightOneSpectrum (𝓞 D.host.E)) (hv : v ∈ placesOver D.host.E (D.nd.l i)),
      ∃ t : ℤ_[D.nd.l i], algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i)) (t : ℚ_[D.nd.l i]) =
        (D.nbr i v hv).j (algebraMap D.host.E D.nd.Om (D.host.sqd)) ∧
        ((t = s₀ ∧ PlIn (N := D.nd) D.nbr i true v hv) ∨ (t = -s₀ ∧ PlIn (N := D.nd) D.nbr i false v hv)) := by
    intro v hv
    obtain ⟨t, ht, h⟩ := exists_root
      ((algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i))).comp PadicInt.Coe.ringHom) hs0
      (map_sqrt_sq D.host ((D.nbr i v hv).j.comp (algebraMap D.host.E D.nd.Om)))
    refine ⟨t, h, ?_⟩
    rcases ht with ht | ht
    · refine Or.inl ⟨ht, nonempty_emb D i v hv, fun τ => ?_⟩
      rcases embIn_xor D i v hv τ with e | e
      · exact e.1
      · exact absurd (ht.symm.trans ((root_of_embIn D i v hv h₀ h τ).2 e.1)) hne
    · refine Or.inr ⟨ht, nonempty_emb D i v hv, fun τ => ?_⟩
      rcases embIn_xor D i v hv τ with e | e
      · exact absurd (((root_of_embIn D i v hv h₀ h τ).1 e.1).symm.trans ht) hne
      · exact e.1
  obtain ⟨t, ht, h⟩ := key w hw
  obtain ⟨t', ht', h'⟩ := key w' hw'
  rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> rcases h' with ⟨e, h'⟩ | ⟨e, h'⟩
  · exact (root_ne D i w w' hw hw' hc hn0 ht (e ▸ ht')).elim
  · exact Or.inl ⟨h, h'⟩
  · exact Or.inr ⟨h, h'⟩
  · exact (root_ne D i w w' hw hw' hc (by simpa using hn0) ht (e ▸ ht')).elim

end GlobalTheory.SplitType

end
