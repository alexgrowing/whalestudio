import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SetStab
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceProjectionZeroIntegralIffComponentsAbove

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

noncomputable section

namespace GlobalTheory.Mem.Col2.BasePoint

open GlobalTheory.Mem.Col2.PtExist

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]

private lemma mem_divs_iff' {E : Type} [Field E] [NumberField E] {π : 𝓞 E} {P : HeightOneSpectrum (𝓞 E)}
    (h : P ∈ divs π) : π ∈ P.asIdeal := by
  unfold divs at h
  split_ifs at h with hf
  · simpa using h
  · simp at h

private lemma false_of_mem_of_conj_mem_of_isCoprime {E : Type} [Field E] [NumberField E] [StarRing E] {π : 𝓞 E} (hcp : IsCoprime π (cO E π))
    (P : HeightOneSpectrum (𝓞 E)) (h1 : π ∈ P.asIdeal) (h2 : cO E π ∈ P.asIdeal) : False := by
  obtain ⟨u, v, h⟩ := hcp
  apply P.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← h]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

private lemma valued_algebraMap_int_le_one' {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E) :
    Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r)) ≤ 1 := by
  erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation, HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_le_one P r

private lemma valued_algebraMap_eq_one_of_not_mem {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E)
    (hr : r ∉ P.asIdeal) : Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r)) = 1 := by
  erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation, HeightOneSpectrum.valuation_of_algebraMap]
  have h2 : ¬ P.intValuation r < 1 := fun h => hr ((HeightOneSpectrum.intValuation_lt_one_iff_mem P r).1 h)
  exact le_antisymm (HeightOneSpectrum.intValuation_le_one P r) (not_lt.1 h2)

private lemma valued_inv_algebraMap_le_one_of_not_mem {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E)
    (hr : r ∉ P.asIdeal) : Valued.v (algebraMap E (P.adicCompletion E) ((algebraMap (𝓞 E) E r)⁻¹)) ≤ 1 := by
  rw [map_inv₀, map_inv₀, valued_algebraMap_eq_one_of_not_mem P r hr, inv_one]

private lemma mem_RInt_of_valued_le_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (y : AfE F E)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), Valued.v (adAt F P y) ≤ 1) : y ∈ RInt F E :=
  (GlobalTheory.Mem.Col2.mem_rInt_iff F E y).2 h

theorem exists_unit (hc : Formalism.BasicNotions.CMData F E) {π : 𝓞 E} (h0 : π ≠ 0) (h1 : cO E π ≠ 0) (hcp : IsCoprime π (cO E π)) :
    ∃ a a' : AfE F E, a' * a = 1 ∧ sigR hc.sig (FiniteAdeleRing (𝓞 F) F) a = a' ∧ a ∈ RInt F E ∧ a' ∈ RInt F E ∧
      (∀ P ∈ divs π, adAt F P a' = algebraMap E _ (algebraMap (𝓞 E) E (cO E π))) ∧
      ∀ w : HeightOneSpectrum (𝓞 E), π * cO E π ∉ w.asIdeal → adAt F w a = 1 := by
  classical
  have hmem : ∀ {P : HeightOneSpectrum (𝓞 E)}, P ∈ divs π → π ∈ P.asIdeal := fun h => mem_divs_iff' h
  have hQ : ∀ P ∈ divs π, conjPrime₂ P ∉ divs π := by
    intro P hP hP'
    exact false_of_mem_of_conj_mem_of_isCoprime hcp P (hmem hP) ((mem_conjP P π).1 (hmem hP'))
  have hc0 : (algebraMap (𝓞 E) E (cO E π)) ≠ 0 := by
    intro h
    exact h1 ((map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 E) E)).1 h)
  have hst : star (algebraMap (𝓞 E) E (cO E π)) = algebraMap (𝓞 E) E π := by
    change star (starRingEnd E (algebraMap (𝓞 E) E π)) = _
    rw [starRingEnd_apply, star_star]
  let α : HeightOneSpectrum (𝓞 E) → E := fun _ => (algebraMap (𝓞 E) E (cO E π))⁻¹
  let β : HeightOneSpectrum (𝓞 E) → E := fun _ => algebraMap (𝓞 E) E (cO E π)
  let a := GlobalTheory.Mem.Col2.PtExist.glue hc (divs π) 1 α β
  have ha : ∀ w, adAt F w a = if w ∈ divs π then algebraMap E _ (α w)
      else if conjPrime₂ w ∈ divs π then algebraMap E _ (star (β (conjPrime₂ w))) else 1 := fun w => by
    rw [GlobalTheory.Mem.Col2.PtExist.adAt_glue hc (divs π) hQ 1 α β w, map_one]
  have ha' : ∀ w, adAt F w (sigR hc.sig (FiniteAdeleRing (𝓞 F) F) a) = if w ∈ divs π then algebraMap E _ (β w)
      else if conjPrime₂ w ∈ divs π then algebraMap E _ (star (α (conjPrime₂ w))) else 1 := fun w => by
    rw [GlobalTheory.Mem.Col2.PtExist.sig_glue hc (divs π) 1 α β, map_one,
      GlobalTheory.Mem.Col2.PtExist.adAt_glue hc (divs π) hQ 1 β α w, map_one]
  refine ⟨a, sigR hc.sig (FiniteAdeleRing (𝓞 F) F) a, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · apply GlobalTheory.Mem.Col2.PtExist.ad_ext
    intro w
    rw [map_mul, ha, ha', map_one]
    split_ifs with hw hw'
    · rw [← map_mul, mul_inv_cancel₀ hc0, map_one]
    · rw [← map_mul, star_inv₀, inv_mul_cancel₀ (star_ne_zero.2 hc0), map_one]
    · rw [mul_one]
  · apply mem_RInt_of_valued_le_one
    intro P
    rw [ha]
    split_ifs with hw hw'
    · exact valued_inv_algebraMap_le_one_of_not_mem P _ (fun h => false_of_mem_of_conj_mem_of_isCoprime hcp P (hmem hw) h)
    · rw [hst]
      exact valued_algebraMap_int_le_one' P π
    · rw [map_one]
  · apply mem_RInt_of_valued_le_one
    intro P
    rw [ha']
    split_ifs with hw hw'
    · exact valued_algebraMap_int_le_one' P _
    · rw [star_inv₀, hst]
      exact valued_inv_algebraMap_le_one_of_not_mem P π (fun h => false_of_mem_of_conj_mem_of_isCoprime hcp P h ((mem_conjP P π).1 (hmem hw')))
    · rw [map_one]
  · intro P hP
    rw [ha', if_pos hP]
  · intro w hw
    rw [ha]
    split_ifs with h2 h3
    · exact absurd (Ideal.mul_mem_right _ _ (hmem h2)) hw
    · exact absurd (Ideal.mul_mem_left _ _ ((mem_conjP w π).1 (hmem h3))) hw
    · rfl

def stdPt (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) : DecoF E n ∅ ∅ ∅ :=
  ⟨(⟨⟨stdLat E n, fun _ _ => 0, fun _ _ _ => 0⟩, stdLat_lattice, stdLat_unimodular,
      fun P => (Finset.notMem_empty _ P.2).elim, fun P => (Finset.notMem_empty _ P.2).elim,
      fun P => (Finset.notMem_empty _ P.2).elim, fun P => (Finset.notMem_empty _ P.2).elim,
      fun P => (Finset.notMem_empty _ P.2).elim, fun P => (Finset.notMem_empty _ P.2).elim,
      fun P => (Finset.notMem_empty _ P.2).elim, fun P => (Finset.notMem_empty _ P.2).elim,
      fun P => (Finset.notMem_empty _ P.2).elim⟩, fun _ => 1), fun P => (Finset.notMem_empty _ P.2).elim⟩

theorem exists_base (hc : Formalism.BasicNotions.CMData F E) {π : 𝓞 E} {T : ℕ} (hT : T ≠ 0) (hπ : π * cO E π = T)
    (hcp : IsCoprime π (cO E π)) (n : ℕ) :
    ∃ k : GL (Fin n) (AfE F E), (∃ p : DecoF E n ∅ ∅ ∅, IsPtOf hc k p ∧ p.deco.1.N = stdLat E n) ∧
      (∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∉ v.asIdeal → bc (prV (E := E) v) k = 1) ∧
      ∀ (P : divs π) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt F P.1 ((k⁻¹).1 r j))
        (if j = r then Ideal.Quotient.mk P.1.asIdeal (cO E π) else 0) := by
  classical
  have hT0 : ((T : ℕ) : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hT
  have h0 : π ≠ 0 := fun h => hT0 (by rw [← hπ, h, zero_mul])
  have h1 : cO E π ≠ 0 := fun h => hT0 (by rw [← hπ, h, mul_zero])
  obtain ⟨a, a', haa, hσ, hai, hai', hP, hw⟩ := exists_unit hc h0 h1 hcp
  let d : Fin n → AfE F E := fun i => if i.1 + 1 = n then a else 1
  let d' : Fin n → AfE F E := fun i => if i.1 + 1 = n then a' else 1
  have hd : ∀ i, d' i * d i = 1 := fun i => by
    simp only [d, d']
    split_ifs
    · exact haa
    · exact mul_one 1
  have hd' : ∀ i, d i * d' i = 1 := fun i => by rw [mul_comm]; exact hd i
  have hdi : ∀ i, d i ∈ RInt F E := fun i => by
    simp only [d]
    split_ifs
    · exact hai
    · exact one_mem _
  have hdi' : ∀ i, d' i ∈ RInt F E := fun i => by
    simp only [d']
    split_ifs
    · exact hai'
    · exact one_mem _
  let k : GL (Fin n) (AfE F E) := ⟨Matrix.diagonal d, Matrix.diagonal d',
    by rw [Matrix.diagonal_mul_diagonal]; simp only [hd']; exact Matrix.diagonal_one,
    by rw [Matrix.diagonal_mul_diagonal]; simp only [hd]; exact Matrix.diagonal_one⟩
  have hk : ((k : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) = Matrix.diagonal d := rfl
  have hk' : ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) = Matrix.diagonal d' := rfl
  refine ⟨k, ⟨stdPt E n, ?_, rfl⟩, ?_, ?_⟩
  · constructor
    · apply (GlobalTheory.Mem.Col2.PtExist.mem_uad_iff k).2
      unfold Formalism.UG.cT
      rw [hk, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
        ← Matrix.diagonal_one]
      congr 1
      funext i
      simp only [d]
      split_ifs
      · rw [hσ, haa]
      · rw [map_one, one_mul]
    · intro x
      unfold Formalism.L2.Herm.hatL
      change x ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (Formalism.L2.Col.stdLat E n) ↔ _
      rw [Formalism.L2.Col.mem_latS_std, Formalism.L2.Col.mem_latS_std, hk']
      constructor
      · intro h i
        rw [Matrix.mulVec_diagonal]
        exact mul_mem (hdi' i) (h i)
      · intro h i
        have := mul_mem (hdi i) (h i)
        rwa [Matrix.mulVec_diagonal, ← mul_assoc, hd' i, one_mul] at this
    all_goals intro P; exact (Finset.notMem_empty _ P.2).elim
  · intro v hv
    have hpa : prV (E := E) v a = 1 := by
      have h := ((GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff F E v (a - 1)).1).2 (fun w hwv => by
        have hnot : π * cO E π ∉ w.asIdeal := by
          intro hmw
          apply hv
          rw [← hwv]
          change algebraMap (𝓞 F) (𝓞 E) (T : 𝓞 F) ∈ w.asIdeal
          rw [map_natCast, ← hπ]
          exact hmw
        rw [map_sub, hw w hnot, map_one, sub_self])
      rwa [map_sub, map_one, sub_eq_zero] at h
    apply Units.ext
    rw [Units.val_one]
    change (Matrix.diagonal d).map (prV (E := E) v) = 1
    rw [Matrix.diagonal_map (map_zero _), ← Matrix.diagonal_one]
    congr 1
    funext i
    simp only [d]
    split_ifs
    · exact hpa
    · exact map_one _
  · intro P r j hr
    rw [hk']
    unfold HasRes
    by_cases hj : j = r
    · subst hj
      rw [Matrix.diagonal_apply_eq, if_pos rfl]
      simp only [d', if_pos hr]
      rw [hP P.1 P.2]
      exact ⟨cO E π, rfl, by rw [sub_self, map_zero]; exact zero_lt_one⟩
    · rw [Matrix.diagonal_apply_ne _ (Ne.symm hj), if_neg hj, map_zero]
      exact ⟨0, map_zero _, by rw [map_zero, map_zero, sub_self, map_zero]; exact zero_lt_one⟩

end General

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem exists_kStd : ∀ {B : Base} (X : PreX B.toPre), (B.primes X).Ok → ∀ (u : B.Word) (n : ℕ), ∃ k : GA B n, (∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf k p ∧ p.deco.1.N = stdLat B.fields.E n) ∧ (∀ v : HeightOneSpectrum (𝓞 B.host.F), (B.T u : 𝓞 B.host.F) ∉ v.asIdeal → bc (prV (E := B.host.E) v) k = 1) ∧ ∀ (P : (B.primes X).vT u) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt B.host.F P.1 ((k⁻¹ : GA B n).1 r j)) (if j = r then Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) else 0) := by
  intro B X hX u n
  exact exists_base B.sp.cm (π := X.piT u) (T := B.T u) (hX.T_prime u).ne_zero (hX.piT_norm u) (hX.piT_cop u) n

end GlobalTheory.Mem.Col2.BasePoint
