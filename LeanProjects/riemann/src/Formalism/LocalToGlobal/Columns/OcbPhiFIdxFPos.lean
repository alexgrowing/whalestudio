import Formalism.LocalToGlobal.Columns.OcbBEntEntB

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

theorem ocbPhi_forb_iff {k₀ m t a p p' : ℕ} (hk : 1 ≤ k₀) (hm : 4 ≤ m) (hra : k₀ + m - 1 ≤ a) (hne : p ≠ p') (hp' : p' < a) :
    (a ≤ p ∨ (p' < k₀ + m - 1 ∧ p < a ∧ (k₀ + m - 1 ≤ p ∨ symIdx k₀ (m / 2 - 1) p' < symIdx k₀ (m / 2 - 1) p ∨
        (p' = k₀ + (m / 2 - 1) ∧ p < k₀))) ∨
      (k₀ + m - 1 ≤ p' ∧ p < a ∧ (p' - (k₀ + m - 1)) / t < (p - (k₀ + m - 1)) / t)) ↔ ¬ ocbAllow k₀ m t a p p' := by
  have hdiv : p ≤ p' → (p - (k₀ + m - 1)) / t ≤ (p' - (k₀ + m - 1)) / t :=
    fun h => Nat.div_le_div_right (by omega)
  unfold ocbAllow symIdx
  split_ifs <;> omega

theorem ocbPhi_fIdx_fPos {k₀ c n l : ℕ} (hk : k₀ ≤ n) (hl : l < n + c) : LocE.fIdx k₀ c n (LocE.fPos k₀ c n l) = l := by
  unfold LocE.fPos LocE.fIdx
  split_ifs <;> omega

theorem ocbPhi_fPos_lt {k₀ c n l : ℕ} (_hk : k₀ ≤ n) (hl : l < n + c) : LocE.fPos k₀ c n l < n + c := by
  unfold LocE.fPos
  split_ifs <;> omega

theorem ocbPhi_fIdx_lt {k₀ c n p : ℕ} (_hk : k₀ ≤ n) (hp : p < n + c) : LocE.fIdx k₀ c n p < n + c := by
  unfold LocE.fIdx
  split_ifs <;> omega

theorem ocbPhi_ranks {k₀ m t j n' c n : ℕ} (hr : ocbRanks k₀ m t j n' c n) :
    k₀ ≤ n' ∧ k₀ ≤ n ∧ k₀ + m - 1 + (j - 1) * t ≤ n + c ∧ k₀ + m - 1 + (j - 1) * t = n' + (c + 1) ∧ 1 ≤ k₀ ∧ 4 ≤ m := by
  obtain ⟨h1, -, h4, hj, hjm, hc, hn', hn⟩ := hr
  have hjt : (j - 1) * t ≤ j * t := Nat.mul_le_mul_right t (Nat.sub_le j 1)
  refine ⟨by omega, by omega, by omega, by omega, h1, h4⟩

theorem ocbPhi_sum_split {R : Type} [CommRing R] (k₀ r : ℕ) (hk : 1 ≤ k₀) (hr : k₀ + 1 ≤ r) (M : ℕ → ℕ → R) :
    ∑ i ∈ Finset.range (r - 1), M i (i + 1) =
      (∑ i ∈ Finset.range (k₀ - 1), M i (i + 1) + ∑ i ∈ Finset.range (r - k₀ - 1), M (k₀ + i) (k₀ + i + 1)) + M (k₀ - 1) k₀ := by
  obtain ⟨a, rfl⟩ : ∃ a, k₀ = a + 1 := ⟨k₀ - 1, by omega⟩
  have hs : r - 1 = (a + 1) + (r - (a + 1) - 1) := by omega
  rw [hs, Finset.sum_range_add, Finset.sum_range_succ]
  simp only [Nat.add_sub_cancel]
  ring

section Loc

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem ocbPhi_unitV (σ : K →+* ℂ) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) :
    σ (LocE.unitV χ a) = @ocbChiV (𝓞 E ⧸ P.asIdeal) (resField P) ((Units.map (σ : K →* ℂ)).comp χ) (redP P a) := by
  letI := resField P
  unfold LocE.unitV ocbChiV
  by_cases hx : redP P a = 0
  · have hnu : ¬ IsUnit (redP P a) := by
      rw [hx]
      exact not_isUnit_zero
    rw [dif_neg hnu, dif_pos hx, map_zero]
  · have hu : IsUnit (redP P a) := isUnit_iff_ne_zero.mpr hx
    rw [dif_pos hu, dif_neg hx]
    rw [show hu.unit = Units.mk0 _ hx from Units.ext rfl]
    rfl

theorem ocbPhiGS_supp (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {k₀ m t j n' c' c n : ℕ}
    (hr : ocbRanks k₀ m t j n' c n) (hc' : c' = c + 1) (y : HomE E (n' + c') (n + c))
    (h : LocE.PhiGS q ψ₀ χ k₀ (m / 2 - 1) (k₀ + m - 1) t j c' n' c n y ≠ 0) :
    ∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s) := by
  intro l s hl hs
  obtain ⟨hk', hk, -, hsrc, -, -⟩ := ocbPhi_ranks hr
  subst hc'
  unfold LocE.PhiGS at h
  dsimp only at h
  split_ifs at h with hc
  · have hp := ocbPhi_fPos_lt hk hl
    have hp' := ocbPhi_fPos_lt hk' hs
    have e := hc.1 (LocE.fPos k₀ c n l) (LocE.fPos k₀ (c + 1) n' s) hp (by omega)
    rw [ocbBEnt_entB, ocbPhi_fIdx_fPos hk hl, ocbPhi_fIdx_fPos hk' hs] at e
    exact e
  · exact absurd rfl h

private theorem redP_mul_of_intAt_of_intAt {F : Type} [Field F] [NumberField F] {Q : HeightOneSpectrum (𝓞 F)} {a b : F}
    (ha : IntAt Q a) (hb : IntAt Q b) : redP Q (a * b) = redP Q a * redP Q b := by
  have h := redP_prod (P := Q) (Finset.univ : Finset (Fin 2)) ![a, b] (by
    intro i _
    fin_cases i
    · exact ha
    · exact hb)
  simpa [Fin.prod_univ_two] using h

private theorem redP_add_of_intAt {F : Type} [Field F] [NumberField F] {Q : HeightOneSpectrum (𝓞 F)} {a b : F}
    (ha : IntAt Q a) (hb : IntAt Q b) : redP Q (a + b) = redP Q a + redP Q b := by
  have h := redP_sum (P := Q) (Finset.univ : Finset (Fin 2)) ![a, b] (by
    intro i _
    fin_cases i
    · exact ha
    · exact hb)
  simpa [Fin.sum_univ_two] using h

theorem ocbPhiGS_red (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (σ : K →+* ℂ)
    (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {k₀ m t j n' c' c n : ℕ}
    (hr : ocbRanks k₀ m t j n' c n) (hc' : c' = c + 1) (y : HomE E (n' + c') (n + c))
    (ybar : (Fin (n' + (c + 1)) → 𝓞 E ⧸ P.asIdeal) →ₗ[𝓞 E ⧸ P.asIdeal] (Fin (n + c) → 𝓞 E ⧸ P.asIdeal))
    (hint : ∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s))
    (hred : ∀ l s, l < n + c → s < n' + c' → Loc.atN (ybar (Loc.eN _ _ s)) l = redP P (ocbBEnt n' n q y l s)) :
    σ (LocE.PhiGS q ψ₀ χ k₀ (m / 2 - 1) (k₀ + m - 1) t j c' n' c n y) =
      @ocbPhiS (𝓞 E ⧸ P.asIdeal) (resField P) ((σ : K →* ℂ).compAddChar ψ₀) (fun i => (Units.map (σ : K →* ℂ)).comp (χ i))
        k₀ m t j n' c n ybar := by
  obtain ⟨hk', hk, haN, hsrc, hk1, hm4⟩ := ocbPhi_ranks hr
  subst hc'
  letI := resField P
  have hqn : q ≠ 0 := by
    rintro rfl
    exact hu (by simp)
  have hq0 : ((q : ℕ) : E) ≠ 0 := Nat.cast_ne_zero.mpr hqn
  have hF : ∀ p p', p < n + c → p' < n' + (c + 1) →
      ocbEnt k₀ (c + 1) n' c n ybar p p' =
        redP P (LocE.entB q k₀ (c + 1) n' c n (fun i => i + 1) (fun i => i + 1) y p p') := by
    intro p p' hp hp'
    rw [ocbBEnt_entB]
    exact hred _ _ (ocbPhi_fIdx_lt hk hp) (ocbPhi_fIdx_lt hk' hp')
  have hI : ∀ p p', p < n + c → p' < n' + (c + 1) →
      IntAt P (LocE.entB q k₀ (c + 1) n' c n (fun i => i + 1) (fun i => i + 1) y p p') := by
    intro p p' hp hp'
    rw [ocbBEnt_entB]
    exact hint _ _ (ocbPhi_fIdx_lt hk hp) (ocbPhi_fIdx_lt hk' hp')
  have hz : ∀ x : E, IntAt P x → (redP P x = 0 ↔ IntAt P (x / (q : E))) := by
    intro x hx
    constructor
    · intro h0
      exact ciIntAt_div hq hu hx h0
    · intro hb
      have e : x = (q : E) * (x / (q : E)) := by
        field_simp
      rw [e, redP_mul_of_intAt_of_intAt ciIntAt_q hb, redP_natCast_eq_zero hq, zero_mul]
  unfold LocE.PhiGS ocbPhiS
  dsimp only
  split_ifs with h1 h2 h2
  · rw [map_mul, map_inv₀, ocbPhi_unitV]
    unfold LocE.lamGvS
    rw [map_mul, map_prod]
    simp_rw [ocbPhi_unitV]
    have h0 : ocbEnt k₀ (c + 1) n' c n ybar (k₀ - 1) k₀ = 0 := by
      by_contra hnz
      have ha := h2.2 (k₀ - 1) k₀ (by omega) (by omega) (by omega) hnz
      unfold ocbAllow at ha
      split_ifs at ha <;> omega
    have e1 : ∑ i ∈ Finset.range (k₀ - 1),
        redP P (LocE.entB q k₀ (c + 1) n' c n (fun i => i + 1) (fun i => i + 1) y i (i + 1)) =
        ∑ i ∈ Finset.range (k₀ - 1), ocbEnt k₀ (c + 1) n' c n ybar i (i + 1) := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have := Finset.mem_range.mp hi
      exact (hF _ _ (by omega) (by omega)).symm
    have e2 : ∑ i ∈ Finset.range (k₀ + m - 1 - k₀ - 1),
        redP P (LocE.entB q k₀ (c + 1) n' c n (fun i => i + 1) (fun i => i + 1) y (k₀ + i) (k₀ + i + 1)) =
        ∑ i ∈ Finset.range (k₀ + m - 1 - k₀ - 1), ocbEnt k₀ (c + 1) n' c n ybar (k₀ + i) (k₀ + i + 1) := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have := Finset.mem_range.mp hi
      exact (hF _ _ (by omega) (by omega)).symm
    have hS : redP P (∑ i ∈ Finset.range (k₀ - 1),
          LocE.entB q k₀ (c + 1) n' c n (fun i => i + 1) (fun i => i + 1) y i (i + 1) +
        ∑ i ∈ Finset.range (k₀ + m - 1 - k₀ - 1),
          LocE.entB q k₀ (c + 1) n' c n (fun i => i + 1) (fun i => i + 1) y (k₀ + i) (k₀ + i + 1)) =
        ∑ i ∈ Finset.range (k₀ + m - 1 - 1), ocbEnt k₀ (c + 1) n' c n ybar i (i + 1) := by
      have i1 : ∀ i ∈ Finset.range (k₀ - 1),
          IntAt P (LocE.entB q k₀ (c + 1) n' c n (fun i => i + 1) (fun i => i + 1) y i (i + 1)) := by
        intro i hi
        have := Finset.mem_range.mp hi
        exact hI _ _ (by omega) (by omega)
      have i2 : ∀ i ∈ Finset.range (k₀ + m - 1 - k₀ - 1),
          IntAt P (LocE.entB q k₀ (c + 1) n' c n (fun i => i + 1) (fun i => i + 1) y (k₀ + i) (k₀ + i + 1)) := by
        intro i hi
        have := Finset.mem_range.mp hi
        exact hI _ _ (by omega) (by omega)
      rw [redP_add_of_intAt (ciIntAt_sum _ _ i1) (ciIntAt_sum _ _ i2), redP_sum _ _ i1, redP_sum _ _ i2, e1, e2,
        ocbPhi_sum_split k₀ (k₀ + m - 1) hk1 (by omega), h0, add_zero]
    have hB : ∀ i ∈ Finset.range (j - 1),
        redP P (Matrix.of fun (s s' : Fin t) =>
          LocE.entB q k₀ (c + 1) n' c n (fun i => i + 1) (fun i => i + 1) y
            (k₀ + m - 1 + i * t + ↑s) (k₀ + m - 1 + i * t + ↑s')).det =
        (Matrix.of fun (s s' : Fin t) =>
          ocbEnt k₀ (c + 1) n' c n ybar (k₀ + m - 1 + i * t + ↑s) (k₀ + m - 1 + i * t + ↑s')).det := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have hmul : (i + 1) * t ≤ (j - 1) * t := Nat.mul_le_mul_right t hi'
      rw [Nat.add_mul, one_mul] at hmul
      have hlt : ∀ s : Fin t, k₀ + m - 1 + i * t + ↑s < k₀ + m - 1 + (j - 1) * t := fun s => by
        have := s.isLt
        omega
      rw [redP_det (Matrix.of fun (s s' : Fin t) =>
          LocE.entB q k₀ (c + 1) n' c n (fun i => i + 1) (fun i => i + 1) y
            (k₀ + m - 1 + i * t + ↑s) (k₀ + m - 1 + i * t + ↑s'))
        (fun (s s' : Fin t) => hI (k₀ + m - 1 + i * t + ↑s) (k₀ + m - 1 + i * t + ↑s')
          (by have := hlt s; omega) (by have := hlt s'; omega))]
      congr 1
      ext s s'
      simp only [Matrix.map_apply, Matrix.of_apply]
      exact (hF _ _ (by have := hlt s; omega) (by have := hlt s'; omega)).symm
    have hT : redP P (Matrix.of fun (s s' : Fin (k₀ + m - 1 + (j - 1) * t)) =>
          LocE.entB q k₀ (c + 1) n' c n (fun i => i + 1) (fun i => i + 1) y ↑s ↑s').det =
        (Matrix.of fun (s s' : Fin (k₀ + m - 1 + (j - 1) * t)) => ocbEnt k₀ (c + 1) n' c n ybar ↑s ↑s').det := by
      rw [redP_det (Matrix.of fun (s s' : Fin (k₀ + m - 1 + (j - 1) * t)) =>
          LocE.entB q k₀ (c + 1) n' c n (fun i => i + 1) (fun i => i + 1) y ↑s ↑s')
        (fun (s s' : Fin (k₀ + m - 1 + (j - 1) * t)) => hI (↑s) (↑s')
          (by have := s.isLt; omega) (by have := s'.isLt; omega))]
      congr 1
      ext s s'
      simp only [Matrix.map_apply, Matrix.of_apply]
      exact (hF _ _ (by have := s.isLt; omega) (by have := s'.isLt; omega)).symm
    rw [hS, hT, Finset.prod_congr rfl (fun i hi => by rw [hB i hi])]
    rfl
  · exfalso
    apply h2
    constructor
    · intro p' hp'
      rw [hF p' p' (by omega) (by omega)]
      exact (h1.2.2.1 p' hp').1
    · intro p p' hp hp' hne hnz
      by_contra hna
      apply hnz
      rw [hF p p' hp (by omega)]
      have hd := (ocbPhi_forb_iff (a := k₀ + m - 1 + (j - 1) * t) (t := t) hk1 hm4 (by omega) hne hp').mpr hna
      rcases hd with hd | ⟨h3, h4, h5⟩ | ⟨h3, h4, h5⟩
      · exact (hz _ (hI p p' hp (by omega))).mpr (h1.2.1 p p' hd hp hp')
      · exact (h1.2.2.1 p' h3).2 p h4 hne h5
      · exact h1.2.2.2 p p' h3 hp' h4 h5
  · exfalso
    apply h1
    refine ⟨fun p p' hp hp' => hI p p' hp (by omega), ?_, ?_, ?_⟩
    · intro p p' hap hp hp'
      apply (hz _ (hI p p' hp (by omega))).mp
      rw [← hF p p' hp (by omega)]
      by_contra hnz
      exact (ocbPhi_forb_iff (a := k₀ + m - 1 + (j - 1) * t) (t := t) hk1 hm4 (by omega) (by omega) hp').mp
        (Or.inl hap) (h2.2 p p' hp hp' (by omega) hnz)
    · intro p' hp'
      refine ⟨?_, ?_⟩
      · rw [← hF p' p' (by omega) (by omega)]
        exact h2.1 p' hp'
      · intro p hp hne h5
        rw [← hF p p' (by omega) (by omega)]
        by_contra hnz
        exact (ocbPhi_forb_iff (a := k₀ + m - 1 + (j - 1) * t) (t := t) hk1 hm4 (by omega) hne (by omega)).mp
          (Or.inr (Or.inl ⟨hp', hp, h5⟩)) (h2.2 p p' (by omega) (by omega) hne hnz)
    · intro p p' h3 hp' hp h5
      rw [← hF p p' (by omega) (by omega)]
      by_contra hnz
      have hne : p ≠ p' := by
        rintro rfl
        exact lt_irrefl _ h5
      exact (ocbPhi_forb_iff (a := k₀ + m - 1 + (j - 1) * t) (t := t) hk1 hm4 (by omega) hne hp').mp
        (Or.inr (Or.inr ⟨h3, hp, h5⟩)) (h2.2 p p' (by omega) hp' hne hnz)
  · exact map_zero σ

end Loc

end Formalism.L2.Col
