import Formalism.LocalToGlobal.Columns.ChainInstY
import Formalism.LocalToGlobal.Columns.ChainInstS

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section PhiS

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem xtLamGvS_congr (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {k₀ r t j a : ℕ} (M M' : ℕ → ℕ → E)
    (hk : k₀ ≤ a) (_hr : r ≤ a) (hja : r + j * t ≤ a)
    (h : ∀ p p', p < a → p' < a → IntAt P (M p p') ∧ IntAt P (M' p p') ∧ redP P (M' p p') = redP P (M p p')) :
    LocE.lamGvS ψ₀ χ k₀ r t j M' = LocE.lamGvS ψ₀ χ k₀ r t j M := by
  unfold LocE.lamGvS
  have hS : ∀ M0 : ℕ → ℕ → E, (∀ p p', p < a → p' < a → IntAt P (M0 p p')) →
      redP P (∑ i ∈ Finset.range (k₀ - 1), M0 i (i + 1) +
        ∑ i ∈ Finset.range (r - k₀ - 1), M0 (k₀ + i) (k₀ + i + 1)) =
        ∑ i ∈ Finset.range (k₀ - 1), redP P (M0 i (i + 1)) +
          ∑ i ∈ Finset.range (r - k₀ - 1), redP P (M0 (k₀ + i) (k₀ + i + 1)) := by
    intro M0 hM0
    have h1 : ∀ i ∈ Finset.range (k₀ - 1), IntAt P (M0 i (i + 1)) := fun i hi => by
      rw [Finset.mem_range] at hi
      exact hM0 _ _ (by omega) (by omega)
    have h2 : ∀ i ∈ Finset.range (r - k₀ - 1), IntAt P (M0 (k₀ + i) (k₀ + i + 1)) := fun i hi => by
      rw [Finset.mem_range] at hi
      exact hM0 _ _ (by omega) (by omega)
    rw [reduction_add (ciIntAt_sum _ _ h1) (ciIntAt_sum _ _ h2), redP_sum _ _ h1, redP_sum _ _ h2]
  rw [hS M' (fun p p' hp hp' => (h p p' hp hp').2.1), hS M (fun p p' hp hp' => (h p p' hp hp').1)]
  have hblk : ∀ i ∈ Finset.range j, ∀ s s' : Fin t,
      r + i * t + s.1 < a ∧ r + i * t + s'.1 < a := by
    intro i hi s s'
    rw [Finset.mem_range] at hi
    have hit : i * t + t ≤ j * t := by
      have h3 := Nat.mul_le_mul_right t (show i + 1 ≤ j by omega)
      rwa [Nat.succ_mul] at h3
    have hs := s.2
    have hs' := s'.2
    generalize i * t = u at hit ⊢
    generalize j * t = v at hit hja
    constructor <;> omega
  congr 1
  · congr 1
    congr 1
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      exact (h _ _ (by omega) (by omega)).2.2
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      exact (h _ _ (by omega) (by omega)).2.2
  · refine Finset.prod_congr rfl fun i hi => ?_
    apply ciUnitV_congr
    rw [redP_det (Matrix.of fun s s' : Fin t => M' (r + i * t + s.1) (r + i * t + s'.1))
        (fun s s' => (h _ _ (hblk i hi s s').1 (hblk i hi s s').2).2.1),
      redP_det (Matrix.of fun s s' : Fin t => M (r + i * t + s.1) (r + i * t + s'.1))
        (fun s s' => (h _ _ (hblk i hi s s').1 (hblk i hi s s').2).1)]
    congr 1
    ext s s'
    simp only [Matrix.map_apply, Matrix.of_apply]
    exact (h _ _ (hblk i hi s s').1 (hblk i hi s s').2).2.2

open Classical in

theorem xtPhiGS_congr (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hq0 : (q : E) ≠ 0) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K)
    (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {k₀ rS r t j c' n' c n : ℕ} (x x' : HomE E (n' + c') (n + c))
    (hk : k₀ ≤ r) (han : r + (j - 1) * t ≤ n + c)
    (hD : ∀ p p', p < n + c → p' < r + (j - 1) * t → ∃ d, IntAt P d ∧
      LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x' p p' =
        LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x p p' + q * d) :
    LocE.PhiGS (P := P) q ψ₀ χ k₀ rS r t j c' n' c n x' = LocE.PhiGS (P := P) q ψ₀ χ k₀ rS r t j c' n' c n x := by
  have hone : IntAt P (-1 : E) := ⟨-1, 1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  have hneg : ∀ z : E, IntAt P z → IntAt P (-z) := fun z hz => by
    rw [← neg_one_mul]
    exact hone.mul hz
  have hqI : IntAt P (q : E) := ⟨q, 1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  have hra : r ≤ r + (j - 1) * t := Nat.le_add_right _ _
  have imp : ∀ A B : ℕ → ℕ → E,
      (∀ p p', p < n + c → p' < r + (j - 1) * t → ∃ d, IntAt P d ∧ B p p' = A p p' + q * d) →
      ((∀ p p', p < n + c → p' < r + (j - 1) * t → IntAt P (A p p')) ∧
        (∀ p p', r + (j - 1) * t ≤ p → p < n + c → p' < r + (j - 1) * t → IntAt P (A p p' / (q : E))) ∧
        (∀ p', p' < r → redP P (A p' p') = 1 ∧ ∀ p, p < r + (j - 1) * t → p ≠ p' →
          (r ≤ p ∨ symIdx k₀ rS p' < symIdx k₀ rS p ∨ (p' = k₀ + rS ∧ p < k₀)) → redP P (A p p') = 0) ∧
        (∀ p p', r ≤ p' → p' < r + (j - 1) * t → p < r + (j - 1) * t → (p' - r) / t < (p - r) / t →
          redP P (A p p') = 0)) →
      ((∀ p p', p < n + c → p' < r + (j - 1) * t → IntAt P (B p p')) ∧
        (∀ p p', r + (j - 1) * t ≤ p → p < n + c → p' < r + (j - 1) * t → IntAt P (B p p' / (q : E))) ∧
        (∀ p', p' < r → redP P (B p' p') = 1 ∧ ∀ p, p < r + (j - 1) * t → p ≠ p' →
          (r ≤ p ∨ symIdx k₀ rS p' < symIdx k₀ rS p ∨ (p' = k₀ + rS ∧ p < k₀)) → redP P (B p p') = 0) ∧
        (∀ p p', r ≤ p' → p' < r + (j - 1) * t → p < r + (j - 1) * t → (p' - r) / t < (p - r) / t →
          redP P (B p p') = 0)) := by
    intro A B hAB ⟨c1, c2, c3, c4⟩
    have hint : ∀ p p', p < n + c → p' < r + (j - 1) * t → IntAt P (B p p') := by
      intro p p' hp hp'
      obtain ⟨d, hd, he⟩ := hAB p p' hp hp'
      rw [he]
      exact (c1 p p' hp hp').add (hqI.mul hd)
    have hred : ∀ p p', p < n + c → p' < r + (j - 1) * t → redP P (B p p') = redP P (A p p') := by
      intro p p' hp hp'
      obtain ⟨d, hd, he⟩ := hAB p p' hp hp'
      rw [he, reduction_add (c1 p p' hp hp') (hqI.mul hd), reduction_mul hqI hd, redP_natCast_eq_zero hq, zero_mul, add_zero]
    refine ⟨hint, ?_, ?_, ?_⟩
    · intro p p' h1 h2 h3
      obtain ⟨d, hd, he⟩ := hAB p p' h2 h3
      rw [he, add_div, mul_div_cancel_left₀ _ hq0]
      exact (c2 p p' h1 h2 h3).add hd
    · intro p' hp'
      have hp'a : p' < r + (j - 1) * t := by omega
      have hp'n : p' < n + c := by omega
      refine ⟨by rw [hred p' p' hp'n hp'a]; exact (c3 p' hp').1, fun p hp hne hcond => ?_⟩
      rw [hred p p' (by omega) hp'a]
      exact (c3 p' hp').2 p hp hne hcond
    · intro p p' h1 h2 h3 h4
      rw [hred p p' (by omega) h2]
      exact c4 p p' h1 h2 h3 h4
  have fwd : ∀ p p', p < n + c → p' < r + (j - 1) * t → ∃ d, IntAt P d ∧
      LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x' p p' =
        LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x p p' + q * d := hD
  have bwd : ∀ p p', p < n + c → p' < r + (j - 1) * t → ∃ d, IntAt P d ∧
      LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x p p' =
        LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x' p p' + q * d := by
    intro p p' hp hp'
    obtain ⟨d, hd, he⟩ := hD p p' hp hp'
    exact ⟨-d, hneg d hd, by rw [he]; ring⟩
  unfold LocE.PhiGS
  simp only
  split_ifs with h1 h2 h2
  · have hM := h2.1
    have hall : ∀ p p', p < r + (j - 1) * t → p' < r + (j - 1) * t →
        IntAt P (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x p p') ∧
        IntAt P (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x' p p') ∧
        redP P (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x' p p') =
          redP P (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x p p') := by
      intro p p' hp hp'
      have hpn : p < n + c := by omega
      refine ⟨hM p p' hpn hp', h1.1 p p' hpn hp', ?_⟩
      obtain ⟨d, hd, he⟩ := hD p p' hpn hp'
      rw [he, reduction_add (hM p p' hpn hp') (hqI.mul hd), reduction_mul hqI hd, redP_natCast_eq_zero hq, zero_mul, add_zero]
    rw [xtLamGvS_congr ψ₀ χ _ _ (by omega) hra le_rfl hall]
    congr 2
    apply ciUnitV_congr
    rw [redP_det (Matrix.of fun s s' : Fin (r + (j - 1) * t) =>
          LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x' s.1 s'.1)
        (fun s s' => (hall _ _ s.2 s'.2).2.1),
      redP_det (Matrix.of fun s s' : Fin (r + (j - 1) * t) =>
          LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x s.1 s'.1)
        (fun s s' => (hall _ _ s.2 s'.2).1)]
    congr 1
    ext s s'
    simp only [Matrix.map_apply, Matrix.of_apply]
    exact (hall _ _ s.2 s'.2).2.2
  · exact absurd (imp _ _ bwd h1) h2
  · exact absurd (imp _ _ fwd h2) h1
  · rfl

open Classical in
theorem xtPhiGS_int (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    {k₀ rS r t j c' n' c n : ℕ} (x : HomE E (n' + c') (n + c)) (h : LocE.PhiGS (P := P) q ψ₀ χ k₀ rS r t j c' n' c n x ≠ 0) :
    ∀ p p', p < n + c → p' < r + (j - 1) * t →
      IntAt P (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x p p') := by
  intro p p' hp hp'
  by_contra hn
  apply h
  unfold LocE.PhiGS
  simp only
  rw [if_neg]
  intro hc
  exact hn (hc.1 p p' hp hp')

end PhiS

section Til

variable {E : Type} [Field E] [NumberField E] [StarRing E] {N n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem xtTilH_mem (hN : N = n + 1) (d : DecoSet E n ∅ SG) {pi : 𝓞 E} (hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal) (hG : ∀ w : SG, pi ∉ w.1.asIdeal)
    (w : HeightOneSpectrum (𝓞 E)) (v : Sp E N) :
    v ∈ (DecoSet.tilH (ST := ST) hN pi d).1.at w ↔
      (fun i : Fin n => v ⟨i.1, by omega⟩) ∈ d.1.at w ∧ IntAt w (v ⟨n, by omega⟩) := by
  subst hN
  have hOk := Deco.Ok.til (ST := ST) d.2 hT hG
  have htil : DecoSet.tilH (ST := ST) rfl pi d = ⟨d.1.til (ST := ST) pi, hOk⟩ := by
    show DecoSet.til (ST := ST) pi d = _
    unfold DecoSet.til
    rw [dif_pos hOk]
  rw [htil]
  show v ∈ localization₂ w.asIdeal (tilN d.1.N) ↔ _
  rw [mem_localization_tilN]
  rfl

open Classical in

theorem xtTilH_be (hN : N = n + 1) (d : DecoSet E n ∅ SG) {pi : 𝓞 E} (hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal) (hG : ∀ w : SG, pi ∉ w.1.asIdeal)
    (w : SG) (v : Sp E N) (hv : v ∈ (DecoSet.tilH (ST := ST) hN pi d).1.at w.1) (i : Fin N) :
    (DecoSet.tilH (ST := ST) hN pi d).1.be w v i =
      if h : i.1 < n then d.1.be w (fun i : Fin n => v ⟨i.1, by omega⟩) ⟨i.1, h⟩
      else redP w.1 (v ⟨n, by omega⟩ / algebraMap (𝓞 E) E pi) := by
  subst hN
  have hOk := Deco.Ok.til (ST := ST) d.2 hT hG
  have htil : DecoSet.tilH (ST := ST) rfl pi d = ⟨d.1.til (ST := ST) pi, hOk⟩ := by
    show DecoSet.til (ST := ST) pi d = _
    unfold DecoSet.til
    rw [dif_pos hOk]
  rw [htil] at hv ⊢
  have hv' : v ∈ localization₂ w.1.asIdeal (tilN d.1.N) := hv
  show (if v ∈ localization₂ w.1.asIdeal (tilN d.1.N) then
      Fin.snoc (α := fun _ => 𝓞 E ⧸ w.1.asIdeal) (d.1.be w (initL E n v))
        (redP w.1 (v (Fin.last n) / algebraMap (𝓞 E) E pi)) else 0) i = _
  rw [if_pos hv']
  split_ifs with h
  · have hi : i = Fin.castSucc ⟨i.1, h⟩ := Fin.ext rfl
    conv_lhs => rw [hi, Fin.snoc_castSucc]
    rfl
  · have hi : i = Fin.last n := Fin.ext (by have := i.2; simp only [Fin.val_last]; omega)
    rw [hi, Fin.snoc_last]
    rfl

end Til

end Formalism.L2.Col
