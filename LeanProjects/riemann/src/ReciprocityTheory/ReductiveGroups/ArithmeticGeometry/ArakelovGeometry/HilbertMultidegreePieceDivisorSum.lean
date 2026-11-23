import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.NatCardEqPowLength

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem multigraded_length_stable_dim_zero {p : ℕ} (hp : p.Prime) {W : Ideal (MRing ι)} (hW : IsMultiProjPrime W)
    (hpW : (p : MRing ι) ∈ W)
    (hd : ringKrullDim (MRing ι ⧸ W) = ((0 + Fintype.card K : ℕ) : WithBot ℕ∞)) (b : K) :
    ∃ a₀ : ℕ, ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) → lg W a = lg W (a - Pi.single b 1) := by
  obtain ⟨hWp, hWm, hWr⟩ := hW
  haveI := hWp
  obtain ⟨i, hi⟩ := hWr b
  have hf : IsMultiHomog (X ⟨b, i⟩ : MRing ι) (Pi.single b 1) := isMultiHomog_X' b i
  have hJm : IsMultiHomogIdeal (W ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι)}) :=
    isMultiHomogIdeal_sup_span hWm hf
  obtain ⟨N, F, f, c, q, h0, hlast, hj⟩ := exists_primeFiltration_of_isMultiHomogIdeal _ hJm
  have hle : ∀ j, W ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι)} ≤ q j := fun j =>
    le_colon_chain h0 (fun j => ⟨(hj j).2.1, (hj j).2.2.2.2⟩) j

  have hirr : ∀ j, ∃ k, ∀ i', (X ⟨k, i'⟩ : MRing ι) ∈ q j := by
    intro j
    haveI := (hj j).2.2.1
    obtain ⟨W', hW'min, hW'le⟩ := Ideal.exists_minimalPrimes_le (hle j)
    have hnr := not_relevant_of_dim_zero hWm hd hf hi hW'min
    rw [IsRelevant] at hnr
    push_neg at hnr
    obtain ⟨k, hk⟩ := hnr
    exact ⟨k, fun i' => hW'le (hk i')⟩
  have hp0 : 0 < p := hp.pos
  refine ⟨(Finset.univ.sup fun jk : Fin N × K => c jk.1 jk.2) + 1, fun a ha => ?_⟩
  have hca : ∀ j k, c j k < a k := by
    intro j k
    have h1 : c j k ≤ Finset.univ.sup fun jk : Fin N × K => c jk.1 jk.2 :=
      Finset.le_sup (f := fun jk : Fin N × K => c jk.1 jk.2) (Finset.mem_univ (j, k))
    have h2 := ha k
    omega
  have hsingle : ∀ k, (Pi.single b 1 : K → ℕ) k ≤ a k := by
    intro k
    rcases eq_or_ne k b with rfl | hk
    · have h2 := ha k
      simp only [Pi.single_eq_same]
      omega
    · simp [hk]
  have hstep := lg_step hWm hf (q := W)
    (fun g => ⟨fun hg => W.mul_mem_right _ hg,
      fun hg => (hWp.mem_or_mem hg).resolve_right hi⟩) hsingle hp0 hpW
  have hF0 : IsMultiHomogIdeal (F 0) := by rw [h0]; exact hJm
  have hchain := lg_chain a (F := F) (f := f) (c := c) (q := q) hF0 hlast
    (fun j => ⟨(hj j).1, (hj j).2.1, (hj j).2.2.2.2⟩) (fun j k => (hca j k).le) hp0
    (fun j => hle j (Ideal.mem_sup_left hpW))
  have hzero : ∀ j, lg (q j) (a - c j) = 0 := by
    intro j
    obtain ⟨k, hk⟩ := hirr j
    have hpos : 0 < (a - c j) k := by
      show 0 < a k - c j k
      have h3 := hca j k
      omega
    rw [lg, card_mPiece_irrel hk hpos]
    simp
  rw [hstep, ← h0, hchain, Finset.sum_eq_zero (fun j _ => hzero j), zero_add]

theorem hasymp_base {p : ℕ} (hp : p.Prime) {L : ℝ} (hL : L = Real.log p) {W : Ideal (MRing ι)}
    (hW : IsMultiProjPrime W) (hpW : (p : MRing ι) ∈ W)
    (hd : ringKrullDim (MRing ι ⧸ W) = ((0 + Fintype.card K : ℕ) : WithBot ℕ∞)) : HAsymp L 0 W := by
  have hW0 := hW
  obtain ⟨hWp, hWm, hWr⟩ := hW0
  have hp0 : 0 < p := hp.pos
  choose a₀ ha₀ using fun b : K => multigraded_length_stable_dim_zero hp hW hpW hd b
  obtain ⟨a₁, ha₁⟩ : ∃ a₁ : ℕ, ∀ b, a₀ b ≤ a₁ :=
    ⟨Finset.univ.sup a₀, fun b => Finset.le_sup (Finset.mem_univ b)⟩

  have hconst_lg : ∀ a : K → ℕ, (∀ k, a₁ ≤ a k) → lg W a = lg W (fun _ => a₁) := by
    have hwalk := walk_bound (fun a => lg W a - lg W (fun _ => a₁)) a₁ 0 (le_refl (0 : ℝ))
      (by
        intro a b ha _
        have h1 := ha₀ b a (fun k => (ha₁ b).trans (ha k))
        simp [h1])
    intro a ha
    have h1 := hwalk a ha
    simp only [sub_self, abs_zero, zero_add, Nat.cast_zero, mul_zero, zero_mul] at h1
    have h2 : |lg W a - lg W (fun _ => a₁)| = 0 := le_antisymm h1 (abs_nonneg _)
    rw [abs_eq_zero, sub_eq_zero] at h2
    exact h2
  have hcard : ∀ a : K → ℕ, (∀ k, a₁ ≤ a k) →
      Nat.card (mPiece W a) = Nat.card (mPiece W (fun _ => a₁)) := by
    intro a ha
    have h := hconst_lg a ha
    simp only [lg] at h
    have h1 : (0 : ℝ) < Nat.card (mPiece W a) := by
      exact_mod_cast card_mPiece_pos W a hp0 hpW
    have h2 : (0 : ℝ) < Nat.card (mPiece W (fun _ => a₁)) := by
      exact_mod_cast card_mPiece_pos W _ hp0 hpW
    exact_mod_cast Real.log_injOn_pos (Set.mem_Ioi.2 h1) (Set.mem_Ioi.2 h2) h
  let i : ∀ k, ι k := fun k => (hWr k).choose
  have hi : ∀ k, (X ⟨k, i k⟩ : MRing ι) ∉ W := fun k => (hWr k).choose_spec
  have hD : Nat.card (MRing ι ⧸ dehomI W i) = Nat.card (mPiece W (fun _ => a₁)) :=
    card_dehom hWp hWm hi hcard (fun a => finite_mPiece W a hp0 hpW)
      (a := fun _ => a₁) (fun _ => le_refl _)
  have hpD : (p : MRing ι) ∈ dehomI W i := by
    rw [dehomI]
    exact Ideal.mem_sup_left hpW
  have hA : ∀ x : MRing ι ⧸ dehomI W i, p • x = 0 := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [nsmul_eq_mul, ← map_natCast (Ideal.Quotient.mk (dehomI W i)) p, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right y _ hpD
  haveI : Finite (MRing ι ⧸ dehomI W i) :=
    Nat.finite_of_card_ne_zero (by rw [hD]; exact (card_mPiece_pos W _ hp0 hpW).ne')
  have hpow := natCard_eq_pow_length hp hA
  refine ⟨a₁, 0, le_refl 0, fun a ha => ?_⟩
  have hgeo : geoNum 0 W (fun _ k => (a k : ℤ)) =
      ((Module.length ℤ (MRing ι ⧸ dehomI W i)).toNat : ℤ) := by
    rw [geoNum, dif_pos hWr]
    rfl
  have hc : (Nat.card (mPiece W a) : ℝ) =
      (p : ℝ) ^ (Module.length ℤ (MRing ι ⧸ dehomI W i)).toNat := by
    rw [hcard a ha, ← hD, hpow]
    norm_cast
  have h0 : lg W a - appr L 0 W a = 0 := by
    rw [lg, appr, hc, hgeo, Real.log_pow, hL]
    simp only [Nat.factorial_zero, Nat.cast_one, div_one]
    push_cast
    ring
  rw [h0]
  simp

theorem hilbert_multidegree_piece_divisor_sum
    (hR4 : ∀ (n : ℕ) (V : Ideal (MRing ι)) (a : Fin (n + 1) → K → ℤ) (k : K) (i : ι k),
      IsMultiProjPrime V → charOf V ≠ 0 →
      ringKrullDim (MRing ι ⧸ V) = ((n + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
      (X ⟨k, i⟩ : MRing ι) ∉ V →
      (a (Fin.last n) = fun k' => if k' = k then 1 else 0) →
      geoNum (n + 1) V a = ∑ᶠ W' ∈ divSupp V (X ⟨k, i⟩),
        (multAt (V ⊔ Ideal.span {(X ⟨k, i⟩ : MRing ι)}) W' : ℤ) * geoNum n W' (Fin.init a))
    (hSymm : ∀ (n : ℕ) (V : Ideal (MRing ι)) (a : Fin n → K → ℤ) (σ : Equiv.Perm (Fin n)),
      IsMultiProjPrime V → charOf V ≠ 0 →
      ringKrullDim (MRing ι ⧸ V) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞) →
      geoNum n V (a ∘ σ) = geoNum n V a)
    (W : Ideal (MRing ι)) (hW : IsMultiProjPrime W) (hp : (charOf W).Prime) (d : ℕ)
    (hd : ringKrullDim (MRing ι ⧸ W) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    ∃ (a₀ : ℕ) (C : ℝ), ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
      |Real.log (Nat.card (mPiece W a)) / Real.log (charOf W) -
          (geoNum d W (fun _ k => (a k : ℤ)) : ℝ) / (d.factorial : ℝ)| ≤
        C * ((∑ k, a k : ℕ) + 1 : ℝ) ^ d / ((∑ k, a k : ℕ) + 1 : ℝ) := by
  have hmem : ((charOf W : ℕ) : MRing ι) ∈ W := natCast_mem_of_charOf W
  obtain ⟨⟨a₀, C, hC, hA⟩, -⟩ := hasymp_all (L := Real.log (charOf W)) hp hR4 hSymm
    (fun W' hW' hpW' hd' => hasymp_base hp rfl hW' hpW' hd') d W hW hmem hd
  have hL : 0 < Real.log (charOf W) := Real.log_pos (by exact_mod_cast hp.one_lt)
  refine ⟨a₀, C * d / Real.log (charOf W), fun a ha => ?_⟩
  have h := hA a ha
  simp only [lg, appr, tdeg] at h
  generalize hT : ((∑ k, a k : ℕ) : ℝ) = T at h ⊢
  generalize Real.log (Nat.card (mPiece W a)) = x at h ⊢
  generalize (geoNum d W (fun _ k => (a k : ℤ)) : ℝ) = g at h ⊢
  generalize Real.log (charOf W) = L at h hL ⊢
  have hT0 : 0 ≤ T := by rw [← hT]; exact Nat.cast_nonneg _
  have hT1 : 0 < T + 1 := by linarith
  have hT1' : T + 1 ≠ 0 := hT1.ne'
  have hL0 : L ≠ 0 := hL.ne'
  have hf : (d.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  have e1 : x / L - g / d.factorial = (x - L * g / d.factorial) / L := by
    field_simp
  have e2 : C * d / L * (T + 1) ^ d / (T + 1) = C * d * (T + 1) ^ (d - 1) / L := by
    rcases d with _ | n
    · simp
    · rw [Nat.add_sub_cancel, pow_succ]
      field_simp
  rw [e1, abs_div, abs_of_pos hL, e2]
  exact div_le_div_of_nonneg_right h hL.le

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
