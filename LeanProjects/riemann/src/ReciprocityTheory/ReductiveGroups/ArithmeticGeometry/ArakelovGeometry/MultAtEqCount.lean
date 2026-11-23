import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.DimOfMinimal

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem le_colon_chain {J : Ideal (MRing ι)} {N : ℕ} {F : Fin (N + 1) → Ideal (MRing ι)}
    {f : Fin N → MRing ι} {q : Fin N → Ideal (MRing ι)} (h0 : F 0 = J)
    (hj : ∀ j : Fin N, F j.succ = F j.castSucc ⊔ Ideal.span {f j} ∧
      ∀ g, g ∈ q j ↔ g * f j ∈ F j.castSucc) (j : Fin N) : J ≤ q j := by

  have mono : ∀ k : ℕ, ∀ hk : k ≤ N, J ≤ F ⟨k, Nat.lt_succ_of_le hk⟩ := by
    intro k
    induction k with
    | zero =>
      intro hk
      have e : (⟨0, Nat.lt_succ_of_le hk⟩ : Fin (N + 1)) = 0 := Fin.ext (by simp)
      rw [e, h0]
    | succ k ih =>
      intro hk
      have hk' : k < N := hk
      have step := (hj ⟨k, hk'⟩).1
      calc J ≤ F (Fin.castSucc ⟨k, hk'⟩) := ih hk'.le
        _ ≤ F (Fin.castSucc ⟨k, hk'⟩) ⊔ Ideal.span {f ⟨k, hk'⟩} := le_sup_left
        _ = F (Fin.succ ⟨k, hk'⟩) := step.symm
  intro g hg
  exact ((hj j).2 g).2 (Ideal.mul_mem_right _ _ (mono j.val j.isLt.le hg))

theorem multAt_eq_count {J : Ideal (MRing ι)} {N : ℕ} {F : Fin (N + 1) → Ideal (MRing ι)}
    {f : Fin N → MRing ι} {q : Fin N → Ideal (MRing ι)} (h0 : F 0 = J) (hlast : F (Fin.last N) = ⊤)
    (hj : ∀ j : Fin N, F j.succ = F j.castSucc ⊔ Ideal.span {f j} ∧ (q j).IsPrime ∧
      ∀ g, g ∈ q j ↔ g * f j ∈ F j.castSucc)
    {W' : Ideal (MRing ι)} (hW' : W' ∈ J.minimalPrimes) :
    multAt J W' = ∑ j, if q j = W' then 1 else 0 := by
  classical
  have hp : W'.IsPrime := hW'.1.1
  have hJq : ∀ j, J ≤ q j := le_colon_chain h0 fun j => ⟨(hj j).1, (hj j).2.2⟩
  have hmin : ∀ j, q j ≤ W' → q j = W' := fun j h => le_antisymm h (hW'.2 ⟨(hj j).2.1, hJq j⟩ h)
  have := length_loc_chain W' N F f q hlast hj hmin
  rw [h0] at this
  unfold multAt
  rw [dif_pos hp, this]
  simp

theorem block_step {L : ℝ} {m p : ℕ} (hp : p.Prime) {W : Ideal (MRing ι)} (hW : IsMultiProjPrime W)
    (hpW : (p : MRing ι) ∈ W)
    (hdim : ringKrullDim (MRing ι ⧸ W) = ((m + 1 + Fintype.card K : ℕ) : WithBot ℕ∞))
    (hR4W : ∀ (a : Fin (m + 1) → K → ℤ) (k : K) (i : ι k), (X ⟨k, i⟩ : MRing ι) ∉ W →
      (a (Fin.last m) = fun k' => if k' = k then 1 else 0) →
      geoNum (m + 1) W a = ∑ᶠ W' ∈ divSupp W (X ⟨k, i⟩),
        (multAt (W ⊔ Ideal.span {(X ⟨k, i⟩ : MRing ι)}) W' : ℤ) * geoNum m W' (Fin.init a))
    (IH : ∀ W' : Ideal (MRing ι), IsMultiProjPrime W' → (p : MRing ι) ∈ W' →
      ringKrullDim (MRing ι ⧸ W') = ((m + Fintype.card K : ℕ) : WithBot ℕ∞) →
      HAsymp L m W' ∧ SymmAt m W')
    (b : K) :
    ∃ (a₀ : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
      |lg W a - lg W (a - Pi.single b 1) -
          L * (geoNum (m + 1) W (Fin.snoc (fun _ k => (a k : ℤ)) (uv b)) : ℝ) / m.factorial| ≤
        C * m * ((tdeg a : ℝ) + 1) ^ (m - 1) := by
  classical
  obtain ⟨hWp, hWm, hWr⟩ := hW
  obtain ⟨i, hi⟩ := hWr b
  set s : MRing ι := X ⟨b, i⟩ with hsdef
  have hs : IsMultiHomog s (Pi.single b 1) := isMultiHomog_X' b i
  set J := W ⊔ Ideal.span {s} with hJdef
  have hJ : IsMultiHomogIdeal J := isMultiHomogIdeal_sup_span hWm hs
  obtain ⟨N, F, f, c, q, h0, hlast, hj⟩ := exists_primeFiltration_of_isMultiHomogIdeal J hJ
  have hJq : ∀ j, J ≤ q j := le_colon_chain h0 fun j => ⟨(hj j).2.1, (hj j).2.2.2.2⟩
  have hFm : IsMultiHomogIdeal (F 0) := h0 ▸ hJ
  choose a0 C hC hb using fun j => per_factor (L := L) hp hWm hpW hdim hs hi IH (hj j).2.2.1
    (hj j).2.2.2.1 (hJq j) (c j)
  refine ⟨1 + ∑ j, a0 j + ∑ j, tdeg (c j), ∑ j, C j, Finset.sum_nonneg fun j _ => hC j,
    fun a ha => ?_⟩
  have ha0 : ∀ j k, a0 j ≤ a k := fun j k => by
    have h1 : a0 j ≤ ∑ j, a0 j := Finset.single_le_sum (f := a0) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)
    have := ha k
    omega
  have hca : ∀ j k, c j k ≤ a k := fun j k => by
    have h1 : c j k ≤ tdeg (c j) := Finset.single_le_sum (f := c j) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ k)
    have h2 : tdeg (c j) ≤ ∑ j, tdeg (c j) := Finset.single_le_sum (f := fun j => tdeg (c j))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have := ha k
    omega
  have hb1 : ∀ k, (Pi.single b 1 : K → ℕ) k ≤ a k := fun k => by
    have := ha k
    by_cases hk : k = b
    · subst hk; simp; omega
    · simp [Pi.single_apply, hk]
  have hstep := lg_step hWm hs (q := W)
    (fun g => ⟨fun h => W.mul_mem_right _ h, fun h => (hWp.mem_or_mem h).resolve_right hi⟩)
    hb1 hp.pos hpW
  have hch := lg_chain a hFm hlast (fun j => ⟨(hj j).1, (hj j).2.1, (hj j).2.2.2.2⟩) hca hp.pos
    (fun j => hJq j (Ideal.mem_sup_left hpW))
  rw [h0] at hch
  have hfin := divSupp_finite W s
  have hsum : L * (geoNum (m + 1) W (Fin.snoc (fun _ k => (a k : ℤ)) (uv b)) : ℝ) / m.factorial =
      ∑ j, (if q j ∈ divSupp W s then appr L m (q j) a else 0) := by
    rw [hR4W _ b i hi (by funext k'; simp [uv, Pi.single_apply]), Fin.init_snoc,
      finsum_mem_eq_finite_toFinset_sum _ hfin]
    have hcount : ∀ W' ∈ hfin.toFinset, multAt J W' = ∑ j, if q j = W' then 1 else 0 :=
      fun W' hW' => multAt_eq_count h0 hlast (fun j => ⟨(hj j).2.1, (hj j).2.2.1, (hj j).2.2.2.2⟩)
        ((Set.Finite.mem_toFinset hfin).mp hW').1
    rw [Finset.sum_congr rfl fun W' hW' => by rw [hcount W' hW']]
    push_cast
    simp_rw [Finset.sum_mul, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_comm, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_ite_eq]
    simp only [Set.Finite.mem_toFinset, appr]
    split_ifs <;> simp
  rw [hsum, hstep, hch, add_sub_cancel_right, ← Finset.sum_sub_distrib, Finset.sum_mul,
    Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hb j a fun k => ha0 j k)

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
