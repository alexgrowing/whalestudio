import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MultAtEqCount

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem main_step {L : ℝ} {m p : ℕ} (hp : p.Prime) {W : Ideal (MRing ι)} (hW : IsMultiProjPrime W)
    (hpW : (p : MRing ι) ∈ W)
    (hdim : ringKrullDim (MRing ι ⧸ W) = ((m + 1 + Fintype.card K : ℕ) : WithBot ℕ∞))
    (hR4W : ∀ (a : Fin (m + 1) → K → ℤ) (k : K) (i : ι k), (X ⟨k, i⟩ : MRing ι) ∉ W →
      (a (Fin.last m) = fun k' => if k' = k then 1 else 0) →
      geoNum (m + 1) W a = ∑ᶠ W' ∈ divSupp W (X ⟨k, i⟩),
        (multAt (W ⊔ Ideal.span {(X ⟨k, i⟩ : MRing ι)}) W' : ℤ) * geoNum m W' (Fin.init a))
    (hSW : SymmAt (m + 1) W)
    (IH : ∀ W' : Ideal (MRing ι), IsMultiProjPrime W' → (p : MRing ι) ∈ W' →
      ringKrullDim (MRing ι ⧸ W') = ((m + Fintype.card K : ℕ) : WithBot ℕ∞) →
      HAsymp L m W' ∧ SymmAt m W') :
    HAsymp L (m + 1) W := by
  choose a0 C hC hb using fun b => block_step (L := L) hp hW hpW hdim hR4W IH b
  set a₁ := 1 + ∑ b, a0 b
  set Δ : (K → ℕ) → ℝ := fun a => lg W a - appr L (m + 1) W a with hΔ
  set B := coefB (m + 1) W
  have hB : 0 ≤ B := coefB_nonneg _ _
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  set Kst := ∑ b, C b + |L| * B * 2 ^ (m - 1) / m.factorial
  have hKst : 0 ≤ Kst := by
    have := Finset.sum_nonneg fun b (_ : b ∈ Finset.univ) => hC b
    positivity
  have hstep : ∀ a : K → ℕ, ∀ b, (∀ k, a₁ ≤ a k) → a₁ < a b →
      |Δ a - Δ (a - Pi.single b 1)| ≤ Kst * m * ((tdeg a : ℝ) + 1) ^ (m - 1) := by
    intro a b ha hab
    have ha0 : ∀ k, a0 b ≤ a k := fun k => by
      have h1 : a0 b ≤ ∑ b, a0 b := Finset.single_le_sum (f := a0) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ b)
      have := ha k
      omega
    have h1 := hb b a ha0
    set x : K → ℤ := fun k => (a k : ℤ)
    have hx : (fun _ : Fin (m + 1) => fun k => ((a - (Pi.single b 1 : K → ℕ)) k : ℤ)) =
        fun _ => x - uv b := by
      funext _ k
      by_cases hk : k = b
      · subst hk
        have : 1 ≤ a k := by omega
        simp [x, uv, Nat.cast_sub this]
      · simp [x, uv, Pi.single_apply, hk]
    have h2 := geoNum_diff_est m W hSW x b
    rw [show nrm x = tdeg a from nrm_natCast a] at h2
    have hfs : ((m + 1).factorial : ℝ) = (m + 1) * m.factorial := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hid : Δ a - Δ (a - Pi.single b 1) =
        (lg W a - lg W (a - Pi.single b 1) -
          L * (geoNum (m + 1) W (Fin.snoc (fun _ k => (a k : ℤ)) (uv b)) : ℝ) / m.factorial) -
        L / ((m + 1).factorial : ℝ) * ((geoNum (m + 1) W (fun _ => x) : ℝ) -
          geoNum (m + 1) W (fun _ => x - uv b) -
          (m + 1) * geoNum (m + 1) W (Fin.snoc (fun _ => x) (uv b))) := by
      simp only [hΔ, appr]
      rw [hx, hfs]
      field_simp
      ring
    have h3 : |L / ((m + 1).factorial : ℝ) * ((geoNum (m + 1) W (fun _ => x) : ℝ) -
          geoNum (m + 1) W (fun _ => x - uv b) -
          (m + 1) * geoNum (m + 1) W (Fin.snoc (fun _ => x) (uv b)))| ≤
        |L| * B * 2 ^ (m - 1) / m.factorial * m * ((tdeg a : ℝ) + 1) ^ (m - 1) := by
      rw [abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((m + 1).factorial : ℝ)), hfs]
      have hN : (0 : ℝ) ≤ tdeg a := by positivity
      have h4 : ((tdeg a : ℝ) + 2) ^ (m + 1 - 2) ≤ 2 ^ (m - 1) * ((tdeg a : ℝ) + 1) ^ (m - 1) := by
        rw [show m + 1 - 2 = m - 1 by omega, ← mul_pow]
        gcongr
        linarith
      calc |L| / ((m + 1) * m.factorial) * |(geoNum (m + 1) W (fun _ => x) : ℝ) -
            geoNum (m + 1) W (fun _ => x - uv b) -
            (m + 1) * geoNum (m + 1) W (Fin.snoc (fun _ => x) (uv b))|
          ≤ |L| / ((m + 1) * m.factorial) * (B * ((m + 1) * m * ((tdeg a : ℝ) + 2) ^ (m + 1 - 2))) := by
            gcongr
        _ ≤ |L| / ((m + 1) * m.factorial) * (B * ((m + 1) * m * (2 ^ (m - 1) *
              ((tdeg a : ℝ) + 1) ^ (m - 1)))) := by
            gcongr
        _ = |L| * B * 2 ^ (m - 1) / m.factorial * m * ((tdeg a : ℝ) + 1) ^ (m - 1) := by
            field_simp
    have hCb : C b ≤ ∑ b, C b := Finset.single_le_sum (f := C) (fun b _ => hC b) (Finset.mem_univ b)
    rw [hid]
    calc _ ≤ |lg W a - lg W (a - Pi.single b 1) -
            L * (geoNum (m + 1) W (Fin.snoc (fun _ k => (a k : ℤ)) (uv b)) : ℝ) / m.factorial| +
          |L / ((m + 1).factorial : ℝ) * ((geoNum (m + 1) W (fun _ => x) : ℝ) -
            geoNum (m + 1) W (fun _ => x - uv b) -
            (m + 1) * geoNum (m + 1) W (Fin.snoc (fun _ => x) (uv b)))| := abs_sub _ _
      _ ≤ C b * m * ((tdeg a : ℝ) + 1) ^ (m - 1) +
          |L| * B * 2 ^ (m - 1) / m.factorial * m * ((tdeg a : ℝ) + 1) ^ (m - 1) := add_le_add h1 h3
      _ ≤ (∑ b, C b) * m * ((tdeg a : ℝ) + 1) ^ (m - 1) +
          |L| * B * 2 ^ (m - 1) / m.factorial * m * ((tdeg a : ℝ) + 1) ^ (m - 1) := by gcongr
      _ = Kst * m * ((tdeg a : ℝ) + 1) ^ (m - 1) := by ring
  have hw := walk_bound Δ a₁ m hKst hstep
  refine ⟨a₁, |Δ (fun _ => a₁)| + Kst * m, by positivity, fun a ha => ?_⟩
  have h := hw a ha
  have hN : (0 : ℝ) ≤ tdeg a := by positivity
  have hp1 : (1 : ℝ) ≤ ((tdeg a : ℝ) + 1) ^ m := one_le_pow₀ (by linarith)
  have hkey : Kst * m * tdeg a * ((tdeg a : ℝ) + 1) ^ (m - 1) ≤ Kst * m * ((tdeg a : ℝ) + 1) ^ m := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp
    · have : ((tdeg a : ℝ) + 1) ^ m = ((tdeg a : ℝ) + 1) ^ (m - 1) * ((tdeg a : ℝ) + 1) := by
        rw [← pow_succ]; congr 1; omega
      rw [this]
      have : (0 : ℝ) ≤ ((tdeg a : ℝ) + 1) ^ (m - 1) := by positivity
      have : (0 : ℝ) ≤ Kst * m := by positivity
      nlinarith
  simp only [Nat.add_sub_cancel]
  push_cast
  have hΔc := abs_nonneg (Δ (fun _ => a₁))
  have hKm : (0 : ℝ) ≤ Kst * m := by positivity
  change |Δ a| ≤ _
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hA : (1 : ℝ) ≤ ((m : ℝ) + 1) * ((tdeg a : ℝ) + 1) ^ m := by nlinarith
  have hB1 : |Δ (fun _ => a₁)| ≤ |Δ (fun _ => a₁)| * (((m : ℝ) + 1) * ((tdeg a : ℝ) + 1) ^ m) :=
    le_mul_of_one_le_right hΔc hA
  have hB2 : Kst * m * ((tdeg a : ℝ) + 1) ^ m ≤
      Kst * m * (((m : ℝ) + 1) * ((tdeg a : ℝ) + 1) ^ m) := by
    have : ((tdeg a : ℝ) + 1) ^ m ≤ ((m : ℝ) + 1) * ((tdeg a : ℝ) + 1) ^ m :=
      le_mul_of_one_le_left (by positivity) (by linarith)
    exact mul_le_mul_of_nonneg_left this hKm
  calc |Δ a| ≤ |Δ (fun _ => a₁)| + Kst * m * ((tdeg a : ℝ) + 1) ^ m := by linarith
    _ ≤ |Δ (fun _ => a₁)| * (((m : ℝ) + 1) * ((tdeg a : ℝ) + 1) ^ m) +
        Kst * m * (((m : ℝ) + 1) * ((tdeg a : ℝ) + 1) ^ m) := by linarith
    _ = (|Δ (fun _ => a₁)| + Kst * m) * ((m : ℝ) + 1) * ((tdeg a : ℝ) + 1) ^ m := by ring

theorem hasymp_all {L : ℝ} {p : ℕ} (hp : p.Prime)
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
    (hbase : ∀ W : Ideal (MRing ι), IsMultiProjPrime W → (p : MRing ι) ∈ W →
      ringKrullDim (MRing ι ⧸ W) = ((0 + Fintype.card K : ℕ) : WithBot ℕ∞) → HAsymp L 0 W) :
    ∀ (d : ℕ) (W : Ideal (MRing ι)), IsMultiProjPrime W → (p : MRing ι) ∈ W →
      ringKrullDim (MRing ι ⧸ W) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) →
      HAsymp L d W ∧ SymmAt d W := by
  intro d
  induction d with
  | zero =>
    intro W hW hpW hdim
    exact ⟨hbase W hW hpW hdim,
      fun a σ => hSymm 0 W a σ hW (charOf_ne_zero_of_mem hp.ne_zero hpW) hdim⟩
  | succ m ih =>
    intro W hW hpW hdim
    have hc := charOf_ne_zero_of_mem hp.ne_zero hpW
    have hS : SymmAt (m + 1) W := fun a σ => hSymm (m + 1) W a σ hW hc hdim
    exact ⟨main_step hp hW hpW hdim (fun a k i hX ha => hR4 m W a k i hW hc hdim hX ha) hS
      (fun W' hW' hpW' hdim' => ih W' hW' hpW' hdim'), hS⟩

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
