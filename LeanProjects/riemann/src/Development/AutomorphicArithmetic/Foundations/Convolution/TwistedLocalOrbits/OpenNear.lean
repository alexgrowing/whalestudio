import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]

private theorem lim_ex (a : ℕ → E) (s : ℕ → ValueGroupWithZero E) (hs : ∀ m, s (m + 1) ≤ s m)
    (ha : ∀ m, valuation E (a (m + 1) - a m) ≤ s m) : ∃ L, ∀ m, valuation E (L - a m) ≤ s m := by
  have hT : T2Space E := by
    let := IsTopologicalAddGroup.rightUniformSpace E
    have := isUniformAddGroup_of_addCommGroup (G := E)
    infer_instance
  let S : ℕ → Set E := fun m => {y | valuation E (y - a m) ≤ s m}
  have hc : ∀ m, IsCompact (S m) := fun m => by
    have h := (IsNonarchimedeanLocalField.isCompact_closedBall E (s m)).image (continuous_add_const (a m))
    convert h using 1
    ext y
    constructor
    · intro hy
      exact ⟨y - a m, hy, by simp⟩
    · rintro ⟨z, hz, rfl⟩
      simpa [S] using hz
  have hn : ∀ m, S (m + 1) ⊆ S m := fun m y hy => by
    have : y - a m = (y - a (m + 1)) + (a (m + 1) - a m) := by ring
    show valuation E (y - a m) ≤ s m
    rw [this]
    exact Valuation.map_add_le _ (le_trans hy (hs m)) (ha m)
  obtain ⟨L, hL⟩ := (hc 0).nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hn
    (fun m => ⟨a m, by simp [S]⟩) (fun m => (hc m).isClosed)
  exact ⟨L, fun m => Set.mem_iInter.mp hL m⟩

private theorem eq_zero_of_le_pow {x c R : ValueGroupWithZero E} (hc : c < 1) (h : ∀ m : ℕ, x ≤ c ^ m * R) :
    x = 0 := by
  by_contra hx
  have hA : MulArchimedean (ValueGroupWithZero E) := ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  have hR : R ≠ 0 := by
    rintro rfl
    exact hx (by simpa using h 0)
  obtain ⟨m, hm⟩ := exists_pow_lt₀ hc (Units.mk0 (x / R) (div_ne_zero hx hR))
  have := h m
  rw [Units.val_mk0, lt_div_iff₀ (zero_lt_iff.mpr hR)] at hm
  exact absurd this (not_le.mpr hm)

private theorem fix_ex {ι κ : Type} (f : Matrix ι κ E → Matrix ι κ E) (c R : ValueGroupWithZero E) (hc : c < 1)
    (hm : ∀ x, (∀ i j, valuation E (x i j) ≤ R) → ∀ i j, valuation E (f x i j) ≤ R)
    (hl : ∀ x y s, (∀ i j, valuation E (x i j) ≤ R) → (∀ i j, valuation E (y i j) ≤ R) →
      (∀ i j, valuation E ((x - y) i j) ≤ s) → ∀ i j, valuation E ((f x - f y) i j) ≤ c * s) :
    ∃ x, (∀ i j, valuation E (x i j) ≤ R) ∧ f x = x := by
  let a : ℕ → Matrix ι κ E := fun m => f^[m] 0
  have hs : ∀ m, a (m + 1) = f (a m) := fun m => Function.iterate_succ_apply' _ _ _
  have h0 : a 0 = 0 := rfl
  have hb : ∀ m i j, valuation E (a m i j) ≤ R := by
    intro m
    induction m with
    | zero => intro i j; simp [h0]
    | succ m ih => rw [hs]; exact hm _ ih
  have hd : ∀ m i j, valuation E ((a (m + 1) - a m) i j) ≤ c ^ m * R := by
    intro m
    induction m with
    | zero => intro i j; simpa [h0] using hb 1 i j
    | succ m ih =>
      intro i j
      have := hl _ _ _ (hb (m + 1)) (hb m) ih i j
      rw [← hs, ← hs] at this
      rwa [pow_succ', mul_assoc]
  have hdec : ∀ m, c ^ (m + 1) * R ≤ c ^ m * R := fun m => by
    rw [pow_succ', mul_assoc]
    exact mul_le_of_le_one_left' hc.le
  choose L hL using fun i j => lim_ex (fun m => a m i j) (fun m => c ^ m * R) hdec (fun m => hd m i j)
  have hLR : ∀ i j, valuation E (L i j) ≤ R := fun i j => by simpa [h0] using hL i j 0
  refine ⟨Matrix.of L, hLR, ?_⟩
  ext i j
  rw [← sub_eq_zero, ← (valuation E).zero_iff]
  refine eq_zero_of_le_pow (R := R) hc fun m => ?_
  have h1 := hl (Matrix.of L) (a m) _ hLR (hb m) (fun i j => hL i j m) i j
  rw [← hs, ← mul_assoc, ← pow_succ'] at h1
  have h2 := hL i j (m + 1)
  have : f (Matrix.of L) i j - Matrix.of L i j = (f (Matrix.of L) - a (m + 1)) i j - (L i j - a (m + 1) i j) := by
    simp
  rw [this]
  exact (Valuation.map_sub_le _ h1 h2).trans (hdec m)

omit [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem lin_ex (σ : E ≃+* E) (q : ℕ) (hi : ∀ x, valuation E (σ x) = valuation E x)
    (ho : ∀ x, σ^[q] x = x) (hq : (q : E) ≠ 0) :
    ∃ t p : E →+ E, (∀ x, σ (t x) = t x) ∧ (∀ x, t x + σ (p x) - p x = x) ∧
      (∀ x, valuation E (t x) ≤ valuation E x / valuation E (q : E)) ∧
      (∀ x, valuation E (p x) ≤ valuation E x / valuation E (q : E)) := by
  have hp : ∀ (j : ℕ) x, (σ ^ j) x = σ^[j] x := fun j x => by
    rw [RingAut.coe_pow]
  have hiv : ∀ (j : ℕ) x, valuation E (σ^[j] x) = valuation E x := fun j x => by
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', hi, ih]
  have hadd : ∀ (j : ℕ) x y, σ^[j] (x + y) = σ^[j] x + σ^[j] y := fun j x y => by
    rw [← hp, ← hp, ← hp, map_add]
  have hn : ∀ j : ℕ, valuation E (j : E) ≤ 1 := fun j => by
    induction j with
    | zero => simp
    | succ j ih => rw [Nat.cast_succ]; exact Valuation.map_add_le _ ih (by simp)
  refine ⟨AddMonoidHom.mk' (fun x => (∑ j ∈ Finset.range q, σ^[j] x) / q) ?_,
    AddMonoidHom.mk' (fun x => (∑ j ∈ Finset.range q, (j : E) * σ^[j] x) / q) ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    simp only [hadd, Finset.sum_add_distrib, add_div]
  · intro x y
    simp only [hadd, mul_add, Finset.sum_add_distrib, add_div]
  · intro x
    simp only [AddMonoidHom.mk'_apply, map_div₀, map_natCast, map_sum]
    congr 1
    have h1 := Finset.sum_range_succ (fun j => σ^[j] x) q
    have h2 := Finset.sum_range_succ' (fun j => σ^[j] x) q
    simp only [Function.iterate_succ_apply', Function.iterate_zero, id, ho] at h1 h2
    exact add_right_cancel (h2.symm.trans h1)
  · intro x
    simp only [AddMonoidHom.mk'_apply, map_div₀, map_natCast, map_sum, map_mul]
    have h1 := Finset.sum_range_succ (fun j => (j : E) * σ^[j] x) q
    have h2 := Finset.sum_range_succ' (fun j => (j : E) * σ^[j] x) q
    have h3 := Finset.sum_range_succ (fun j => σ^[j] x) q
    have h4 := Finset.sum_range_succ' (fun j => σ^[j] x) q
    simp only [Function.iterate_succ_apply', Function.iterate_zero, id, ho, Nat.cast_succ, add_mul, one_mul,
      Finset.sum_add_distrib, Nat.cast_zero, zero_mul, add_zero] at h1 h2 h3 h4
    field_simp
    linear_combination h1 - h2 - h3 + h4
  · intro x
    simp only [AddMonoidHom.mk'_apply, map_div₀]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul' (Valuation.map_sum_le _ fun j _ => (hiv j x).le) le_rfl
  · intro x
    simp only [AddMonoidHom.mk'_apply, map_div₀]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    refine mul_le_mul' (Valuation.map_sum_le _ fun j _ => ?_) le_rfl
    rw [map_mul, hiv]
    exact mul_le_of_le_one_left' (hn j)

end SlopeTestRemainingChoices

section Bd

variable {E : Type} [Field E] [ValuativeRel E] {n : ℕ}

private def Bd (s : ValueGroupWithZero E) (M : Matrix (Fin n) (Fin n) E) : Prop :=
  ∀ i j, valuation E (M i j) ≤ s

variable {s s' : ValueGroupWithZero E} {M N : Matrix (Fin n) (Fin n) E}

private theorem Bd.mono (h : Bd s M) (hs : s ≤ s') : Bd s' M := fun i j => (h i j).trans hs

private theorem Bd.add (h : Bd s M) (h' : Bd s N) : Bd s (M + N) := fun i j =>
  Valuation.map_add_le _ (h i j) (h' i j)

private theorem Bd.sub (h : Bd s M) (h' : Bd s N) : Bd s (M - N) := fun i j =>
  Valuation.map_sub_le _ (h i j) (h' i j)

private theorem Bd.neg (h : Bd s M) : Bd s (-M) := fun i j => by simpa using h i j

private theorem Bd.mul (h : Bd s M) (h' : Bd s' N) : Bd (s * s') (M * N) := fun i j => by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [map_mul]
  exact mul_le_mul' (h i k) (h' k j)

private theorem Bd.mul' (h : Bd s M) (h' : Bd s' N) : Bd (s' * s) (M * N) := mul_comm s s' ▸ h.mul h'

private theorem Bd.mul_one_left (h : Bd 1 M) (h' : Bd s N) : Bd s (M * N) := one_mul s ▸ h.mul h'

private theorem Bd.isUnit [TopologicalSpace E] [IsNonarchimedeanLocalField E] (h : Bd s M) (hs : s < 1) :
    IsUnit (1 + M) := by
  obtain ⟨N, -, hN⟩ := fix_ex (fun N => -M - M * N) s s hs
    (fun x hx => h.neg.sub ((h.mono hs.le).mul_one_left hx))
    (fun x y s' _ _ hd => by
      have : (-M - M * x) - (-M - M * y) = -(M * (x - y)) := by noncomm_ring
      show Bd _ ((-M - M * x) - (-M - M * y))
      rw [this]
      exact (h.mul hd).neg)
  have : (1 + M) * (1 + N) = 1 := by
    have : (1 + M) * (1 + N) = 1 + (N - (-M - M * N)) := by noncomm_ring
    rw [this, hN, sub_self, add_zero]
  exact IsUnit.of_mul_eq_one _ this

end Bd

theorem UpperTheory.ConvolutionTheory.Loc.openNear :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (σ : E ≃+* E) (q : ℕ), Cyc σ q → ∀ r ρ : ValueGroupWithZero E, r < valuation E (q : E) → ρ ≤ r →
      ∀ u₀ ∈ ball n r, sg σ u₀ = u₀ → ∀ g ∈ ball n (ρ * valuation E (q : E)),
        ∃ k ∈ ball n ρ, ∃ u ∈ ball n ρ, sg σ u = u ∧ u₀ * g = k⁻¹ * (u₀ * u) * sg σ k := by
  intro E _ _ _ _ n σ q hC r ρ hr hρ u₀ hu₀ _ g hg
  have hw0 : valuation E (q : E) ≠ 0 := (lt_of_le_of_lt zero_le hr).ne'
  have hq : (q : E) ≠ 0 := by simpa using hw0
  have hn : ∀ j : ℕ, valuation E (j : E) ≤ 1 := fun j => by
    induction j with
    | zero => simp
    | succ j ih => rw [Nat.cast_succ]; exact Valuation.map_add_le _ ih (by simp)
  obtain ⟨t, p, ht, htp, hvt, hvp⟩ := lin_ex σ q hC.isom hC.ord hq
  set w := valuation E (q : E) with hw
  have hw1 : w ≤ 1 := hn q
  have hr1 : r < 1 := hr.trans_le hw1
  obtain ⟨A, hA⟩ : ∃ A, (u₀ : Matrix (Fin n) (Fin n) E) = 1 + A := ⟨u₀ - 1, by abel⟩
  obtain ⟨X, hX⟩ : ∃ X, (g : Matrix (Fin n) (Fin n) E) = 1 + X := ⟨g - 1, by abel⟩
  have bA : Bd r A := fun i j => by simpa [hA] using hu₀ i j
  have bX : Bd (ρ * w) X := fun i j => by simpa [hX] using hg i j
  have hρw : ρ * w ≤ r := (mul_le_of_le_one_right' hw1).trans hρ
  have hrρ : r * ρ ≤ ρ * w := by rw [mul_comm]; exact mul_le_mul' le_rfl hr.le
  have bA1 : Bd 1 A := bA.mono hr1.le
  have bB : Bd r (A + X + A * X) := (bA.add (bX.mono hρw)).add (bA1.mul_one_left (bX.mono hρw))
  let U : Matrix (Fin n) (Fin n) E → Matrix (Fin n) (Fin n) E := fun Y => Y.map t
  let K : Matrix (Fin n) (Fin n) E → Matrix (Fin n) (Fin n) E := fun Y => Y.map p
  let S : Matrix (Fin n) (Fin n) E → Matrix (Fin n) (Fin n) E := fun Y => (Y.map p).map σ
  have hdiv : ∀ {a b : ValueGroupWithZero E}, a ≤ b → a / w ≤ b / w := fun h => by
    rw [div_eq_mul_inv, div_eq_mul_inv]; exact mul_le_mul' h le_rfl
  have bU : ∀ {s Y}, Bd s Y → Bd (s / w) (U Y) := fun h i j => (hvt _).trans (hdiv (h i j))
  have bK : ∀ {s Y}, Bd s Y → Bd (s / w) (K Y) := fun h i j => (hvp _).trans (hdiv (h i j))
  have bS : ∀ {s Y}, Bd s Y → Bd (s / w) (S Y) := fun h i j =>
    (hC.isom _).le.trans ((hvp _).trans (hdiv (h i j)))
  have hcan : ρ * w / w = ρ := mul_div_cancel_right₀ _ hw0
  have bU' : ∀ {Y}, Bd (ρ * w) Y → Bd ρ (U Y) := fun h => hcan ▸ bU h
  have bK' : ∀ {Y}, Bd (ρ * w) Y → Bd ρ (K Y) := fun h => hcan ▸ bK h
  have bS' : ∀ {Y}, Bd (ρ * w) Y → Bd ρ (S Y) := fun h => hcan ▸ bS h
  have sU : ∀ Y Z, U (Y - Z) = U Y - U Z := fun Y Z => by ext i j; simp [U]
  have sK : ∀ Y Z, K (Y - Z) = K Y - K Z := fun Y Z => by ext i j; simp [K]
  have sS : ∀ Y Z, S (Y - Z) = S Y - S Z := fun Y Z => by ext i j; simp [S]
  obtain ⟨Y, bY, hY⟩ := fix_ex
    (fun Y => X + A * X + K Y * (A + X + A * X) - U Y * S Y - A * U Y - A * S Y - A * (U Y * S Y))
    (r / w) (ρ * w) ((div_lt_one₀ (zero_lt_iff.mpr hw0)).mpr hr)
    (fun Y hY => by
      have hUS : Bd (ρ * w) (U Y * S Y) := (((bU' hY).mono hρ).mul (bS' hY)).mono hrρ
      exact (((((bX.add (bA1.mul_one_left bX)).add (((bK' hY).mul' bB).mono hrρ)).sub hUS).sub
        ((bA.mul (bU' hY)).mono hrρ)).sub ((bA.mul (bS' hY)).mono hrρ)).sub (bA1.mul_one_left hUS))
    (fun Y Z s hY hZ hd => by
      have e : r / w * s = r * (s / w) := by rw [div_mul_eq_mul_div, mul_div_assoc]
      have hUS : Bd (r * (s / w)) (U (Y - Z) * S Y + U Z * S (Y - Z)) :=
        ((bU hd).mul' ((bS' hY).mono hρ)).add (((bU' hZ).mono hρ).mul (bS hd))
      have : (X + A * X + K Y * (A + X + A * X) - U Y * S Y - A * U Y - A * S Y - A * (U Y * S Y)) -
          (X + A * X + K Z * (A + X + A * X) - U Z * S Z - A * U Z - A * S Z - A * (U Z * S Z)) =
          K (Y - Z) * (A + X + A * X) - (U (Y - Z) * S Y + U Z * S (Y - Z)) - A * U (Y - Z) - A * S (Y - Z) -
            A * (U (Y - Z) * S Y + U Z * S (Y - Z)) := by
        rw [sU, sK, sS]; noncomm_ring
      show Bd _ ((X + A * X + K Y * (A + X + A * X) - U Y * S Y - A * U Y - A * S Y - A * (U Y * S Y)) -
          (X + A * X + K Z * (A + X + A * X) - U Z * S Z - A * U Z - A * S Z - A * (U Z * S Z)))
      rw [this, e]
      exact (((((bK hd).mul' bB).sub hUS).sub (bA.mul (bU hd))).sub (bA.mul (bS hd))).sub
        (bA1.mul_one_left hUS))
  have hlin : U Y + S Y - K Y = Y := by ext i j; simpa [U, S, K] using htp (Y i j)
  have hρ1 : ρ < 1 := hρ.trans_lt hr1
  obtain ⟨k, hk⟩ := (bK' bY).isUnit hρ1
  obtain ⟨u, hu⟩ := (bU' bY).isUnit hρ1
  have hsg : ∀ x : GL (Fin n) E, ((sg σ x : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
      (x : Matrix (Fin n) (Fin n) E).map σ := fun x => rfl
  have hsk : ((sg σ k : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = 1 + S Y := by
    rw [hsg, hk]; ext i j; simp [S, K, Matrix.one_apply, apply_ite σ]
  refine ⟨k, fun i j => by simpa [hk] using bK' bY i j, u, fun i j => by simpa [hu] using bU' bY i j, ?_, ?_⟩
  · apply Units.ext
    rw [hsg, hu]; ext i j; simp [U, ht, Matrix.one_apply, apply_ite σ]
  · rw [mul_assoc, eq_inv_mul_iff_mul_eq]
    apply Units.ext
    simp only [Units.val_mul, hsk, hk, hu, hA, hX]
    rw [← sub_eq_zero]
    have : (1 + K Y) * ((1 + A) * (1 + X)) - (1 + A) * (1 + U Y) * (1 + S Y) =
        (X + A * X + K Y * (A + X + A * X) - U Y * S Y - A * U Y - A * S Y - A * (U Y * S Y)) -
          (U Y + S Y - K Y) := by noncomm_ring
    rw [this, hlin]
    exact sub_eq_zero.mpr hY
