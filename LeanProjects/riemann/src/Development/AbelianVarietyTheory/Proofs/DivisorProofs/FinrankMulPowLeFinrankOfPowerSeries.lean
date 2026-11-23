import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentOfDistinctValuationLikeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLeCardValuesStatement

open Filter Topology

namespace GlobalTheory
namespace HilbertSamuelPS

open MvPowerSeries

section LexLemmas
variable {D : ℕ}

theorem lexOrder_congr' {g h : MvPowerSeries (Fin D) ℂ}
    (H : ∀ d, coeff d g = 0 ↔ coeff d h = 0) : lexOrder g = lexOrder h :=
  le_antisymm (le_lexOrder_iff.mpr fun d hd => (H d).1 (coeff_eq_zero_of_lt_lexOrder hd))
    (le_lexOrder_iff.mpr fun d hd => (H d).2 (coeff_eq_zero_of_lt_lexOrder hd))

theorem lexOrder_smul' {c : ℂ} (hc : c ≠ 0) (g : MvPowerSeries (Fin D) ℂ) :
    lexOrder (c • g) = lexOrder g :=
  lexOrder_congr' fun d => by simp [hc]

theorem lexOrder_add_of_lt' {g h : MvPowerSeries (Fin D) ℂ} (hlt : lexOrder g < lexOrder h) :
    lexOrder (g + h) = lexOrder g := by
  apply le_antisymm
  · have hg : g ≠ 0 := by rw [ne_eq, ← lexOrder_eq_top_iff_eq_zero]; exact ne_top_of_lt hlt
    obtain ⟨d, hd⟩ := exists_finsupp_eq_lexOrder_of_ne_zero hg
    rw [hd]
    apply lexOrder_le_of_coeff_ne_zero
    rw [map_add, coeff_eq_zero_of_lt_lexOrder (φ := h) (d := d) (by rw [← hd]; exact hlt), add_zero]
    exact coeff_ne_zero_of_lexOrder hd.symm
  · calc lexOrder g = min (lexOrder g) (lexOrder h) := (min_eq_left hlt.le).symm
      _ ≤ _ := min_lexOrder_le

theorem lexOrder_sub_smul' {g h : MvPowerSeries (Fin D) ℂ} (hg : g ≠ 0)
    (heq : lexOrder g = lexOrder h) : ∃ c : ℂ, lexOrder g < lexOrder (g - c • h) := by
  obtain ⟨d, hd⟩ := exists_finsupp_eq_lexOrder_of_ne_zero hg
  have hhd := coeff_ne_zero_of_lexOrder (hd.symm.trans heq)
  refine ⟨coeff d g / coeff d h, lt_of_le_of_ne ?_ ?_⟩
  · rw [le_lexOrder_iff]
    intro d' hd'
    have h1 := coeff_eq_zero_of_lt_lexOrder hd'
    have h2 := coeff_eq_zero_of_lt_lexOrder (heq ▸ hd')
    simp [h1, h2]
  · intro heq2
    apply coeff_ne_zero_of_lexOrder (hd.symm.trans heq2)
    simp [div_mul_cancel₀ _ hhd]

theorem lexOrder_monomial_one' (a : Fin D →₀ ℕ) :
    lexOrder (monomial a (1 : ℂ)) = ((toLex a : Lex (Fin D →₀ ℕ)) : WithTop (Lex (Fin D →₀ ℕ))) := by
  apply le_antisymm
  · apply lexOrder_le_of_coeff_ne_zero; simp
  · rw [le_lexOrder_iff]
    intro d hd
    rw [coeff_monomial, if_neg]
    rintro rfl
    exact lt_irrefl _ (WithTop.coe_lt_coe.mp hd)

theorem lexOrder_one' :
    lexOrder (1 : MvPowerSeries (Fin D) ℂ) = ((toLex (0 : Fin D →₀ ℕ) : Lex (Fin D →₀ ℕ)) : WithTop (Lex (Fin D →₀ ℕ))) := by
  rw [← lexOrder_monomial_one' 0]; simp

theorem lexOrder_pow' {g : MvPowerSeries (Fin D) ℂ} {e : Fin D →₀ ℕ}
    (he : lexOrder g = ((toLex e : Lex (Fin D →₀ ℕ)) : WithTop (Lex (Fin D →₀ ℕ)))) (k : ℕ) :
    lexOrder (g ^ k) = ((toLex (k • e) : Lex (Fin D →₀ ℕ)) : WithTop (Lex (Fin D →₀ ℕ))) := by
  induction k with
  | zero => simpa using lexOrder_one' (D := D)
  | succ k ih => rw [pow_succ, lexOrder_mul, ih, he, succ_nsmul, ← WithTop.coe_add, ← toLex_add]

theorem lexOrder_prod_X_pow' (a : Fin D → ℕ) :
    lexOrder (∏ i, (X i : MvPowerSeries (Fin D) ℂ) ^ a i) =
      ((toLex (∑ i, Finsupp.single i (a i)) : Lex (Fin D →₀ ℕ)) : WithTop (Lex (Fin D →₀ ℕ))) := by
  classical
  suffices ∀ s : Finset (Fin D), lexOrder (∏ i ∈ s, (X i : MvPowerSeries (Fin D) ℂ) ^ a i) =
      ((toLex (∑ i ∈ s, Finsupp.single i (a i)) : Lex (Fin D →₀ ℕ)) : WithTop (Lex (Fin D →₀ ℕ))) from this _
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using lexOrder_one' (D := D)
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, lexOrder_mul, ih, X_pow_eq,
      lexOrder_monomial_one', ← WithTop.coe_add, ← toLex_add]

end LexLemmas

end HilbertSamuelPS
end GlobalTheory

namespace GlobalTheory
namespace HilbertSamuelPS

open MvPowerSeries

section Valuation
variable {D n : ℕ} {A : Type} [CommRing A] [Algebra ℂ A]
  (φ : Fin n → (A →ₐ[ℂ] MvPowerSeries (Fin D) ℂ))

noncomputable def evalAt (k : ℕ) (u : A) : MvPowerSeries (Fin D) ℂ :=
  if h : k < n then φ ⟨k, h⟩ u else 0

theorem evalAt_of_lt {k : ℕ} (h : k < n) (u : A) : evalAt φ k u = φ ⟨k, h⟩ u := dif_pos h
theorem evalAt_of_not_lt {k : ℕ} (h : ¬ k < n) (u : A) : evalAt φ k u = 0 := dif_neg h

theorem evalAt_zero (k : ℕ) : evalAt φ k (0 : A) = 0 := by
  unfold evalAt; split_ifs <;> simp
theorem evalAt_add (k : ℕ) (u v : A) : evalAt φ k (u + v) = evalAt φ k u + evalAt φ k v := by
  unfold evalAt; split_ifs <;> simp
theorem evalAt_sub (k : ℕ) (u v : A) : evalAt φ k (u - v) = evalAt φ k u - evalAt φ k v := by
  unfold evalAt; split_ifs <;> simp
theorem evalAt_smul (k : ℕ) (c : ℂ) (u : A) : evalAt φ k (c • u) = c • evalAt φ k u := by
  unfold evalAt; split_ifs <;> simp
theorem evalAt_mul (k : ℕ) (u v : A) : evalAt φ k (u * v) = evalAt φ k u * evalAt φ k v := by
  unfold evalAt; split_ifs <;> simp
theorem evalAt_pow (k : ℕ) (u : A) {m : ℕ} (hm : m ≠ 0) : evalAt φ k (u ^ m) = evalAt φ k u ^ m := by
  unfold evalAt; split_ifs <;> simp [zero_pow hm]

open Classical in

noncomputable def firstIdx (u : A) : ℕ := if h : ∃ k, evalAt φ k u ≠ 0 then Nat.find h else 0

noncomputable def val (u : A) : Lex (ℕ × WithTop (Lex (Fin D →₀ ℕ))) :=
  toLex (firstIdx φ u, lexOrder (evalAt φ (firstIdx φ u) u))

theorem firstIdx_spec {u : A} (h : ∃ k, evalAt φ k u ≠ 0) :
    evalAt φ (firstIdx φ u) u ≠ 0 ∧ ∀ i < firstIdx φ u, evalAt φ i u = 0 := by
  classical
  unfold firstIdx
  rw [dif_pos h]
  exact ⟨Nat.find_spec h, fun i hi => not_not.mp (Nat.find_min h hi)⟩

theorem firstIdx_eq {u : A} {k : ℕ} (hk : evalAt φ k u ≠ 0) (hlt : ∀ i < k, evalAt φ i u = 0) :
    firstIdx φ u = k := by
  classical
  have h : ∃ k, evalAt φ k u ≠ 0 := ⟨k, hk⟩
  unfold firstIdx
  rw [dif_pos h, Nat.find_eq_iff]
  exact ⟨hk, fun i hi => not_not.mpr (hlt i hi)⟩

theorem val_eq {u : A} {k : ℕ} (hk : evalAt φ k u ≠ 0) (hlt : ∀ i < k, evalAt φ i u = 0) :
    val φ u = toLex (k, lexOrder (evalAt φ k u)) := by
  unfold val; rw [firstIdx_eq φ hk hlt]

variable {φ}

theorem exists_evalAt_ne_zero (hinj : ∀ u : A, (∀ j, φ j u = 0) → u = 0) {u : A} (hu : u ≠ 0) :
    ∃ k, evalAt φ k u ≠ 0 := by
  by_contra h
  push_neg at h
  exact hu (hinj u fun j => by simpa [evalAt_of_lt φ j.2] using h j)

theorem val_smul (c : ℂ) (u : A) (hc : c ≠ 0) : val φ (c • u) = val φ u := by
  by_cases h : ∃ k, evalAt φ k u ≠ 0
  · obtain ⟨h1, h2⟩ := firstIdx_spec φ h
    rw [val_eq φ (k := firstIdx φ u) (by rw [evalAt_smul]; exact smul_ne_zero hc h1)
      (fun i hi => by rw [evalAt_smul, h2 i hi, smul_zero]), evalAt_smul, lexOrder_smul' hc]
    rfl
  · push_neg at h
    have : ∀ k, evalAt φ k (c • u) = evalAt φ k u := fun k => by rw [evalAt_smul, h, smul_zero]
    have h' : ¬ ∃ k, evalAt φ k (c • u) ≠ 0 := by simpa [this] using h
    have h'' : ¬ ∃ k, evalAt φ k u ≠ 0 := by simpa using h
    unfold val firstIdx
    rw [dif_neg h', dif_neg h'', this]

theorem val_add (hinj : ∀ u : A, (∀ j, φ j u = 0) → u = 0) (u v : A) (hu : u ≠ 0) (hv : v ≠ 0)
    (hlt : val φ u < val φ v) : u + v ≠ 0 ∧ val φ (u + v) = val φ u := by
  obtain ⟨hu1, hu2⟩ := firstIdx_spec φ (exists_evalAt_ne_zero hinj hu)
  obtain ⟨hv1, hv2⟩ := firstIdx_spec φ (exists_evalAt_ne_zero hinj hv)
  unfold val at hlt
  rw [Prod.Lex.toLex_lt_toLex] at hlt
  rcases hlt with hlt | ⟨heq, hlt⟩
  · dsimp only at hlt
    have e1 : evalAt φ (firstIdx φ u) (u + v) = evalAt φ (firstIdx φ u) u := by
      rw [evalAt_add, hv2 _ hlt, add_zero]
    have e2 : ∀ i < firstIdx φ u, evalAt φ i (u + v) = 0 := fun i hi => by
      rw [evalAt_add, hu2 i hi, hv2 i (hi.trans hlt), add_zero]
    refine ⟨fun h0 => hu1 (by rw [← e1, h0, evalAt_zero]), ?_⟩
    rw [val_eq φ (by rw [e1]; exact hu1) e2, e1]; rfl
  · dsimp only at heq hlt
    rw [← heq] at hlt
    have e1 : lexOrder (evalAt φ (firstIdx φ u) (u + v)) = lexOrder (evalAt φ (firstIdx φ u) u) := by
      rw [evalAt_add, lexOrder_add_of_lt' hlt]
    have hne : evalAt φ (firstIdx φ u) (u + v) ≠ 0 := by
      rw [ne_eq, ← lexOrder_eq_top_iff_eq_zero, e1, lexOrder_eq_top_iff_eq_zero]; exact hu1
    have e2 : ∀ i < firstIdx φ u, evalAt φ i (u + v) = 0 := fun i hi => by
      rw [evalAt_add, hu2 i hi, hv2 i (heq ▸ hi), add_zero]
    refine ⟨fun h0 => hne (by rw [h0, evalAt_zero]), ?_⟩
    rw [val_eq φ hne e2, e1]; rfl

theorem val_sub (hinj : ∀ u : A, (∀ j, φ j u = 0) → u = 0) (u v : A) (hu : u ≠ 0) (hv : v ≠ 0)
    (heq : val φ u = val φ v) : ∃ c : ℂ, u - c • v = 0 ∨ val φ u < val φ (u - c • v) := by
  obtain ⟨hu1, hu2⟩ := firstIdx_spec φ (exists_evalAt_ne_zero hinj hu)
  obtain ⟨hv1, hv2⟩ := firstIdx_spec φ (exists_evalAt_ne_zero hinj hv)
  unfold val at heq
  have hk : firstIdx φ u = firstIdx φ v := congrArg (fun p => (ofLex p).1) heq
  have hl : lexOrder (evalAt φ (firstIdx φ u) u) = lexOrder (evalAt φ (firstIdx φ u) v) := by
    have := congrArg (fun p => (ofLex p).2) heq
    simp only [ofLex_toLex] at this
    rw [this, hk]
  obtain ⟨c, hc⟩ := lexOrder_sub_smul' hu1 hl
  refine ⟨c, ?_⟩
  by_cases hw : u - c • v = 0
  · exact Or.inl hw
  right
  set k := firstIdx φ u with hkdef
  have e2 : ∀ i < k, evalAt φ i (u - c • v) = 0 := fun i hi => by
    rw [evalAt_sub, evalAt_smul, hu2 i hi, hv2 i (hk ▸ hi), smul_zero, sub_zero]
  have e1 : evalAt φ k (u - c • v) = evalAt φ k u - c • evalAt φ k v := by
    rw [evalAt_sub, evalAt_smul]
  obtain ⟨hw1, hw2⟩ := firstIdx_spec φ (exists_evalAt_ne_zero hinj hw)
  have hge : k ≤ firstIdx φ (u - c • v) := by
    by_contra hlt; push_neg at hlt
    exact hw1 (e2 _ hlt)
  by_cases hz : evalAt φ k (u - c • v) = 0
  · have hlt : k < firstIdx φ (u - c • v) := lt_of_le_of_ne hge (fun h => hw1 (h ▸ hz))
    unfold val
    rw [Prod.Lex.toLex_lt_toLex]
    exact Or.inl hlt
  · rw [val_eq φ hz e2]
    unfold val
    rw [Prod.Lex.toLex_lt_toLex]
    exact Or.inr ⟨rfl, by rw [e1]; exact hc⟩

end Valuation

end HilbertSamuelPS
end GlobalTheory

namespace GlobalTheory
namespace HilbertSamuelPS

open MvPowerSeries

theorem expand_mem {D : ℕ} {A : Type} [CommRing A] [Algebra ℂ A] (x : Fin D → A) (c : Fin D → ℂ)
    (F G : Submodule ℂ A) (m : ℕ)
    (hG : ∀ (f : Fin m → A) (a : Fin D → ℕ), (∀ l, f l ∈ F) → (∀ i, a i < m) →
      (∏ l, f l) * ∏ i, x i ^ a i ∈ G)
    (g : A) (hg : g ∈ F) (a : Fin D → ℕ) (ha : ∀ d, a d < m) :
    g ^ m * ∏ d, (x d - algebraMap ℂ A (c d)) ^ a d ∈ G := by
  have key : ∀ b : Fin D → ℕ, (∀ d, b d < m) → g ^ m * ∏ d, x d ^ b d ∈ G := fun b hb => by
    simpa [Finset.prod_const] using hG (fun _ => g) b (fun _ => hg) hb
  have hexp : ∀ d, (x d - algebraMap ℂ A (c d)) ^ a d = ∑ j ∈ Finset.range (a d + 1),
      ((-c d) ^ (a d - j) * ((a d).choose j : ℂ)) • x d ^ j := by
    intro d
    rw [sub_eq_add_neg, add_pow]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def]
    simp only [map_mul, map_pow, map_neg, map_natCast]
    ring
  simp_rw [hexp]
  rw [Finset.prod_univ_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun b hb => ?_
  rw [Fintype.mem_piFinset] at hb
  have hb' : ∀ d, b d < m := fun d =>
    lt_of_le_of_lt (Nat.lt_succ_iff.mp (Finset.mem_range.mp (hb d))) (ha d)
  have : ∏ d, ((-c d) ^ (a d - b d) * ((a d).choose (b d) : ℂ)) • x d ^ b d =
      (∏ d, ((-c d) ^ (a d - b d) * ((a d).choose (b d) : ℂ))) • ∏ d, x d ^ b d := by
    simp only [Algebra.smul_def, Finset.prod_mul_distrib, map_prod, map_mul]
  rw [this, mul_smul_comm]
  exact G.smul_mem _ (key b hb')

theorem nat_mul_add_inj {m x y x' y' : ℕ} (hy : y < m) (hy' : y' < m)
    (h : m * x + y = m * x' + y') : x = x' ∧ y = y' := by
  have hm : 0 < m := by omega
  have e1 : (m * x + y) / m = x := by rw [Nat.mul_add_div hm, Nat.div_eq_of_lt hy, add_zero]
  have e2 : (m * x' + y') / m = x' := by rw [Nat.mul_add_div hm, Nat.div_eq_of_lt hy', add_zero]
  have hx : x = x' := by rw [← e1, h, e2]
  subst hx
  exact ⟨rfl, by omega⟩

theorem finsupp_coord {D : ℕ} (e : Fin D →₀ ℕ) (a : Fin D → ℕ) (m : ℕ) (d : Fin D) :
    (m • e + ∑ d', Finsupp.single d' (a d')) d = m * e d + a d := by
  simp [Finsupp.single_apply]

section Vectors
variable {D n : ℕ} {A : Type} [CommRing A] [Algebra ℂ A]
  {φ : Fin n → (A →ₐ[ℂ] MvPowerSeries (Fin D) ℂ)} {x : Fin D → A} {c : Fin D → ℂ}

theorem vector_val (hx : ∀ j i, φ j (x i) = MvPowerSeries.X i + MvPowerSeries.C (c i))
    {m : ℕ} (hm : m ≠ 0) {b : A} (hb : ∃ k, evalAt φ k b ≠ 0) {e : Fin D →₀ ℕ}
    (he : lexOrder (evalAt φ (firstIdx φ b) b) = ((toLex e : Lex (Fin D →₀ ℕ)) : WithTop (Lex (Fin D →₀ ℕ))))
    (a : Fin D → ℕ) :
    b ^ m * ∏ d, (x d - algebraMap ℂ A (c d)) ^ a d ≠ 0 ∧
    val φ (b ^ m * ∏ d, (x d - algebraMap ℂ A (c d)) ^ a d) =
      toLex (firstIdx φ b, ((toLex (m • e + ∑ d, Finsupp.single d (a d)) : Lex (Fin D →₀ ℕ)) :
        WithTop (Lex (Fin D →₀ ℕ)))) := by
  obtain ⟨hb1, hb2⟩ := firstIdx_spec φ hb
  set k := firstIdx φ b
  have hkn : k < n := by
    by_contra h; exact hb1 (evalAt_of_not_lt φ h b)
  have hP : evalAt φ k (∏ d, (x d - algebraMap ℂ A (c d)) ^ a d) = ∏ d, (X d : MvPowerSeries (Fin D) ℂ) ^ a d := by
    rw [evalAt_of_lt φ hkn]
    simp [map_prod, hx, MvPowerSeries.algebraMap_apply]
  set w := b ^ m * ∏ d, (x d - algebraMap ℂ A (c d)) ^ a d with hw
  have hwk : evalAt φ k w = evalAt φ k b ^ m * ∏ d, (X d : MvPowerSeries (Fin D) ℂ) ^ a d := by
    rw [hw, evalAt_mul, evalAt_pow φ _ _ hm, hP]
  have hlex : lexOrder (evalAt φ k w) = ((toLex (m • e + ∑ d, Finsupp.single d (a d)) : Lex (Fin D →₀ ℕ)) :
        WithTop (Lex (Fin D →₀ ℕ))) := by
    rw [hwk, lexOrder_mul, lexOrder_pow' he, lexOrder_prod_X_pow', ← WithTop.coe_add, ← toLex_add]
  have hne : evalAt φ k w ≠ 0 := by
    rw [ne_eq, ← lexOrder_eq_top_iff_eq_zero, hlex]; exact WithTop.coe_ne_top
  have hlt : ∀ i < k, evalAt φ i w = 0 := by
    intro i hi
    rw [hw, evalAt_mul, evalAt_pow φ _ _ hm, hb2 i hi, zero_pow hm, zero_mul]
  refine ⟨fun h0 => hne (by rw [h0, evalAt_zero]), ?_⟩
  rw [val_eq φ hne hlt, hlex]

end Vectors

end HilbertSamuelPS

open HilbertSamuelPS MvPowerSeries in

theorem finrank_mul_pow_le_finrank_of_powerSeries :
    ∀ (D n : ℕ) (A : Type) [CommRing A] [Algebra ℂ A] (φ : Fin n → (A →ₐ[ℂ] MvPowerSeries (Fin D) ℂ)) (x : Fin D → A) (c : Fin D → ℂ), (∀ u : A, (∀ j, φ j u = 0) → u = 0) → (∀ j i, φ j (x i) = MvPowerSeries.X i + MvPowerSeries.C (c i)) → ∀ (F G : Submodule ℂ A) [Module.Finite ℂ F] [Module.Finite ℂ G] (m : ℕ), 0 < m → (∀ (f : Fin m → A) (a : Fin D → ℕ), (∀ l, f l ∈ F) → (∀ i, a i < m) → (∏ l, f l) * ∏ i, x i ^ a i ∈ G) → Module.finrank ℂ F * m ^ D ≤ Module.finrank ℂ G := by
  intro D n A _ _ φ x c hinj hx F G _ _ m hm hG
  classical
  have h1 : ∀ (c : ℂ) (u : A), c ≠ 0 → val φ (c • u) = val φ u := fun c u hc => val_smul c u hc
  have h2 := val_add hinj
  have h3 := val_sub hinj
  obtain ⟨b, hbF, hbinj⟩ := GlobalTheory.T.exists_injective_values_on_finrank_family ℂ A _ (val φ) h1 h2 h3 F
  have hbne : ∀ i, ∃ k, evalAt φ k (b i) ≠ 0 := fun i => exists_evalAt_ne_zero hinj (hbF i).2
  have hex : ∀ i, ∃ e : Fin D →₀ ℕ, lexOrder (evalAt φ (firstIdx φ (b i)) (b i)) =
      ((toLex e : Lex (Fin D →₀ ℕ)) : WithTop (Lex (Fin D →₀ ℕ))) :=
    fun i => exists_finsupp_eq_lexOrder_of_ne_zero (firstIdx_spec φ (hbne i)).1
  choose e he using hex
  let w : Fin (Module.finrank ℂ F) × (Fin D → Fin m) → A := fun p =>
    b p.1 ^ m * ∏ d, (x d - algebraMap ℂ A (c d)) ^ ((p.2 d : ℕ))
  have hwv := fun p : Fin (Module.finrank ℂ F) × (Fin D → Fin m) =>
    vector_val (φ := φ) hx hm.ne' (hbne p.1) (he p.1) (fun d => (p.2 d : ℕ))
  have hwinj : Function.Injective (fun p => val φ (w p)) := by
    rintro ⟨i, a⟩ ⟨i', a'⟩ h
    have e1 := (hwv (i, a)).2
    have e2 := (hwv (i', a')).2
    have h'' := e1.symm.trans (h.trans e2)
    have h' := congrArg ofLex h''
    simp only [ofLex_toLex, Prod.mk.injEq, WithTop.coe_inj, toLex_inj] at h'
    obtain ⟨hk, hs⟩ := h'
    have hcoord : ∀ d, e i d = e i' d ∧ (a d : ℕ) = a' d := fun d => by
      have := congrArg (fun f : Fin D →₀ ℕ => f d) hs
      simp only [finsupp_coord] at this
      exact nat_mul_add_inj (a d).2 (a' d).2 this
    have hee : e i = e i' := Finsupp.ext fun d => (hcoord d).1
    have hii : i = i' := hbinj (by
      show toLex (firstIdx φ (b i), lexOrder (evalAt φ (firstIdx φ (b i)) (b i))) =
        toLex (firstIdx φ (b i'), lexOrder (evalAt φ (firstIdx φ (b i')) (b i')))
      rw [he i, he i', hk, hee])
    subst hii
    have haa : a = a' := funext fun d => Fin.ext (hcoord d).2
    rw [haa]
  have hli : LinearIndependent ℂ w :=
    GlobalTheory.T.linearIndependent_of_injective_valuationLike ℂ A _ _ (val φ) h1 h2 w (fun p => (hwv p).1) hwinj
  have hwG : ∀ p, w p ∈ G := fun p =>
    expand_mem x c F G m hG (b p.1) (hbF p.1).1 (fun d => (p.2 d : ℕ)) (fun d => (p.2 d).2)
  let wG : Fin (Module.finrank ℂ F) × (Fin D → Fin m) → G := fun p => ⟨w p, hwG p⟩
  have hliG : LinearIndependent ℂ wG := LinearIndependent.of_comp G.subtype hli
  have := hliG.fintype_card_le_finrank
  simpa [Fintype.card_prod, Fintype.card_fun] using this

end GlobalTheory
