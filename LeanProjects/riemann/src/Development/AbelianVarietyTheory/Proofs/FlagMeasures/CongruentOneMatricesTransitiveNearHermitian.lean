import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.CongTrans

open GlobalTheory.UnramOrder

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

section Mat

variable (L : LocE F E) {m : ℕ}

theorem int_add {A B : Matrix (Fin m) (Fin m) E} (hA : IsIntM L A) (hB : IsIntM L B) :
    IsIntM L (A + B) := fun i j => L.O.add_mem (hA i j) (hB i j)

theorem int_sub {A B : Matrix (Fin m) (Fin m) E} (hA : IsIntM L A) (hB : IsIntM L B) :
    IsIntM L (A - B) := fun i j => L.O.sub_mem (hA i j) (hB i j)

theorem int_neg {A : Matrix (Fin m) (Fin m) E} (hA : IsIntM L A) :
    IsIntM L (-A) := fun i j => L.O.neg_mem (hA i j)

theorem int_smul {c : E} {A : Matrix (Fin m) (Fin m) E} (hc : c ∈ L.O) (hA : IsIntM L A) :
    IsIntM L (c • A) := fun i j => L.O.mul_mem hc (hA i j)

theorem int_mul {A B : Matrix (Fin m) (Fin m) E} (hA : IsIntM L A) (hB : IsIntM L B) :
    IsIntM L (A * B) := fun i j => by
  rw [Matrix.mul_apply]
  exact L.O.sum_mem fun k _ => L.O.mul_mem (hA i k) (hB k j)

theorem int_one : IsIntM L (1 : Matrix (Fin m) (Fin m) E) := fun i j => by
  rw [Matrix.one_apply]
  split_ifs
  · exact L.O.one_mem
  · exact L.O.zero_mem

theorem int_cT {A : Matrix (Fin m) (Fin m) E} (hA : IsIntM L A) : IsIntM L (cT L A) :=
  fun i j => cj_mem L (hA j i)

theorem cT_add (A B : Matrix (Fin m) (Fin m) E) : cT L (A + B) = cT L A + cT L B := by
  ext a b; simp [cT]

theorem cT_sub (A B : Matrix (Fin m) (Fin m) E) : cT L (A - B) = cT L A - cT L B := by
  ext a b; simp [cT]

theorem cT_smul (c : E) (A : Matrix (Fin m) (Fin m) E) : cT L (c • A) = L.cj c • cT L A := by
  ext a b; simp [cT]

theorem cT_mul (A B : Matrix (Fin m) (Fin m) E) : cT L (A * B) = cT L B * cT L A := by
  ext a b; simp [cT, Matrix.mul_apply, mul_comm]

theorem cT_cT (A : Matrix (Fin m) (Fin m) E) : cT L (cT L A) = A := by
  ext a b; simp [cT, L.cj_cj]

theorem cT_one : cT L (1 : Matrix (Fin m) (Fin m) E) = 1 := by
  ext a b
  by_cases h : a = b
  · subst h; simp [cT]
  · simp [cT, Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]

theorem mem_congK_iff (ϖ : 𝒪[F]) (i : ℕ) (A : Matrix (Fin m) (Fin m) E) :
    A ∈ congK L ϖ m i ↔ ∃ N, IsIntM L N ∧ A = 1 + algebraMap F E ϖ ^ i • N := by
  constructor
  · intro h
    choose c hc hc' using h
    refine ⟨Matrix.of c, hc, ?_⟩
    ext a b
    have := hc' a b
    rw [map_pow] at this
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    linear_combination this
  · rintro ⟨N, hN, rfl⟩ a b
    exact ⟨N a b, hN a b, by simp⟩

end Mat

variable [IsNonarchimedeanLocalField F]

theorem isAdicComplete_int : IsAdicComplete (IsLocalRing.maximalIdeal 𝒪[F]) 𝒪[F] := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  infer_instance

theorem series_int {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (a : ℕ → 𝒪[F]) :
    ∃ l : 𝒪[F], ∀ n, ∃ w, l = ∑ k ∈ Finset.range n, ϖ ^ k * a k + ϖ ^ n * w := by
  have hc := isAdicComplete_int (F := F)
  rw [hϖ.maximalIdeal_eq] at hc
  have key : ∀ (n : ℕ) (x y : 𝒪[F]),
      x ≡ y [SMOD (Ideal.span {ϖ} ^ n • ⊤ : Submodule 𝒪[F] 𝒪[F])] ↔ ϖ ^ n ∣ x - y := by
    intro n x y
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
  obtain ⟨l, hl⟩ := hc.toIsPrecomplete.prec (f := fun n => ∑ k ∈ Finset.range n, ϖ ^ k * a k) (by
    intro m n hmn
    rw [key, ← dvd_neg, neg_sub, ← Finset.sum_Ico_eq_sub _ hmn]
    exact Finset.dvd_sum fun k hk =>
      (pow_dvd_pow _ (Finset.mem_Ico.1 hk).1).mul_right _)
  refine ⟨l, fun n => ?_⟩
  obtain ⟨w, hw⟩ := (key _ _ _).1 (hl n)
  exact ⟨-w, by linear_combination -hw⟩

theorem eq_zero_int {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (x : 𝒪[F]) (h : ∀ n, ϖ ^ n ∣ x) : x = 0 := by
  have hc := isAdicComplete_int (F := F)
  rw [hϖ.maximalIdeal_eq] at hc
  refine hc.toIsHausdorff.haus x fun n => ?_
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, sub_zero]
  exact h n

variable [CharZero F] (L : LocE F E)

theorem series_ord {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (a : ℕ → E) (ha : ∀ k, a k ∈ L.O) :
    ∃ l : E, ∀ n, ∃ w ∈ L.O,
      l = ∑ k ∈ Finset.range n, algebraMap F E ϖ ^ k * a k + algebraMap F E ϖ ^ n * w := by
  obtain ⟨ω, hω, e, he, hωe⟩ := exists_sub_cj_mul_eq_one L
  have hint : ∀ a : 𝒪[F], algebraMap F E a ∈ L.O := fun a => (algebraMap_mem_iff L a).2 a.2
  have hco : ∀ x ∈ L.O, ∃ s r : 𝒪[F], x = (algebraMap F E s * ω - algebraMap F E r) * e := by
    intro x hx
    obtain ⟨s, hs⟩ := exists_trace L hx
    obtain ⟨r, hr⟩ := exists_trace L (L.O.mul_mem hx (cj_mem L hω))
    simp only [map_mul, L.cj_cj] at hr
    refine ⟨s, r, ?_⟩
    rw [← hs, ← hr]
    linear_combination (-x) * hωe
  choose s r hsr using fun k => hco (a k) (ha k)
  obtain ⟨l₁, h₁⟩ := series_int hϖ s
  obtain ⟨l₂, h₂⟩ := series_int hϖ r
  refine ⟨(algebraMap F E l₁ * ω - algebraMap F E l₂) * e, fun n => ?_⟩
  obtain ⟨w₁, hw₁⟩ := h₁ n
  obtain ⟨w₂, hw₂⟩ := h₂ n
  refine ⟨(algebraMap F E w₁ * ω - algebraMap F E w₂) * e,
    L.O.mul_mem (L.O.sub_mem (L.O.mul_mem (hint _) hω) (hint _)) he, ?_⟩
  have e1 : ∑ k ∈ Finset.range n, algebraMap F E ϖ ^ k * a k
      = ((∑ k ∈ Finset.range n, algebraMap F E ϖ ^ k * algebraMap F E (s k)) * ω
        - ∑ k ∈ Finset.range n, algebraMap F E ϖ ^ k * algebraMap F E (r k)) * e := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hsr k]; ring
  rw [e1, hw₁, hw₂]
  push_cast
  ring

theorem eq_zero_ord {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (x : E)
    (h : ∀ n, ∃ w ∈ L.O, x = algebraMap F E ϖ ^ n * w) : x = 0 := by
  obtain ⟨ω, hω, e, he, hωe⟩ := exists_sub_cj_mul_eq_one L
  have hx : x ∈ L.O := by
    obtain ⟨w, hw, rfl⟩ := h 0
    simpa using hw
  have tr : ∀ b ∈ L.O, x * b + L.cj (x * b) = 0 := by
    intro b hb
    obtain ⟨t, ht⟩ := exists_trace L (L.O.mul_mem hx hb)
    have : t = 0 := eq_zero_int hϖ t fun n => by
      obtain ⟨w, hw, hxw⟩ := h n
      obtain ⟨u, hu⟩ := exists_trace L (L.O.mul_mem hw hb)
      refine ⟨u, Subtype.ext (algebraMap_inj L ?_)⟩
      rw [← ht, Subring.coe_mul, Subring.coe_pow, map_mul (algebraMap F E), map_pow, ← hu, hxw]
      simp only [map_mul, map_pow, AlgEquiv.commutes]
      ring
    rw [ht, this]; simp
  have h1 := tr 1 L.O.one_mem
  have h2 := tr _ (cj_mem L hω)
  simp only [map_mul, L.cj_cj, mul_one] at h1 h2
  linear_combination (-x) * hωe + e * ω * h1 - e * h2

theorem exists_fixed {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {m : ℕ}
    (T : Matrix (Fin m) (Fin m) E → Matrix (Fin m) (Fin m) E)
    (h0 : ∀ Y, IsIntM L Y → IsIntM L (T Y))
    (hT : ∀ (n : ℕ) Y W, IsIntM L Y → IsIntM L W → ∃ W', IsIntM L W' ∧
      T (Y + algebraMap F E ϖ ^ n • W) = T Y + algebraMap F E ϖ ^ (n + 1) • W') :
    ∃ Z, IsIntM L Z ∧ T Z = Z := by
  have hp : algebraMap F E ϖ ∈ L.O := (algebraMap_mem_iff L _).2 ϖ.2
  set p := algebraMap F E ϖ with hpdef
  let f : ℕ → Matrix (Fin m) (Fin m) E := fun n => T^[n] 0
  have hf : ∀ n, f (n + 1) = T (f n) := fun n => Function.iterate_succ_apply' T n 0
  have hfi : ∀ n, IsIntM L (f n) := by
    intro n
    induction n with
    | zero => exact fun _ _ => L.O.zero_mem
    | succ n ih => rw [hf]; exact h0 _ ih
  have hW : ∀ n, ∃ W, IsIntM L W ∧ f (n + 1) = f n + p ^ n • W := by
    intro n
    induction n with
    | zero => exact ⟨f 1 - f 0, int_sub L (hfi _) (hfi _), by simp⟩
    | succ n ih =>
      obtain ⟨W, hW, h⟩ := ih
      obtain ⟨W', hW', h'⟩ := hT n (f n) W (hfi n) hW
      exact ⟨W', hW', by rw [hf (n + 1), h, h', ← hf, h]⟩
  choose W hWi hW using hW
  have hsum : ∀ n a b, f n a b = ∑ k ∈ Finset.range n, p ^ k * W k a b := by
    intro n a b
    induction n with
    | zero => simp [f]
    | succ n ih => rw [hW, Finset.sum_range_succ, ← ih]; simp
  choose Z hZ using fun a b => series_ord L hϖ (fun k => W k a b) (fun k => hWi k a b)
  have hZ' : ∀ n, ∃ V, IsIntM L V ∧ Matrix.of Z = f n + p ^ n • V := by
    intro n
    choose V hV hV' using fun a b => hZ a b n
    refine ⟨Matrix.of V, hV, ?_⟩
    ext a b
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [hsum]; exact hV' a b
  refine ⟨Matrix.of Z, ?_, ?_⟩
  · obtain ⟨V, hV, h⟩ := hZ' 0
    rw [h]
    exact int_add L (hfi _) (int_smul L (L.O.pow_mem hp _) hV)
  · rw [← sub_eq_zero]
    ext a b
    refine eq_zero_ord L hϖ _ fun n => ?_
    obtain ⟨V, hV, h⟩ := hZ' n
    obtain ⟨V', hV', h'⟩ := hZ' (n + 1)
    obtain ⟨U, hU, hU'⟩ := hT n (f n) V (hfi n) hV
    refine ⟨p * (U a b - V' a b), L.O.mul_mem hp (L.O.sub_mem (hU a b) (hV' a b)), ?_⟩
    rw [← h, ← hf] at hU'
    rw [hU', h']
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring

theorem exists_inv {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {m i : ℕ} (hi : 1 ≤ i)
    {A : Matrix (Fin m) (Fin m) E} (hA : A ∈ congK L ϖ m i) :
    ∃ B, IsIntM L B ∧ A * B = 1 := by
  have hp : algebraMap F E ϖ ∈ L.O := (algebraMap_mem_iff L _).2 ϖ.2
  obtain ⟨N, hN, rfl⟩ := (mem_congK_iff L ϖ i A).1 hA
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hi
  obtain ⟨B, hB, h⟩ := exists_fixed L hϖ (fun B => 1 - algebraMap F E ϖ ^ (1 + i) • (N * B))
    (fun Y hY => int_sub L (int_one L) (int_smul L (L.O.pow_mem hp _) (int_mul L hN hY)))
    (fun n Y W hY hW => ⟨-(algebraMap F E ϖ ^ i • (N * W)),
      int_neg L (int_smul L (L.O.pow_mem hp _) (int_mul L hN hW)), by
        simp only [Matrix.mul_add, Matrix.mul_smul]
        module⟩)
  refine ⟨B, hB, ?_⟩
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]
  exact eq_sub_iff_add_eq.1 h.symm

theorem exists_solution {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {m i : ℕ} (hi : 1 ≤ i)
    {G D : Matrix (Fin m) (Fin m) E} (hG : IsHerm L G) (hGi : IsIntM L G) (hD : IsHerm L D)
    (hDi : IsIntM L D) :
    ∃ Z, IsIntM L Z ∧ Z + cT L Z + algebraMap F E ϖ ^ i • (cT L Z * G * Z) = D := by
  have hp : algebraMap F E ϖ ∈ L.O := (algebraMap_mem_iff L _).2 ϖ.2
  obtain ⟨τ, hτ, hτ1⟩ := (order_facts L ϖ hϖ).1 1
  have hτ2 : L.cj τ = 1 - τ := by
    have : algebraMap F E ((1 : 𝒪[F]) : F) = 1 := by simp
    rw [this] at hτ1
    linear_combination hτ1
  have hcp : ∀ n : ℕ, L.cj (algebraMap F E ϖ ^ n) = algebraMap F E ϖ ^ n := fun n => by
    rw [map_pow, AlgEquiv.commutes]
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hi
  obtain ⟨Z, hZ, h⟩ := exists_fixed L hϖ
    (fun Z => τ • (D - algebraMap F E ϖ ^ (1 + i) • (cT L Z * G * Z)))
    (fun Y hY => int_smul L hτ (int_sub L hDi (int_smul L (L.O.pow_mem hp _)
      (int_mul L (int_mul L (int_cT L hY) hGi) hY))))
    (fun n Y W hY hW => ⟨-(τ • algebraMap F E ϖ ^ i • (cT L W * G * Y + cT L Y * G * W
        + algebraMap F E ϖ ^ n • (cT L W * G * W))),
      int_neg L (int_smul L hτ (int_smul L (L.O.pow_mem hp _) (int_add L (int_add L
        (int_mul L (int_mul L (int_cT L hW) hGi) hY) (int_mul L (int_mul L (int_cT L hY) hGi) hW))
        (int_smul L (L.O.pow_mem hp _) (int_mul L (int_mul L (int_cT L hW) hGi) hW))))), by
        simp only [cT_add, cT_smul, hcp, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
          Matrix.smul_mul]
        module⟩)
  refine ⟨Z, hZ, ?_⟩
  have h' := congrArg (cT L) h
  simp only [cT_smul, cT_sub, cT_mul, cT_cT, hcp, hτ2] at h'
  rw [show cT L D = D from hD, show cT L G = G from hG, ← Matrix.mul_assoc] at h'
  set Q := cT L Z * G * Z
  rw [← h', ← h]
  module

omit [CharZero F] in

theorem exists_pow_mul_mem {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (x : E) :
    ∃ c : ℕ, algebraMap F E ϖ ^ c * x ∈ L.O := by
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; omega)
  have hal : IsAlgebraic 𝒪[F] x :=
    (IsFractionRing.isAlgebraic_iff 𝒪[F] F E).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨y, hy0, hy⟩ := hal.exists_integral_multiple
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hϖ
  refine ⟨k, (L.O_def _).2 ?_⟩
  have := hy.smul ((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F])
  rw [smul_smul, ← mul_assoc, Units.inv_mul, one_mul, Algebra.smul_def, map_pow] at this
  exact this

end GlobalTheory.CongTrans

open GlobalTheory.CongTrans GlobalTheory.UnramOrder in

theorem GlobalTheory.CongTrans.congK_transitive : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ (m : ℕ) (Γ : Matrix (Fin m) (Fin m) E), IsHerm L Γ → IsUnit Γ.det → ∀ i : ℕ, 1 ≤ i → ∃ j : ℕ, ∀ X ∈ horb L ϖ Γ i, ∀ D : Matrix (Fin m) (Fin m) E, IsHerm L D → IsIntM L D → ∃ A ∈ congK L ϖ m i, X + algebraMap F E ((ϖ : F) ^ j) • D = cT L A * X * A := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ m Γ hΓ hdet i hi
  have hp : algebraMap F E ϖ ∈ L.O := (algebraMap_mem_iff L _).2 ϖ.2
  have hcp : ∀ n : ℕ, L.cj (algebraMap F E ϖ ^ n) = algebraMap F E ϖ ^ n := fun n => by
    rw [map_pow, AlgEquiv.commutes]
  have hΓ' : cT L Γ = Γ := hΓ
  have hinv : Γ * Γ⁻¹ = 1 := Matrix.mul_nonsing_inv Γ hdet
  have hH : cT L Γ⁻¹ = Γ⁻¹ := by
    have h := congrArg (cT L) hinv
    rw [cT_mul, hΓ', cT_one] at h
    calc cT L Γ⁻¹ = cT L Γ⁻¹ * (Γ * Γ⁻¹) := by rw [hinv, Matrix.mul_one]
      _ = Γ⁻¹ := by rw [← Matrix.mul_assoc, h, Matrix.one_mul]
  choose k hk using fun ab : Fin m × Fin m => exists_pow_mul_mem L hϖ (Γ⁻¹ ab.1 ab.2)
  obtain ⟨c, hc⟩ : ∃ c : ℕ, IsIntM L (algebraMap F E ϖ ^ c • Γ⁻¹) := by
    refine ⟨Finset.univ.sup k, fun a b => ?_⟩
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := k) (Finset.mem_univ (a, b)))
    rw [hd, Matrix.smul_apply, smul_eq_mul, pow_add, mul_assoc]
    exact L.O.mul_mem (L.O.pow_mem hp _) (hk (a, b))
  refine ⟨i + c, ?_⟩
  rintro X ⟨A, hA, hX⟩ D hD hDi
  obtain ⟨B, hB, hAB⟩ := exists_inv L hϖ hi hA
  have hBA : B * A = 1 := mul_eq_one_comm.1 hAB
  have hBA' : cT L A * cT L B = 1 := by rw [← cT_mul, hBA, cT_one]
  obtain ⟨G, hG⟩ : ∃ G, G = B * (algebraMap F E ϖ ^ c • Γ⁻¹) * cT L B := ⟨_, rfl⟩
  have hGi : IsIntM L G := hG ▸ int_mul L (int_mul L hB hc) (int_cT L hB)
  have hGh : cT L G = G := by
    rw [hG, cT_mul, cT_mul, cT_cT, cT_smul, hcp, hH, Matrix.mul_assoc]
  have hXh : cT L X = X := by
    rw [hX, cT_mul, cT_mul, cT_cT, hΓ', Matrix.mul_assoc]
  have hXG : X * G = algebraMap F E ϖ ^ c • (1 : Matrix (Fin m) (Fin m) E) := by
    calc X * G = algebraMap F E ϖ ^ c • (cT L A * (Γ * (A * B) * Γ⁻¹) * cT L B) := by
          rw [hX, hG]; simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = _ := by rw [hAB, Matrix.mul_one, hinv, Matrix.mul_one, hBA']
  have hGX : G * X = algebraMap F E ϖ ^ c • (1 : Matrix (Fin m) (Fin m) E) := by
    have h := congrArg (cT L) hXG
    rwa [cT_mul, hGh, hXh, cT_smul, hcp, cT_one] at h
  obtain ⟨Z, hZ, hZD⟩ := exists_solution L hϖ hi hGh hGi hD hDi
  refine ⟨1 + algebraMap F E ϖ ^ i • (G * Z),
    (mem_congK_iff L ϖ i _).2 ⟨_, int_mul L hGi hZ, rfl⟩, ?_⟩
  have e1 : X * (G * Z) = algebraMap F E ϖ ^ c • Z := by
    rw [← Matrix.mul_assoc, hXG, Matrix.smul_mul, Matrix.one_mul]
  have e2 : cT L Z * G * X = algebraMap F E ϖ ^ c • cT L Z := by
    rw [Matrix.mul_assoc, hGX, Matrix.mul_smul, Matrix.mul_one]
  rw [cT_add, cT_smul, hcp, cT_mul, hGh, cT_one, map_pow, ← hZD]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, e1, e2, ← Matrix.mul_assoc (cT L Z) G Z]
  module
