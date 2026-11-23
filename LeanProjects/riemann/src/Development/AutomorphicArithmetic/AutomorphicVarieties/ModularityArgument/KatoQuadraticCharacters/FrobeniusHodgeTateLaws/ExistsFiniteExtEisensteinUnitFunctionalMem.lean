import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.RhoFrob

noncomputable section

open Formalism.ConjugateSelfDual UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.EisM

namespace UpperTheory.V.Z.Kato.Joint.M3

variable {l : ℕ} [Fact l.Prime]

omit [Fact l.Prime] in
theorem iter_uo (r : ℕ) (a : ℕ → ℂ) (n : ℕ) : (Uo l)^[r] a n = a (l ^ r * n) := by
  induction r generalizing a with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply, ih]
    simp only [Uo]
    rw [pow_succ', mul_assoc]

omit [Fact l.Prime] in
theorem mes_lin (k : ℕ) (u w : ℤ → ℂ) (α : ℂ) (B : ℕ) (c : ℕ → ℂ) (m : ℕ) (a : ℂ) (f f' : ZMod (l ^ m) → ℂ) :
    mesMu k l u w α B c m (fun y => a * f y + f' y) = a * mesMu k l u w α B c m f + mesMu k l u w α B c m f' := by
  have h : ∀ n, Zm k l u w (fun A d => a * f ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹) + f' ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹)) n
      = a * Zm k l u w (fun A d => f ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹)) n +
        Zm k l u w (fun A d => f' ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹)) n := by
    intro n
    simp only [Zm, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    split_ifs <;> ring
  simp only [mesMu, val, lam, iter_uo, h, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

omit [Fact l.Prime] in
theorem mes_smul (k : ℕ) (u w : ℤ → ℂ) (α : ℂ) (B : ℕ) (c : ℕ → ℂ) (m : ℕ) (a : ℂ) (f : ZMod (l ^ m) → ℂ) :
    mesMu k l u w α B c m (fun y => a * f y) = a * mesMu k l u w α B c m f := by
  have key : ∀ n, Zm k l u w (fun A d => (fun y => a * f y) ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹)) n =
      a * Zm k l u w (fun A d => f ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹)) n := by
    intro n
    simp only [Zm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    split_ifs <;> ring
  simp only [mesMu, val, lam, iter_uo]
  simp only [key, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

open Classical in

def sym (ι : Qbar l ≃+* ℂ) (s : ℂ) {N : ℕ} (g : ZMod N → Qbar l) : ZMod N → ℂ :=
  fun y => if IsUnit y then (ι (g y⁻¹) + s * ι (g (-y)⁻¹)) / 2 else 0

def nu0 (ι : Qbar l ≃+* ℂ) (e : ℕ) (s : ℂ) (u w : ℤ → ℂ) (α : ℂ) (B : ℕ) (c : ℕ → ℂ) (M : ℕ) :
    (ZMod (l ^ M) → Qbar l) →ₗ[Qbar l] Qbar l where
  toFun g := ι.symm (mesMu (2 * e + 1) l u w α B c M (sym ι s g))
  map_add' g g' := by
    have : sym ι s (g + g') = fun y => 1 * sym ι s g y + sym ι s g' y := by
      funext y; simp only [sym, Pi.add_apply, map_add]; split_ifs <;> ring
    rw [this, mes_lin, one_mul, map_add]
  map_smul' a g := by
    have : sym ι s (a • g) = fun y => ι a * sym ι s g y := by
      funext y; simp only [sym, Pi.smul_apply, smul_eq_mul, map_mul]; split_ifs <;> ring
    rw [this, mes_smul, map_mul]; simp

theorem eisensteinUnitFunctional_apply (ι : Qbar l ≃+* ℂ) (e : ℕ) (s : ℂ) (u w : ℤ → ℂ) (α : ℂ) (B : ℕ) (c : ℕ → ℂ) (M : ℕ)
    (g : ZMod (l ^ M) → Qbar l) : nu0 ι e s u w α B c M g = ι.symm (mesMu (2 * e + 1) l u w α B c M (sym ι s g)) := rfl

theorem inv_unit {N : ℕ} {y : ZMod N} (h : IsUnit y) : IsUnit y⁻¹ := IsUnit.of_mul_eq_one y (ZMod.inv_mul_of_unit y h)

theorem neg_inv_unit {N : ℕ} {y : ZMod N} (h : IsUnit y) : (-y)⁻¹ = -y⁻¹ := by
  obtain ⟨u, rfl⟩ := h
  rw [← Units.val_neg, ZMod.inv_coe_unit, ZMod.inv_coe_unit, inv_neg, Units.val_neg]

theorem sym_par (ι : Qbar l ≃+* ℂ) {s : ℂ} (hs : s * s = 1) {N : ℕ} (g : ZMod N → Qbar l) (y : ZMod N) :
    sym ι s g (-y) = s * sym ι s g y := by
  by_cases hy : IsUnit y
  · simp only [sym, if_pos hy, if_pos hy.neg, neg_neg]
    linear_combination (-ι (g (-y)⁻¹) / 2) * hs
  · simp [sym, hy]

theorem eisensteinUnitFunctional_congr_on_units (ι : Qbar l ≃+* ℂ) (e : ℕ) (s : ℂ) (u w : ℤ → ℂ) (α : ℂ) (B : ℕ) (c : ℕ → ℂ) (M : ℕ)
    (g g' : ZMod (l ^ M) → Qbar l) (h : ∀ x, IsUnit x → g x = g' x) : nu0 ι e s u w α B c M g = nu0 ι e s u w α B c M g' := by
  have hs : sym ι s g = sym ι s g' := by
    funext y
    unfold sym
    split_ifs with hy
    · rw [h _ (inv_unit hy), h _ (inv_unit hy.neg)]
    · rfl
  rw [eisensteinUnitFunctional_apply, eisensteinUnitFunctional_apply, hs]

theorem unit_iff {M : ℕ} (hM : 1 ≤ M) (y : ℕ) : IsUnit (y : ZMod (l ^ M)) ↔ ¬ l ∣ y := by
  rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff hM, Nat.coprime_comm, (Fact.out : l.Prime).coprime_iff_not_dvd]

theorem eisensteinUnitFunctional_compat_succ {ι : Qbar l ≃+* ℂ} {e : ℕ} {s : ℂ} {u w : ℤ → ℂ} {ψ : DirichletCharacter ℂ l} {α : ℂ} {B : ℕ} {c : ℕ → ℂ} {v : ℂ}
    (H : MeasMu ι e s u w ψ α B c v) (hs : s * s = 1) (M : ℕ) (hM : 1 ≤ M) (g : ZMod (l ^ M) → Qbar l)
    (g' : ZMod (l ^ (M + 1)) → Qbar l) (h : ∀ y : ℕ, g' y = g y) :
    nu0 ι e s u w α B c (M + 1) g' = nu0 ι e s u w α B c M g := by
  have hdvd : l ^ M ∣ l ^ (M + 1) := pow_dvd_pow l (Nat.le_succ M)
  haveI : NeZero (l ^ (M + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  set φ := ZMod.castHom hdvd (ZMod (l ^ M))
  have hg : ∀ x, g' x = g (φ x) := by
    intro x
    rw [← ZMod.natCast_zmod_val x, h, map_natCast]
  have hinv : ∀ x : ZMod (l ^ (M + 1)), IsUnit x → φ x⁻¹ = (φ x)⁻¹ := by
    intro x hx
    symm
    apply ZMod.inv_eq_of_mul_eq_one
    rw [← map_mul, ZMod.mul_inv_of_unit x hx, map_one]
  have hsym : ∀ y : ℕ, sym ι s g' (y : ZMod (l ^ (M + 1))) = sym ι s g y := by
    intro y
    unfold sym
    by_cases hy : l ∣ y
    · rw [if_neg (by rw [unit_iff (M := M + 1) (by omega)]; exact not_not.2 hy),
        if_neg (by rw [unit_iff hM]; exact not_not.2 hy)]
    · have h1 : IsUnit (y : ZMod (l ^ (M + 1))) := (unit_iff (M := M + 1) (by omega) y).2 hy
      rw [if_pos h1, if_pos ((unit_iff hM y).2 hy), hg, hg, hinv _ h1, hinv _ h1.neg, map_neg, map_natCast]
  rw [eisensteinUnitFunctional_apply, eisensteinUnitFunctional_apply, H.compat M hM (sym ι s g) (sym ι s g') (sym_par ι hs g) hsym]

theorem norm_nat {a : ℕ} (ha : ¬ l ∣ a) : ‖(a : Qbar l)‖ = 1 := by
  have h1 : algebraMap ℚ_[l] (Qbar l) (a : ℚ_[l]) = (a : Qbar l) := map_natCast _ a
  have h2 : ((a : ℚ) : ℚ_[l]) = (a : ℚ_[l]) := by push_cast; rfl
  rw [← h1, PadicAlgCl.norm_extends l (a : ℚ_[l])]
  rw [← h2, Padic.eq_padicNorm, (padicNorm.nat_eq_one_iff a).2 ha]
  simp

theorem norm_half (hl : l ≠ 2) {a b : Qbar l} {δ : ℝ} (ha : ‖a‖ ≤ δ) (hb : ‖b‖ ≤ δ) : ‖(a + b) / 2‖ ≤ δ := by
  have h2 : ‖(2 : Qbar l)‖ = 1 := by
    simpa using norm_nat (l := l) (a := 2) fun h => hl ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h)
  rw [norm_div, h2, div_one]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)

theorem sgn_cases {s : ℂ} (hs : s * s = 1) : s = 1 ∨ s = -1 := mul_self_eq_one_iff.1 hs

theorem symm_sym (ι : Qbar l ≃+* ℂ) (s : ℂ) {N : ℕ} (g : ZMod N → Qbar l) {y : ZMod N} (hy : IsUnit y) :
    ι.symm (sym ι s g y) = (g y⁻¹ + ι.symm s * g (-y⁻¹)) / 2 := by
  unfold sym
  rw [if_pos hy, neg_inv_unit hy, map_div₀, map_add, map_mul, RingEquiv.symm_apply_apply,
    RingEquiv.symm_apply_apply, map_ofNat]

theorem eisensteinUnitFunctional_bounded {ι : Qbar l ≃+* ℂ} {e : ℕ} {s : ℂ} {u w : ℤ → ℂ} {ψ : DirichletCharacter ℂ l} {α : ℂ} {B : ℕ} {c : ℕ → ℂ} {v : ℂ}
    (H : MeasMu ι e s u w ψ α B c v) (hs : s * s = 1) (hl : l ≠ 2) :
    ∃ C : ℝ, ∀ (M : ℕ) (g : ZMod (l ^ M) → Qbar l), (∀ y, ‖g y‖ ≤ 1) → ‖nu0 ι e s u w α B c M g‖ ≤ C := by
  obtain ⟨C, hC⟩ := H.bound
  refine ⟨C * 1, fun M g hg => ?_⟩
  rw [eisensteinUnitFunctional_apply]
  apply hC M _ 1 zero_le_one
  intro y
  by_cases hy : IsUnit y
  · rw [symm_sym ι s g hy]
    apply norm_half hl (hg _)
    rw [norm_mul]
    have hn : ‖ι.symm s‖ = 1 := by
      rcases sgn_cases hs with rfl | rfl <;> simp
    rw [hn, one_mul]
    exact hg _
  · simp [sym, hy]

theorem exists_finiteExt_eisensteinUnitFunctional_mem {ι : Qbar l ≃+* ℂ} {e : ℕ} {s : ℂ} {u w : ℤ → ℂ} {ψ : DirichletCharacter ℂ l} {α : ℂ} {B : ℕ} {c : ℕ → ℂ} {v : ℂ}
    (H : MeasMu ι e s u w ψ α B c v) (hs : s * s = 1) :
    ∃ E : IntermediateField ℚ_[l] (Qbar l), FiniteDimensional ℚ_[l] E ∧
      ∀ (M : ℕ) (g : ZMod (l ^ M) → Qbar l), (∀ y, g y ∈ E) → nu0 ι e s u w α B c M g ∈ E := by
  obtain ⟨E, hE, hf⟩ := H.field
  refine ⟨E, hE, fun M g hg => ?_⟩
  rw [eisensteinUnitFunctional_apply]
  apply hf M _ E le_rfl
  intro y
  by_cases hy : IsUnit y
  · rw [symm_sym ι s g hy]
    have hs' : ι.symm s ∈ E := by
      rcases sgn_cases hs with rfl | rfl
      · rw [map_one]
        exact E.one_mem
      · rw [map_neg, map_one]
        exact E.neg_mem E.one_mem
    have h2 : (2 : Qbar l) ∈ E := by
      rw [← one_add_one_eq_two]
      exact E.add_mem E.one_mem E.one_mem
    exact E.div_mem (E.add_mem (hg _) (E.mul_mem hs' (hg _))) h2
  · simp only [sym, if_neg hy, map_zero]
    exact E.zero_mem

theorem sym_char (ι : Qbar l ≃+* ℂ) (s : ℂ) {N : ℕ} (χ : DirichletCharacter (Qbar l) N) (y : ZMod N) :
    sym ι s (fun x => χ⁻¹ x) y = (1 + s * ι (χ (-1))) / 2 * ι (χ y) := by
  unfold sym
  split_ifs with hy
  · have key : ∀ z : ZMod N, IsUnit z → χ⁻¹ z⁻¹ = χ z := by
      intro z hz
      rw [MulChar.inv_apply_eq_inv']
      have hm : χ z⁻¹ * χ z = 1 := by rw [← map_mul, ZMod.inv_mul_of_unit z hz, map_one]
      exact inv_eq_of_mul_eq_one_right hm
    dsimp only
    rw [key y hy, key (-y) hy.neg]
    have hn : χ (-y) = χ (-1) * χ y := by rw [← map_mul, neg_one_mul]
    rw [hn, map_mul ι]
    ring
  · rw [MulChar.map_nonunit χ hy, map_zero, mul_zero]

theorem eisensteinUnitFunctional_dirichletChar (ι : Qbar l ≃+* ℂ) (e : ℕ) (s : ℂ) (u w : ℤ → ℂ) (α : ℂ) (B : ℕ) (c : ℕ → ℂ) (M : ℕ)
    (χ : DirichletCharacter (Qbar l) (l ^ M)) :
    nu0 ι e s u w α B c M (fun x => χ⁻¹ x) =
      (1 + ι.symm s * χ (-1)) / 2 * ι.symm (mesMu (2 * e + 1) l u w α B c M (fun y => ι (χ y))) := by
  rw [eisensteinUnitFunctional_apply]
  have hs : sym ι s (fun x => χ⁻¹ x) = fun y => (1 + s * ι (χ (-1))) / 2 * ι (χ y) := funext (sym_char ι s χ)
  rw [hs, mes_smul, map_mul]
  congr 1
  rw [map_div₀, map_add, map_one, map_mul, RingEquiv.symm_apply_apply, map_ofNat]

theorem eisensteinUnitFunctional_interpolation {ι : Qbar l ≃+* ℂ} {e : ℕ} {s : ℂ} {u w : ℤ → ℂ} {ψ : DirichletCharacter ℂ l} {α : ℂ} {B : ℕ} {c : ℕ → ℂ} {v : ℂ}
    (H : MeasMu ι e s u w ψ α B c v) (hs : s * s = 1) (hl : l ≠ 2) :
    ∃ C : ℝ, ∀ (M : ℕ), 1 ≤ M → ∀ (g : ZMod (l ^ M) → Qbar l) (δ : ℝ), 0 ≤ δ →
      (∀ a d : ℕ, ¬ l ∣ a → ¬ l ∣ d → ∀ y : ZMod (l ^ M), y * a = d →
        ‖g y - ι.symm (ψ a * ψ⁻¹ d * ((d : ℂ) / a) ^ e)‖ ≤ δ ∧ ‖ι.symm s * g (-y) - ι.symm (ψ a * ψ⁻¹ d * ((d : ℂ) / a) ^ e)‖ ≤ δ) →
      ‖nu0 ι e s u w α B c M g - ι.symm v‖ ≤ C * δ := by
  obtain ⟨C, hC⟩ := H.interp
  refine ⟨C, fun M hM g δ hδ hg => ?_⟩
  rw [eisensteinUnitFunctional_apply, ← map_sub]
  apply hC M hM _ δ hδ (sym_par ι hs g)
  intro a d ha hd
  have hua : IsUnit (a : ZMod (l ^ M)) := (unit_iff hM a).2 ha
  have hud : IsUnit (d : ZMod (l ^ M)) := (unit_iff hM d).2 hd
  set x : ZMod (l ^ M) := (a : ZMod (l ^ M)) * (d : ZMod (l ^ M))⁻¹ with hxdef
  have hx : IsUnit x := hua.mul (inv_unit hud)
  have hxd : x * d = a := by rw [hxdef, mul_assoc, ZMod.inv_mul_of_unit _ hud, mul_one]
  have hy : x⁻¹ * a = d := by rw [← hxd, ← mul_assoc, ZMod.inv_mul_of_unit _ hx, one_mul]
  obtain ⟨h1, h2⟩ := hg a d ha hd x⁻¹ hy
  rw [map_sub, symm_sym ι s g hx]
  set T := ι.symm (ψ a * ψ⁻¹ d * ((d : ℂ) / a) ^ e)
  have hT : (g x⁻¹ + ι.symm s * g (-x⁻¹)) / 2 - T = ((g x⁻¹ - T) + (ι.symm s * g (-x⁻¹) - T)) / 2 := by ring
  rw [hT]
  exact norm_half hl h1 h2

end UpperTheory.V.Z.Kato.Joint.M3

end
