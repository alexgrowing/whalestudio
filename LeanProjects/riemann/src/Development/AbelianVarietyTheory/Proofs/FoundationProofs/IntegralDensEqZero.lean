import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.IsSemiChar
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IntegrableOnFundamentalDomainOfContinuous

noncomputable section

namespace GlobalTheory.ThetaInter

open Formalism.L2.Th1.H Complex
open scoped BigOperators ComplexConjugate

theorem sum_out_shift {G M : Type*} [AddCommGroup G] [AddCommMonoid M] (S : AddSubgroup G) [Fintype (G ⧸ S)]
    (f : G → M) (hf : ∀ a, ∀ s ∈ S, f (a + s) = f a) (g : G) :
    ∑ c : G ⧸ S, f (g + Quotient.out c) = ∑ c : G ⧸ S, f (Quotient.out c) := by
  refine Fintype.sum_equiv (Equiv.addLeft (g : G ⧸ S)) _ _ fun c => ?_
  have h : -(g + Quotient.out c) + Quotient.out ((g : G ⧸ S) + c) ∈ S := by
    rw [← QuotientAddGroup.eq]
    simp
  have := hf (g + Quotient.out c) _ h
  rw [add_neg_cancel_left] at this
  simpa using this.symm

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {H : Sesq V}

def chi (H : Sesq V) (x y : V) : ℂ := cexp (-(2 * Real.pi * I * (altE H x y : ℂ)))

theorem sub_swap (hH : IsHerm H) (x y : V) : H y x = H x y - 2 * I * (altE H x y : ℂ) := by
  rw [hH x y]
  apply Complex.ext <;> simp [altE]
  ring

theorem altE_swap (hH : IsHerm H) (x y : V) : altE H y x = -altE H x y := by
  simp [altE, hH x y]

theorem chi_add_left (x x' y : V) : chi H (x + x') y = chi H x y * chi H x' y := by
  simp only [chi, ← Complex.exp_add, altE, map_add, LinearMap.add_apply, add_im]
  congr 1; push_cast; ring

theorem chi_add_right (x y y' : V) : chi H x (y + y') = chi H x y * chi H x y' := by
  simp only [chi, ← Complex.exp_add, altE, map_add, add_im]
  congr 1; push_cast; ring

theorem chi_eq_one_iff (x y : V) : chi H x y = 1 ↔ ∃ m : ℤ, altE H x y = m := by
  rw [chi, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    have : (altE H x y : ℂ) = -k := by
      apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
      linear_combination -hk
    exact_mod_cast this
  · rintro ⟨m, hm⟩
    exact ⟨-m, by rw [hm]; push_cast; ring⟩

theorem chi_mul_conj (x y y' : V) : chi H x y * conj (chi H x y') = chi H x (y - y') := by
  simp only [chi, ← Complex.exp_conj, ← Complex.exp_add, altE, map_sub, sub_im, map_neg, map_mul,
    Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  congr 1; push_cast; ring

theorem int_swap (hH : IsHerm H) {x y : V} (h : ∃ m : ℤ, altE H x y = m) : ∃ m : ℤ, altE H y x = m := by
  obtain ⟨m, hm⟩ := h
  exact ⟨-m, by rw [altE_swap hH, hm]; simp⟩

theorem opU_opU (hH : IsHerm H) (x y : V) (F : V → ℂ) (z : V) :
    opU H x (opU H y F) z = cexp (-(Real.pi * I * (altE H x y : ℂ))) * opU H (x + y) F z := by
  simp only [opU, add_assoc, map_add, LinearMap.add_apply]
  rw [mul_assoc, mul_left_comm _ (F _), ← Complex.exp_add, ← Complex.exp_add, sub_swap hH x y]
  congr 2
  ring

theorem opU_comm (hH : IsHerm H) (x y : V) (F : V → ℂ) (z : V) :
    opU H x (opU H y F) z = chi H x y * opU H y (opU H x F) z := by
  rw [opU_opU hH, opU_opU hH, altE_swap hH x y, chi, ← mul_assoc, ← Complex.exp_add, add_comm y x]
  congr 2
  push_cast
  ring

theorem opU_mul (x : V) (c : ℂ) (F : V → ℂ) (z : V) :
    opU H x (fun w => c * F w) z = c * opU H x F z := by
  simp only [opU]; ring

theorem opU_sum {ι : Type*} (s : Finset ι) (x : V) (F : ι → V → ℂ) (z : V) :
    opU H x (fun w => ∑ i ∈ s, F i w) z = ∑ i ∈ s, opU H x (F i) z := by
  simp only [opU, Finset.sum_mul]

variable {α : V → ℂ}

theorem alpha_sq {A : AddSubgroup V} (hs : IsSemiChar H A α) {x : V} (hx : x ∈ A) : α x * α x = 1 := by
  rcases hs.1 x hx with h | h <;> simp [h]

theorem alpha_conj {A : AddSubgroup V} (hs : IsSemiChar H A α) {x : V} (hx : x ∈ A) : conj (α x) = α x := by
  rcases hs.1 x hx with h | h <;> simp [h]

theorem alpha_opU_add (hH : IsHerm H) {A : AddSubgroup V} (hd : IsSelfDual H A) (hs : IsSemiChar H A α)
    {x y : V} (hx : x ∈ A) (hy : y ∈ A) (F : V → ℂ) (z : V) :
    α (x + y) * opU H (x + y) F z = α x * (α y * opU H x (opU H y F) z) := by
  have hx' : x ∈ dualLat H A := by rw [hd]; exact hx
  have h1 : chi H x y = 1 := (chi_eq_one_iff x y).2 (hx' y hy)
  rw [opU_opU hH, hs.2 x hx y hy]
  have : cexp (-(Real.pi * I * (altE H x y : ℂ))) = cexp (Real.pi * I * (altE H x y : ℂ)) * chi H x y := by
    rw [chi, ← Complex.exp_add]; congr 1; ring
  rw [this, h1]; ring

theorem opU_of_fixed {A : AddSubgroup V} (hs : IsSemiChar H A α) {F : V → ℂ} (hF : F ∈ fixedBy H α A)
    {x : V} (hx : x ∈ A) : opU H x F = fun z => α x * F z := by
  funext z
  rw [← hF x hx z, ← mul_assoc, alpha_sq hs hx, one_mul]

theorem inter_eq (A₁ A₂ : AddSubgroup V) [Fintype (A₂ ⧸ A₁.addSubgroupOf A₂)] (F : V → ℂ) :
    inter H α A₁ A₂ F = fun z => ((Real.sqrt (Fintype.card (A₂ ⧸ A₁.addSubgroupOf A₂)) : ℝ) : ℂ)⁻¹ *
      ∑ c : A₂ ⧸ A₁.addSubgroupOf A₂,
        α ((Quotient.out c : A₂) : V) * opU H ((Quotient.out c : A₂) : V) F z := by
  funext z
  rw [inter, finsum_eq_sum_of_fintype, relIdx, AddSubgroup.relIndex, AddSubgroup.index, Nat.card_eq_fintype_card]

theorem inter_mem_fixedBy (hH : IsHerm H) {A₁ A₂ : AddSubgroup V} [Finite (A₂ ⧸ A₁.addSubgroupOf A₂)]
    (hs₁ : IsSemiChar H A₁ α) (hd₂ : IsSelfDual H A₂) (hs₂ : IsSemiChar H A₂ α)
    {F : V → ℂ} (hF : F ∈ fixedBy H α A₁) : inter H α A₁ A₂ F ∈ fixedBy H α A₂ := by
  have := Fintype.ofFinite (A₂ ⧸ A₁.addSubgroupOf A₂)
  intro y hy z
  rw [inter_eq, opU_mul, opU_sum, mul_left_comm, Finset.mul_sum]
  congr 1
  rw [← sum_out_shift (A₁.addSubgroupOf A₂) (fun a : A₂ => α (a : V) * opU H (a : V) F z) ?_ ⟨y, hy⟩]
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [opU_mul, AddSubgroup.coe_add, alpha_opU_add hH hd₂ hs₂ hy (Quotient.out c).2]
  · intro a s hs
    rw [AddSubgroup.coe_add, alpha_opU_add hH hd₂ hs₂ a.2 s.2, opU_of_fixed hs₁ hF (AddSubgroup.mem_addSubgroupOf.1 hs), opU_mul,
      ← mul_assoc (α s), alpha_sq hs₂ s.2, one_mul]

open Classical in

theorem sum_chi (hH : IsHerm H) {A₁ A₂ : AddSubgroup V} [Fintype (A₁ ⧸ A₂.addSubgroupOf A₁)]
    (hd₁ : IsSelfDual H A₁) (hd₂ : IsSelfDual H A₂) {y : V} (hy : y ∈ A₂) :
    ∑ c : A₁ ⧸ A₂.addSubgroupOf A₁, chi H ((Quotient.out c : A₁) : V) y =
      if y ∈ A₁ then (Fintype.card (A₁ ⧸ A₂.addSubgroupOf A₁) : ℂ) else 0 := by
  split_ifs with h
  · have : ∀ c : A₁, chi H (c : V) y = 1 := fun c => (chi_eq_one_iff _ y).2 ((hd₁.ge c.2) y h)
    simp [this]
  · obtain ⟨p, hp, hp'⟩ : ∃ p ∈ A₁, chi H p y ≠ 1 := by
      by_contra hc
      push Not at hc
      exact h (hd₁.le fun p hp => int_swap hH ((chi_eq_one_iff _ _).1 (hc p hp)))
    have := sum_out_shift (A₂.addSubgroupOf A₁) (fun a : A₁ => chi H (a : V) y) (fun a s hs => by
      rw [AddSubgroup.coe_add, chi_add_left, (chi_eq_one_iff _ y).2 ((hd₂.ge (AddSubgroup.mem_addSubgroupOf.1 hs)) y hy), mul_one]) ⟨p, hp⟩
    simp only [AddSubgroup.coe_add, chi_add_left, ← Finset.mul_sum] at this
    have h2 := sub_eq_zero.2 this
    rw [← sub_one_mul] at h2
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hp')

theorem out_mem_iff {A₁ A₂ : AddSubgroup V} (c : A₂ ⧸ A₁.addSubgroupOf A₂) :
    ((Quotient.out c : A₂) : V) ∈ A₁ ↔ c = 0 := by
  rw [← AddSubgroup.mem_addSubgroupOf, ← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.out_eq']

theorem card_eq_card (hH : IsHerm H) {A₁ A₂ : AddSubgroup V} [Fintype (A₁ ⧸ A₂.addSubgroupOf A₁)]
    [Fintype (A₂ ⧸ A₁.addSubgroupOf A₂)] (hd₁ : IsSelfDual H A₁) (hd₂ : IsSelfDual H A₂) :
    Fintype.card (A₁ ⧸ A₂.addSubgroupOf A₁) = Fintype.card (A₂ ⧸ A₁.addSubgroupOf A₂) := by
  classical
  have h1 : ∑ d : A₂ ⧸ A₁.addSubgroupOf A₂, ∑ c : A₁ ⧸ A₂.addSubgroupOf A₁,
      chi H ((Quotient.out c : A₁) : V) ((Quotient.out d : A₂) : V) =
      Fintype.card (A₁ ⧸ A₂.addSubgroupOf A₁) := by
    simp only [fun d : A₂ ⧸ A₁.addSubgroupOf A₂ => sum_chi hH hd₁ hd₂ (Quotient.out d : A₂).2, out_mem_iff]
    simp
  have h2 : ∑ c : A₁ ⧸ A₂.addSubgroupOf A₁, ∑ d : A₂ ⧸ A₁.addSubgroupOf A₂,
      chi H ((Quotient.out d : A₂) : V) ((Quotient.out c : A₁) : V) =
      Fintype.card (A₂ ⧸ A₁.addSubgroupOf A₂) := by
    simp only [fun c : A₁ ⧸ A₂.addSubgroupOf A₁ => sum_chi hH hd₂ hd₁ (Quotient.out c : A₁).2, out_mem_iff]
    simp
  have h3 : ∀ x y : V, chi H x y = conj (chi H y x) := by
    intro x y
    simp only [chi, ← Complex.exp_conj, map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat,
      altE_swap hH y x]
    congr 1; push_cast; ring
  rw [Finset.sum_comm] at h1
  simp only [fun (c : A₁ ⧸ A₂.addSubgroupOf A₁) (d : A₂ ⧸ A₁.addSubgroupOf A₂) =>
    h3 ((Quotient.out c : A₁) : V) ((Quotient.out d : A₂) : V), ← map_sum] at h1
  rw [h2, map_natCast] at h1
  exact_mod_cast h1.symm

theorem inter_inter (hH : IsHerm H) {A₁ A₂ : AddSubgroup V} [Finite (A₁ ⧸ A₂.addSubgroupOf A₁)]
    [Finite (A₂ ⧸ A₁.addSubgroupOf A₂)] (hd₁ : IsSelfDual H A₁) (hd₂ : IsSelfDual H A₂)
    (hs₁ : IsSemiChar H A₁ α) {F : V → ℂ} (hF : F ∈ fixedBy H α A₁) :
    inter H α A₂ A₁ (inter H α A₁ A₂ F) = F := by
  classical
  have := Fintype.ofFinite (A₂ ⧸ A₁.addSubgroupOf A₂)
  have := Fintype.ofFinite (A₁ ⧸ A₂.addSubgroupOf A₁)
  rw [inter_eq A₂ A₁, inter_eq A₁ A₂]
  funext z
  have key : ∀ (p : A₁) (q : V), α p * opU H p (fun w => α q * opU H q F w) z =
      chi H p q * (α q * opU H q F z) := by
    intro p q
    rw [opU_mul, opU_comm hH, opU_of_fixed hs₁ hF p.2, opU_mul]
    linear_combination (α q * chi H p q * opU H q F z) * alpha_sq hs₁ p.2
  have e : ∀ p : A₁, α p * opU H p (fun z => ((Real.sqrt (Fintype.card (A₂ ⧸ A₁.addSubgroupOf A₂)) : ℝ) : ℂ)⁻¹ *
      ∑ c : A₂ ⧸ A₁.addSubgroupOf A₂,
        α ((Quotient.out c : A₂) : V) * opU H ((Quotient.out c : A₂) : V) F z) z =
      ((Real.sqrt (Fintype.card (A₂ ⧸ A₁.addSubgroupOf A₂)) : ℝ) : ℂ)⁻¹ *
      ∑ c : A₂ ⧸ A₁.addSubgroupOf A₂, chi H p ((Quotient.out c : A₂) : V) *
        (α ((Quotient.out c : A₂) : V) * opU H ((Quotient.out c : A₂) : V) F z) := by
    intro p
    rw [opU_mul, opU_sum, mul_left_comm, Finset.mul_sum]
    simp only [key]
  simp only [e]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [← Finset.sum_mul,
    fun d : A₂ ⧸ A₁.addSubgroupOf A₂ => sum_chi hH hd₁ hd₂ (Quotient.out d : A₂).2, out_mem_iff]
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_univ _) fun b _ hb => by simp [hb], if_pos rfl,
    hF _ ((out_mem_iff _).2 rfl), ← card_eq_card hH hd₁ hd₂]
  have hpos : (0 : ℝ) < Fintype.card (A₁ ⧸ A₂.addSubgroupOf A₁) := by exact_mod_cast Fintype.card_pos
  have h1 : ((Real.sqrt (Fintype.card (A₁ ⧸ A₂.addSubgroupOf A₁)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hpos).ne'
  have h2 : ((Real.sqrt (Fintype.card (A₁ ⧸ A₂.addSubgroupOf A₁)) : ℝ) : ℂ) ^ 2 =
      Fintype.card (A₁ ⧸ A₂.addSubgroupOf A₁) := by
    exact_mod_cast Real.sq_sqrt hpos.le
  rw [← h2]
  field_simp

omit [Module ℂ V] in

theorem finite_quot {A₁ A₂ : AddSubgroup V} (hfg : A₂.FG) (h : ∀ x ∈ A₂, ∃ m : ℕ, 0 < m ∧ m • x ∈ A₁) :
    Finite (A₂ ⧸ A₁.addSubgroupOf A₂) := by
  have : AddGroup.FG A₂ := (AddGroup.fg_iff_addSubgroup_fg A₂).2 hfg
  refine AddCommGroup.finite_of_fg_torsion _ fun q => ?_
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨m, hm, hx⟩ := h x x.2
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨m, hm, ?_⟩
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  exact hx

theorem isSemiChar_round (hH : IsHerm H) (s : ℝ) {A : AddSubgroup V} (hint : A ≤ dualLat H A)
    (hw : ∀ x ∈ A, ((1 + I * (s : ℂ)) / 2) • x ∈ A) (hq : ∀ x ∈ A, ∃ m : ℤ, s / 2 * (H x x).re = m) :
    IsSemiChar H A fun x => (-1 : ℂ) ^ (round (s / 2 * (H x x).re)) := by
  refine ⟨fun x _ => ?_, fun x hx y hy => ?_⟩
  · rcases Int.even_or_odd (round (s / 2 * (H x x).re)) with h | h
    · exact Or.inl h.neg_one_zpow
    · exact Or.inr h.neg_one_zpow
  · obtain ⟨a, ha⟩ := hq x hx
    obtain ⟨b, hb⟩ := hq y hy
    obtain ⟨e, he⟩ := hint hx y hy
    obtain ⟨k, hk⟩ := hint (hw x hx) y hy
    have hk' : ((H x y).im + s * (H x y).re) / 2 = k := by
      rw [← hk, altE, map_smul]
      simp
      ring
    have hs : s / 2 * (H (x + y) (x + y)).re = ((a + b + e + 2 * (k - e) : ℤ) : ℝ) := by
      simp only [map_add, LinearMap.add_apply, add_re, hH x y, conj_re]
      rw [altE] at he
      push_cast
      linarith
    simp only [hs, ha, hb, he, round_intCast]
    have h1 : (-1 : ℂ) ≠ 0 := by norm_num
    rw [zpow_add₀ h1, zpow_add₀ h1, zpow_add₀ h1, (even_two_mul _).neg_one_zpow, mul_one,
      mul_comm _ ((e : ℝ) : ℂ), Complex.ofReal_intCast, Complex.exp_int_mul, Complex.exp_pi_mul_I]

def dens (H : Sesq V) (F G : V → ℂ) (z : V) : ℂ := F z * conj (G z) * cexp (-(Real.pi : ℂ) * H z z)

def rho (H : Sesq V) (F : V → ℂ) (z : V) : ℝ := ‖F z‖ ^ 2 * Real.exp (-Real.pi * (H z z).re)

theorem rho_eq (hH : IsHerm H) (F : V → ℂ) (z : V) : (rho H F z : ℂ) = dens H F F z := by
  have : ((H z z).re : ℂ) = H z z := Complex.conj_eq_iff_re.1 (hH z z).symm
  rw [rho, dens, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rw [this]

theorem dens_opU (hH : IsHerm H) (x : V) (F G : V → ℂ) (z : V) :
    dens H (opU H x F) (opU H x G) z = dens H F G (z + x) := by
  simp only [dens, opU, map_mul, ← Complex.exp_conj, map_sub, map_neg, map_div₀, Complex.conj_ofReal,
    ← hH _ _, map_ofNat, map_add, LinearMap.add_apply]
  have key : cexp (-(Real.pi : ℂ) * H z x - Real.pi * H x x / 2) *
      cexp (-(Real.pi : ℂ) * H x z - Real.pi * H x x / 2) * cexp (-(Real.pi : ℂ) * H z z) =
      cexp (-(Real.pi : ℂ) * (H z z + H x z + (H z x + H x x))) := by
    simp only [← Complex.exp_add]; congr 1; ring
  rw [← key]; ring

theorem rho_opU (hH : IsHerm H) (x : V) (F : V → ℂ) (z : V) : rho H (opU H x F) z = rho H F (z + x) := by
  apply Complex.ofReal_injective
  rw [rho_eq hH, rho_eq hH, dens_opU hH]

theorem dens_add_of_fixed (hH : IsHerm H) {A : AddSubgroup V} (hs : IsSemiChar H A α) {F : V → ℂ}
    (hF : F ∈ fixedBy H α A) (y y' : V) {x : V} (hx : x ∈ A) (z : V) :
    dens H (opU H y F) (opU H y' F) (z + x) = chi H x (y - y') * dens H (opU H y F) (opU H y' F) z := by
  rw [← dens_opU hH, ← chi_mul_conj]
  simp only [dens, opU_comm hH x, opU_of_fixed hs hF hx, opU_mul, map_mul, alpha_conj hs hx]
  linear_combination (chi H x y * conj (chi H x y') * opU H y F z * conj (opU H y' F z) *
    cexp (-(Real.pi : ℂ) * H z z)) * alpha_sq hs hx

theorem rho_add_of_fixed (hH : IsHerm H) {A : AddSubgroup V} (hs : IsSemiChar H A α) {F : V → ℂ}
    (hF : F ∈ fixedBy H α A) {x : V} (hx : x ∈ A) (z : V) : rho H F (z + x) = rho H F z := by
  apply Complex.ofReal_injective
  have h0 : opU H 0 F = F := by funext w; simp [opU]
  have := dens_add_of_fixed hH hs hF 0 0 hx z
  rw [h0] at this
  rw [rho_eq hH, rho_eq hH, this]
  simp [chi, altE]

section Analytic

open MeasureTheory

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedSpace ℝ W] [IsScalarTower ℝ ℂ W]
  [FiniteDimensional ℝ W] {H : Sesq W} {α : W → ℂ}

omit [FiniteDimensional ℝ W] in
theorem real_smul_eq (t : ℝ) (x : W) : t • x = (t : ℂ) • x := (algebraMap_smul ℂ t x).symm

omit [FiniteDimensional ℝ W] in
theorem altE_real_smul_left (t : ℝ) (x y : W) : altE H (t • x) y = t * altE H x y := by
  rw [real_smul_eq t, altE, altE, map_smul]
  simp

def altL (H : Sesq W) (y : W) : W →ₗ[ℝ] ℝ where
  toFun x := altE H x y
  map_add' x x' := by simp [altE]
  map_smul' t x := altE_real_smul_left t x y

theorem discrete_of_selfDual (hH : IsHerm H) {A : AddSubgroup W} (hd : IsSelfDual H A) (hfg : A.FG) :
    DiscreteTopology A := by
  obtain ⟨s, hs⟩ := hfg
  have hfg' : AddGroup.FG A := (AddGroup.fg_iff_addSubgroup_fg A).2 ⟨s, hs⟩
  have : Module.Finite ℤ A := Module.Finite.iff_addGroup_fg.2 hfg'
  have hc : Countable A := Finsupp.Countable.of_moduleFinite (R := ℤ)
  refine discreteTopology_iff_isOpen_singleton_zero.2 ⟨⋂ y ∈ s, {x | |altE H x y| < 1}, ?_, ?_⟩
  · exact isOpen_biInter_finset fun y _ =>
      isOpen_lt (altL H y).continuous_of_finiteDimensional.abs continuous_const
  · ext x
    simp only [Set.mem_preimage, Set.mem_iInter, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro h
      have h0 : ∀ y ∈ A, altE H x y = 0 := by
        intro y hy
        rw [← hs] at hy
        induction hy using AddSubgroup.closure_induction with
        | mem y hy =>
          obtain ⟨m, hm⟩ := hd.ge x.2 y (hs ▸ AddSubgroup.subset_closure hy)
          have := h y hy
          rw [hm] at this ⊢
          have : |m| < 1 := by exact_mod_cast this
          exact_mod_cast Int.abs_lt_one_iff.1 this
        | zero => simp [altE]
        | add a b _ _ ha hb => simp only [altE, map_add, add_im] at ha hb ⊢; rw [ha, hb, add_zero]
        | neg a _ ha => simp only [altE, map_neg, neg_im] at ha ⊢; rw [ha, neg_zero]
      by_contra hx
      have hx' : (x : W) ≠ 0 := fun h => hx (Subtype.ext h)
      have hm : ∀ t : ℝ, t • (x : W) ∈ A := fun t => hd.le fun y hy =>
        ⟨0, by rw [altE_real_smul_left, h0 y hy]; simp⟩
      have : Function.Injective fun t : ℝ => (⟨t • (x : W), hm t⟩ : A) := fun a b hab =>
        smul_left_injective ℝ hx' (congrArg Subtype.val hab)
      exact not_countable this.countable
    · rintro rfl y _
      simp [altE]

theorem exists_basis {A : AddSubgroup W} (hA : DiscreteTopology A) (hsp : Submodule.span ℝ (A : Set W) = ⊤) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℝ W), (Submodule.span ℤ (Set.range b)).toAddSubgroup = A := by
  have : DiscreteTopology (AddSubgroup.toIntSubmodule A) := hA
  have : IsZLattice ℝ (AddSubgroup.toIntSubmodule A) := ⟨hsp⟩
  have := ZLattice.module_finite ℝ (AddSubgroup.toIntSubmodule A)
  have := ZLattice.module_free ℝ (AddSubgroup.toIntSubmodule A)
  refine ⟨_, (Module.finBasis ℤ (AddSubgroup.toIntSubmodule A)).ofZLatticeBasis ℝ _, ?_⟩
  rw [Module.Basis.ofZLatticeBasis_span]
  rfl

theorem span_inf_eq_top {A₁ A₂ : AddSubgroup W} [Finite (A₂ ⧸ A₁.addSubgroupOf A₂)]
    (hsp : Submodule.span ℝ (A₂ : Set W) = ⊤) : Submodule.span ℝ ((A₁ ⊓ A₂ : AddSubgroup W) : Set W) = ⊤ := by
  rw [eq_top_iff, ← hsp, Submodule.span_le]
  intro x hx
  have h0 : (A₁.addSubgroupOf A₂).index ≠ 0 := AddSubgroup.index_ne_zero_of_finite
  have h1 := AddSubgroup.mem_addSubgroupOf.1 ((A₁.addSubgroupOf A₂).nsmul_index_mem ⟨x, hx⟩)
  have h2 : (A₁.addSubgroupOf A₂).index • x ∈ A₁ ⊓ A₂ := ⟨h1, A₂.nsmul_mem hx _⟩
  have h3 := Submodule.smul_mem _ (((A₁.addSubgroupOf A₂).index : ℝ)⁻¹) (Submodule.subset_span (R := ℝ) h2)
  rwa [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast h0), one_smul] at h3

theorem continuous_H (H : Sesq W) (hH : IsHerm H) : Continuous fun p : W × W => H p.1 p.2 := by
  let B : W →ₗ[ℝ] W →ₗ[ℝ] ℂ := LinearMap.mk₂ ℝ (fun x y => H x y) (by simp)
    (fun t x y => by rw [real_smul_eq t, map_smul]; simp) (by simp)
    (fun t x y => by rw [real_smul_eq t, map_smulₛₗ]; simp)
  let B' : W →L[ℝ] W →L[ℝ] ℂ := LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (W →ₗ[ℝ] ℂ) ≃ₗ[ℝ] W →L[ℝ] ℂ).toLinearMap ∘ₗ B)
  exact B'.continuous₂

theorem differentiable_opU {F : W → ℂ} (hF : Differentiable ℂ F) (x : W) : Differentiable ℂ (opU H x F) := by
  have : FiniteDimensional ℂ W := Module.Finite.of_restrictScalars_finite ℝ ℂ W
  have h : Differentiable ℂ fun z => H z x := (LinearMap.toContinuousLinearMap (H.flip x)).differentiable
  unfold opU
  fun_prop

theorem differentiable_inter (A₁ A₂ : AddSubgroup W) [Finite (A₂ ⧸ A₁.addSubgroupOf A₂)] {F : W → ℂ}
    (hF : Differentiable ℂ F) : Differentiable ℂ (inter H α A₁ A₂ F) := by
  have := Fintype.ofFinite (A₂ ⧸ A₁.addSubgroupOf A₂)
  rw [inter_eq]
  exact (Differentiable.fun_sum fun c _ => (differentiable_opU hF _).const_mul _).const_mul _

theorem continuous_dens (hH : IsHerm H) {F G : W → ℂ} (hF : Continuous F) (hG : Continuous G) :
    Continuous (dens H F G) := by
  have : Continuous fun z : W => H z z := (continuous_H H hH).comp (continuous_id.prodMk continuous_id)
  exact (hF.mul (Complex.continuous_conj.comp hG)).mul (Complex.continuous_exp.comp (continuous_const.mul this))

theorem continuous_rho (hH : IsHerm H) {F : W → ℂ} (hF : Continuous F) : Continuous (rho H F) := by
  have : Continuous fun z : W => H z z := (continuous_H H hH).comp (continuous_id.prodMk continuous_id)
  exact (hF.norm.pow 2).mul (Real.continuous_exp.comp (continuous_const.mul (Complex.continuous_re.comp this)))

variable [MeasurableSpace W] [BorelSpace W] (μ : Measure W) [μ.IsAddHaarMeasure]

def mean (A : AddSubgroup W) (f : W → ℝ) : ℝ :=
  ⨍ z in Classical.epsilon (fun Fd => IsAddFundamentalDomain A Fd μ), f z ∂μ

theorem mean_eq {κ : Type} [Fintype κ] (b : Module.Basis κ ℝ W) {A : AddSubgroup W}
    (hb : (Submodule.span ℤ (Set.range b)).toAddSubgroup = A) {f : W → ℝ} (hf : ∀ x ∈ A, ∀ z, f (z + x) = f z) :
    mean μ A f = ⨍ z in ZSpan.fundamentalDomain b, f z ∂μ := by
  subst hb
  have h1 := ZSpan.isAddFundamentalDomain' b μ
  have h2 := Classical.epsilon_spec
    (p := fun Fd => IsAddFundamentalDomain (Submodule.span ℤ (Set.range b)).toAddSubgroup Fd μ) ⟨_, h1⟩
  rw [mean, setAverage_eq, setAverage_eq, measureReal_def, measureReal_def, h2.measure_eq h1,
    h2.setIntegral_eq h1]
  intro g x
  change f ((g : W) + x) = f x
  rw [add_comm]
  exact hf g g.2 x

theorem mean_opU (hH : IsHerm H) {A : AddSubgroup W} (hA : DiscreteTopology A)
    (hsp : Submodule.span ℝ (A : Set W) = ⊤) (hs : IsSemiChar H A α) {F : W → ℂ} (hc : Continuous F)
    (hF : F ∈ fixedBy H α A) (x : W) : mean μ A (rho H (opU H x F)) = mean μ A (rho H F) := by
  obtain ⟨n, b, hb⟩ := exists_basis hA hsp
  rw [mean_eq μ b hb fun y hy z => by rw [rho_opU hH, rho_opU hH, add_right_comm, rho_add_of_fixed hH hs hF hy],
    mean_eq μ b hb fun y hy z => rho_add_of_fixed hH hs hF hy z]
  simp only [rho_opU hH]
  exact average_fundamentalDomain_eq_real μ b b _ (continuous_rho hH hc)
    (fun y hy z => rho_add_of_fixed hH hs hF (hb.le hy) z) le_rfl x

theorem integral_dens_eq_zero (hH : IsHerm H) {A : AddSubgroup W} (hd : IsSelfDual H A) (hs : IsSemiChar H A α)
    {F : W → ℂ} (hF : F ∈ fixedBy H α A) {κ : Type} [Fintype κ] (b : Module.Basis κ ℝ W)
    (hb : ∀ x ∈ Submodule.span ℤ (Set.range b), x ∈ A) (y y' : W)
    (hint : ∀ x ∈ Submodule.span ℤ (Set.range b), chi H x (y - y') = 1) (hne : y - y' ∉ A) :
    ∫ z in ZSpan.fundamentalDomain b, dens H (opU H y F) (opU H y' F) z ∂μ = 0 := by
  obtain ⟨x, hx, hx'⟩ : ∃ p ∈ A, chi H p (y - y') ≠ 1 := by
    by_contra hc
    push Not at hc
    exact hne (hd.le fun p hp => int_swap hH ((chi_eq_one_iff _ _).1 (hc p hp)))
  have h := setIntegral_fundamentalDomain_add_right μ b (dens H (opU H y F) (opU H y' F))
    (fun γ hγ v => by rw [dens_add_of_fixed hH hs hF y y' (hb γ hγ), hint γ hγ, one_mul]) x
  simp only [dens_add_of_fixed hH hs hF y y' hx] at h
  rw [integral_const_mul] at h
  have h2 := sub_eq_zero.2 h
  rw [← sub_one_mul] at h2
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hx')

theorem mean_inter (hH : IsHerm H) {A₁ A₂ : AddSubgroup W} [Finite (A₂ ⧸ A₁.addSubgroupOf A₂)]
    (hA₁ : DiscreteTopology A₁) (hsp₁ : Submodule.span ℝ (A₁ : Set W) = ⊤)
    (hA₂ : DiscreteTopology A₂) (hsp₂ : Submodule.span ℝ (A₂ : Set W) = ⊤)
    (hd₁ : IsSelfDual H A₁) (hs₁ : IsSemiChar H A₁ α) (hd₂ : IsSelfDual H A₂) (hs₂ : IsSemiChar H A₂ α)
    {F : W → ℂ} (hc : Differentiable ℂ F) (hF : F ∈ fixedBy H α A₁) :
    mean μ A₂ (rho H (inter H α A₁ A₂ F)) = mean μ A₁ (rho H F) := by
  classical
  have := Fintype.ofFinite (A₂ ⧸ A₁.addSubgroupOf A₂)
  obtain ⟨n₁, b₁, hb₁⟩ := exists_basis hA₁ hsp₁
  obtain ⟨n₂, b₂, hb₂⟩ := exists_basis hA₂ hsp₂
  obtain ⟨n, b, hb⟩ := exists_basis (A := A₁ ⊓ A₂)
    (DiscreteTopology.of_subset (s := (A₂ : Set W)) hA₂ fun x hx => hx.2) (span_inf_eq_top hsp₂)
  have hm := inter_mem_fixedBy hH hs₁ hd₂ hs₂ hF
  have hle₁ : Submodule.span ℤ (Set.range b) ≤ Submodule.span ℤ (Set.range b₁) := fun x hx =>
    hb₁.ge (hb.le hx).1
  have hle₂ : Submodule.span ℤ (Set.range b) ≤ Submodule.span ℤ (Set.range b₂) := fun x hx =>
    hb₂.ge (hb.le hx).2
  have e1 := average_fundamentalDomain_eq_real μ b₂ b _
    (continuous_rho hH (differentiable_inter (H := H) (α := α) A₁ A₂ hc).continuous)
    (fun y hy z => rho_add_of_fixed hH hs₂ hm (hb₂.le hy) z) hle₂ 0
  have e2 := fun a => average_fundamentalDomain_eq_real μ b₁ b _ (continuous_rho hH hc.continuous)
    (fun y hy z => rho_add_of_fixed hH hs₁ hF (hb₁.le hy) z) hle₁ a
  simp only [add_zero] at e1
  rw [mean_eq μ b₂ hb₂ fun y hy z => rho_add_of_fixed hH hs₂ hm hy z,
    mean_eq μ b₁ hb₁ fun y hy z => rho_add_of_fixed hH hs₁ hF hy z, ← e1]
  set m : ℝ := (Fintype.card (A₂ ⧸ A₁.addSubgroupOf A₂) : ℝ) with hmdef
  have hpos : 0 < m := by rw [hmdef]; exact_mod_cast Fintype.card_pos
  set r : A₂ ⧸ A₁.addSubgroupOf A₂ → W := fun c => ((Quotient.out c : A₂) : W) with hr
  have hrm : ∀ c, r c ∈ A₂ := fun c => (Quotient.out c : A₂).2
  have e3 : ∫ v in ZSpan.fundamentalDomain b, rho H (inter H α A₁ A₂ F) v ∂μ =
      m⁻¹ * ∑ c, ∫ v in ZSpan.fundamentalDomain b, rho H F (v + r c) ∂μ := by
    apply Complex.ofReal_injective
    rw [← integral_complex_ofReal]
    have hpt : ∀ v, ((rho H (inter H α A₁ A₂ F) v : ℝ) : ℂ) =
        (m⁻¹ : ℝ) * ∑ c, ∑ c', (α (r c) * α (r c')) * dens H (opU H (r c) F) (opU H (r c') F) v := by
      intro v
      have h2 : ((Real.sqrt m : ℝ) : ℂ)⁻¹ * ((Real.sqrt m : ℝ) : ℂ)⁻¹ = (m⁻¹ : ℝ) := by
        rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt hpos.le, Complex.ofReal_inv]
      rw [rho_eq hH, inter_eq, ← h2]
      simp only [dens, map_mul, map_sum, map_inv₀, Complex.conj_ofReal]
      rw [mul_mul_mul_comm, Finset.sum_mul_sum, mul_assoc]
      congr 1
      simp only [Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
      rw [alpha_conj hs₂ (hrm c')]
      ring
    have hint : ∀ c c', IntegrableOn (fun v => (α (r c) * α (r c')) *
          dens H (opU H (r c) F) (opU H (r c') F) v) (ZSpan.fundamentalDomain b) μ := fun c c' =>
      integrableOn_fundamentalDomain_of_continuous μ b _
        (continuous_const.mul (continuous_dens hH (differentiable_opU hc _).continuous
          (differentiable_opU hc _).continuous))
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
      integral_finset_sum _ fun y _ => integrable_finset_sum _ fun y' _ => hint y y',
      Complex.ofReal_mul, Complex.ofReal_sum]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [integral_finset_sum _ fun y' _ => hint c y', Finset.sum_eq_single_of_mem c (Finset.mem_univ _)]
    · rw [alpha_sq hs₂ (hrm c), ← integral_complex_ofReal]
      simp only [one_mul, ← rho_eq hH, rho_opU hH]
    · intro c' _ hne
      rw [integral_const_mul, integral_dens_eq_zero μ hH hd₁ hs₁ hF b (fun x hx => (hb.le hx).1) _ _
        (fun x hx => (chi_eq_one_iff _ _).2 (hd₂.ge (hb.le hx).2 _ (A₂.sub_mem (hrm c) (hrm c'))))
        (fun h => hne ?_), mul_zero]
      rw [← QuotientAddGroup.out_eq' c, ← QuotientAddGroup.out_eq' c', QuotientAddGroup.eq,
        AddSubgroup.mem_addSubgroupOf]
      simpa [hr, neg_add_eq_sub] using h
  rw [setAverage_eq, e3, smul_eq_mul, mul_left_comm, Finset.mul_sum]
  simp only [← smul_eq_mul, ← setAverage_eq, e2]
  simp [← hmdef, hpos.ne']

end Analytic

end GlobalTheory.ThetaInter
