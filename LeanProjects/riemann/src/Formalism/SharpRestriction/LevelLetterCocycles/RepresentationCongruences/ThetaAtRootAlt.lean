import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsGLLatBasisOfIsSplitEquiv

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.LTB

open PowerSeries

section Roots

variable {O : Type*} [CommRing O] [IsDomain O] [IsLocalRing O]

theorem root_eq (l : ℕ) [hp : Fact l.Prime] {x₀ y w : O} (hx : x₀ ≠ 0)
    (hrx : (1 + x₀) ^ l = 1) (hry : (1 + y) ^ l = 1)
    (hw : w ∈ IsLocalRing.maximalIdeal O) (hyw : y - x₀ = x₀ * w) : y = x₀ := by
  have hl0 : 0 < l := hp.out.pos
  have hζ1 : (1 + x₀) ≠ 1 := fun h => hx (by linear_combination h)
  have hprim : IsPrimitiveRoot (1 + x₀) l := by
    have h := IsPrimitiveRoot.orderOf (1 + x₀)
    rwa [orderOf_eq_prime hrx hζ1] at h
  have hζu : IsUnit (1 + x₀) := by
    first
    | exact hprim.isUnit hl0
    | exact hprim.isUnit hl0.ne'
  have hwu : ¬ IsUnit w := (IsLocalRing.mem_maximalIdeal w).1 hw
  obtain ⟨i, hil, hi⟩ : ∃ i < l, (1 + x₀) ^ i = 1 + y := by
    first
    | exact hprim.eq_pow_of_pow_eq_one hry
    | exact hprim.eq_pow_of_pow_eq_one hry hl0
  rcases i with _ | j
  · exfalso
    have hy0 : y = 0 := by linear_combination -hi
    have hxw : x₀ * (1 + w) = 0 := by linear_combination -hyw + hy0
    rcases mul_eq_zero.1 hxw with h | h
    · exact hx h
    · apply hwu
      have hw1 : w = -1 := by linear_combination h
      rw [hw1]
      exact isUnit_one.neg
  · rcases j with _ | j
    · linear_combination -hi
    · exfalso
      have hk0 : 0 < j + 1 := Nat.succ_pos j
      have hkl : j + 1 < l := by omega
      have hcop : (j + 1).Coprime l :=
        Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).2 (Nat.not_dvd_of_pos_of_lt hk0 hkl))
      have hprim' := hprim.pow_of_coprime (j + 1) hcop
      obtain ⟨m, -, hm⟩ : ∃ m < l, ((1 + x₀) ^ (j + 1)) ^ m = 1 + x₀ := by
        first
        | exact hprim'.eq_pow_of_pow_eq_one hrx
        | exact hprim'.eq_pow_of_pow_eq_one hrx hl0
      have e1 := geom_sum_mul ((1 + x₀) ^ (j + 1)) m
      have e2 := geom_sum_mul (1 + x₀) (j + 1)
      rw [hm] at e1
      set S := ∑ i ∈ Finset.range m, ((1 + x₀) ^ (j + 1)) ^ i with hS
      set v := ∑ i ∈ Finset.range (j + 1), (1 + x₀) ^ i with hv
      have hSv0 : x₀ * (S * v - 1) = 0 := by linear_combination S * e2 + e1
      have hSv : S * v = 1 := by
        have := (mul_eq_zero.1 hSv0).resolve_left hx
        linear_combination this
      have hvu : IsUnit v := ⟨⟨v, S, by rw [mul_comm]; exact hSv, hSv⟩, rfl⟩
      have hwz : x₀ * (w - (1 + x₀) * v) = 0 := by
        linear_combination -hyw - hi - (1 + x₀) * e2
      have hw' : w = (1 + x₀) * v := by
        have := (mul_eq_zero.1 hwz).resolve_left hx
        linear_combination this
      exact hwu (hw' ▸ hζu.mul hvu)

end Roots

section Main

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

theorem mem_max (l : ℕ) [hp : Fact l.Prime] (hl : ((l : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
    {x₀ : O} (hroot : (1 + x₀) ^ l = 1) : x₀ ∈ IsLocalRing.maximalIdeal O := by
  have hk : ((l : ℕ) : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O)]
    exact (IsLocalRing.residue_eq_zero_iff _).2 hl
  haveI : CharP (IsLocalRing.ResidueField O) l := by
    first
    | exact (CharP.charP_iff_prime_eq_zero hp.out).2 hk
    | exact ringChar.of_eq ((hp.out.eq_one_or_self_of_dvd _ (ringChar.dvd hk)).resolve_left
        CharP.ringChar_ne_one)
  have h := congrArg (IsLocalRing.residue O) hroot
  simp only [map_pow, map_add, map_one] at h
  rw [add_pow_char, one_pow] at h
  have h2 : (IsLocalRing.residue O x₀) ^ l = 0 := by linear_combination h
  exact (IsLocalRing.residue_eq_zero_iff _).1 (pow_eq_zero_iff hp.out.ne_zero |>.1 h2)

theorem map_res {x₀ : O} (hx : x₀ ∈ IsLocalRing.maximalIdeal O) :
    PowerSeries.map (IsLocalRing.residue O) (X - C x₀) = X := by
  have h : IsLocalRing.residue O x₀ = 0 := (IsLocalRing.residue_eq_zero_iff x₀).2 hx
  rw [map_sub, PowerSeries.map_X, PowerSeries.map_C, h, map_zero, sub_zero]

theorem map_mk {x₀ : O} (hx : x₀ ∈ IsLocalRing.maximalIdeal O) :
    PowerSeries.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)) (X - C x₀) = X := by
  have h : Ideal.Quotient.mk (IsLocalRing.maximalIdeal O) x₀ = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 hx
  rw [map_sub, PowerSeries.map_X, PowerSeries.map_C, h, map_zero, sub_zero]

theorem decomp {x₀ : O} (hx : x₀ ∈ IsLocalRing.maximalIdeal O) (p : O⟦X⟧) :
    ∃ c : O, ∃ q : O⟦X⟧, p = (X - C x₀) * q + C c := by
  have hord : PowerSeries.map (IsLocalRing.residue O) (X - C x₀) ≠ 0 := by
    rw [map_res hx]; exact PowerSeries.X_ne_zero
  obtain ⟨q, r, hqr⟩ := PowerSeries.exists_isWeierstrassDivision (f := p) (g := X - C x₀) hord
  have hdeg := hqr.1
  first
  | rw [map_mk hx, PowerSeries.order_X] at hdeg
  | rw [map_res hx, PowerSeries.order_X] at hdeg
  simp at hdeg
  have hrc : (r : O⟦X⟧) = C (r.coeff 0) := by
    first
    | (have hr0 : r.degree ≤ 0 := by
          first
          | exact Nat.WithBot.lt_one_iff_le_zero.1 hdeg
          | exact Order.le_of_lt_succ hdeg
       conv_lhs => rw [Polynomial.eq_C_of_degree_le_zero hr0]
       exact Polynomial.coe_C _)
    | (ext n
       rcases n with _ | n
       · simp
       · rw [Polynomial.coeff_coe, PowerSeries.coeff_C, if_neg (Nat.succ_ne_zero n)]
         exact Polynomial.coeff_eq_zero_of_degree_lt
           (lt_of_lt_of_le hdeg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))))
  refine ⟨r.coeff 0, q, ?_⟩
  rw [← hrc]
  exact hqr.2

theorem uniq {x₀ : O} (hx : x₀ ∈ IsLocalRing.maximalIdeal O) {c : O}
    (hc : C c ∈ Ideal.span {X - C x₀}) : c = 0 := by
  obtain ⟨f, hf⟩ := Ideal.mem_span_singleton'.1 hc
  have hrec : ∀ n, coeff n f = x₀ * coeff (n + 1) f := by
    intro n
    have h := congrArg (fun g => coeff (n + 1) g) hf
    simp only [mul_sub, map_sub, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mul_C,
      PowerSeries.coeff_C, Nat.succ_ne_zero, if_false] at h
    linear_combination h
  have hpow : ∀ n, coeff 0 f = x₀ ^ n * coeff n f := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [ih, hrec n]; ring
  have hall : ∀ n : ℕ, coeff 0 f ≡ 0 [SMOD ((IsLocalRing.maximalIdeal O) ^ n • ⊤ : Submodule O O)] := by
    intro n
    rw [SModEq.zero]
    have hmem := Submodule.smul_mem_smul
      (Ideal.mul_mem_right (coeff n f) _ (Ideal.pow_mem_pow hx n)) (Submodule.mem_top : (1 : O) ∈ ⊤)
    rw [hpow n]
    simpa using hmem
  have hcoef0 : coeff 0 f = 0 := by
    first
    | exact IsHausdorff.haus inferInstance _ hall
    | exact IsHausdorff.haus' _ hall
  have h0 := congrArg (fun g => coeff 0 g) hf
  simp only [mul_sub, map_sub, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mul_C, hcoef0,
    PowerSeries.coeff_zero_C] at h0
  linear_combination -h0

def Fs (l : ℕ) (x₀ : O) (a : O⟦X⟧) : O⟦X⟧ :=
  ∑ i ∈ Finset.range l, (1 + a) ^ i * (1 + C x₀) ^ (l - 1 - i)

theorem Fs_mul (l : ℕ) {x₀ : O} (hroot : (1 + x₀) ^ l = 1) (a : O⟦X⟧) :
    (1 + a) ^ l - 1 = Fs l x₀ a * (a - C x₀) := by
  have hy : (1 + C x₀ : O⟦X⟧) ^ l = 1 := by
    simpa [map_pow, map_add, map_one] using congrArg (C : O →+* O⟦X⟧) hroot
  have h := geom_sum₂_mul (1 + a) (1 + C x₀) l
  rw [hy] at h
  unfold Fs
  rw [← h]
  congr 1
  ring

private theorem algHom_C_eq_C (h : O⟦X⟧ →ₐ[O] O⟦X⟧) (a : O) : h (C a) = C a := by
  first
  | (rw [show (C a : O⟦X⟧) = a • (1 : O⟦X⟧) by rw [PowerSeries.smul_eq_C_mul, mul_one], map_smul,
      map_one])
  | (have e := h.commutes a; simpa using e)

private theorem coeff_one_one_add_X_pow_eq (n : ℕ) : coeff 1 ((1 + X : O⟦X⟧) ^ n) = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : coeff 1 ((1 + X : O⟦X⟧) ^ n * X) = 1 := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_mul_X]
      simp
    rw [pow_succ, mul_add, mul_one, map_add, ih, e]
    push_cast
    ring

theorem theta_at_root (l : ℕ) [hp : Fact l.Prime] (hl : ((l : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
    (φ₀ γ : O⟦X⟧ →ₐ[O] O⟦X⟧) (hφ₀ : φ₀ X = (1 + X) ^ l - 1) (hc : ∀ f, φ₀ (γ f) = γ (φ₀ f))
    (χ : O) (h0 : constantCoeff (γ X) = 0) (h1 : coeff 1 (γ X) = χ)
    (hχ : χ - 1 ∈ Ideal.span {((l : ℕ) : O)})
    (x₀ : O) (hx₀ : x₀ ≠ 0) (hroot : (1 + x₀) ^ l = 1)
    (Q : O⟦X⟧) (hQ : X * Q = (1 + X) ^ l - 1) (u : O⟦X⟧) (hu : IsUnit u) (θ : O⟦X⟧)
    (hθ : γ (u * Q) = u * Q * θ) :
    θ - C χ ∈ Ideal.span {X - C x₀} := by
  set I : Ideal O⟦X⟧ := Ideal.span {X - C x₀} with hI
  have hxm : x₀ ∈ IsLocalRing.maximalIdeal O := mem_max l hl hroot
  have hgen : X - C x₀ ∈ I := Ideal.subset_span (Set.mem_singleton _)
  have hinj : ∀ a b : O, Ideal.Quotient.mk I (C a) = Ideal.Quotient.mk I (C b) → a = b := by
    intro a b h
    rw [Ideal.Quotient.eq, ← map_sub] at h
    exact sub_eq_zero.1 (uniq hxm h)
  have hsurj : ∀ f : O⟦X⟧, ∃ c : O, Ideal.Quotient.mk I f = Ideal.Quotient.mk I (C c) := by
    intro f
    obtain ⟨c, q, hq⟩ := decomp hxm f
    refine ⟨c, ?_⟩
    rw [Ideal.Quotient.eq, hq, add_sub_cancel_right]
    exact Ideal.mul_mem_right _ _ hgen
  have hXI : Ideal.Quotient.mk I X = Ideal.Quotient.mk I (C x₀) := by
    rw [Ideal.Quotient.eq]; exact hgen
  have hφX : φ₀ X ∈ I := by
    rw [hφ₀, Fs_mul l hroot X]
    exact Ideal.mul_mem_left _ _ hgen
  have hL2 : ∀ f, Ideal.Quotient.mk I (φ₀ f) = Ideal.Quotient.mk I (C (constantCoeff f)) := by
    intro f
    obtain ⟨h, hh⟩ : X ∣ f - C (constantCoeff f) := by
      rw [PowerSeries.X_dvd_iff]; simp
    rw [Ideal.Quotient.eq, ← algHom_C_eq_C φ₀, ← map_sub, hh, map_mul]
    exact Ideal.mul_mem_right _ _ hφX
  obtain ⟨g₁, hg₁⟩ : X ∣ γ X := PowerSeries.X_dvd_iff.2 h0
  have hg₁c : constantCoeff g₁ = χ := by
    have e : coeff (0 + 1) (γ X) = χ := h1
    rw [hg₁, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply] at e
    exact e
  obtain ⟨h₂, hh₂⟩ : X ∣ g₁ - C χ := by
    rw [PowerSeries.X_dvd_iff]; simp [hg₁c]
  obtain ⟨d, hd⟩ := hsurj h₂
  obtain ⟨b, hb⟩ := hsurj (γ X)
  have hb' : b = x₀ * (χ + x₀ * d) := by
    apply hinj
    have eg : g₁ = C χ + X * h₂ := by rw [← hh₂]; ring
    rw [← hb, hg₁, eg]
    simp only [map_add, map_mul, hXI, hd]
  have hbroot : (1 + b) ^ l = 1 := by
    have e1 : γ (φ₀ X) = (1 + γ X) ^ l - 1 := by
      simp only [hφ₀, map_sub, map_pow, map_add, map_one]
    have e2 : Ideal.Quotient.mk I (γ (φ₀ X)) = 0 := by
      rw [← hc, hL2, h0, map_zero, map_zero]
    rw [e1] at e2
    have e3 : Ideal.Quotient.mk I ((1 + γ X) ^ l - 1) =
        Ideal.Quotient.mk I (C ((1 + b) ^ l - 1)) := by
      simp only [map_sub, map_pow, map_add, map_one, hb]
    have h3 : (1 + b) ^ l - 1 = 0 := hinj _ _ (by rw [← e3, e2, map_zero, map_zero])
    linear_combination h3
  have hbx : b = x₀ := by
    refine root_eq l hx₀ hroot hbroot (w := χ - 1 + x₀ * d) ?_ ?_
    · refine Ideal.add_mem _ ?_ (Ideal.mul_mem_right _ _ hxm)
      exact (Ideal.span_singleton_le_iff_mem _).2 hl hχ
    · rw [hb']; ring
  have hγX : Ideal.Quotient.mk I (γ X) = Ideal.Quotient.mk I (C x₀) := by rw [hb, hbx]
  have hL4 : ∀ f, Ideal.Quotient.mk I (γ f) = Ideal.Quotient.mk I f := by
    intro f
    obtain ⟨c, q, hq⟩ := decomp hxm f
    simp only [hq, map_add, map_mul, map_sub, algHom_C_eq_C γ, hγX, hXI, sub_self, zero_mul,
      zero_add]
  have hXQ : X * Q ≠ 0 := by
    rw [hQ]
    intro h
    have e := congrArg (fun f => coeff 1 f) h
    have hl' : ((l : ℕ) : O) = 0 := by simpa [coeff_one_one_add_X_pow_eq] using e
    exact hp.out.ne_zero (by exact_mod_cast hl')
  have key : X * Q * (g₁ * u * θ) = X * Q * (γ u * φ₀ g₁) := by
    have e1 : γ (X * (u * Q)) = X * g₁ * (u * Q * θ) := by rw [map_mul, hθ, hg₁]
    have e2 : γ (X * (u * Q)) = γ u * (X * Q * φ₀ g₁) := by
      rw [show X * (u * Q) = u * (X * Q) by ring, map_mul, hQ, ← hφ₀, ← hc, hg₁, map_mul]
    calc X * Q * (g₁ * u * θ) = X * g₁ * (u * Q * θ) := by ring
      _ = γ (X * (u * Q)) := e1.symm
      _ = γ u * (X * Q * φ₀ g₁) := e2
      _ = X * Q * (γ u * φ₀ g₁) := by ring
  have key2 := mul_left_cancel₀ hXQ key
  obtain ⟨e, he⟩ := hsurj g₁
  have he1 : e = 1 := by
    have hxe : x₀ * e = x₀ * 1 := by
      apply hinj
      have h := hγX
      rw [hg₁, map_mul, hXI, he] at h
      simpa [map_mul] using h
    exact mul_left_cancel₀ hx₀ hxe
  have hg1 : Ideal.Quotient.mk I g₁ = 1 := by rw [he, he1, map_one, map_one]
  have hπ := congrArg (Ideal.Quotient.mk I) key2
  simp only [map_mul] at hπ
  rw [hL4 u, hL2 g₁, hg₁c, hg1, one_mul] at hπ
  have hθ' : Ideal.Quotient.mk I θ = Ideal.Quotient.mk I (C χ) := (hu.map _).mul_left_cancel hπ
  exact Ideal.Quotient.eq.1 hθ'

end Main

end Formalism.MainNotions.N.FrobeniusPowerSeries.LTB
