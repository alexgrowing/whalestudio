import Development.AutomorphicArithmetic.QuadraticCharacters.LogDerivAtOne

open ArithmeticFunction

namespace HostParam

abbrev PrimChar : Type := Σ M : ℕ, DirichletCharacter ℂ M

structure HostType where

  eps : ℝ
  eps_pos : 0 < eps
  eps_lt : eps < 1 / 52

  J : ℝ
  one_le_J : 1 ≤ J

  zp : ℝ → ℝ
  zp_ge : ∀ X : ℝ, 1 ≤ X → X ^ (eps / (5 * J)) * Real.log (X ^ (1 / J)) ^ 2 ≤ zp X
  zp_le : ∀ X : ℝ, 1 ≤ X → zp X ≤ X ^ (eps / (5 * J)) * Real.log X ^ 2

  kept : Set PrimChar
  kept_finite : kept.Finite
  kept_pos : ∀ χ ∈ kept, 0 < χ.1
  kept_primitive : ∀ χ ∈ kept, χ.2.IsPrimitive
  kept_conj : ∀ χ ∈ kept, (⟨χ.1, χ.2⁻¹⟩ : PrimChar) ∈ kept
  one_mem_kept : (⟨1, 1⟩ : PrimChar) ∈ kept

  P0 : ℕ
  P0_pos : 0 < P0

  psK : Option PrimChar
  psK_spec : ∀ ψ ∈ psK, ψ ∈ kept ∧ ψ.2 ≠ 1 ∧ ψ.2 ^ 2 = 1 ∧ ψ.2.Odd

  Ct : ℝ
  t : ℝ → ℕ
  t_le : ∀ x : ℝ, 1 ≤ x → (t x : ℝ) ≤ x ^ Ct

  o : ℕ
  o_pos : 0 < o

  rrBound : ℕ

  cA : ℝ
  cA_pos : 0 < cA

  CB : ℝ

namespace HostType

variable (T : HostType)

def SM (l : ℕ) : Prop :=
  l.Prime ∧ l ∣ 2 * T.P0 * ∏ᶠ (χ : PrimChar) (_ : χ ∈ T.kept), χ.1

noncomputable def aStar : ℝ := 1 / (3 * (T.o : ℝ) + 1)

def TopSized : Prop :=
  (∃ j : ℕ, T.J = j) ∧ ∀ X : ℝ, T.zp X = X ^ (T.eps / (5 * T.J)) * Real.log X ^ 2

def BottomSized : Prop :=
  ∀ X : ℝ, T.zp X = X ^ (T.eps / (5 * T.J)) * Real.log (X ^ (1 / T.J)) ^ 2

def StandardT : Prop := T.Ct = 401 ∧ ∀ x : ℝ, T.t x = ⌊x ^ (401 : ℝ)⌋₊

end HostType

noncomputable def zR (T : HostType) (X : ℝ) : ℝ := X ^ (T.eps / (5 * T.J))

noncomputable def zR' (T : HostType) (X : ℝ) : ℝ := T.zp X

def IsRangeText (T : HostType) (x : ℝ) (e : ℕ) : Prop :=
  x ^ (2 + 8 * T.eps) / 2 ≤ (2 ^ e : ℝ) ∧ (2 ^ e : ℝ) ≤ 2 * x ^ (2 + 8 * T.eps)

def IsRangeN (T : HostType) (x : ℝ) (e : ℕ) : Prop :=
  2 ≤ e ∧ x ^ (2 + 8 * T.eps) / (2 * T.o) ≤ (2 ^ e : ℝ) ∧ (2 ^ e : ℝ) ≤ 2 * x ^ (2 + 8 * T.eps)

theorem IsRangeText.isRangeN {T : HostType} {x : ℝ} {e : ℕ} (h : IsRangeText T x e) (hx : 3 ≤ x) :
    IsRangeN T x e := by
  have h1 : x ^ (2 : ℝ) ≤ x ^ (2 + 8 * T.eps) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [T.eps_pos])
  rw [Real.rpow_two] at h1
  have h2 := h.1
  have ho : (1 : ℝ) ≤ T.o := by exact_mod_cast T.o_pos
  refine ⟨?_, le_trans (div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)) h2, h.2⟩
  by_contra hlt
  have h4 : (2 : ℝ) ^ e ≤ 2 ^ 1 := pow_le_pow_right₀ (by norm_num) (by omega)
  nlinarith

abbrev GalRealCyclotomic (n : ℕ) : Type := (ZMod (4 * n))ˣ ⧸ Subgroup.zpowers (-1 : (ZMod (4 * n))ˣ)

structure PreHost (T : HostType) (X x : ℝ) where

  one_le_X : 1 ≤ X
  x_ge : X ^ (1 / (T.J : ℝ)) ≤ x
  x_le : x ≤ X
  e : ℕ
  range_n : IsRangeN T x e

  E : AbField
  not_real : ¬ E.IsReal

  d : ℕ
  d_prime : d.Prime
  d_mod : d % 16 = 7
  d_dvd : d ∣ E.N
  K_le : E.chOf d d_dvd ∈ E.chars

  card_inertia_d : Nat.card (E.inertia d) = 2

  ps : DirichletCharacter ℂ E.N
  ps_mem : ps ∈ E.chars
  ps_ne_one : ps ≠ 1
  ps_sq : ps ^ 2 = 1
  ps_odd : ps.Odd
  ps_inertia : ∀ u ∈ E.inertiaUnits d, ps (u : ZMod E.N) = 1

  four_n_dvd : 4 * 2 ^ e ∣ E.N
  attached_subfield_le_adjoin_simple : ∀ u ∈ E.H, ZMod.unitsMap four_n_dvd u = 1 ∨ ZMod.unitsMap four_n_dvd u = -1

  A0 : Subgroup E.Gal
  base_exponent_le_a : A0 ≤ (E.toGalChar (E.chOf d d_dvd) K_le).ker ⊓ (E.toGalChar ps ps_mem).ker
  A0_inf_stabilizer_trivial : ∀ u : (ZMod E.N)ˣ, E.res u ∈ A0 →
    (QuotientGroup.mk (ZMod.unitsMap four_n_dvd u) : GalRealCyclotomic (2 ^ e)) = 1 → E.res u = 1
  index_A0_eq_o : (A0.subgroupOf ((E.toGalChar (E.chOf d d_dvd) K_le).ker ⊓
      (E.toGalChar ps ps_mem).ker)).index = T.o

  z_ge : 11 ≤ zR T X
  split_small : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ zR T X → SplitsIn d p
  split_ram : ∀ l : ℕ, l.Prime → l ≠ d → E.Ramified l → SplitsIn d l

  ram_kinds : ∀ l : ℕ, l.Prime → l ≠ d → E.Ramified l →
    ((l : ℝ) ≤ zR T X / 4 ∧ T.SM l) ∨
      (zR T X / 2 < Real.log l ∧ Nat.card (E.inertia l) = 2)
  large_unique : ∀ l l' : ℕ, l.Prime → l'.Prime → l ≠ d → l' ≠ d → E.Ramified l →
    E.Ramified l' → zR T X / 2 < Real.log l → zR T X / 2 < Real.log l' → l = l'

  log_d_gt : zR' T X / 2 < Real.log d
  log_d_le : Real.log d ≤ zR' T X
  log_large_le : ∀ l : ℕ, l.Prime → l ≠ d → E.Ramified l → zR T X / 2 < Real.log l →
    Real.log l ≤ zR T X
  Nsharp : ℕ
  cond_dvd : E.conductor ∣ Nsharp
  log_Nsharp : Real.log Nsharp ≤ 3 * zR' T X

  qs : ℕ
  qs_prime : qs.Prime
  qs_ne : qs ≠ d
  qs_mod : qs % 8 = 3
  qs_split : SplitsIn d qs
  log_qs_gt : zR T X / 2 < Real.log qs
  log_qs_le : Real.log qs ≤ zR T X
  large_eq_qs : ∀ l : ℕ, l.Prime → l ≠ d → E.Ramified l → zR T X / 2 < Real.log l → l = qs
  Nsharp_eq : Nsharp = Nat.lcm E.conductor qs

  rr : ℕ
  rr' : ℕ
  rr_prime : rr.Prime
  rr'_prime : rr'.Prime
  rr_odd : rr ≠ 2
  rr_lt : rr < rr'
  rr'_lt : rr' < 2 * rr
  rr_unram : ¬ E.Ramified rr
  rr'_unram : ¬ E.Ramified rr'
  rr'_le_alt : (rr' : ℝ) ≤ zR T X
  rr'_le : rr' ≤ T.rrBound

end HostParam
