import Mathlib
import Formalism.LocalToGlobal.Columns.ScaledRamifiedLattice
import Formalism.LocalToGlobal.Columns.ColFormsLemmas
import Formalism.LocalToGlobal.Columns.ColFormsInst
import Formalism.LocalToGlobal.Columns.BaseInst

open NumberField IsDedekindDomain IntermediateField Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.Host Formalism.L2.DIV

section Res

variable {A : Type} [CommRing A] [Finite A] {p : ℕ}

def owedC_res (hp : p.Prime) (h : Nat.card A = p) : A ≃+* ZMod p :=
  letI := Fintype.ofFinite A
  (ZMod.ringEquivOfPrime A hp (by rw [← Nat.card_eq_fintype_card]; exact h)).symm

theorem owedC_res_intCast (hp : p.Prime) (h : Nat.card A = p) (a : ℤ) :
    owedC_res hp h (a : A) = (a : ZMod p) := map_intCast _ _

theorem owedC_exists_int (hp : p.Prime) (h : Nat.card A = p) (x : A) : ∃ a : ℤ, x = (a : A) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  refine ⟨((owedC_res hp h x).val : ℤ), ?_⟩
  apply (owedC_res hp h).injective
  rw [owedC_res_intCast]
  simp

theorem owedC_intCast_eq_iff (hp : p.Prime) (h : Nat.card A = p) (a b : ℤ) :
    (a : A) = (b : A) ↔ (p : ℤ) ∣ a - b := by
  rw [← (owedC_res hp h).injective.eq_iff, owedC_res_intCast, owedC_res_intCast,
    ZMod.intCast_eq_intCast_iff_dvd_sub, ← dvd_neg, neg_sub]

variable {K : Type} [Field K]

theorem owedC_zpow_emod {ζ : K} (hζ : ζ ^ p = 1) (a : ℤ) : ζ ^ (a % (p : ℤ)) = ζ ^ a := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  have h0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne'] at hζ
    exact zero_ne_one hζ
  conv_rhs => rw [← Int.emod_add_mul_ediv a p, zpow_add₀ h0, zpow_mul, zpow_natCast, hζ, one_zpow, mul_one]

def owedC_chr (hp : p.Prime) (h : Nat.card A = p) {ζ : K} (hζ : ζ ^ p = 1) : AddChar A K :=
  haveI : NeZero p := ⟨hp.ne_zero⟩
  (AddChar.zmodChar p hζ).compAddMonoidHom (owedC_res hp h).toAddEquiv.toAddMonoidHom

theorem owedC_chr_intCast (hp : p.Prime) (h : Nat.card A = p) {ζ : K} (hζ : ζ ^ p = 1) (a : ℤ) :
    owedC_chr hp h hζ (a : A) = ζ ^ a := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have e : owedC_chr hp h hζ (a : A) = AddChar.zmodChar p hζ (owedC_res hp h (a : A)) := rfl
  rw [e, owedC_res_intCast, AddChar.zmodChar_apply, ← owedC_zpow_emod hζ a, ← ZMod.val_intCast, zpow_natCast]

end Res

section Chars

variable {X : Fields} {Pr : Primes X}

theorem card_quotient_eq_prime (hPr : Pr.Ok) (u : Pr.Word) (P : {P // P ∈ Pr.vT u}) :
    Nat.card (𝓞 X.E ⧸ P.1.asIdeal) = Pr.T u := by
  rw [← hPr.vT_norm u P.1 P.2, Ideal.absNorm_apply, Submodule.cardQuot_apply]

def CharT.ofRootMul (hPr : Pr.Ok) (ζ : Pr.Word → X.K) (hζ : ∀ u, ζ u ^ Pr.T u = 1)
    (x : ∀ (u : Pr.Word) (P : {P // P ∈ Pr.vT u}), 𝓞 X.E ⧸ P.1.asIdeal) : CharT X Pr where
  psiT u P := AddChar.mulShift (owedC_chr (hPr.T_prime u) (card_quotient_eq_prime hPr u P) (hζ u)) (x u P)

def CharT.ofRoot (hPr : Pr.Ok) (ζ : Pr.Word → X.K) (hζ : ∀ u, ζ u ^ Pr.T u = 1) : CharT X Pr :=
  CharT.ofRootMul hPr ζ hζ fun _ _ => 1

end Chars

section Weil

variable {X : Fields} {Pr : Primes X}

def CharT.WeilTied (Ps : CharT X Pr) (σ₀ : X.K →+* ℂ) (xi0 : X.E) : Prop :=
  ∀ (u : Pr.Word) (P : {P // P ∈ Pr.vT u}) (a b : ℤ),
    redP P.1 xi0 * (a : 𝓞 X.E ⧸ P.1.asIdeal) = (b : 𝓞 X.E ⧸ P.1.asIdeal) →
      σ₀ (Ps.psiT u P (a : 𝓞 X.E ⧸ P.1.asIdeal)) = Complex.exp (2 * Real.pi * Complex.I * b / Pr.T u)

def XiUnitT (Pr : Primes X) (xi0 : X.E) : Prop :=
  ∀ u : Pr.Word, ∃ b : ℤ, ¬ (Pr.T u : ℤ) ∣ b ∧
    ∀ P : {P // P ∈ Pr.vT u}, redP P.1 xi0 = (b : 𝓞 X.E ⧸ P.1.asIdeal)

theorem owedC_exp_zpow (n : ℕ) (b : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I / n) ^ b = Complex.exp (2 * Real.pi * Complex.I * b / n) := by
  rw [← Complex.exp_int_mul]
  congr 1
  ring

theorem CharT.WeilTied.unique (hPr : Pr.Ok) {Ps Ps' : CharT X Pr} {σ₀ : X.K →+* ℂ} {xi0 : X.E}
    (h : Ps.WeilTied σ₀ xi0) (h' : Ps'.WeilTied σ₀ xi0) : Ps = Ps' := by
  obtain ⟨ψ⟩ := Ps
  obtain ⟨ψ'⟩ := Ps'
  congr 1
  funext u P
  ext c
  obtain ⟨a, rfl⟩ := owedC_exists_int (hPr.T_prime u) (card_quotient_eq_prime hPr u P) c
  obtain ⟨b, hb⟩ := owedC_exists_int (hPr.T_prime u) (card_quotient_eq_prime hPr u P)
    (redP P.1 xi0 * (a : 𝓞 X.E ⧸ P.1.asIdeal))
  exact σ₀.injective ((h u P a b hb).trans (h' u P a b hb).symm)

theorem CharT.WeilTied.ok (hPr : Pr.Ok) {Ps : CharT X Pr} {σ₀ : X.K →+* ℂ} {xi0 : X.E}
    (h : Ps.WeilTied σ₀ xi0) (hxi : XiUnitT Pr xi0) : Ps.Ok where
  ne u P hp := by
    obtain ⟨b, hb, hbP⟩ := hxi u
    have h1 := h u P 1 b (by rw [hbP P]; simp)
    rw [hp, AddChar.one_apply, map_one, ← owedC_exp_zpow] at h1
    exact hb (((Complex.isPrimitiveRoot_exp (Pr.T u) (hPr.T_prime u).ne_zero).zpow_eq_one_iff_dvd b).1 h1.symm)
  same u P P' a := by
    obtain ⟨b, -, hbP⟩ := hxi u
    apply σ₀.injective
    rw [h u P a (b * a) (by rw [hbP P]; push_cast; rfl), h u P' a (b * a) (by rw [hbP P']; push_cast; rfl)]

theorem owedC_exists_exp {K : Type} [Field K] (σ₀ : K →+* ℂ) {n : ℕ} (hn : n ≠ 0) {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    ∃ ζ' : K, σ₀ ζ' = Complex.exp (2 * Real.pi * Complex.I / n) := by
  have : NeZero n := ⟨hn⟩
  obtain ⟨i, -, hi⟩ := (hζ.map_of_injective σ₀.injective).eq_pow_of_pow_eq_one
    (Complex.isPrimitiveRoot_exp n hn).pow_eq_one
  exact ⟨ζ ^ i, by rw [map_pow, hi]⟩

def CharT.psiC (Ps : CharT X Pr) (σ₀ : X.K →+* ℂ) (u : Pr.Word) (P : {P // P ∈ Pr.vT u}) :
    AddChar (𝓞 X.E ⧸ P.1.asIdeal) ℂ :=
  (σ₀ : X.K →* ℂ).compAddChar (Ps.psiT u P)

theorem CharT.psiC_apply (Ps : CharT X Pr) (σ₀ : X.K →+* ℂ) (u : Pr.Word) (P : {P // P ∈ Pr.vT u})
    (c : 𝓞 X.E ⧸ P.1.asIdeal) : Ps.psiC σ₀ u P c = σ₀ (Ps.psiT u P c) := rfl

theorem CharT.Ok.psiC_ne {Ps : CharT X Pr} (h : Ps.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word) (P : {P // P ∈ Pr.vT u}) :
    Ps.psiC σ₀ u P ≠ 1 := by
  intro h1
  apply h.ne u P
  ext c
  apply σ₀.injective
  rw [← CharT.psiC_apply, h1, AddChar.one_apply, AddChar.one_apply, map_one]

end Weil

section Gauss

variable (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : KQ 1 ≤ LL)

end Gauss

end Formalism.L2.Col
