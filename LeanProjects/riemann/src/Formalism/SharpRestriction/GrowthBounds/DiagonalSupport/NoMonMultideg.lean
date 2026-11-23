import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.PickDefs

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

section Fock

variable {R : Type} [CommRing R] {σ : Type}

theorem fockR_add (G T₁ T₂ : MvPolynomial σ R) : fock G (T₁ + T₂) = fock G T₁ + fock G T₂ := by
  simp only [fock, coeff_add, mul_add, add_mul, Finset.sum_add_distrib]

theorem fockR_zero (G : MvPolynomial σ R) : fock G 0 = 0 := by
  simp [fock]

theorem fockR_sum {ι : Type} (G : MvPolynomial σ R) (s : Finset ι) (f : ι → MvPolynomial σ R) :
    fock G (∑ i ∈ s, f i) = ∑ i ∈ s, fock G (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [fockR_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fockR_add, ih]

theorem fockR_monomial (G : MvPolynomial σ R) (mo : σ →₀ ℕ) (c : R) :
    fock G (monomial mo c) = G.coeff mo * c * (expFact mo : R) := by
  unfold fock
  rw [Finset.sum_eq_single mo]
  · simp [coeff_monomial]
  · intro b _ hb
    simp [coeff_monomial, Ne.symm hb]
  · intro h
    simp [MvPolynomial.notMem_support_iff.1 h]

end Fock

section Split

variable {T : Type} [Fintype T] {r K : ℕ}

theorem sum_split {M : Type} [AddCommMonoid M] (f : T × Fin (r + K) → M) :
    ∑ v, f v = (∑ v : T × Fin r, f (v.1, Fin.castAdd K v.2)) + ∑ v : T × Fin K, f (v.1, Fin.natAdd r v.2) := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact Fin.sum_univ_add _

theorem prod_split {M : Type} [CommMonoid M] (f : T × Fin (r + K) → M) :
    ∏ v, f v = (∏ v : T × Fin r, f (v.1, Fin.castAdd K v.2)) * ∏ v : T × Fin K, f (v.1, Fin.natAdd r v.2) := by
  rw [Fintype.prod_prod_type, Fintype.prod_prod_type, Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun x _ => ?_
  exact Fin.prod_univ_add _

end Split

section Mon

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (hk : m + 1 = r + K) {J : ℕ} [NeZero J]
  (nL : ZMod J → ℕ)

def tvar (v : TL J nL r × Fin (r + K)) : TV n' (m + 1) := (posOf n' (posTL Fr v.1), Fin.cast hk.symm v.2)

theorem plVar_eq (x : TL J nL r) (a : Fin r) : plVar Fr hk nL x a = tvar Fr hk nL (x, Fin.castAdd K a) := rfl

theorem noVar_eq (x : TL J nL r) (b : Fin K) : noVar Fr hk nL x b = tvar Fr hk nL (x, Fin.natAdd r b) := rfl

def joinE (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ) : TL J nL r × Fin (r + K) → ℕ :=
  fun v => Fin.addCases (fun a => bp (v.1, a)) (fun b => bn (v.1, b)) v.2

theorem joinE_left (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ) (x : TL J nL r) (a : Fin r) :
    joinE nL bp bn (x, Fin.castAdd K a) = bp (x, a) := by
  simp [joinE]

theorem joinE_right (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ) (x : TL J nL r) (b : Fin K) :
    joinE nL bp bn (x, Fin.natAdd r b) = bn (x, b) := by
  simp [joinE]

def bigE (rho : TL J nL r × Fin (r + K) → ℕ) (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ) :
    TL J nL r × Fin (r + K) → ℕ :=
  fun v => rho v + lowP Fr p v.1 * joinE nL bp bn v

def bigM (rho : TL J nL r × Fin (r + K) → ℕ) (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ) :
    TV n' (m + 1) →₀ ℕ :=
  Finsupp.mapDomain (tvar Fr hk nL) (Finsupp.equivFunOnFinite.symm (bigE Fr p nL rho bp bn))

def mPl (bp : TL J nL r × Fin r →₀ ℕ) : TV n' (m + 1) →₀ ℕ :=
  ∑ v : TL J nL r × Fin r, Finsupp.single (plVar Fr hk nL v.1 v.2) (lowP Fr p v.1 * bp v)

def mNo (bn : TL J nL r × Fin K →₀ ℕ) : TV n' (m + 1) →₀ ℕ :=
  ∑ v : TL J nL r × Fin K, Finsupp.single (noVar Fr hk nL v.1 v.2) (lowP Fr p v.1 * bn v)

theorem labMon_eq (rho : TL J nL r × Fin (r + K) → ℕ) :
    labMon Fr hk nL rho = ∑ v : TL J nL r × Fin (r + K), Finsupp.single (tvar Fr hk nL v) (rho v) := by
  rw [labMon, sum_split, Fintype.sum_prod_type, Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  rfl

theorem bigM_eq (rho : TL J nL r × Fin (r + K) → ℕ) (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ) :
    labMon Fr hk nL rho + mPl Fr p hk nL bp + mNo Fr p hk nL bn = bigM Fr p hk nL rho bp bn := by
  have hmd : bigM Fr p hk nL rho bp bn =
      ∑ v : TL J nL r × Fin (r + K), Finsupp.single (tvar Fr hk nL v) (bigE Fr p nL rho bp bn v) := by
    rw [bigM, Finsupp.mapDomain, Finsupp.sum_fintype _ _ (by simp)]
    rfl
  rw [hmd, labMon_eq]
  simp only [bigE, Finsupp.single_add, Finset.sum_add_distrib]
  rw [add_assoc]
  congr 1
  rw [sum_split]
  simp only [joinE_left, joinE_right]
  rfl

variable {Fr p hk nL}

theorem tvar_inj (hinj : Function.Injective fun x : TL J nL r => posOf n' (posTL Fr x)) :
    Function.Injective (tvar Fr hk nL) := by
  intro v w h
  simp only [tvar, Prod.mk.injEq] at h
  exact Prod.ext (hinj h.1) (Fin.cast_injective _ h.2)

theorem bigM_apply (hinj : Function.Injective fun x : TL J nL r => posOf n' (posTL Fr x))
    (rho : TL J nL r × Fin (r + K) → ℕ) (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ)
    (v : TL J nL r × Fin (r + K)) : bigM Fr p hk nL rho bp bn (tvar Fr hk nL v) = bigE Fr p nL rho bp bn v := by
  rw [bigM, Finsupp.mapDomain_apply (tvar_inj hinj)]
  rfl

theorem bigM_pl (hinj : Function.Injective fun x : TL J nL r => posOf n' (posTL Fr x))
    (rho : TL J nL r × Fin (r + K) → ℕ) (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ)
    (x : TL J nL r) (a : Fin r) :
    bigM Fr p hk nL rho bp bn (plVar Fr hk nL x a) = rho (x, Fin.castAdd K a) + lowP Fr p x * bp (x, a) := by
  rw [plVar_eq, bigM_apply hinj]
  simp only [bigE, joinE_left]

theorem bigM_no (hinj : Function.Injective fun x : TL J nL r => posOf n' (posTL Fr x))
    (rho : TL J nL r × Fin (r + K) → ℕ) (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ)
    (x : TL J nL r) (b : Fin K) :
    bigM Fr p hk nL rho bp bn (noVar Fr hk nL x b) = rho (x, Fin.natAdd r b) + lowP Fr p x * bn (x, b) := by
  rw [noVar_eq, bigM_apply hinj]
  simp only [bigE, joinE_right]

theorem bigM_notin (rho : TL J nL r × Fin (r + K) → ℕ) (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ)
    (w : TV n' (m + 1)) (hw : w ∉ Set.range (tvar Fr hk nL)) : bigM Fr p hk nL rho bp bn w = 0 := by
  rw [bigM]
  exact Finsupp.mapDomain_notin_range _ _ hw

theorem eq_bigM (hinj : Function.Injective fun x : TL J nL r => posOf n' (posTL Fr x))
    (rho : TL J nL r × Fin (r + K) → ℕ) (mo : TV n' (m + 1) →₀ ℕ)
    (hz : ∀ w, w ∉ Set.range (tvar Fr hk nL) → mo w = 0) (hlow : InLow Fr p hk nL rho mo) :
    mo = bigM Fr p hk nL rho (plMon Fr p hk nL mo) (noMon Fr p hk nL mo) := by
  ext w
  by_cases hw : w ∈ Set.range (tvar Fr hk nL)
  · obtain ⟨⟨x, c⟩, rfl⟩ := hw
    rw [bigM_apply hinj]
    induction c using Fin.addCases with
    | left a =>
      simp only [bigE, joinE_left, plMon, Finsupp.coe_equivFunOnFinite_symm, ← hlow.1 x a]
      exact (Nat.mod_add_div _ _).symm
    | right b =>
      simp only [bigE, joinE_right, noMon, Finsupp.coe_equivFunOnFinite_symm, ← hlow.2 x b]
      exact (Nat.mod_add_div _ _).symm
  · rw [bigM_notin _ _ _ _ hw, hz w hw]

theorem lowP_pos (hp : 0 < p) (x : TL J nL r) : 0 < lowP Fr p x := by
  unfold lowP
  exact pow_pos hp _

theorem bigM_inLow (hinj : Function.Injective fun x : TL J nL r => posOf n' (posTL Fr x))
    (rho : TL J nL r × Fin (r + K) → ℕ) (hrho : ∀ x c, rho (x, c) < lowP Fr p x)
    (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ) :
    InLow Fr p hk nL rho (bigM Fr p hk nL rho bp bn) := by
  refine ⟨fun x a => ?_, fun x b => ?_⟩
  · rw [bigM_pl hinj, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hrho _ _)]
  · rw [bigM_no hinj, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hrho _ _)]

theorem bigM_plMon (hp : 0 < p) (hinj : Function.Injective fun x : TL J nL r => posOf n' (posTL Fr x))
    (rho : TL J nL r × Fin (r + K) → ℕ) (hrho : ∀ x c, rho (x, c) < lowP Fr p x)
    (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ) :
    plMon Fr p hk nL (bigM Fr p hk nL rho bp bn) = bp := by
  ext ⟨x, a⟩
  simp only [plMon, Finsupp.coe_equivFunOnFinite_symm]
  rw [bigM_pl hinj, Nat.add_mul_div_left _ _ (lowP_pos hp x), Nat.div_eq_of_lt (hrho _ _), zero_add]

theorem bigM_noMon (hp : 0 < p) (hinj : Function.Injective fun x : TL J nL r => posOf n' (posTL Fr x))
    (rho : TL J nL r × Fin (r + K) → ℕ) (hrho : ∀ x c, rho (x, c) < lowP Fr p x)
    (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ) :
    noMon Fr p hk nL (bigM Fr p hk nL rho bp bn) = bn := by
  ext ⟨x, b⟩
  simp only [noMon, Finsupp.coe_equivFunOnFinite_symm]
  rw [bigM_no hinj, Nat.add_mul_div_left _ _ (lowP_pos hp x), Nat.div_eq_of_lt (hrho _ _), zero_add]

theorem plMon_multideg (mo : TV n' (m + 1) →₀ ℕ) (x : TL J nL r) :
    multideg (plMon Fr p hk nL mo) x = ∑ a : Fin r, mo (plVar Fr hk nL x a) / lowP Fr p x := rfl

theorem noMon_multideg (mo : TV n' (m + 1) →₀ ℕ) (x : TL J nL r) :
    multideg (noMon Fr p hk nL mo) x = ∑ b : Fin K, mo (noVar Fr hk nL x b) / lowP Fr p x := rfl

theorem bigM_inBlock (hp : 0 < p) (hinj : Function.Injective fun x : TL J nL r => posOf n' (posTL Fr x))
    (rho : TL J nL r × Fin (r + K) → ℕ) (hrho : ∀ x c, rho (x, c) < lowP Fr p x)
    (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ) (dPl dNo : TL J nL r → ℕ)
    (h1 : ∀ x, multideg bp x = dPl x) (h2 : ∀ x, multideg bn x = dNo x) :
    InBlock Fr p hk nL dPl dNo (bigM Fr p hk nL rho bp bn) := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · rw [← h1 x]
    unfold multideg
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [bigM_pl hinj, Nat.add_mul_div_left _ _ (lowP_pos hp x), Nat.div_eq_of_lt (hrho _ _), zero_add]
  · rw [← h2 x]
    unfold multideg
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [bigM_no hinj, Nat.add_mul_div_left _ _ (lowP_pos hp x), Nat.div_eq_of_lt (hrho _ _), zero_add]

end Mon

end Formalism.MainNotions.Proposition5Numerics
