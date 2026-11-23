import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj
import Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.Top

namespace UpperTheory.V

theorem length_eq_add_eigen {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (h2 : IsUnit (2 : R))
    (N : Submodule R M) (f : Module.End R M) (hN : ∀ x ∈ N, f x ∈ N) (hf : ∀ x, f (f x) = x) (s : R) (hs : s * s = 1) :
    Module.length R N = Module.length R ↥(N ⊓ f.eigenspace s) + Module.length R ↥(N ⊓ f.eigenspace (-s)) := by
  set c : R := ↑h2.unit⁻¹ with hc_def
  have hc : (2 : R) * c = 1 := h2.mul_val_inv
  have eP : ∀ x : M, f (x + s • f x) = s • (x + s • f x) := by
    intro x
    rw [map_add, map_smul, hf, smul_add, smul_smul, hs, one_smul, add_comm]
  have eQ : ∀ x : M, f (x - s • f x) = (-s) • (x - s • f x) := by
    intro x
    rw [map_sub, map_smul, hf, smul_sub, smul_smul, neg_mul, hs, neg_smul, neg_smul, one_smul]
    abel
  have memP : ∀ x ∈ N, c • (x + s • f x) ∈ N ⊓ f.eigenspace s := fun x hx =>
    ⟨N.smul_mem c (N.add_mem hx (N.smul_mem s (hN x hx))),
      (f.eigenspace s).smul_mem c (Module.End.mem_eigenspace_iff.mpr (eP x))⟩
  have memQ : ∀ x ∈ N, c • (x - s • f x) ∈ N ⊓ f.eigenspace (-s) := fun x hx =>
    ⟨N.smul_mem c (N.sub_mem hx (N.smul_mem s (hN x hx))),
      (f.eigenspace (-s)).smul_mem c (Module.End.mem_eigenspace_iff.mpr (eQ x))⟩
  let toP : N →ₗ[R] ↥(N ⊓ f.eigenspace s) :=
    (c • (N.subtype + s • (f ∘ₗ N.subtype))).codRestrict _ (fun x => by
      simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply,
        Submodule.coe_subtype]
      exact memP _ x.2)
  let toQ : N →ₗ[R] ↥(N ⊓ f.eigenspace (-s)) :=
    (c • (N.subtype - s • (f ∘ₗ N.subtype))).codRestrict _ (fun x => by
      simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply,
        Submodule.coe_subtype]
      exact memQ _ x.2)
  let back : (↥(N ⊓ f.eigenspace s) × ↥(N ⊓ f.eigenspace (-s))) →ₗ[R] N :=
    (Submodule.inclusion inf_le_left).coprod (Submodule.inclusion inf_le_left)
  have h₁ : (toP.prod toQ) ∘ₗ back = LinearMap.id := by
    ext ⟨a, ha⟩
    all_goals simp [toP, toQ, back]
    · rw [Module.End.mem_eigenspace_iff.mp ha.2]
      linear_combination (norm := module) hs • (c • a) + hc • a
    · rw [Module.End.mem_eigenspace_iff.mp ha.2]
      linear_combination (norm := module) hs • (-(c • a))
    · rw [Module.End.mem_eigenspace_iff.mp ha.2]
      linear_combination (norm := module) hs • (-(c • a))
    · rw [Module.End.mem_eigenspace_iff.mp ha.2]
      linear_combination (norm := module) hs • (c • a) + hc • a
  have h₂ : back ∘ₗ (toP.prod toQ) = LinearMap.id := by
    ext ⟨x, hx⟩
    simp [toP, toQ, back]
    linear_combination (norm := module) hc • x
  rw [(LinearEquiv.ofLinear (toP.prod toQ) back h₁ h₂).length_eq, Module.length_prod]

section Parts

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {l : ℕ} [Fact l.Prime]

variable (E) in

def cE : E ≃+* E := (IsCMField.complexConj E).toRingEquiv

def cAct (D : LData E Ω l) (e : ℤ) : Module.End ℤ_[l] (H1 (qzTw D e)) := galoisActionOnCohomology D e (cE E)

def ShaPlus (D : LData E Ω l) (e : ℕ) : Submodule ℤ_[l] (H1 (qzTw D (e : ℤ))) :=
  Sha D e ⊓ (cAct D e).eigenspace ((-1) ^ e)

def ShaMinus (D : LData E Ω l) (e : ℕ) : Submodule ℤ_[l] (H1 (qzTw D (e : ℤ))) :=
  Sha D e ⊓ (cAct D e).eigenspace ((-1) ^ (e + 1))

def plusLen (D : LData E Ω l) (e : ℕ) : ℕ∞ := Module.length ℤ_[l] (ShaPlus D e)

def minusLen (D : LData E Ω l) (e : ℕ) : ℕ∞ := Module.length ℤ_[l] (ShaMinus D e)

theorem cAct_cAct (D : LData E Ω l) (e : ℤ) (x : H1 (qzTw D e)) : cAct D e (cAct D e x) = x := by
  have hc : cE E * cE E = 1 := by
    ext y
    simp [cE, IsCMField.complexConj_apply_apply]
  show galoisActionOnCohomology D e (cE E) (galoisActionOnCohomology D e (cE E) x) = x
  rw [← Module.End.mul_apply, ← galois_action_cohomology_mul, hc, galois_action_cohomology_one, Module.End.one_apply]

theorem cAct_mem_Sha (D : LData E Ω l) (e : ℤ) {x : H1 (qzTw D e)} (hx : x ∈ Sha D e) : cAct D e x ∈ Sha D e :=
  galois_action_preserves_sha D e _ hx

theorem shaLen_eq_add (hl : l ≠ 2) (D : LData E Ω l) (e : ℕ) : shaLen D e = plusLen D e + minusLen D e := by
  have h2 : IsUnit (2 : ℤ_[l]) := by
    by_contra hn
    have hmem : (2 : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] :=
      (IsLocalRing.mem_maximalIdeal _).mpr hn
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_ofNat] at hmem
    have h3 : ((2 : ℕ) : ZMod l) = 0 := by simpa using hmem
    rw [ZMod.natCast_eq_zero_iff] at h3
    exact hl ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h3)
  have hs : ((-1 : ℤ_[l]) ^ e) * ((-1) ^ e) = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  have key := length_eq_add_eigen h2 (Sha D e) (cAct D e) (fun x hx => cAct_mem_Sha D e hx)
    (cAct_cAct D e) _ hs
  have hneg : -((-1 : ℤ_[l]) ^ e) = (-1) ^ (e + 1) := by rw [pow_succ, mul_neg_one]
  rw [hneg] at key
  exact key

end Parts

def VVat (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E] (t : ℕ) (B : ℝ) : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (D : LData E Ω l),
    (∀ e : ℕ, 0 < e → e < t → shaLen D (e : ℤ) ≠ ⊤) ∧ ∑ e ∈ Finset.Ico 1 t, ((shaLen D (e : ℤ)).toNat : ℝ) ≤ B

def BoundedHeightTwoPlaceCondition (E : Type) [Field E] [NumberField E] (t : ℕ) (B : ℝ) : Prop := VVat 2 E t B

def VVminusLe (E : Type) [Field E] [NumberField E] [IsCMField E] (t : ℕ) (B : ℝ) : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (ld : ∀ (p : ℕ) [Fact p.Prime], LData E Ω p),
    (∀ (p : ℕ) [Fact p.Prime] (e : ℕ), p ≠ 2 → 0 < e → e < t → minusLen (ld p) e ≠ ⊤) ∧
    ∀ S : Finset Nat.Primes, (∀ l ∈ S, (l : ℕ) ≠ 2) →
      ∑ l ∈ S, Real.log (l : ℕ) *
        ∑ e ∈ Finset.Ico 1 t, ((@minusLen E Ω _ _ _ _ _ _ l ⟨l.2⟩ (@ld l ⟨l.2⟩) e).toNat : ℝ) ≤ B

def VVplusLe (E : Type) [Field E] [NumberField E] [IsCMField E] (t : ℕ) (B : ℝ) : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (ld : ∀ (p : ℕ) [Fact p.Prime], LData E Ω p),
    (∀ (p : ℕ) [Fact p.Prime] (e : ℕ), p ≠ 2 → 0 < e → e < t → plusLen (ld p) e ≠ ⊤) ∧
    ∀ S : Finset Nat.Primes, (∀ l ∈ S, (l : ℕ) ≠ 2) →
      ∑ l ∈ S, Real.log (l : ℕ) *
        ∑ e ∈ Finset.Ico 1 t, ((@plusLen E Ω _ _ _ _ _ _ l ⟨l.2⟩ (@ld l ⟨l.2⟩) e).toNat : ℝ) ≤ B

theorem vvle_of_parts {E : Type} [Field E] [NumberField E] [IsCMField E] {t : ℕ} {B₂ Bm Bp : ℝ}
    (h2 : BoundedHeightTwoPlaceCondition E t B₂) (hm : VVminusLe E t Bm) (hp : VVplusLe E t Bp) : VVle E t (B₂ * Real.log 2 + Bm + Bp) := by
  intro Ω _ _ _ ld
  have h2' := h2 Ω (ld 2)
  have hm' := hm Ω ld
  have hp' := hp Ω ld
  refine ⟨?_, ?_⟩
  · intro p _ e he1 he2
    by_cases hp2 : p = 2
    · subst hp2
      exact h2'.1 e he1 he2
    · rw [shaLen_eq_add hp2 (ld p) e]
      exact WithTop.add_ne_top.mpr ⟨hp'.1 p e hp2 he1 he2, hm'.1 p e hp2 he1 he2⟩
  · intro S
    set g : Nat.Primes → ℝ := fun l => Real.log (l : ℕ) *
      ∑ e ∈ Finset.Ico 1 t,
        ((@shaLen E Ω _ _ _ _ _ l ⟨l.2⟩ (@ld l ⟨l.2⟩) (e : ℤ)).toNat : ℝ) with hg
    show ∑ l ∈ S, g l ≤ _
    have hnn : ∀ l : Nat.Primes, 0 ≤ g l := fun l =>
      mul_nonneg (Real.log_nonneg (by exact_mod_cast l.2.one_lt.le))
        (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
    rw [← Finset.sum_filter_add_sum_filter_not S (fun l : Nat.Primes => (l : ℕ) = 2)]
    let p2 : Nat.Primes := ⟨2, Nat.prime_two⟩
    have hA : ∑ l ∈ S.filter (fun l : Nat.Primes => (l : ℕ) = 2), g l ≤ B₂ * Real.log 2 := by
      calc ∑ l ∈ S.filter (fun l : Nat.Primes => (l : ℕ) = 2), g l
          ≤ ∑ l ∈ ({p2} : Finset Nat.Primes), g l := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro l hl
              simp only [Finset.mem_filter] at hl
              simp only [Finset.mem_singleton]
              exact Subtype.ext hl.2
            · intro l _ _
              exact hnn l
        _ = g p2 := Finset.sum_singleton g p2
        _ = Real.log 2 * ∑ e ∈ Finset.Ico 1 t, ((shaLen (ld 2) (e : ℤ)).toNat : ℝ) := by
            simp only [hg, p2]
            norm_num
        _ ≤ Real.log 2 * B₂ := mul_le_mul_of_nonneg_left h2'.2 (Real.log_nonneg (by norm_num))
        _ = B₂ * Real.log 2 := mul_comm _ _
    have hB : ∑ l ∈ S.filter (fun l : Nat.Primes => ¬ (l : ℕ) = 2), g l ≤ Bm + Bp := by
      have hS : ∀ l ∈ S.filter (fun l : Nat.Primes => ¬ (l : ℕ) = 2), (l : ℕ) ≠ 2 :=
        fun l hl => (Finset.mem_filter.mp hl).2
      have e1 := hm'.2 _ hS
      have e2 := hp'.2 _ hS
      have heq : ∑ l ∈ S.filter (fun l : Nat.Primes => ¬ (l : ℕ) = 2), g l =
          (∑ l ∈ S.filter (fun l : Nat.Primes => ¬ (l : ℕ) = 2), Real.log (l : ℕ) *
            ∑ e ∈ Finset.Ico 1 t, ((@minusLen E Ω _ _ _ _ _ _ l ⟨l.2⟩ (@ld l ⟨l.2⟩) e).toNat : ℝ)) +
          (∑ l ∈ S.filter (fun l : Nat.Primes => ¬ (l : ℕ) = 2), Real.log (l : ℕ) *
            ∑ e ∈ Finset.Ico 1 t, ((@plusLen E Ω _ _ _ _ _ _ l ⟨l.2⟩ (@ld l ⟨l.2⟩) e).toNat : ℝ)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun l hl => ?_
        simp only [hg]
        rw [← mul_add, ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun e he => ?_
        haveI : Fact (l : ℕ).Prime := ⟨l.2⟩
        have hl2 := (Finset.mem_filter.mp hl).2
        obtain ⟨he1, he2⟩ := Finset.mem_Ico.mp he
        rw [shaLen_eq_add hl2 (ld l) e, ENat.toNat_add (hp'.1 l e hl2 he1 he2) (hm'.1 l e hl2 he1 he2),
          Nat.cast_add, add_comm]
      rw [heq]
      linarith
    linarith

end UpperTheory.V

end
