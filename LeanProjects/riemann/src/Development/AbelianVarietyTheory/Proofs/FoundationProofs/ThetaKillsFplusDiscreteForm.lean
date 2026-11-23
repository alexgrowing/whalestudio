import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import ReciprocityTheory.GaloisValuations.Global
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFunctionalValueGalBEquivariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralTateInertiaCyclotomicTwistTorsionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaBasisLinearCombination
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFunctionalValueModPrimePowUniqueOddWeightStatement

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.KZ GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory.ThKill

theorem cgA_natCast {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (l n a b : ℕ)
    (h : ((a : ℕ) : ZMod (l ^ n)) = ((b : ℕ) : ZMod (l ^ n))) : CgA A l n (a : Ω) (b : Ω) := by
  have h' : ((a : ℤ) : ZMod (l ^ n)) = ((b : ℤ) : ZMod (l ^ n)) := by exact_mod_cast h
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h'
  obtain ⟨k, hk⟩ := h'
  refine ⟨((-k : ℤ) : Ω), intCast_mem A (-k), ?_⟩
  have hk' : ((b : ℤ) : Ω) - ((a : ℤ) : Ω) = ((l : ℤ) : Ω) ^ n * (k : Ω) := by
    have := congrArg (fun z : ℤ => (z : Ω)) hk
    push_cast at this ⊢
    linear_combination this
  push_cast at hk' ⊢
  linear_combination -hk'

theorem cgA_trans {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {l n : ℕ} {x y z : Ω}
    (h1 : CgA A l n x y) (h2 : CgA A l n y z) : CgA A l n x z := by
  obtain ⟨a, ha, e1⟩ := h1
  obtain ⟨b, hb, e2⟩ := h2
  exact ⟨a + b, add_mem ha hb, by linear_combination e1 + e2⟩

theorem cgA_mul {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {l n : ℕ} {x y t : Ω}
    (h : CgA A l n x y) (ht : t ∈ A) : CgA A l n (x * t) (y * t) := by
  obtain ⟨a, ha, e⟩ := h
  exact ⟨a * t, mul_mem ha ht, by linear_combination t * e⟩

theorem gamma1_le_of_dvd {N M : ℕ} (h : N ∣ M) :
    CongruenceSubgroup.Gamma1 M ≤ CongruenceSubgroup.Gamma1 N := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma1_mem] at hγ ⊢
  obtain ⟨h1, h2, h3⟩ := hγ
  have key : ∀ x y : ℤ, ((x : ZMod M)) = (y : ZMod M) → (x : ZMod N) = (y : ZMod N) := by
    intro x y hxy
    have := congrArg (ZMod.castHom h (ZMod N)) hxy
    simpa using this
  refine ⟨?_, ?_, ?_⟩
  · simpa using key _ 1 (by simpa using h1)
  · simpa using key _ 1 (by simpa using h2)
  · simpa using key _ 0 (by simpa using h3)

theorem isThB_level_mul {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (A : ValuationSubring Ω)
    (N M l n : ℕ) [Fact l.Prime] (b : X.Fn l) (φ : HahnSeries ℚ Ω) (h : IsThB X A N l n b φ) :
    IsThB X A (N * M) l n b φ := by
  obtain ⟨f, hI, hc, hδ, hD⟩ := h
  have hle : CongruenceSubgroup.Gamma1 (N * M * l ^ n) ≤ CongruenceSubgroup.Gamma1 (N * l ^ n) :=
    gamma1_le_of_dvd ⟨M, by ring⟩
  refine ⟨f, fun γ hγ => hI γ (hle hγ), hc, fun δ hδ' hneg => ?_, hD⟩
  obtain ⟨g, hg, e⟩ := hδ δ (gamma1_le_of_dvd (dvd_mul_right N M) hδ') hneg
  exact ⟨g, fun γ hγ => hg γ (hle hγ), e⟩

theorem B_level_mul {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N M l w : ℕ) [Fact l.Prime] :
    X.B N l w ≤ X.B (N * M) l w := by
  apply Submodule.span_mono
  rintro b ⟨hp, hg⟩
  refine ⟨hp, fun γ hγ => hg γ ?_⟩
  rw [Gam, Subgroup.mem_inf] at hγ ⊢
  exact ⟨gamma1_le_of_dvd (dvd_mul_right N M) hγ.1, hγ.2⟩

theorem auxiliaryLevel_coprime_ge_five (l N : ℕ) [hl : Fact l.Prime] (hN : 1 ≤ N) (hlN : ¬ l ∣ N) :
    5 ≤ N * (if l = 5 then 7 else 5) ∧ ¬ l ∣ N * (if l = 5 then 7 else 5) := by
  refine ⟨?_, ?_⟩
  · split_ifs <;> nlinarith
  · intro h
    rcases (Nat.Prime.dvd_mul hl.out).1 h with h' | h'
    · exact hlN h'
    · split_ifs at h' with h5
      · subst h5; norm_num at h'
      · have := (Nat.prime_dvd_prime_iff_eq hl.out (by norm_num)).1 h'
        exact h5 this

theorem discrete (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (hj : ∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) (hA : A.valuation (l : Ω) < 1) (hl2 : l ≠ 2)
    (N : ℕ) (hN : 1 ≤ N) (hlN : ¬ l ∣ N) (w : ℕ) (hw : Odd w) (F : Finset Ω) :
    ∃ c : ℕ, ∀ v : X.Fn l, v ∈ X.B N l w →
      (∀ s ∈ Ine (F := ℚ) A, (∀ y ∈ F, s y = y) → X.galB l s v = ((cycZ ℚ Ω l s : ℤ_[l]) ^ (w + 1)) • v) →
      ∀ (n : ℕ) (φ : HahnSeries ℚ Ω), IsThB X A N l n v φ → ∀ r, CgA A l n ((l : Ω) ^ c * φ.coeff r) 0 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨c, hc⟩ := GlobalTheory.T.integral_tate_inertia_cyclotomic_twist_torsion l Ω A hA (w + 1) (by omega) F
  refine ⟨c, fun v hv hgal n φ hφ r => ?_⟩
  have hφA : ∀ r, φ.coeff r ∈ A := by
    obtain ⟨f, -, -, -, hDl⟩ := hφ
    exact hDl.1
  refine hc n (φ.coeff r) (hφA r) (fun s hs hF => ?_)
  have hsA : ∀ x, x ∈ A ↔ s x ∈ A := fun x => (apply_mem_iff_of_mem_Dec (Ine_le_Dec A hs) x).symm
  set u : ℤ_[l] := (cycZ ℚ Ω l s : ℤ_[l]) ^ (w + 1) with hu
  have h1 := GlobalTheory.isThB_galB Ω ε X A N l n w s ((ValuationSubring.mem_nonunits_iff A).2 hA) hsA v hv φ hφ
  rw [hgal s hs hF] at h1
  have h2 := GlobalTheory.ThAdd.isThB_add Ω ε X A N l n w v v ((ValuationSubring.mem_nonunits_iff A).2 hA) hv hv u 0 φ φ hφ hφ
  rw [zero_smul, add_zero] at h2
  have huv : u • v ∈ X.B N l w := Submodule.smul_mem _ u hv
  obtain ⟨hN5, hlN5⟩ := auxiliaryLevel_coprime_ge_five l N hN hlN
  have h3 := GlobalTheory.T.cuspFunctionalValueModPrimePow_unique_oddWeight Ω ε X A _ l hj hl2 hlN5 hN5 ((ValuationSubring.mem_nonunits_iff A).2 hA) n w hw (u • v)
    (B_level_mul X N _ l w huv) _ _ (isThB_level_mul X A N _ l n _ _ h1) (isThB_level_mul X A N _ l n _ _ h2) r

  have h0 : ((0 : ℤ_[l]).appr n : ℕ) = 0 := by
    have hlt := PadicInt.appr_lt (0 : ℤ_[l]) n
    have hk : ((PadicInt.toZModPow n (0 : ℤ_[l]) : ZMod (l ^ n))) = 0 := map_zero _
    have hk' : (((0 : ℤ_[l]).appr n : ℕ) : ZMod (l ^ n)) = 0 := hk
    rw [ZMod.natCast_eq_zero_iff] at hk'
    exact Nat.eq_zero_of_dvd_of_lt hk' hlt
  rw [h0] at h3
  have e : ((((u.appr n : ℕ)) : Ω) • φ + ((0 : ℕ) : Ω) • φ).coeff r = ((u.appr n : ℕ) : Ω) * φ.coeff r := by simp
  have e' : (HahnSeries.map φ (s : Ω →+* Ω)).coeff r = s (φ.coeff r) := rfl
  rw [e, e'] at h3
  have hcg : CgA A l n ((u.appr n : ℕ) : Ω) ((((cycMod ℚ Ω l n s : ZMod (l ^ n)).val ^ (w + 1) : ℕ) : Ω)) :=
    cgA_natCast A l n _ _ (by
      have e1 : (((u.appr n : ℕ)) : ZMod (l ^ n)) = PadicInt.toZModPow n u := rfl
      rw [e1, hu, map_pow]
      push_cast
      congr 1
      simp [cycMod])
  rw [Nat.cast_pow] at hcg
  exact cgA_trans h3 (cgA_mul hcg (hφA r))

theorem th_kills_Fplus_discrete : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω),
  (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → A.valuation (l : Ω) < 1 → ∀ (N w : ℕ) (F : Finset Ω), l ≠ 2 → ¬ l ∣ N → 1 ≤ N → Odd w → ∃ c : ℕ, ∀ b : X.Fn l, b ∈ X.B N l w →
  (∀ s ∈ Ine (F := ℚ) A, (∀ y ∈ F, s y = y) → X.galB l s b = ((cycZ ℚ Ω l s : ℤ_[l]) ^ (w + 1)) • b) →
  ∀ (n : ℕ) (φ : HahnSeries ℚ Ω), IsThB X A N l n b φ → ∀ r, CgA A l n ((l : Ω) ^ c * φ.coeff r) 0 := by
  intro l _ Ω _ _ _ ε X A hj hA N w F hl2 hlN hN hw
  exact discrete l Ω ε X A hj hA hl2 N hN hlN w hw F

end GlobalTheory.ThKill
