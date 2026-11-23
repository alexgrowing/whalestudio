import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsModularFormCoeffSeqHeckeTOfPrimeNotDvdStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsModularFormCoeffSeqHeckeUAndDepletionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AtkinLehnerIntertwinesHeckeOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AtkinLehnerSlashIsModularFormCoeffSeqStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LamExtendByZeroStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LinearFunctionalEqCoeffLinearCombinationFinite
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionFunctionInjectiveOfPolynomialGrowth
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormCoeffSeqLinearStructure
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSturmBoundIsModularFormCoeffSeq
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem lam_add' (B : ℕ) (c a b : ℕ → ℂ) : lam B c (a + b) = lam B c a + lam B c b := by
  simp only [lam, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem lam_smul' (B : ℕ) (c a : ℕ → ℂ) (z : ℂ) : lam B c (z • a) = z * lam B c a := by
  simp only [lam, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem slz_add' (k : ℕ) (δ : M2) (f g : ℍ → ℂ) : slz k δ (f + g) = slz k δ f + slz k δ g := by
  funext τ; simp only [slz, Pi.add_apply]; ring

theorem slz_smul' (k : ℕ) (δ : M2) (z : ℂ) (f : ℍ → ℂ) : slz k δ (z • f) = z • slz k δ f := by
  funext τ; simp only [slz, Pi.smul_apply, smul_eq_mul]; ring

theorem eigAll_of_atkinLehner : ∀ (k N l : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ) (α : ℂ) (B : ℕ) (c : ℕ → ℂ)
    (a₀ b₀ c₀ d₀ : ℤ), N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ k → 0 < N → l.Prime → ¬ l ∣ N →
    EigF k N l χ⁻¹ (fun q => χ⁻¹ q * g q) α B c → ∃ (B' : ℕ) (c' : ℕ → ℂ), EigAll k N l χ g (χ l * α) B' c' ∧
    ∀ a a', MF k (N * l) (ch χ) a → MF k (N * l) (ch χ⁻¹) a' →
      qs a' = slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs a) → lam B' c' a = lam B c a' := by
  intro k N l χ g α B c a₀ b₀ c₀ d₀ hdet hk hN hl hlN hE
  set δ : M2 := !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] with hδ
  have hL : 0 < N * l := Nat.mul_pos hN hl.pos
  obtain ⟨hz1, hadd1, hsm1, -, -, -⟩ := mf_linear k (N * l) (ch χ)
  obtain ⟨hz2, hadd2, hsm2, -, -, -⟩ := mf_linear k (N * l) (ch χ⁻¹)

  have uniq : ∀ x y, MF k (N * l) (ch χ⁻¹) x → MF k (N * l) (ch χ⁻¹) y → qs x = qs y → x = y :=
    fun x y hx hy h => qs_injective x y hx.1 hy.1 h
  let S : Set (ℕ → ℂ) := {a | MF k (N * l) (ch χ) a}
  classical
  let φ : (ℕ → ℂ) → ℂ := fun a =>
    if h : ∃ a', MF k (N * l) (ch χ⁻¹) a' ∧ qs a' = slz k δ (qs a) then lam B c h.choose else 0
  have hφ : ∀ a a', MF k (N * l) (ch χ⁻¹) a' → qs a' = slz k δ (qs a) → φ a = lam B c a' := by
    intro a a' h1 h2
    have h : ∃ a', MF k (N * l) (ch χ⁻¹) a' ∧ qs a' = slz k δ (qs a) := ⟨a', h1, h2⟩
    simp only [φ, dif_pos h]
    rw [uniq _ _ h.choose_spec.1 h1 (h.choose_spec.2.trans h2.symm)]
  have hex : ∀ a, MF k (N * l) (ch χ) a → ∃ a', MF k (N * l) (ch χ⁻¹) a' ∧ qs a' = slz k δ (qs a) :=
    fun a ha => GlobalTheory.T.atkinLehner_slash_isModularFormCoeffSeq k N l χ a a₀ b₀ c₀ d₀ hdet hk hN ha
  obtain ⟨B₀, hB₀⟩ := sturm_coef_zero k (N * l) N χ hL (dvd_mul_right N l)
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.func_eq_lam S B₀ φ hz1
    (by
      intro a ha b hb
      obtain ⟨a', ha', ea⟩ := hex a ha
      obtain ⟨b', hb', eb⟩ := hex b hb
      obtain ⟨hab, hqab⟩ := hadd1 a b ha hb
      obtain ⟨hab', hqab'⟩ := hadd2 a' b' ha' hb'
      refine ⟨hab, ?_⟩
      rw [hφ a a' ha' ea, hφ b b' hb' eb, hφ (a + b) (a' + b') hab' (by rw [hqab', hqab, slz_add', ea, eb]),
        lam_add'])
    (by
      intro z a ha
      obtain ⟨a', ha', ea⟩ := hex a ha
      obtain ⟨hza, hqza⟩ := hsm1 z a ha
      obtain ⟨hza', hqza'⟩ := hsm2 z a' ha'
      refine ⟨hza, ?_⟩
      rw [hφ a a' ha' ea, hφ (z • a) (z • a') hza' (by rw [hqza', hqza, slz_smul', ea]), lam_smul'])
    (fun a ha h => hB₀ a ha h)
  obtain ⟨B', c', hagree, hkill⟩ := GlobalTheory.T.exists_lam_eq_and_vanishes_off_character k (N * l) N χ B₀ c₁ hL (dvd_mul_right N l)
  have key : ∀ a a', MF k (N * l) (ch χ) a → MF k (N * l) (ch χ⁻¹) a' → qs a' = slz k δ (qs a) →
      lam B' c' a = lam B c a' := by
    intro a a' ha ha' e
    rw [hagree a ha, ← hc₁ a ha, hφ a a' ha' e]
  refine ⟨B', c', ⟨⟨?_, ?_⟩, hkill⟩, key⟩
  · intro a ha q hq hqNl
    obtain ⟨a', ha', ea⟩ := hex a ha
    have hqN : ¬ q ∣ N := fun h => hqNl (dvd_mul_of_dvd_left h l)
    obtain ⟨hT, -⟩ := GlobalTheory.T.atkinLehner_intertwines_hecke_operators k N l χ a a' a₀ b₀ c₀ d₀ hdet hk hN hl hlN ha ha' ea
    have hTa : MF k (N * l) (ch χ) (To k (ch χ q) q a) :=
      GlobalTheory.T.isModularFormCoeffSeq_heckeT_of_prime_not_dvd k (N * l) N q χ a hk (dvd_mul_right N l) hq hqNl ha
    have hTa' : MF k (N * l) (ch χ⁻¹) (To k (ch χ⁻¹ q) q a') :=
      GlobalTheory.T.isModularFormCoeffSeq_heckeT_of_prime_not_dvd k (N * l) N q χ⁻¹ a' hk (dvd_mul_right N l) hq hqNl ha'
    obtain ⟨hs, hqs⟩ := hsm2 (ch χ q) _ hTa'
    rw [key _ _ hTa hs (by rw [hqs, hT q hq hqNl]), lam_smul', hE.T a' ha' q hq hqNl, key a a' ha ha' ea]
    have hunit : IsUnit ((q : ℕ) : ZMod N) := by
      rw [ZMod.isUnit_iff_coprime]
      exact (Nat.Prime.coprime_iff_not_dvd hq).mpr hqN
    have h1 : χ (q : ZMod N) * χ⁻¹ (q : ZMod N) = 1 := by
      rw [show χ (q : ZMod N) * χ⁻¹ (q : ZMod N) = (χ * χ⁻¹) (q : ZMod N) by rw [MulChar.coeToFun_mul]; rfl,
        mul_inv_cancel, MulChar.one_apply hunit]
    simp only [ch, Int.cast_natCast]
    linear_combination (g q * lam B c a') * h1
  · intro a ha
    obtain ⟨a', ha', ea⟩ := hex a ha
    obtain ⟨-, hU⟩ := GlobalTheory.T.atkinLehner_intertwines_hecke_operators k N l χ a a' a₀ b₀ c₀ d₀ hdet hk hN hl hlN ha ha' ea
    have hper : ∀ (ε : DirichletCharacter ℂ N) (d : ℤ), ch ε (d + (N * l : ℕ)) = ch ε d := by
      intro ε d
      simp [ch]
    have hUa := (GlobalTheory.T.isModularFormCoeffSeq_heckeU_and_depletion k (N * l) l (ch χ) a hk hl (dvd_mul_left l N) (hper χ) ha).1
    have hUa' := (GlobalTheory.T.isModularFormCoeffSeq_heckeU_and_depletion k (N * l) l (ch χ⁻¹) a' hk hl (dvd_mul_left l N) (hper χ⁻¹) ha').1
    obtain ⟨hs, hqs⟩ := hsm2 (ch χ l) _ hUa'
    rw [key _ _ hUa hs (by rw [hqs, hU]), lam_smul', hE.U a' ha', key a a' ha ha' ea]
    simp only [ch, Int.cast_natCast]
    ring

end GlobalTheory.EisM
