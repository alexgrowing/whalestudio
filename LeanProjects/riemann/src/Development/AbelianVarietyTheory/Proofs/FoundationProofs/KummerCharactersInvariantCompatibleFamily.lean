import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.LiftApplyOfMemAdmissibleSubalgebra
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BinaryMonomialDegreeSubstExpansion
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralConjugateSL2IntLawsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKummerCharacterAtLevelAddZeroCongrStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKummerCharacterAtLevelOfMemKummerModuleStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCharacterAdditiveOnCongruenceStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKummerCharacterAtLevelSuccReduceStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKummerCharacterAtLevelIntegralMatrixConjStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKummerCharacterAtLevelPadicIntSmulStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCharactersEqOnPrincipalCongruenceStatement

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

noncomputable section

namespace GlobalTheory.KZ.H3.KumFam

theorem gamma_dvd {M N : ℕ} (h : M ∣ N) {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma N) :
    δ ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem] at hδ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hδ
  have e : ∀ x : ℤ, ZMod.castHom h (ZMod M) (x : ZMod N) = (x : ZMod M) := fun x => map_intCast _ x
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← e, h1, map_one]
  · rw [← e, h2, map_zero]
  · rw [← e, h3, map_zero]
  · rw [← e, h4, map_one]

theorem common_level {k : ℕ} (Q : Fin k → ℕ → Prop) (hmono : ∀ i M M', M ∣ M' → Q i M → Q i M')
    (h : ∀ i, ∃ M, 0 < M ∧ Q i M) : ∃ M, 0 < M ∧ ∀ i, Q i M := by
  choose M hM hQ using h
  exact ⟨∏ i, M i, Finset.prod_pos fun i _ => hM i,
    fun i => hmono i _ _ (Finset.dvd_prod_of_mem M (Finset.mem_univ i)) (hQ i)⟩

theorem near_fin {V : Type} {k : ℕ} (φ ψ : Fin k → SL(2, ℤ) → V) (h : ∀ i, Near (φ i) (ψ i)) :
    ∃ M, 0 < M ∧ ∀ δ ∈ CongruenceSubgroup.Gamma M, ∀ i, φ i δ = ψ i δ := by
  obtain ⟨M, hM, hQ⟩ := common_level (fun i M => ∀ δ ∈ CongruenceSubgroup.Gamma M, φ i δ = ψ i δ)
    (fun _ _ _ hd hq δ hδ => hq δ (gamma_dvd hd hδ)) h
  exact ⟨M, hM, fun δ hδ i => hQ i δ hδ⟩

theorem kum_sum {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ)
    {ι : Type} [DecidableEq ι] (s : Finset ι) (x : ι → X.Khat l) (χ : ι → SL(2, ℤ) → ZMod (l ^ n))
    (h : ∀ k ∈ s, Kum X l n (x k) (χ k)) : Kum X l n (∑ k ∈ s, x k) (∑ k ∈ s, χ k) := by
  induction s using Finset.induction_on with
  | empty => simpa using (GlobalTheory.T.isKummerCharacterAtLevel_add_zero_congr Ω ε X l n).2.1
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (GlobalTheory.T.isKummerCharacterAtLevel_add_zero_congr Ω ε X l n).1 _ _ _ _ (h a (Finset.mem_insert_self a s))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem map_mon {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (w : ℕ) (i : Fin (w + 1)) :
    MvPolynomial.map f (mon R w i) = mon S w i := by
  simp [mon]

end GlobalTheory.KZ.H3.KumFam

open GlobalTheory.KZ.H3.KumFam in

theorem GlobalTheory.KZ.H3.kum_family : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], [IsAlgClosed Ω] → JHol X → ∀ (N w : ℕ) (c : Fin (w + 1) → X.Khat l), (∀ i, c i ∈ X.A l) → (∀ γ ∈ Gam N l, ∀ i, c i = ∑ k, (cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ_[l]) • X.kmap l (X.sl (ofSL γ)).toRingEquiv (c k)) → ∃ Φ, IsFam l w (Gam N l) Φ ∧ ∀ n i, Kum X l n (c i) (fun δ => MvPolynomial.coeff (Finsupp.single 0 (i : ℕ) + Finsupp.single 1 (w - (i : ℕ))) (Φ n δ)) := by
  intro Ω _ _ ε X l _ _ hj N w c hA hinv
  choose χ hχ using fun n i => GlobalTheory.T.exists_kummerCharacterAtLevel_of_mem_kummerModule Ω ε X l hj n (c i) (hA i)
  refine ⟨fun n δ => ∑ i, MvPolynomial.C (χ n i δ) * mon (ZMod (l ^ n)) w i, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro n δ
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => ?_
    have h := (MvPolynomial.isHomogeneous_C (Fin 2) (χ n i δ)).mul ((mon_expand (ZMod (l ^ n)) w).2.2.1 i)
    rwa [zero_add] at h
  · intro n
    obtain ⟨M, hM, hQ⟩ := common_level
      (fun i M => ∀ δ ∈ CongruenceSubgroup.Gamma M, ∀ δ' ∈ CongruenceSubgroup.Gamma M,
        χ n i (δ * δ') = χ n i δ + χ n i δ')
      (fun _ _ _ hd hq δ hδ δ' hδ' => hq δ (gamma_dvd hd hδ) δ' (gamma_dvd hd hδ'))
      (fun i => GlobalTheory.T.kummerCharacter_additive_on_congruence Ω ε X l n (c i) (χ n i) (hχ n i))
    refine ⟨M, hM, fun δ hδ δ' hδ' => ?_⟩
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hQ i δ hδ δ' hδ', map_add, add_mul]
  · intro n γ hγ
    have hdet : (0 : ℤ) < (γ : Matrix (Fin 2) (Fin 2) ℤ).det := by rw [γ.det_coe]; exact one_pos
    have hK : ∀ i, Kum X l n (c i)
        (fun δ => ∑ k, ((cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ) : ZMod (l ^ n)) * χ n k (γ * δ * γ⁻¹)) := by
      intro i
      have hk : ∀ k, Kum X l n ((cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ_[l]) •
          X.kmap l (X.sl (ofSL γ)).toRingEquiv (c k))
          (fun δ => PadicInt.toZModPow n (cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ_[l]) *
            χ n k (cj (γ : Matrix (Fin 2) (Fin 2) ℤ) δ)) := by
        intro k
        have h1 := GlobalTheory.T.isKummerCharacterAtLevel_integral_matrix_conj Ω ε X l n γ (c k) (χ n k) hdet (hχ n k)
        rw [Betti.toGQ_sl] at h1
        exact GlobalTheory.T.isKummerCharacterAtLevel_padicInt_smul Ω ε X l n _ _ _ h1
      have hs := kum_sum X l n Finset.univ _ _ (fun k _ => hk k)
      rw [← hinv γ hγ i] at hs
      refine (GlobalTheory.T.isKummerCharacterAtLevel_add_zero_congr Ω ε X l n).2.2 _ _ _ hs ⟨1, one_pos, fun δ _ => ?_⟩
      rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [GlobalTheory.T.integralConjugateSL2Int_laws.2.1, map_intCast]
    obtain ⟨M, hM, hQ⟩ := near_fin _ _ fun i => GlobalTheory.T.kummerCharacters_eqOn_principalCongruence Ω ε X l n (c i) _ _ (hK i) (hχ n i)
    refine ⟨M, hM, fun δ hδ => ?_⟩
    simp only [map_sum, map_mul, MvPolynomial.algHom_C, (mon_expand (ZMod (l ^ n)) w).1, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hQ δ hδ i, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, MvPolynomial.algebraMap_eq]; ring
  · intro n
    obtain ⟨M, hM, hQ⟩ := near_fin _ _ fun i => GlobalTheory.T.kummerCharacters_eqOn_principalCongruence Ω ε X l n (c i) _ _
      (GlobalTheory.T.isKummerCharacterAtLevel_succ_reduce Ω ε X l n (c i) (χ (n + 1) i) (hχ (n + 1) i)) (hχ n i)
    refine ⟨M, hM, fun δ hδ => ?_⟩
    simp only [map_sum, map_mul, MvPolynomial.map_C, map_mon]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hQ δ hδ i]
  · intro n i
    convert hχ n i using 1
    funext δ
    exact MonExp.coeff_sum_mon _ w (fun j => χ n j δ) i
