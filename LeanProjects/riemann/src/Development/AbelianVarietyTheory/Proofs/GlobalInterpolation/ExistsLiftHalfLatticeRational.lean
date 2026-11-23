import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PerLatticeFactsStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.MomT

theorem natCast_smul_eq_ring {E : Type} [Field E] [NumberField E] {a b : ℕ} (n : ℕ) (y : HomE E a b) :
    (n : 𝓞 E) • y = (n : E) • y := by
  rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]

theorem natCast_smul_mem {E : Type} [Field E] [NumberField E] {a b : ℕ} (M : Submodule (𝓞 E) (HomE E a b)) (n : ℕ)
    {y : HomE E a b} (hy : y ∈ M) : (n : E) • y ∈ M := by
  rw [← natCast_smul_eq_ring]; exact M.smul_mem _ hy

theorem exists_lift_halfAO : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (cA c : ℕ), A.AA.FG → A.AA ≠ ⊥ → (∀ P ∈ S, conjPrime₂ P ∉ S) → A.AAUnit S → IsSdLat N → IsSdLat N' → 0 < cA → 0 < c → ∀ x ∈ divLat cA (homAt S N N'), ∃ t ∈ halfAO S (per A N N') (cA * c), t - x ∈ mulLat c (homAt S N N') := by
  intro X A a b S N N' cA c hfg hne _ hU hN hN' hcA hc x hx
  obtain ⟨-, hfull, -, hloc⟩ := GlobalTheory.T.per_relIndex_ne_zero_and_mem_locP_iff X A a b N N' hfg hne hN hN'
  have hF : GlobalTheory.ThetaMove.Full (per A N N') := fun y => by
    obtain ⟨n, hn, hy⟩ := hfull y
    exact ⟨n, hn, by rwa [natCast_smul_eq_ring]⟩
  have hD : ((cA * c : ℕ) : X.E) ≠ 0 := by exact_mod_cast (Nat.mul_pos hcA hc).ne'
  obtain ⟨t, h1, h2⟩ := hF.approx S (((cA * c : ℕ) : X.E)⁻¹ • x)
  have hx' : (cA : X.E) • x ∈ homAt S N N' := by
    rw [← natCast_smul_eq_ring]; exact hx
  refine ⟨((cA * c : ℕ) : X.E) • t, ?_, (cA : X.E) • (t - ((cA * c : ℕ) : X.E)⁻¹ • x), ?_, ?_⟩
  · unfold halfAO twist₂
    rw [Submodule.mem_iInf]
    intro Q
    rw [Submodule.mem_comap]
    change ((((cA * c : ℕ) : X.E) ^ (-expS S Q))⁻¹ • ((cA * c : ℕ) : X.E) • t) ∈ _
    unfold expS
    split_ifs with hQ hQ'
    · have e : ((((cA * c : ℕ) : X.E) ^ (-(1 : ℤ)))⁻¹ • ((cA * c : ℕ) : X.E) • t) =
          ((cA * c : ℕ) : X.E) • ((cA * c : ℕ) : X.E) • (t - ((cA * c : ℕ) : X.E)⁻¹ • x) + (c : X.E) • (cA : X.E) • x := by
        rw [smul_sub, smul_inv_smul₀ hD, smul_sub, zpow_neg, inv_inv, zpow_one, smul_smul (c : X.E), mul_comm (c : X.E),
          ← Nat.cast_mul, sub_add_cancel]
      rw [e]
      exact add_mem (natCast_smul_mem _ _ (natCast_smul_mem _ _ (h1 Q hQ)))
        (natCast_smul_mem _ _ ((hloc Q (hU Q hQ) _).2 (hx' Q hQ)))
    · rw [neg_neg, zpow_one, inv_smul_smul₀ hD]
      exact h2 Q hQ
    · rw [neg_zero, zpow_zero, inv_one, one_smul]
      exact natCast_smul_mem _ _ (h2 Q hQ)
  · intro P hP
    exact (hloc P (hU P hP) _).1 (natCast_smul_mem _ _ (h1 P hP))
  · change (c : 𝓞 X.E) • (cA : X.E) • (t - ((cA * c : ℕ) : X.E)⁻¹ • x) = _
    rw [natCast_smul_eq_ring, smul_smul, mul_comm (c : X.E), ← Nat.cast_mul, smul_sub, smul_inv_smul₀ hD]

end GlobalTheory.MomT
