import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelAtPrimeEqSumTorsionTranslates
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicValuationThetaKernelJetBound
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JetsTorsionTranslatesCmThetaProductStatement
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.CmbIop
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.CmbJet
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem UpperTheory.WildA.tabBd :
    ∀ (D : D7), Inp D → ∀ (S : Finset ℕ) (dl : ℕ → ℝ), Letters D S dl → ∀ (cc : Ideal (𝓞 D.host.K)), cc = ⊤ → ∀ (δ t0 : ℂ), Crv D cc δ →
      GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (a b : ℕ) (e0 : VC D a b → ℂ), oddE0 D cc δ t0 a b e0 →
      ∀ (Ls : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), SD D Ls → SD D Lt →
      ∀ (l : ℕ) [Fact l.Prime], EqAt D l Ls (stdL D a) → EqAt D l Lt (stdL D b) → ∀ k : ℕ, 0 < k → (l ∣ k → SplitIn D l) →
      ∀ (κ : ℂ) (n g : ℕ) (r : Fin n → Qbar) (s : Fin n → VC D a b), Mod1All κ → (∀ lam : Qbar →+* ℂ_[l], ‖lamC lam κ‖ = 1) →
      (∀ i, k • s i ∈ La D (tor0 D cc δ) Ls Lt) → (∀ i, IsIntegral ℤ ((k : Qbar) ^ g * r i)) →
      ∀ (lam : Qbar →+* ℂ_[l]) (mon : GL3Theta.Idx D a b →₀ ℕ),
        Term.Bd lam ((l : ℝ) ^ ((mon.degree : ℝ) * (dl l + (if l = D.host.d then 1 / 4 else 0) + (padicValNat l k : ℝ)) +
            (g : ℝ) * (padicValNat l k : ℝ)))
          (GL3Theta.applyAt0 D (MvPolynomial.monomial mon 1) fun z => κ * ∑ i, (r i : ℂ) *
            U D (tor0 D cc δ) (s i) (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a b) (La D (tor0 D cc δ) Ls Lt) e0) z) := by
  intro D hI S dl hL cc hcc δ t0 hC ht a b e0 he0 Ls Lt hLs hLt l _ hEs hEt k hk hsp κ n g r s hκ hκ1 hs hr lam mon
  have hp : l.Prime := Fact.out
  have hp0 : (0 : ℝ) < l := by exact_mod_cast hp.pos
  obtain ⟨β, M, hβ, hloc, hM, hMl, hcmb⟩ :=
    UpperTheory.WildA.cmbIop D hI cc hcc δ t0 hC ht a b e0 he0 Ls Lt hLs hLt l lam hEs hEt k hk
  have hv : padicValNat l (M * k) = padicValNat l k := by
    rw [padicValNat.mul hM.ne' hk.ne',
      padicValNat.eq_zero_of_not_dvd (hp.coprime_iff_not_dvd.1 hMl.symm), zero_add]
  have hsp' : l ∣ M * k → SplitIn D l := fun h => hsp (hMl.symm.dvd_of_dvd_mul_left h)
  have hkn := Term.norm_natCast_inv l hk.ne'
  have hk0 : 0 < ‖(k : ℂ_[l])‖ := norm_pos_iff.2 (by exact_mod_cast hk.ne')
  have hrb : ∀ i, KernelAt.Bd lam ((l : ℝ) ^ ((g : ℝ) * (padicValNat l k : ℝ))) (r i : ℂ) := by
    intro i
    refine ⟨(r i).2, ?_⟩
    have h1 : ‖lam ((k : Qbar) ^ g * r i)‖ ≤ 1 := KernelAt.norm_le_one_of_isIntegral (by
      convert map_isIntegral_int lam (hr i) <;> exact Subsingleton.elim _ _)
    rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow] at h1
    rw [mul_comm, Real.rpow_mul_natCast hp0.le, ← hkn, inv_pow, ← one_div, le_div_iff₀ (pow_pos hk0 g), mul_comm]
    exact h1
  have hκb : KernelAt.Bd lam 1 κ := by
    obtain ⟨h, -⟩ := hκ
    refine ⟨h, ?_⟩
    have h1 := hκ1 lam
    rw [lamC, dif_pos h] at h1
    exact h1.le
  have hall := KernelAt.Cmb.smul hκb
    (KernelAt.Cmb.sum fun i => KernelAt.Cmb.smul (hrb i) (hcmb (s i) (hs i)))
  have h := UpperTheory.WildA.cmbJet D hI S dl hL cc hcc δ t0 hC ht a b _ l lam β hβ hloc (M * k)
    (Nat.mul_pos hM hk) hsp' _ (by positivity) _ hall mon
  rw [hv, one_mul, mul_one, ← Real.rpow_add hp0, add_comm] at h
  exact h
