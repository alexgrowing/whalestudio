import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumMovedThetaVacuum
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsPowPrincipalFractionalIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseThetaVectorIsVacuumEvenRanksStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelDetIdealSelfDualNormOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormOneCharacterModulusOneAllEmbeddingsStatement

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.FamilyTieProof

theorem std : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), TaylorLogMetric.adm1 D → GL3Theta.InducedCMType D → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → B.kc.YFinite → ∀ N N' : ℕ, Even N → Even N' → StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc δ) (B.ω₀ / 2) (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') (B.thZero N N') := GlobalTheory.T.base_theta_vector_is_vacuum_even_ranks

theorem detn1 : ∀ (D : D7) (N : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), StandardLatticesGL3.SD D L → TaylorLogMetric.N1 D (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) L) := GlobalTheory.T.relDetIdeal_selfDual_normOne

theorem chin1 : ∀ (D : D7) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → ∀ 𝔞 : TaylorLogMetric.IdE D, TaylorLogMetric.N1 D 𝔞 → StandardLatticesGL3.Mod1All (χ 𝔞) := GlobalTheory.T.normOneCharacter_modulusOne_all_embeddings

theorem mod1All_mul' {a b : ℂ} (ha : StandardLatticesGL3.Mod1All a) (hb : StandardLatticesGL3.Mod1All b) : StandardLatticesGL3.Mod1All (a * b) := by
  obtain ⟨h1, h1'⟩ := ha
  obtain ⟨h2, h2'⟩ := hb
  refine ⟨mul_mem h1 h2, fun σ => ?_⟩
  have e : (⟨a * b, mul_mem h1 h2⟩ : TaylorLogMetric.Qbar) = ⟨a, h1⟩ * ⟨b, h2⟩ := rfl
  rw [e, map_mul, norm_mul, h1' σ, h2' σ, one_mul]

theorem mod1All_inv {a : ℂ} (ha : StandardLatticesGL3.Mod1All a) : StandardLatticesGL3.Mod1All a⁻¹ := by
  obtain ⟨h1, h1'⟩ := ha
  refine ⟨inv_mem h1, fun σ => ?_⟩
  have e : (⟨a⁻¹, inv_mem h1⟩ : TaylorLogMetric.Qbar) = (⟨a, h1⟩ : TaylorLogMetric.Qbar)⁻¹ := rfl
  rw [e, map_inv₀, norm_inv, h1' σ, inv_one]

theorem mod1All_pow {a : ℂ} (ha : StandardLatticesGL3.Mod1All a) (n : ℕ) : StandardLatticesGL3.Mod1All (a ^ n) := by
  induction n with
  | zero =>
    refine ⟨by simpa using one_mem TaylorLogMetric.Qbar, fun σ => ?_⟩
    have e : (⟨a ^ 0, by simpa using one_mem TaylorLogMetric.Qbar⟩ : TaylorLogMetric.Qbar) = 1 := by ext; simp
    rw [e, map_one, norm_one]
  | succ n ih => rw [pow_succ]; exact mod1All_mul' ih ha

theorem mod1All_zpow {a : ℂ} (ha : StandardLatticesGL3.Mod1All a) (n : ℤ) : StandardLatticesGL3.Mod1All (a ^ n) := by
  cases n with
  | ofNat n => simpa using mod1All_pow ha n
  | negSucc n => rw [zpow_negSucc]; exact mod1All_inv (mod1All_pow ha _)

theorem genusOneVacuum_const_mul_modulusOne {D : D7} {T : TaylorLogMetric.Tor D} {t0 : ℂ} {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {G : TaylorLogMetric.VC D N N' → ℂ} {c : ℂ} (hc : StandardLatticesGL3.Mod1All c)
    (hG : StandardLatticesGL3.ThetaVectorUpToUnits D T t0 L L' G) : StandardLatticesGL3.ThetaVectorUpToUnits D T t0 L L' (fun z => c * G z) := by
  obtain ⟨b, κ, hb, hκ, rfl⟩ := hG
  exact ⟨b, c * κ, hb, mod1All_mul' hc hκ, funext fun z => by simp only [mul_assoc]⟩

theorem genusOneVacuum_indep_twoTorsionPoint {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : StandardLatticesGL3.Crv D cc δ) {t t' : ℂ}
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc δ) t) (ht' : GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc δ) t') {N N' : ℕ}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    {G : TaylorLogMetric.VC D N N' → ℂ} (h : StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc δ) t L L' G) :
    StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc δ) t' L L' G := by
  have e : GL3Theta.th0 (TaylorLogMetric.lamOf D cc δ) t = GL3Theta.th0 (TaylorLogMetric.lamOf D cc δ) t' := by
    have := GlobalTheory.ThetaConj.evenTheta_add_lattice_mem (GlobalTheory.ThetaConj.isLat_lamOf hc) t' (GlobalTheory.Glob.isThetaZero_unique_lattice hc ht ht')
    rwa [add_sub_cancel] at this
  unfold StandardLatticesGL3.ThetaVectorUpToUnits at h ⊢
  exact e ▸ h

theorem chiFac_mod1All (D : D7) (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) (N N' : ℕ)
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hA : TaylorLogMetric.admitted D N N' L L') : StandardLatticesGL3.Mod1All (Base.chiFac (D := D) χ N N' L L') :=
  mod1All_mul' (mod1All_zpow (chin1 D χ hχ _ (detn1 D N L hA.2.2.1)) _)
    (mod1All_zpow (chin1 D χ hχ _ (detn1 D N' L' hA.2.2.2)) _)

theorem familyTie : GlobalTheory.ColNorms.FamilyTie := by
  intro D cc δ B χ ha hp hcc hδ hχ hY t0 ht N N' L L' hA
  have hc : StandardLatticesGL3.Crv D cc δ := ⟨hcc, hδ⟩
  have h0 := genusOneVacuum_indep_twoTorsionPoint hc B.t0 ht (std D cc δ B ha hp hcc hδ hY N N' hA.1 hA.2.1)
  exact genusOneVacuum_const_mul_modulusOne (chiFac_mod1All D χ hχ N N' L L' hA)
    (GlobalTheory.MovedVacuum.isVacuum_movedThetaVacuum D cc δ B t0 hc ht N N' L L' hA.2.2.1 hA.2.2.2 h0)

end GlobalTheory.FamilyTieProof
