import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbLLMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairIntAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorCoeffConjugateSeriesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaNormBoundHypothesesSatisfiedStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeUnitNormSqNonneg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjTorsionTranslateCombinationEntireGaussianGro
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaVacuaConjugatesCmPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacEqJets
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTwoTorsionCMPointAllConjugates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumMovedThetaVacuum

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean
open GlobalTheory.ThetaConj

namespace GlobalTheory.ConjJetComb

theorem applyAt0_mono (D : D7) {N N' : ℕ} (α : Mono D N N') (G : VC D N N' → ℂ) :
    GL3Theta.applyAt0 D (MvPolynomial.monomial α 1) G
      = ((α.prod fun _ n => n.factorial : ℕ) : ℂ) * Formalism.MainNotions.TaylorLogMetric.taylor D G α := by
  classical
  unfold Formalism.MainNotions.GL3Theta.applyAt0
  rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.sum_singleton, MvPolynomial.coeff_monomial,
    if_pos rfl, one_mul]
  simp [Finsupp.prod]

theorem jet_of_cjF {D : D7} {N N' : ℕ} {ρ : Qbar →ₐ[ℚ] ℂ} {F F' : VC D N N' → ℂ} (h : CjF D Qbar ρ F F')
    (α : Mono D N N') :
    GL3Theta.applyAt0 D (MvPolynomial.monomial α 1) F ∈ Qbar ∧
      Formalism.MainNotions.StandardLatticesGL3.cj Qbar ρ (GL3Theta.applyAt0 D (MvPolynomial.monomial α 1) F) =
        GL3Theta.applyAt0 D (MvPolynomial.monomial α 1) (fnConj D Qbar ρ F) := by
  rw [h.fnConj_eq, applyAt0_mono, applyAt0_mono]
  set n : ℕ := α.prod fun _ n => n.factorial
  have hn : (n : ℂ) ∈ Qbar := natCast_mem _ n
  refine ⟨mul_mem hn (h.2.2 α).1, ?_⟩
  rw [cj_mul ρ hn (h.2.2 α).1, (h.2.2 α).2, cj_mem ρ hn]
  have : (⟨(n : ℂ), hn⟩ : Qbar) = (n : Qbar) := rfl
  rw [this, map_natCast]

theorem conj_jet : ∀ (D : D7), GlobalTheory.NormSum.Inp D → ∀ (δ t0 : ℂ), Crv D D.host.ccK δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D D.host.ccK δ) t0 →
    ∀ (a b : ℕ), Even (a * b) → ∀ (e0 : VC D a b → ℂ), oddE0 D D.host.ccK δ t0 a b e0 →
    ∀ (Ls : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), SD D Ls → SD D Lt →
    ∀ (κ : ℂ), Mod1All κ → ∀ (k n : ℕ), 0 < k → ∀ (r : Fin n → Qbar) (s : Fin n → VC D a b),
    (∀ i, k • s i ∈ La D (tor0 D D.host.ccK δ) Ls Lt) → ∀ (ρ' : Qbar →ₐ[ℚ] ℂ) (m : Formalism.L2.Ker.DVar D.what₂.Tau a b →₀ ℕ),
      GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) (fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D D.host.ccK δ) (s i)
              (Iop D (tor0 D D.host.ccK δ) (La0 D (tor0 D D.host.ccK δ) _ _) (La D (tor0 D D.host.ccK δ) Ls Lt) e0) z) ∈ Qbar ∧
      Formalism.MainNotions.StandardLatticesGL3.cj Qbar ρ' (GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) (fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D D.host.ccK δ) (s i)
                (Iop D (tor0 D D.host.ccK δ) (La0 D (tor0 D D.host.ccK δ) _ _) (La D (tor0 D D.host.ccK δ) Ls Lt) e0) z)) =
        GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) (fnConj D Qbar ρ' fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D D.host.ccK δ) (s i)
          (Iop D (tor0 D D.host.ccK δ) (La0 D (tor0 D D.host.ccK δ) _ _) (La D (tor0 D D.host.ccK δ) Ls Lt) e0) z) := by
  intro D _ δ t0 hc ht0 N N' _ e0 he Ls Lt hL₁ hL₁' κ hκ k₀ n hk₀ r s hs ρ m
  have hG := (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1
  have hL := GlobalTheory.MovedVacuum.sd_stdL D N
  have hL' := GlobalTheory.MovedVacuum.sd_stdL D N'
  have hGth := he.1
  obtain ⟨b, κ₀, hb, hκ₀, rfl⟩ := he.2.2.2.1
  obtain ⟨k, hk, hC⟩ := GlobalTheory.T.exists_homLattice_commensurable_orthonormal D N N' _ b _ _ hb hL hL'
  have kB : KLat D (tor0 D D.host.ccK δ) (LaB D (tor0 D D.host.ccK δ) b) := Or.inl ⟨_, b, hb, rfl⟩
  have kL : KLat D (tor0 D D.host.ccK δ) (La D (tor0 D D.host.ccK δ) _ _) := Or.inr ⟨_, _, hL, hL', rfl⟩
  obtain ⟨-, -, c1, c2, -⟩ := GlobalTheory.T.coords_along_orthonormal_realSubfield_basis D hG D.host.ccK δ N N' _ b hb
  obtain ⟨d1, d2⟩ := GlobalTheory.T.halfPeriodTheta_differentiable_and_signedTranslate_invariant D hG D.host.ccK δ hc t0 ht0
  have hth0 := GlobalTheory.T.orthoProductTheta_mem_thetaSpace_of_lattice D (tor0 D D.host.ccK δ) N N' _ b _ c1 c2 d1 d2
  have hCb : Comm D b k (Set.range b) := by simpa using (comm_range D b).mul k
  obtain ⟨m1, -⟩ := conj_iop hc ρ hb (GlobalTheory.T.pullB_th0_mem_tr D _ δ hc t0 ht0 N N' _ b hb) hk
    hCb hC (LaB_eq D _ b ▸ kB) kL (LaB_eq D _ b ▸ hth0)
  rw [← LaB_eq, ← La_eq] at m1
  have hGm := Submodule.smul_mem _ (⟨κ₀, hκ₀.1⟩ : Qbar) m1
  obtain ⟨k₁, hk₁, hC₁⟩ := GlobalTheory.T.exists_homLattice_commensurable_orthonormal D N N' _ b Ls Lt hb hL₁ hL₁'
  have hC₂ := hC₁.mul k
  rw [mul_comm k k₁] at hC₂
  obtain ⟨m2, -⟩ := conj_iop hc ρ hb hGm (Nat.mul_pos hk₁ hk) (hC.mul k₁) hC₂ kL
      (Or.inr ⟨Ls, Lt, hL₁, hL₁', rfl⟩) hGth
  have hsB : ∀ i, (k₀ * k₁) • s i ∈ LaB D (tor0 D D.host.ccK δ) b := fun i => by
    rw [mul_nsmul]
    exact nsmul_mem_LaB (isTraceCompatibleTorusEmbedding_standardTorus D hG _ δ) (GlobalTheory.T.idealPeriodLattice_of_curveDatum D hG _ δ hc).2.2.2.2 hC₁ (hs i)
  have m3 := fun i => GlobalTheory.T.torsionTranslate_mem_thetaPullbackSpan D _ δ hc N N' _ b hb _ m2 (s i) _ (Nat.mul_pos hk₀ hk₁) (hsB i)
  choose F' hF' using fun i => galRel_all hc ρ hb (m3 i) one_pos
  exact jet_of_cjF ((CjF.sum Finset.univ fun i _ => (hF' i).1.mul (r i).2).mul hκ.1) m

end GlobalTheory.ConjJetComb
