import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.RhoActionCup.RHofTrGen
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.RhoActionCup.CupGenA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ValuationChainProofs.RHofLev
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.InstSt
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.CrystallineFirstChernLevelCompat
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ValuationChainProofs.fil_lev
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ValuationChainProofs.CrystallineFirstChernLevelCompat
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ValuationChainProofs.CovSm
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ValuationChainProofs.RHofIncl
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.HomSGood
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.NmHONmPullBBMap
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.HomGalGood
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.HomPullRHofGood
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.CupGood
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ExistsLim
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationUniqueStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRealizationOfCompatibleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationAddStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationSmulStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationFunctorialStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationCupProductStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationUnitClassStatement
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.LatLink
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.TranscendentalPeriodUnits.IsUOfIsUnit
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LieComplementChartContDiffAt

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap.Mo

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
variable (S : LevSys (per l K)) (hS : S.Good) (hC : ∀ m, (S.L m).CrisOK)

variable [FiniteDimensional ℚ_[l] K]

theorem chK_good (M : Model l K) (hM : M.Sm) (m : ℕ) :
    ∃ s₁, ∀ s, s₁ ≤ s → (chK S hS hC M m s).Good := by
  obtain ⟨U⟩ := cov_sm_pf M hM
  refine ⟨Finset.univ.sup U.d + (m + 1), fun s hs => ?_⟩
  refine chain_good (hS.lev m) M s hM U (fun α => ?_) (by omega) _ (rHof_tr_gen _ _ M s)
  have := Finset.le_sup (f := U.d) (Finset.mem_univ α)
  omega

theorem rho_mono (M : Model l K) (m : ℕ) {s s' : ℕ} (h : s ≤ s') (hG : (chK S hS hC M m s).Good)
    (hG' : (chK S hS hC M m s').Good) {j : ℕ} (x : ∀ n, M.Hc false n j) (f : Module.Dual K (HdR M.q j) →+ (S.L m).B)
    (hf : (chK S hS hC M m s').Rho x f) : (chK S hS hC M m s).Rho x f := by
  have H := GlobalTheory.T.realization_functorial (chK S hS hC M m s') (chK S hS hC M m s)
    (homS (hS.lev m) M h (qb_le (hS.lev m) M s) (qb_le (hS.lev m) M s')
      (rHof (dOf S hS hC m) (hcOf S hS hC m) M s) (rHof (dOf S hS hC m) (hcOf S hS hC m) M s'))
    hG' hG (homS_good_of_inclHM _ _ _ _ _ _ _ (rHof_incl_pf S hS hC M m h)) x f hf
  have e : (homS (hS.lev m) M h (qb_le (hS.lev m) M s) (qb_le (hS.lev m) M s')
      (rHof (dOf S hS hC m) (hcOf S hS hC m) M s) (rHof (dOf S hS hC m) (hcOf S hS hC m) M s')).tr j f = f := by
    ext φ
    rfl
  rw [e] at H
  exact H

theorem rho_uniq_pf : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ j m x f f',
    rhoK S hS hC a j m x f → rhoK S hS hC a j m x f' → f = f' := by
  intro M a hM j m x f f' ⟨_, s₀, h⟩ ⟨_, s₀', h'⟩
  obtain ⟨s₁, hg⟩ := chK_good S hS hC M hM m
  exact GlobalTheory.T.realization_unique (chK S hS hC M m (max s₁ (max s₀ s₀'))) (hg _ (le_max_left _ _)) _ f f'
    (h _ (le_trans (le_max_left _ _) (le_max_right _ _))) (h' _ (le_trans (le_max_right _ _) (le_max_right _ _)))

theorem rho_ex_pf : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ j m x, ∃ f, rhoK S hS hC a j m x f := by
  intro M a hM j m x
  obtain ⟨s₁, hg⟩ := chK_good S hS hC M hM m
  obtain ⟨f, hf⟩ := GlobalTheory.T.exists_realization_of_compatible (chK S hS hC M m s₁) (hg s₁ le_rfl) (show (M.HS false j).lim from x).1
    (fun n => (show (M.HS false j).lim from x).2 n)
  refine ⟨f, hM, s₁, fun s hs => ?_⟩
  obtain ⟨g, hgs⟩ := GlobalTheory.T.exists_realization_of_compatible (chK S hS hC M m s) (hg s hs) (show (M.HS false j).lim from x).1
    (fun n => (show (M.HS false j).lim from x).2 n)
  have e : g = f := GlobalTheory.T.realization_unique _ (hg s₁ le_rfl) _ g f (rho_mono S hS hC M m hs (hg s₁ le_rfl) (hg s hs) _ g hgs) hf
  rwa [e] at hgs

theorem rho_add_pf : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ j m x y f g,
    rhoK S hS hC a j m x f → rhoK S hS hC a j m y g → rhoK S hS hC a j m (x + y) (f + g) := by
  intro M a hM j m x y f g ⟨_, s₀, h⟩ ⟨_, s₀', h'⟩
  exact ⟨hM, max s₀ s₀', fun s hs => GlobalTheory.T.realization_add (chK S hS hC M m s) _ _ f g
    (h s (le_trans (le_max_left _ _) hs)) (h' s (le_trans (le_max_right _ _) hs))⟩

theorem rho_smul_pf : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ j m (c : (per l K).A) x f, rhoK S hS hC a j m x f →
    rhoK S hS hC a j m (c • x) ((AddMonoidHom.mulLeft ((S.L m).ι ((S.L m).lam c))).comp f) := by
  intro M a hM j m c x f ⟨_, s₀, h⟩
  exact ⟨hM, s₀, fun s hs => GlobalTheory.T.realization_smul (chK S hS hC M m s) c _ f (h s hs)⟩

theorem rho_lin'_pf : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ j m x f, rhoK S hS hC a j m x f →
    ∀ (k : K) φ, f (k • φ) = algebraMap K (S.L m).B k * f φ := by
  intro M a hM j m x f ⟨_, s₀, h⟩ k φ
  exact (h s₀ le_rfl).1 k φ

theorem rho_fil_pf : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ j m x f, rhoK S hS hC a j m x f → ∀ n r : ℕ, n ≤ m →
    (dat Amp).fil a j n x → ∀ φ : Module.Dual K (HdR M.q j), (∀ h ∈ FilR M.q j (r + 1), φ h = 0) →
      f φ ∈ pdP (S.L m).γB (n - r) := by
  intro M a hM j m x f ⟨_, s₀, h⟩ n r hnm hfil φ hφ
  obtain ⟨U⟩ := cov_sm_pf M hM
  have hU : ∀ α, U.d α + (m + 1) ≤ max s₀ (Finset.univ.sup U.d + (m + 1)) := fun α => by
    have := Finset.le_sup (f := U.d) (Finset.mem_univ α)
    omega
  exact fil_lev_pf (hS.lev m) (dOf S hS hC m) (hcOf S hS hC m) M _ hM U hU (by omega) _
    (fun n => (show (M.HS false j).lim from x).2 n) f (h _ (le_max_left _ _)) n r (by omega) hfil φ hφ

theorem rho_firstChern_formula : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ m x f c, rhoK S hS hC a 2 m x f → (dat Amp).c1H a x →
    IsFirstChernDeRham _ (lineK a.1) c → ∀ φ, f φ = algebraMap K (S.L m).B (φ c) := by
  intro M a hM m x f c ⟨_, s₀, h⟩ hx hc φ
  obtain ⟨U⟩ := cov_sm_pf M hM
  obtain ⟨s₁, hg⟩ := chK_good S hS hC M hM m
  have hU : ∀ α, U.d α + (m + 1) ≤ max (max s₀ s₁) (Finset.univ.sup U.d + (m + 1)) := fun α => by
    have := Finset.le_sup (f := U.d) (Finset.mem_univ α)
    omega
  have H := crystalline_firstChern_level (hS.lev m) (dOf S hS hC m) (hcOf S hS hC m) M _ hM U hU (by omega) a x hx c hc
  have e := GlobalTheory.T.realization_unique (chK S hS hC M m _) (hg _ (by omega)) _ f (evB M c) (h _ (by omega)) H
  rw [e]
  rfl

end CrystallineSemistableComparison.Pb.Kap.Mo
