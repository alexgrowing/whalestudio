import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.CompatH
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.IsFirstChernClassOfLineBundle
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquarePull
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwAcrFromBase
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullFrob
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitsPullbackEmptyProductOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientMapFactor
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullCup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapHClsEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmMorImg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulFil
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReductionCommutesGaloisAction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiBaseLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedHcPullHc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedHcCup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedHcOneH
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedCmp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullTransport

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.cp_red : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) {m n : ℕ} (h : n ≤ m) (j : ℕ) (x : Hc F κ k m j), β F κ k n j (redHc F κ k h j x) = (CH.Mor.ofNatTrans (redEl (F.pt κ) h)).pull j (β F κ k m j x) :=
  @GlobalTheory.CompanionTheory.BetaRed.beta_red

theorem CrystallineSemistableComparison.B.P.cp_gal : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ x, galOC σ (κ x) = κ x) (k : Bool) (n j : ℕ) (x : Hc F κ k n j), β F κ k n j (galHc F κ σ hσ k n j x) = (galMor σ (ptTw F κ σ hσ) n).pull j (β F κ k n j x) :=
  @GlobalTheory.CompanionTheory.BetaGal.β_gal

theorem CrystallineSemistableComparison.B.P.cp_phi : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (n j : ℕ) (x : Hc F κ true n j), β F κ true n j (phiHc F κ n j x) = (phiMor (F.pt κ) n).pull j (β F κ true n j x) :=
  @GlobalTheory.CompanionTheory.CrysPhi.phi_beta

theorem CrystallineSemistableComparison.B.P.cp_pull : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] {F F' : Fn O} (κ : O →+* OC l) (u : Fn.Map F F') (k : Bool) (n j : ℕ) (x : Hc F' κ k n j), β F κ k n j (pullHc κ u k n j x) = (pullMor (u.pt κ) n).pull j (β F' κ k n j x) :=
  @GlobalTheory.CompanionTheory.BetaPull.beta_pull

theorem CrystallineSemistableComparison.B.P.cp_cmp : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (n j : ℕ) (x : Hc F κ false n j), β F κ true n j ((cmpMor F κ n).pull j x) = β F κ false n j x :=
  @GlobalTheory.CompanionTheory.BetaCmp.β_cmp

theorem CrystallineSemistableComparison.B.P.cp_cup : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) (n : ℕ) {i j m : ℕ} (h : i + j = m) (x : Hc F κ k n i) (y : Hc F κ k n j), β F κ k n m ((CH.mulP (OcA F κ k n)).cup h x y) = (CH.mulP (AcrEl (F.pt κ) n)).cup h (β F κ k n i x) (β F κ k n j y) :=
  @GlobalTheory.CompanionTheory.CupBeta.beta_cup

theorem CrystallineSemistableComparison.B.P.cp_one : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) (n : ℕ), β F κ k n 0 (CH.oneH (OcA F κ k n)) = CH.oneH (AcrEl (F.pt κ) n) :=
  @GlobalTheory.CompanionTheory.CrisOne.β_one

theorem CrystallineSemistableComparison.B.P.cp_red_fil : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) {m n : ℕ} (h : n ≤ m) (r j : ℕ), ∀ x ∈ HcFil F κ k m r j, redHc F κ k h j x ∈ HcFil F κ k n r j :=
  @GlobalTheory.CompanionTheory.CrisFil.red_fil

theorem CrystallineSemistableComparison.B.P.cp_smul_fil : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) (n r j : ℕ) (a : Acris l), (base l).cris n a ∈ JJ k (base l) n → ∀ x ∈ HcFil F κ k n r j, a • x ∈ HcFil F κ k n (r + 1) j :=
  @GlobalTheory.CompanionTheory.BetaFil.smul_fil

theorem CrystallineSemistableComparison.B.P.ch_gal : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ x, galOC σ (κ x) = κ x) (k : Bool) {m n : ℕ} (h : n ≤ m) (j : ℕ) (x : Hc F κ k m j), redHc F κ k h j (galHc F κ σ hσ k m j x) = galHc F κ σ hσ k n j (redHc F κ k h j x) :=
  @GlobalTheory.CompanionTheory.CrisTransition.redHc_galHc

theorem CrystallineSemistableComparison.B.P.ch_phi : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {m n : ℕ} (h : n ≤ m) (j : ℕ) (x : Hc F κ true m j), redHc F κ true h j (phiHc F κ m j x) = phiHc F κ n j (redHc F κ true h j x) :=
  @GlobalTheory.CompanionTheory.CrisFrob.red_phi_le

theorem CrystallineSemistableComparison.B.P.ch_pull : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] {F F' : Fn O} (κ : O →+* OC l) (u : Fn.Map F F') (k : Bool) {m n : ℕ} (h : n ≤ m) (j : ℕ) (x : Hc F' κ k m j), redHc F κ k h j (pullHc κ u k m j x) = pullHc κ u k n j (redHc F' κ k h j x) :=
  @GlobalTheory.CompanionTheory.CrisTransition.redHc_pullHc

theorem CrystallineSemistableComparison.B.P.ch_cup : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) {m n : ℕ} (h : n ≤ m) {i j s : ℕ} (e : i + j = s) (x : Hc F κ k m i) (y : Hc F κ k m j), redHc F κ k h s ((CH.mulP (OcA F κ k m)).cup e x y) = (CH.mulP (OcA F κ k n)).cup e (redHc F κ k h i x) (redHc F κ k h j y) :=
  @GlobalTheory.CompanionTheory.CupTrans.redHc_cup

theorem CrystallineSemistableComparison.B.P.ch_one : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) {m n : ℕ} (h : n ≤ m), redHc F κ k h 0 (CH.oneH (OcA F κ k m)) = CH.oneH (OcA F κ k n) :=
  @GlobalTheory.CompanionTheory.CrisUnit.redHc_oneH

theorem CrystallineSemistableComparison.B.P.ch_cmp : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {m n : ℕ} (h : n ≤ m) (j : ℕ) (x : Hc F κ false m j), redHc F κ true h j ((cmpMor F κ m).pull j x) = (cmpMor F κ n).pull j (redHc F κ false h j x) :=
  @GlobalTheory.CompanionTheory.CrisCmp.main

theorem CrystallineSemistableComparison.B.P.firstChern_compatible : ∀ (l : ℕ) [Fact l.Prime], FirstChernCompatible l :=
  @GlobalTheory.CompanionTheory.FirstChernComparison.main
