import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergIsotropicFixesVacuum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitProductRescaleDisjointFinsets
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulMemLatOIdem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDualStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLatticeIffIntegralMatrixSplitChart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymplOHEqZeroOfHO
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsTameFinitePlaceHermitianAllStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.CommVac

variable {D : D7}

theorem symplO_add_right (S T : HSp D) (x y y' : WO S T) :
    symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  unfold symplO hO
  simp only [Matrix.add_apply, map_add, mul_add, add_mul, Finset.sum_add_distrib]

theorem hO_smul_left (S T : HSp D) (a : AE D) (x y : WO S T) : hO S T (a • x) y = a * hO S T x y := by
  unfold hO
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem hO_smul_right (S T : HSp D) (a : AE D) (x y : WO S T) : hO S T x (a • y) = cA D a * hO S T x y := by
  unfold hO
  simp only [Matrix.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem symplO_smul_comm (S T : HSp D) {a : AE D} (ha : cA D a = a) (x y : WO S T) :
    symplO S T (a • x) y = symplO S T x (a • y) := by
  unfold symplO
  rw [hO_smul_left, hO_smul_right, ha]

set_option maxHeartbeats 1000000 in

theorem heisO_offPart_vac : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 →
    ∀ w ∈ Ann W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (depLat G (.chi i 0)), w.map (infPart D) = 0 →
    ∃ c : ℂ, heisO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) ((1 - e - cA D e) • w) (W.vac i) = c • W.vac i := by
  intro D _ T L μ0 hL sc G W M _ i hi e he w hw hinf
  classical
  obtain ⟨hsdS, hsdT⟩ := GlobalTheory.CosetRow.selfDual_chi hL G i hi
  obtain ⟨h1, -, h3⟩ := GlobalTheory.T.self_dual_lattice_pairing_dual D W.ψ _ _ (G.latS (.chi i 0)) (G.latT (.chi i 0)) W.ψ_std hsdS hsdT
  have hlat := (W.vac_is i hi).2.lat
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hec : e * cA D e = 0 := he.2
  have hce : cA D e * cA D e = cA D e := by rw [← map_mul, hee]
  have hff : (1 - e - cA D e) * (1 - e - cA D e) = 1 - e - cA D e := by
    linear_combination hee + hce + 2 * hec
  have hfc : cA D (1 - e - cA D e) = 1 - e - cA D e := by
    rw [map_sub, map_sub, map_one, Formalism.L2.Theta.cA_cA]; ring
  have hfint : finPart D (1 - e - cA D e) ∈ intAE D :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hff])
  have hef : ∀ e', IsIdemSum e' G.pl.W0 → e' * (1 - e - cA D e) = 0 := fun e' he' => by
    rw [GlobalTheory.StepVecSum.idemSum_eq (G.V (.grid 0 0)) he he']
    linear_combination -hee - hec
  have hdep : ∀ u ∈ latO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _)
      (fun _ => True), (1 - e - cA D e) • u ∈ depLat G (.chi i 0) := fun u hu =>
    ⟨GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ _ hfint u hu, fun e' he' => by
      rw [smul_smul, hef e' he', zero_smul]; exact AddSubgroup.zero_mem _⟩
  have key : ∀ u ∈ latO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _)
      (fun _ => True), W.ψ (symplO _ _ w ((1 - e - cA D e) • u)) = 1 := by
    intro u hu
    obtain ⟨v, hvdef⟩ : ∃ v, v = (1 - e - cA D e) • u := ⟨_, rfl⟩
    rw [← hvdef]
    have hv : v ∈ latO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _)
        (fun _ => True) := hvdef ▸ GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ _ hfint u hu
    have hpiece : ∀ c : AE D, finPart D c ∈ intAE D → c • v ∈ depLat G (.chi i 0) := fun c hc => by
      rw [hvdef, smul_smul, mul_comm, ← smul_smul]
      exact hdep _ (GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ c hc u hu)
    have hadd : ∀ a b : AE D, W.ψ (symplO _ _ w (a • v)) = 1 → W.ψ (symplO _ _ w (b • v)) = 1 →
        W.ψ (symplO _ _ w ((a + b) • v)) = 1 := fun a b ha hb => by
      rw [add_smul, symplO_add_right, AddChar.map_add_eq_mul, ha, hb, one_mul]
    have hsplit : ∀ e₁, IsSplitIdem D e₁ → W.ψ (symplO _ _ w (e₁ • v)) = 1 := fun e₁ h₁ =>
      hw.2 e₁ h₁ _ (hpiece _ (GlobalTheory.SplitHomLattice.idem_int h₁))
        (fun a b => by rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, h₁.1])
    have hQ := GlobalTheory.FinPl.FlatFix.finite_two (D := D) (fun _ => True)
    have hmemQ : ∀ x, x ∈ hQ.toFinset ↔ True ∧ (2 : 𝓞 D.host.F) ∈ x.asIdeal := fun x => hQ.mem_toFinset
    have hch : ∀ x, x ∈ hQ.toFinset → ∃ e₁ ε, IsSplitIdem D e₁ ∧ IsPlaceIdem D x ε ∧
        e₁ + cA D e₁ = algebraMap (AF D.host.F) (AE D) ε := by
      intro x hx
      rcases (GlobalTheory.T.isTameFinitePlaceHermitian_all D x).2 with h | h
      · exact absurd ((hmemQ x).1 hx).2 h
      · exact h
    choose! es εs hes hεs hsum using hch
    have hdec := GlobalTheory.FinPl.FlatFix.indicatorIdempotent_eq_add_sum (fun _ => True) hQ.toFinset hmemQ εs hεs
    have hvc : algebraMap (AF D.host.F) (AE D) (GlobalTheory.SelfDualAt.cP (fun _ => True)) • v = v := by
      ext a b
      rw [Matrix.smul_apply, smul_eq_mul]
      exact GlobalTheory.SelfDualAt.algebraMap_placeIdempotent_mul _ _ (GlobalTheory.FinPl.LatMem.latO_mxAt hv a b)
    rw [← hvc, hdec, map_add, map_sum]
    refine hadd _ _ ?_ ?_
    · have hβ := GlobalTheory.FinPl.FlatFix.int_alg_pair (D := D) (GlobalTheory.FinPl.FlatFix.halfOff_int (D := D) fun _ => True)
      have e2 : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.FinPl.FlatFix.halfOff (fun _ => True) +
          GlobalTheory.FinPl.FlatFix.halfOff (D := D) (fun _ => True))) • v =
          2 • (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.FinPl.FlatFix.halfOff (D := D) (fun _ => True))) • v) := by
        rw [GlobalTheory.FinPl.FlatFix.pair_add, map_add, add_smul, two_nsmul]
      rw [e2]
      exact hw.1 _ (hpiece _ hβ)
    · refine Finset.sum_induction _ (fun c => W.ψ (symplO _ _ w (c • v)) = 1) hadd ?_ ?_
      · have h0 := symplO_add_right (G.pS (.chi i 0)) (G.pT (.chi i 0)) w 0 0
        rw [add_zero] at h0
        have h0' : symplO (G.pS (.chi i 0)) (G.pT (.chi i 0)) w 0 = 0 := by linear_combination -h0
        show W.ψ (symplO _ _ w ((0 : AE D) • v)) = 1
        rw [zero_smul, h0', AddChar.map_zero_eq_one]
      · intro x hx
        rw [← hsum x hx]
        exact hadd _ _ (hsplit _ (hes x hx)) (hsplit _ (GlobalTheory.IdemSumVac.isSplitIdem_cA (hes x hx)))
  have hfin' : ((1 - e - cA D e) • w).map (infPart D) = 0 := by
    ext a b
    have := congrFun (congrFun hinf a) b
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, Matrix.zero_apply] at this ⊢
    rw [this, mul_zero]
  have hmem : (1 - e - cA D e) • w ∈ latO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _)
      (G.latT (.chi i 0) : Set _) (fun _ => True) :=
    (h1 _ hfin').2 fun u' hu' => by rw [symplO_smul_comm _ _ hfc]; exact key u' hu'
  obtain ⟨ε, -, hε⟩ := h3 _ hlat _ hmem
  exact ⟨ε, hε _ hlat⟩

end GlobalTheory.CommVac

end
