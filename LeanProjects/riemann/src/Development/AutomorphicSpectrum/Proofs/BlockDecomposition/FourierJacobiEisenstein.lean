import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEisensteinLevelSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumMeas
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountableMatricesAndCosetsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiTermsSummableStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionLeftInvariantRationalParabolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeTranslationPreservedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaFourierJacobiLatticeSwapStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StronglyMeasurableCoefficientCompositionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiExpansionBoundedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzLatticeSumBoundedAltBis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StronglyMeasurableTwistedLatticeSumStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCharacterBilinearLawsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeTransformInvarianceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeTwistedSumPeriodicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedLatticeSumsBoundedProductStatement

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.CompanionTheory.FJE in

theorem GlobalTheory.CompanionTheory.FJE.fjEis : ZUnfold → ThTwist → FJEis := by
  intro hZ hTw D n ρ p hn M m ψ hψ b₀ hb χ χ' hχ hχ' θ hθ Ω hΩ s f hf hl hs g
  obtain ⟨i1, i2, i3, i4, -⟩ := lattice_Mx D ρ p
  haveI : BorelSpace (Mx D ρ p) := ⟨rfl⟩
  haveI : m.μ.IsAddHaarMeasure := m.hμ.1
  obtain ⟨hcM, hcC⟩ := GlobalTheory.T.countable_matrices_and_cosets D ρ p
  have hsum := fun g' => (hZ D n ρ p hn M m ψ hψ b₀ hb χ hχ s f hf hl hs g').1
  have hC := (hZ D n ρ p hn M m ψ hψ b₀ hb χ hχ s f hf hl hs g).2
  obtain ⟨t, ht, hT⟩ := GlobalTheory.T.fourier_jacobi_terms_summable M m ψ hψ b₀ χ s f hl g hC
  have hF : LeftInv (GF D n) (eisS f) := GlobalTheory.Eis.leftInv_cosetSum (GlobalTheory.T.section_left_invariant_rational_parabolic χ s f hχ hl)
  have hTr := fun q : GlobalTheory.Eis.Cosets (P D p) (GF D p) => GlobalTheory.T.lattice_translation_preserved M ((q.out : GF D p) : G D p) q.out.2
  choose T hT1 hT2 hT3 using hTr

  have hterm := fun (q : GlobalTheory.Eis.Cosets (P D p) (GF D p)) (v : Mx D ρ p × Mx D ρ p) =>
    GlobalTheory.T.theta_fourier_jacobi_lattice_swap M m ψ hψ b₀ hb hTw χ' hχ' θ hθ Ω hΩ χ s f hl g ((q.out : GF D p) : G D p) q.out.2 (T q) (hT3 q) v

  set A : GlobalTheory.Eis.Cosets (P D p) (GF D p) → Matrix (Fin ρ) (Fin p) D.host.E → Mx D ρ p × Mx D ρ p → ℂ :=
    fun q η v => Wz M m ψ b₀ f (M.sh (rt η) * M.emb (q.out : GF D p) * (M.nzx 0 v.2 * (M.sh v.1 * g))) with hA
  set Sq : GlobalTheory.Eis.Cosets (P D p) (GF D p) → Mx D ρ p × Mx D ρ p → ℂ := fun q v => ∑' η, A q η v with hSq
  have hAs : ∀ q v, Summable (fun η => ‖A q η v‖) := fun q v =>
    (summable_congr fun η => (hterm q v).1 η).2 (hT q (T q v).1).1
  have hSqle : ∀ q v, ‖Sq q v‖ ≤ t q := fun q v => by
    refine (norm_tsum_le_tsum_norm (hAs q v)).trans ?_
    rw [tsum_congr fun η => (hterm q v).1 η]
    exact (hT q (T q v).1).2
  have hAm : ∀ q η, StronglyMeasurable (A q η) := fun q η =>
    GlobalTheory.T.stronglyMeasurable_coefficient_composition M m ψ hψ b₀ f hf _ (by
      have h1 : Continuous fun v : Mx D ρ p × Mx D ρ p => M.nzx 0 v.2 :=
        M.nzx_cont.comp (continuous_const.prodMk continuous_snd)
      have h2 : Continuous fun v : Mx D ρ p × Mx D ρ p => M.sh v.1 := M.sh_cont.comp continuous_fst
      exact continuous_const.mul (h1.mul (h2.mul continuous_const)))
  have hSqm : ∀ q, StronglyMeasurable (Sq q) := fun q =>
    GlobalTheory.CompanionTheory.FJE.tsum_meas (fun η => hAm q η) fun v => (hAs q v).of_norm
  set Fz : Mx D ρ p × Mx D ρ p → ℂ := fun v => zc M m ψ b₀ (eisS f) (M.nzx 0 v.2 * (M.sh v.1 * g)) with hFz
  have hq : ∀ v, HasSum (fun q => Sq q v) (Fz v) := fun v =>
    (hsum (M.nzx 0 v.2 * (M.sh v.1 * g))).prod_fiberwise fun q => (hAs q v).of_norm.hasSum
  have hqn : ∀ v, Summable fun q => ‖Sq q v‖ := fun v => .of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => hSqle q v) ht
  have hFzm : StronglyMeasurable Fz := by
    have : Fz = fun v => ∑' q, Sq q v := funext fun v => (hq v).tsum_eq.symm
    rw [this]
    exact GlobalTheory.CompanionTheory.FJE.tsum_meas hSqm fun v => (hqn v).of_norm
  have hFzb : ∀ y x, ‖zc M m ψ b₀ (eisS f) (M.nzx 0 x * (M.sh y * g))‖ ≤ ∑' q, t q := fun y x => by
    have := (hq (y, x)).tsum_eq
    simp only [hFz] at this
    rw [← this]
    exact (norm_tsum_le_tsum_norm (hqn _)).trans ((hqn _).tsum_le_tsum (fun q => hSqle q _) ht)
  have h1 := GlobalTheory.T.fourier_jacobi_expansion_bounded M m ψ hψ b₀ (eisS f) hF g θ hθ (Ω 1) (hΩ.mem 1) _ hFzb hFzm

  have hcont : ∀ h, Continuous (Ω h) := fun h => hΩ.cont.comp (continuous_const.prodMk continuous_id)
  have hsm : ∀ h, StronglyMeasurable (Ω h) := fun h => (hcont h).stronglyMeasurable
  have hbd := fun h => GlobalTheory.T.exists_bound_lattice_sum_norm_schwartzA θ hθ (Ω h) (hΩ.mem h)
  obtain ⟨Bθ, hBθ⟩ := hbd 1
  have hthm : StronglyMeasurable fun v : Mx D ρ p × Mx D ρ p => conj (th ψ b₀ (Ω 1) 0 v.2 v.1) := by
    simp only [th_zero]
    exact Complex.continuous_conj.comp_stronglyMeasurable
      (GlobalTheory.T.stronglyMeasurable_twisted_lattice_sum ψ hψ b₀ (Ω 1) (hsm 1) fun y => (hBθ y).1)
  have hthb : ∀ v : Mx D ρ p × Mx D ρ p, ‖conj (th ψ b₀ (Ω 1) 0 v.2 v.1)‖ ≤ Bθ := fun v => by
    rw [RCLike.norm_conj, th_zero]
    have hn1 : ∀ ξ : Matrix (Fin ρ) (Fin p) D.host.E, ‖chv ψ b₀ v.2 (rt ξ) * Ω 1 (rt ξ + v.1)‖ = ‖Ω 1 (rt ξ + v.1)‖ := fun ξ => by
      rw [norm_mul, (GlobalTheory.T.heisenberg_character_bilinear_laws ψ hψ b₀).2.2.1, one_mul]
    refine (norm_tsum_le_tsum_norm ((summable_congr hn1).2 (hBθ v.1).1)).trans ?_
    rw [tsum_congr hn1]
    exact (hBθ v.1).2

  have hI : ∀ q, ∫ v in m.𝓕 ×ˢ m.𝓕, Sq q v * conj (th ψ b₀ (Ω 1) 0 v.2 v.1) ∂(m.μ.prod m.μ) =
      Rsec M m ψ b₀ f g Ω (((q.out : GF D p) : G D p) * 1) := fun q => by
    have hΦm : StronglyMeasurable fun y => Wz M m ψ b₀ f (M.sh y * M.emb (q.out : GF D p) * g) :=
      GlobalTheory.T.stronglyMeasurable_coefficient_composition M m ψ hψ b₀ f hf _ ((M.sh_cont.mul continuous_const).mul continuous_const)
    obtain ⟨B₂, hB₂⟩ := hbd ((q.out : GF D p) : G D p)
    have e1 : ∀ v, Sq q v * conj (th ψ b₀ (Ω 1) 0 v.2 v.1) =
        Ap ψ b₀ (fun y => Wz M m ψ b₀ f (M.sh y * M.emb (q.out : GF D p) * g)) (Ω ((q.out : GF D p) : G D p)) (T q v) :=
      fun v => (hterm q v).2
    simp only [e1]
    rw [GlobalTheory.T.lattice_transform_invariance m (T q) (hT1 q) (hT2 q) _ (fun ξ₁ ξ₂ v => GlobalTheory.T.lattice_twisted_sum_periodic ψ hψ b₀ _ _ ξ₁ ξ₂ v),
      GlobalTheory.T.twisted_lattice_sums_bounded_product m ψ hψ b₀ hb _ _ (t q) B₂ hΦm (hsm _) (fun y => hT q y) hB₂, mul_one]
    rfl

  set ν := (m.μ.prod m.μ).restrict (m.𝓕 ×ˢ m.𝓕) with hν
  have hmass : ν Set.univ = 1 := by
    rw [hν, Measure.restrict_apply_univ, Measure.prod_prod, m.hμ.2.2, one_mul]
  haveI : IsFiniteMeasure ν := ⟨by rw [hmass]; exact ENNReal.one_lt_top⟩
  have hbound : ∀ q v, ‖Sq q v * conj (th ψ b₀ (Ω 1) 0 v.2 v.1)‖ ≤ t q * Bθ := fun q v => by
    rw [norm_mul]
    exact mul_le_mul (hSqle q v) (hthb v) (norm_nonneg _) ((norm_nonneg _).trans (hSqle q v))
  have hint : ∀ q, Integrable (fun v => Sq q v * conj (th ψ b₀ (Ω 1) 0 v.2 v.1)) ν := fun q =>
    Integrable.of_bound ((hSqm q).mul hthm).aestronglyMeasurable (t q * Bθ) (.of_forall (hbound q))
  have hnorm : ∀ q, ∫ v, ‖Sq q v * conj (th ψ b₀ (Ω 1) 0 v.2 v.1)‖ ∂ν ≤ t q * Bθ := fun q => by
    have h2 := norm_integral_le_of_norm_le_const (μ := ν)
      (f := fun v => ‖Sq q v * conj (th ψ b₀ (Ω 1) 0 v.2 v.1)‖) (C := t q * Bθ)
      (.of_forall fun v => by simpa using hbound q v)
    have h3 : ν.real Set.univ = 1 := by simp [Measure.real, hmass]
    rw [h3, mul_one] at h2
    exact (le_abs_self _).trans (by simpa using h2)
  have hfs : Summable fun q => ∫ v, ‖Sq q v * conj (th ψ b₀ (Ω 1) 0 v.2 v.1)‖ ∂ν :=
    .of_nonneg_of_le (fun q => integral_nonneg fun _ => norm_nonneg _) hnorm (ht.mul_right Bθ)
  have hfin2 := hasSum_integral_of_summable_integral_norm hint hfs
  have e : (fun v => ∑' q, Sq q v * conj (th ψ b₀ (Ω 1) 0 v.2 v.1)) =
      fun v => Fz v * conj (th ψ b₀ (Ω 1) 0 v.2 v.1) := funext fun v => by
    rw [tsum_mul_right, (hq v).tsum_eq]
  rw [e] at hfin2
  rw [h1, ← hfin2.tsum_eq, eisS, GlobalTheory.Eis.cosetSum]
  exact tsum_congr fun q => hI q
