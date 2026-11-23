import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNatDatumSquareFlip
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestPlacesPrimeToLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleFormConvergentThetaIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDistributionRationalPointsInvariantTripleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityTensorModelVWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationSplitPlaceSkewHermitianUnitarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetOneMulBlockUnitaryDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaTripleOfSquareGridLatticeCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigRouteKernelEqConstMulThetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralConjugateScaledUnitaryGroupEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussianDatumFlippedFiniteTensorBigRouteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPolynomialVectorReachedByRealDatumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareFlipReachesLocalQuotientClassesStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.BigNZ

theorem blkU_mul {D : D7} (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (h : J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram A B e) (x y : GA D A × GA D B) : blkU A B e h x * blkU A B e h y = blkU A B e h (x * y) := by
  refine Subtype.ext (Units.ext ?_)
  exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_mul e _ _ _ _

theorem exists_integral_ne_zero (hSA : GlobalTheory.Published.StrongApproxSU) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree)
    (hLM : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching) {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}
    (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hst : SquareStanding G t) :
    ∃ M : Vol G, M.Is t ∧ ∃ a τ τ' n Φ,
      (∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) ∧ HasFlip B t ρ i j n Φ τ τ' ∧
      ∃ g g₁, ∫ u in M.fd _, kerBig W (tensT W a τ) g g₁ u ∂M.ν _ ≠ 0 := by
  classical
  obtain ⟨M, hM⟩ := exists_vol G hL t
  obtain ⟨e, Bs, Γ, X, om, om', h, hT, hti⟩ := GlobalTheory.T.exists_thetaTripleOfSquareGrid_latticeCompatible hL W t i j hst M hM
  obtain ⟨R, Rf, hm⟩ := hLM _ _ _ Bs _ _ Γ X om om' hT
  obtain ⟨dec, hk⟩ := hK.1 _ _ _ Bs _ _ Γ X om om' hT
  obtain ⟨hc, hco⟩ := hk R Rf hm
  obtain ⟨l, hla, hl⟩ := GlobalTheory.T.exists_adm_eq_thetaIntegral_of_conv Γ.M Bs.ψ _ _ om hT.weil dec.1
  have hw0 : G.pl.w G.pl.v0 ∈ locPl G t :=
    Finset.mem_union_left _ (by
      have : G.pl.v0 ∈ G.pl.S0 := by unfold Places.S0; convert Finset.mem_insert_self _ _
      unfold Places.W0; convert Finset.mem_image_of_mem _ this)
  have hv0 := (hti.2.2.1 _).2 ⟨_, hw0, rfl⟩
  have hd : 0 < (spW G i j).rank + (spW₁ G i j).rank := by have := hT.geo.aBig; omega
  obtain ⟨f, hf, h0⟩ := exists_I_ne_zero_at hm hc hco hla hl (GlobalTheory.T.theta_distribution_rational_points_invariant_triple Bs Γ X om om' hT 1 (one_mem _)) hv0
    (GlobalTheory.T.weilRepresentationLocality_tensorModelVW Bs Γ X om om' hT _) (GlobalTheory.T.strongApproximation_splitPlace_skewHermitian_unitary hSA Bs Γ X om om' hT ⟨_, hT.chars.sub hv0⟩)
    (H := Set.range (blkU _ _ e h.JWW)) fun x => by
      obtain ⟨s, g, h1, h2⟩ := GlobalTheory.T.exists_detOne_mul_blockUnitary_decomposition _ _ e h.JWW hd x
      exact ⟨s, _, ⟨g, rfl⟩, h1, h2⟩
  obtain ⟨φ, hφ, hP, _, ⟨g, rfl⟩, hne⟩ := exists_I_ne_zero_kind hm hc hco (H := Set.range (blkU _ _ e h.JWW))
    (by rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩; exact ⟨x * y, (blkU_mul _ _ e h.JWW x y).symm⟩)
    (fun v χ => ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) = v → ∃ n Φ, depthAt G w ≤ n ∧ IsNatDatum (unifAt w) n Φ ∧
      IsLocFn W B t e Γ w v (flipAt W t i j w n Φ) χ)
    (fun v hv φ₀ hφ₀ => by
      obtain ⟨w, hw, ew⟩ := (hti.2.2.1 v).1 hv
      obtain ⟨n, Φ, φ₂, k, φ₃, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.T.squareFlip_reaches_localQuotient_classes hL W B t i j M hst e Bs Γ X om om' h R Rf hm hti w hw v ew φ₀ hφ₀
      refine ⟨φ₂, h3.1, fun w' hw' ew' => ?_, _, ⟨k, rfl⟩, φ₃, h4, h5, h6⟩
      obtain rfl : w = w' := (hti.2.2.2 ⟨v, hT.chars.sub hv⟩ w hw ew).symm.trans (hti.2.2.2 ⟨v, hT.chars.sub hv⟩ w' hw' ew')
      exact ⟨n, Φ, h1, h2, h3⟩) hf h0
  have H : ∀ w, ∃ n Φ, w ∈ locPl G t → depthAt G w ≤ n ∧ IsNatDatum (unifAt w) n Φ ∧
      IsLocFn W B t e Γ w (w.under (𝓞 D.host.F)) (flipAt W t i j w n Φ) (φ (w.under (𝓞 D.host.F))) := fun w => by
    by_cases hw : w ∈ locPl G t
    · obtain ⟨n, Φ, H⟩ := hP _ ((hti.2.2.1 _).2 ⟨w, hw, rfl⟩) w hw rfl
      exact ⟨n, Φ, fun _ => H⟩
    · exact ⟨0, 0, fun h => absurd h hw⟩
  choose n Φ H using H
  have hnat : ∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w) := fun w hw => ⟨(H w hw).1, (H w hw).2.1⟩
  obtain ⟨τ, τ', hF, -⟩ := (LocTensor.local_tensors hL B ρ t i j).2.2.2 (fun w hw hmem => hst.2 w hw (by
    have e : ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) =
        (D.host.d : 𝓞 D.host.E) * ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) := by push_cast; ring
    rw [e]; exact Ideal.mul_mem_left _ _ hmem)) n Φ hnat
  obtain ⟨f₀, h1, h2, h3⟩ := GlobalTheory.T.exists_gaussianDatum_flippedFiniteTensor_bigRoute hL W B ρ t i j M hst e Bs Γ X om om' h hT hti n Φ τ τ' hnat hF φ hφ
    fun w hw => (H w hw).2.2
  obtain ⟨a, ha⟩ := GlobalTheory.T.realPolynomialVector_reached_by_realDatum hL W B ρ t i j M e Bs Γ X om om' h hT n Φ τ τ' hF φ hφ f₀ h1 h2 h3 f hf
  obtain ⟨b', hb'⟩ := ρ.onto_big i j (toTens a)
  obtain ⟨b, rfl⟩ := toTens_surjective b'
  have hΘ : IsMatched B t ρ i j (tensT W a τ) (tensT W b τ') := ⟨a, b, τ, τ', n, Φ, hb', hnat, hF, rfl, rfl⟩
  obtain ⟨ξ, hξ, hker⟩ := GlobalTheory.T.big_route_kernel_eq_const_mul_theta hL W B ρ t i j M _ _ hΘ e Bs Γ X om om' h hT _ ha g.1 g.2
  refine ⟨M, hM, a, τ, τ', n, Φ, hnat, hF, g.1, g.2, ?_⟩
  have hfd := (hM.vtx (.grid (i + 1) (j + 1)) ⟨i.2, j.2⟩).haar_fund
  simp only [hker]
  rw [integral_const_mul, GlobalTheory.T.setIntegral_conjugate_scaled_unitaryGroup_eq _ 1 one_ne_zero h.JW _ _ hfd.1 hfd.2 Γ.M.dom (h.μW ▸ hT.geo.hM.dom)
    (fun x => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om _ x _) fun γ hγ x => ?_, ← h.μW]
  · exact mul_ne_zero hξ hne
  · have e3 : ((γ * x, blkU _ _ e h.JWW (g.1, g.2)) : UB Γ.V.J × UB Γ.W.J) = (γ, 1) * (x, blkU _ _ e h.JWW (g.1, g.2)) := by
      simp
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta]
    rw [e3, map_mul, Module.End.mul_apply,
      GlobalTheory.T.theta_distribution_rational_points_invariant_triple Bs Γ X om om' hT γ hγ 1 (one_mem _) _ (hT.weil.isUSplitting.pres _ _ ha.1)]

open Formalism.IndefR GlobalTheory.RowTest GlobalTheory.RowClaim

theorem splitBound_ge : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ _ => 11 ≤ D.host.splitBound :=
  ⟨0, fun _ _ _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS _ _ _ => hS.size.2.1.eleven_le⟩⟩

theorem standing : Big fun ch => ∀ t, SquareStanding ch.G t := by
  obtain ⟨CF0, hH⟩ := splitBound_ge.and GlobalTheory.PlacesPrime.places_prime_to_level
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := hH ε CF hCF
  refine ⟨x₀, fun D large₂ he hx0 Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc t => ?_⟩
  obtain ⟨h11, hW⟩ := hx D large₂ he hx0 Γ Pl0 T A Ks R F hS ch hch hsc
  refine ⟨h11, fun w hw => ?_⟩
  classical
  unfold locPl at hw
  rcases Finset.mem_union.1 hw with hw | hw
  · exact hW w hw
  · intro hmem
    have h1 := (hS.core.lev.Q_off t w hw).1
    have h2 := hS.guard.2 t w hw
    push_cast at hmem h1 h2
    rcases w.isPrime.mem_or_mem hmem with h | h
    · exact h1 (Ideal.mul_mem_right _ _ h)
    · exact h2 (Ideal.mul_mem_left _ _ h)

theorem big_nonzero : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → Big fun ch => ∀ i j t, ∃ M : Vol ch.G, M.Is t ∧ ∃ a τ τ' n Φ,
    (∀ w ∈ locPl ch.G t, depthAt ch.G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) ∧ HasFlip ch.S.B t ch.rm i j n Φ τ τ' ∧
    ∃ g g₁, ∫ u in M.fd _, kerBig ch.W (tensT ch.W a τ) g g₁ u ∂M.ν _ ≠ 0 := by
  intro hP hK hLM _ _ _
  obtain ⟨CF0, hH⟩ := standing
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := hH ε CF hCF
  refine ⟨x₀, fun D large₂ he hx0 Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc i j t => ?_⟩
  exact exists_integral_ne_zero hP.strongApproxSU hK hLM hS.core.lev ch.W ch.S.B ch.rm t i j
    (hx D large₂ he hx0 Γ Pl0 T A Ks R F hS ch hch hsc t)

end GlobalTheory.BigNZ

end
