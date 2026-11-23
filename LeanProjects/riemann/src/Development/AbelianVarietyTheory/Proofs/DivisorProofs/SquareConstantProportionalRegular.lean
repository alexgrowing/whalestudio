import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Definitions.Divisors.RegConst
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolynomialRouteSubmodule
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNatDatumSquareFlip
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareCommutativityProjection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepresentationsForTripleStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilConvergenceOfSiegelSetStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.ChainFr Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.RealSep

section Generic

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.BigNZ

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem I_eq_zero (hT : IsTriple B G X om om')
    {l : ((Fin a × Fin (a + a') → AF F) → ℂ) →ₗ[ℂ] ℂ} (hla : l ∈ (adeleClass F).adm _)
    (hl : ∀ Φ ∈ schA F _, l Φ = G.M.I om Φ 1)
    (hrat : ∀ γ ∈ ratU σ G.W.J, ∀ Φ ∈ schA F _, thetaSum F (om (1, γ) Φ) = thetaSum F Φ) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (hv : v ∈ X.T)
    (hloc : ∀ k ∈ UAt σ G.W (evFin F v), ∀ φ ∈ GlobalTheory.WeilM.SB _, ∃ φ₁ ∈ GlobalTheory.WeilM.SB _, Acts (evFin F v) (om (1, k)) φ φ₁)
    (hsa : ∀ s : UA σ G.W.J, (mat s).det = 1 → s ∈ closure {x | ∃ γ ∈ ratU σ G.W.J, ∃ k ∈ UAt σ G.W (evFin F v), x = γ * k})
    {H : Set (UA σ G.W.J)} (hH : ∀ x, ∃ s, ∃ g ∈ H, (mat s).det = 1 ∧ x = s * g) {f : SInf F (Fin a × Fin (a + a'))}
    (h0 : ∀ φ, IsFinPart G.M X.T φ → ∀ g ∈ H, G.M.I om (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) g = 0) {φ} (hφ : IsFinPart G.M X.T φ)
    (x : UA σ G.W.J) : G.M.I om (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) x = 0 := by
  classical
  have hG := hT.geo.hM
  have hΦ := hφ.fam.mem hG f
  obtain ⟨s, g, hg, hs, rfl⟩ := hH x
  have hcont : Continuous fun y : UA σ G.W.J => G.M.I om (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) (y * g) := by
    simp only [I_eq_l hT hl hΦ]
    exact (hT.weil.isUSplitting.cont l hla _ hΦ).comp (continuous_const.prodMk (continuous_mul_right g))
  refine closure_minimal (t := {y | G.M.I om (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) (y * g) = 0}) ?_
    (isClosed_eq hcont continuous_const) (hsa s hs)
  rintro _ ⟨γ, hγ, k, hk, rfl⟩
  obtain ⟨φ₁, h1, ha⟩ := hloc _ (conj_mem_UAt hk g) (φ v) (hφ.1 v)
  have e1 := hφ.fam.acts hG f (hφ.1 v) ha
  rw [Function.update_eq_self] at e1
  have e2 := h0 _ (hφ.update hv h1) g hg
  rw [← e1, I_om] at e2
  refine Eq.trans ?_ e2
  refine integral_congr_ae (.of_forall fun u => ?_)
  have e3 : ((u, γ * k * g) : UA σ G.V.J × UA σ G.W.J) = (1, γ) * (u, g * (g⁻¹ * k * g)) := by
    simp [mul_assoc]
  simp only [theta]
  rw [e3, map_mul, Module.End.mul_apply, hrat γ hγ _ (hT.weil.isUSplitting.pres _ _ hΦ)]

end Generic

section Nonzero

open GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ blkU conjU UB)

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

end Nonzero

section Read

open GlobalTheory.SquareComm GlobalTheory.SquareAgree GlobalTheory.Grid GlobalTheory.TripleRead GlobalTheory.SquareIdent
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (incM conjU)

variable {D : D7}

theorem exists_read {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {W W₁ X : HSp D} (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) {α β : (AE D)ˣ →* Circle} {ωA : WRep W X} (hωA : IsWeil ψ true W X β (β / α) ωA)
    {e : Fin (W.rank + W₁.rank) ≃ Fin X.rank} {Bs Γ Xc}
    (hR : IsReading ψ A A₁ B α β e Bs Γ Xc) {om₀ om'} (hT₀ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om₀ om')
    {ν 𝓕} (hν : IsHaarFD W ν 𝓕) (hμ : Γ.M.μ = ν.map (conjU W 1 hR.JW)) :
    ∃ om, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' ∧
      (∀ Φ (F : WO W X → ℂ), IsDatum Γ.M ψ (fun u => (HMul.hMul (uᵀ.submatrix e.symm id) (incM (sgn true W).gram) :
          Matrix (Fin X.rank) (Fin W.rank) (AE D))) Φ F → ∀ h, thetaInt ωA ν 𝓕 F h = Γ.M.I om Φ (toUX X e hR.JX h)) ∧
      ∀ f₀, Γ.M.IsGauss Bs.ψ Bs.emb f₀ → ∀ P, ∃ f ∈ Γ.M.Pol Bs.ψ Bs.emb, ∀ (s : ℂ) φ, s ≠ 0 →
        GlobalTheory.BigNZ.IsFinPart Γ.M Xc.T φ → ∀ F : WO W X → ℂ,
        IsDatum Γ.M ψ (fun u => (HMul.hMul (uᵀ.submatrix e.symm id) (incM (sgn true W).gram) :
          Matrix (Fin X.rank) (Fin W.rank) (AE D))) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (s • f₀) φ) F →
        IsDatum Γ.M ψ (fun u => (HMul.hMul (uᵀ.submatrix e.symm id) (incM (sgn true W).gram) :
          Matrix (Fin X.rank) (Fin W.rank) (AE D))) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) (s⁻¹ • fockF ψ θ true A B F P) := by
  obtain rfl := hR.ψ
  have hg := hT₀.geo
  have hstd : IsStdChar D Bs.ψ (-1) := GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd D Bs.ψ hT₀.base.std
  obtain ⟨om, hom, tA⟩ := GlobalTheory.TripleDarboux.exists_weil Bs hT₀.base true W X e _ _ hg.hV hg.hW 1 hR.JW
    (by rw [neg_gram, one_smul, neg_neg]) hR.JX Γ.M hg.hM hωA
  have hT : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' :=
    ⟨hT₀.base, hg, hT₀.chars, by rw [hR.α, hR.β]; exact hom, hT₀.weil'⟩
  obtain ⟨cA, hcA⟩ := GlobalTheory.Twist.exists_addEquiv_symplecticCoords_orientedModel.coords D W X e.symm (-1) (neg_ne_zero.2 one_ne_zero)
  have hcA' : ∀ u, cA u = (HMul.hMul (uᵀ.submatrix e.symm id) (incM (sgn true W).gram) :
      Matrix (Fin X.rank) (Fin W.rank) (AE D)) := fun u => by rw [hcA, neg_one_smul]; rfl
  rw [← funext hcA']
  refine ⟨om, hT, fun Φ F hF h => ?_, fun f₀ g1 P => ?_⟩
  · have eF := eq_thO Γ.M Bs.ψ e (GlobalTheory.RouteCoords.gram_det_ne (sgn true W)) cA hcA' hF
    have key : ∀ u, thetaKO ωA u h F = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om Φ (conjU W 1 hR.JW u) (toUX X e hR.JX h) := fun u => by
      have h1 := congrFun (tA Φ hF.1 u h) 0
      have h2 : ptO (D := D) (sgn true W).gram e 0 = 0 := by
        rw [ptO, Matrix.zero_mul]; rfl
      rw [thO, h2, rho_zero, ← eF] at h1
      exact h1.symm
    simp only [thetaInt, key]
    rw [GlobalTheory.T.setIntegral_conjugate_scaled_unitaryGroup_eq _ 1 one_ne_zero hR.JW _ _ hν.1 hν.2 Γ.M.dom (hμ ▸ hg.hM.dom)
      (fun x => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om Φ x (toUX X e hR.JX h)) fun γ hγ x => ?_, ← hμ]
    · rfl
    · have e3 : ((γ * x, toUX X e hR.JX h) : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB Γ.V.J × GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB Γ.W.J) =
          (γ, 1) * (x, toUX X e hR.JX h) := by simp
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta]
      rw [e3, map_mul, Module.End.mul_apply,
        GlobalTheory.T.theta_distribution_rational_points_invariant_triple Bs Γ Xc om om' hT γ hγ 1 (one_mem _) _ (hT.weil.isUSplitting.pres _ _ hF.1)]
  obtain ⟨a1, a2, -⟩ := fock_datum hθ true A B e.symm Bs hT₀.base hR.JW hR.JX hg.hV hg.hW
    (fun w => by
      obtain ⟨τ, a, b, -, d⟩ := hR.cart w
      exact ⟨τ, a, b.trans (one_smul _ _).symm, d⟩) Γ.M hg.hM cA hcA g1
  obtain ⟨f, hf, hPf⟩ := a2 P
  refine ⟨f, hf, fun s φ hs hφ F hF => ?_⟩
  have p2 : ∀ᶠ v in Filter.cofinite, φ v = Γ.M.vac v := Xc.T.eventually_cofinite_notMem.mono hφ.2
  have L := GlobalTheory.SquareAgree.isDatum_linear Γ.M Bs.ψ hT₀.base.std cA
  have h1 := L.2 _ _ _ _ s⁻¹ L.1 hF
  rw [zero_add, zero_add, GlobalTheory.BigNZ.DatReal.pure_smul, smul_smul, inv_mul_cancel₀ hs, one_smul] at h1
  have h2 := (a1 φ hφ.1 p2 _ h1).1
  have h3 := (ptF_sum hstd hθ (frSgn true A) B {()} (fun _ => s) (fun _ => s⁻¹ • F) (fun _ _ => h2) P).2
  rw [Finset.sum_singleton, Finset.sum_singleton, smul_smul, mul_inv_cancel₀ hs, one_smul] at h3
  have h4 : s⁻¹ • fockF Bs.ψ θ true A B F P = fockF Bs.ψ θ true A B (s⁻¹ • F) P := by
    refine (inv_smul_eq_iff₀ hs).2 h3
  rw [h4]
  exact hPf φ hφ.1 p2 _ h1

end Read

section Grid

open GlobalTheory.SquareComm GlobalTheory.SquareAgree GlobalTheory.TripleRead GlobalTheory.SquareIdent GlobalTheory.SquareDict GlobalTheory.BigNZ
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (alpha beta blkU spV spW spW₁ spV₁ xiV xiV₁)

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def IsNull (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m)
    (x : PolRoute G (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid (i + 1) j)) : Prop :=
  ∀ M : Vol G, M.Is t → ∀ a : PolT G (routeBig t i j) →₀ ℂ, toTens a = x → ∀ n Φ τ τ',
    (∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) → HasFlip B t ρ i j n Φ τ τ' →
    ∀ g g₁, ∫ u in M.fd _, kerBig W (tensT W a τ) g g₁ u ∂M.ν _ = 0

theorem toUX_blk (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (h : J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram A B e) (h' : J = D.host.xi0 • ((GlobalTheory.Doubling.hsum A B).gramᵀ).submatrix
      (e.symm.trans finSumFinEquiv) (e.symm.trans finSumFinEquiv)) (g : GA D A × GA D B) :
    toUX (GlobalTheory.Doubling.hsum A B) (e.symm.trans finSumFinEquiv) h' (blk A B g) = blkU A B e h g :=
  Subtype.ext (Units.ext (blkMat_submatrix e _ _))

set_option maxHeartbeats 1000000 in

theorem thetaInt_eq_zero (hSA : GlobalTheory.Published.StrongApproxSU) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree)
    (hLM : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching) {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T)
    (i j : Fin D.R.m) (hst : SquareStanding G t) {A : Fr (spW G i j)} {A₁ : Fr (spW₁ G i j)} {AV : Fr (spV G i j)}
    {AV₁ : Fr (spV₁ G i j)} (hA : IsGridFr W _ A) (hA₁ : IsGridFr W _ A₁) (hV : IsGridFr W _ AV) (hV₁ : IsGridFr W _ AV₁)
    {ωA : GlobalTheory.Grid.WRep (spW G i j) (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j))}
    (hωA : GlobalTheory.Grid.IsWeil W.ψ true _ _ (beta G i j) (beta G i j / alpha G t i j) ωA)
    {a : PolT G (routeBig t i j) →₀ ℂ} {P : PolF D (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).rank (spW G i j).rank}
    (hP : ∀ n Φ τ τ', HasFlip B t ρ i j n Φ τ τ' →
      datumA W (tensT W a τ) = fockF W.ψ W.θ true A (frSum AV AV₁) (datumA W τ) P)
    (h0 : IsNull W B ρ t i j (toTens a)) {M : Vol G} (hM : M.Is t) {n₀ Φ₀ τ₀ τ₀'}
    (hn₀ : ∀ w ∈ locPl G t, depthAt G w ≤ n₀ w ∧ IsNatDatum (unifAt w) (n₀ w) (Φ₀ w)) (hF₀ : HasFlip B t ρ i j n₀ Φ₀ τ₀ τ₀') :
    thetaInt ωA (M.ν _) (M.fd _) (fockF W.ψ W.θ true A (frSum AV AV₁) (datumA W τ₀) P) = 0 := by
  classical
  obtain ⟨e, Bs, Γ, X, om₀, om', h, hT₀, htb⟩ := GlobalTheory.FlipMatch.exists_tiedBoth hL W t i j hst M hM
  have hti := htb.1
  have hR : IsReading W.ψ A A₁ (frSum AV AV₁) _ _ (e.symm.trans finSumFinEquiv) Bs Γ X :=
    ⟨h.ψ, h.JW, h.JW₁, by
      rw [h.JWW, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram, ← GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_transpose, ← blkMat_submatrix, GlobalTheory.Doubling.gram_hsum]
      rfl, fun w => by
      obtain ⟨τ, a, b, c, d⟩ := h.cart w
      refine ⟨τ, a, b.trans (hA τ).2.symm, c.trans (congrArg Neg.neg (hA₁ τ).2.symm), d.trans ?_⟩
      rw [GlobalTheory.SquareAlg.cart_frSum, (hV τ).2, (hV₁ τ).2, ← blkMat_submatrix], h.α, h.β⟩
  obtain ⟨om, hT, hI, hFock⟩ := exists_read W.θ_is A A₁ _ hωA hR hT₀ (hM.vtx (.grid (i + 1) (j + 1)) ⟨i.2, j.2⟩).haar_fund h.μW
  obtain ⟨R, Rf, hm⟩ := hLM _ _ _ Bs _ _ Γ X om om' hT
  obtain ⟨dec, hk⟩ := hK.1 _ _ _ Bs _ _ Γ X om om' hT
  obtain ⟨hc, hco⟩ := hk R Rf hm
  obtain ⟨l, hla, hl⟩ := GlobalTheory.T.exists_adm_eq_thetaIntegral_of_conv Γ.M Bs.ψ _ _ om hT.weil dec.1
  obtain ⟨f₀, f₀', ⟨f1, f2⟩, -, f3⟩ := GlobalTheory.FlipMatch.finite_match hL W B ρ t i j M hst h hm htb
  obtain ⟨φ₀, -, p₀, -, d₀, -⟩ := f3 n₀ Φ₀ τ₀ τ₀' hn₀ hF₀
  obtain ⟨f, hf, hPf⟩ := hFock f₀ f2 P
  have hw0 : G.pl.w G.pl.v0 ∈ locPl G t :=
    Finset.mem_union_left _ (by
      have : G.pl.v0 ∈ G.pl.S0 := by unfold Places.S0; convert Finset.mem_insert_self _ _
      unfold Places.W0; convert Finset.mem_image_of_mem _ this)
  have hv0 := (hti.2.2.1 _).2 ⟨_, hw0, rfl⟩
  have hd : 0 < (spW G i j).rank + (spW₁ G i j).rank := by have := hT.geo.aBig; omega
  funext y
  have k₀ := hI _ _ (hPf 1 φ₀ one_ne_zero p₀ _ (by rw [one_smul]; exact isDatum_of_isDatumA d₀)) y
  rw [inv_one, one_smul] at k₀
  refine k₀.trans (I_eq_zero hT hla hl (GlobalTheory.T.theta_distribution_rational_points_invariant_triple Bs Γ X om om' hT 1 (one_mem _)) hv0
    (GlobalTheory.T.weilRepresentationLocality_tensorModelVW Bs Γ X om om' hT _) (GlobalTheory.T.strongApproximation_splitPlace_skewHermitian_unitary hSA Bs Γ X om om' hT ⟨_, hT.chars.sub hv0⟩)
    (H := Set.range (blkU _ _ e h.JWW)) (fun x => by
      obtain ⟨s, g, h1, h2⟩ := GlobalTheory.T.exists_detOne_mul_blockUnitary_decomposition _ _ e h.JWW hd x
      exact ⟨s, _, ⟨g, rfl⟩, h1, h2⟩) (fun φ₁ p₁ g₀ hg₀ => ?_) p₀ _)
  by_contra hne₁
  obtain ⟨φ, hφ, hQ, _, ⟨g, rfl⟩, hne⟩ := exists_I_ne_zero_kind hm hc hco (H := Set.range (blkU _ _ e h.JWW))
    (by rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩; exact ⟨x * y, (blkU_mul _ _ e h.JWW x y).symm⟩)
    (fun v χ => ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) = v → ∃ n Φ, depthAt G w ≤ n ∧ IsNatDatum (unifAt w) n Φ ∧
      IsLocFn W B t e Γ w v (flipAt W t i j w n Φ) χ)
    (fun v hv φ₀ hφ₀ => by
      obtain ⟨w, hw, ew⟩ := (hti.2.2.1 v).1 hv
      obtain ⟨n, Φ, φ₂, k, φ₃, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.T.squareFlip_reaches_localQuotient_classes hL W B t i j M hst e Bs Γ X om om' h R Rf hm hti w hw v ew φ₀ hφ₀
      refine ⟨φ₂, h3.1, fun w' hw' ew' => ?_, _, ⟨k, rfl⟩, φ₃, h4, h5, h6⟩
      obtain rfl : w = w' := (hti.2.2.2 ⟨v, hT.chars.sub hv⟩ w hw ew).symm.trans (hti.2.2.2 ⟨v, hT.chars.sub hv⟩ w' hw' ew')
      exact ⟨n, Φ, h1, h2, h3⟩) hf ⟨φ₁, p₁, g₀, hg₀, hne₁⟩
  have H : ∀ w, ∃ n Φ, w ∈ locPl G t → depthAt G w ≤ n ∧ IsNatDatum (unifAt w) n Φ ∧
      IsLocFn W B t e Γ w (w.under (𝓞 D.host.F)) (flipAt W t i j w n Φ) (φ (w.under (𝓞 D.host.F))) := fun w => by
    by_cases hw : w ∈ locPl G t
    · obtain ⟨n, Φ, H⟩ := hQ _ ((hti.2.2.1 _).2 ⟨w, hw, rfl⟩) w hw rfl
      exact ⟨n, Φ, fun _ => H⟩
    · exact ⟨0, 0, fun h => absurd h hw⟩
  choose n Φ H using H
  have hnat : ∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w) := fun w hw => ⟨(H w hw).1, (H w hw).2.1⟩
  obtain ⟨τ, τ', hF, -⟩ := (LocTensor.local_tensors hL B ρ t i j).2.2.2 (fun w hw hmem => hst.2 w hw (by
    have e : ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) =
        (D.host.d : 𝓞 D.host.E) * ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) := by push_cast; ring
    rw [e]; exact Ideal.mul_mem_left _ _ hmem)) n Φ hnat
  obtain ⟨f', h1, h2, h3⟩ := GlobalTheory.T.exists_gaussianDatum_flippedFiniteTensor_bigRoute hL W B ρ t i j M hst e Bs Γ X om om' h hT hti n Φ τ τ' hnat hF φ hφ
    fun w hw => (H w hw).2.2
  obtain ⟨s, rfl⟩ := GlobalTheory.T.fockVacua_triple_proportional_to_nonzero Bs Γ X om om' hT f₀ f1 f2 f' h2
  have hs : s ≠ 0 := by rintro rfl; exact h1 (zero_smul _ _)
  have k := hI _ _ (hPf s φ hs hφ _ (isDatum_of_isDatumA h3)) (blk _ _ g)
  rw [toUX_blk _ _ e h.JWW, GlobalTheory.RegCompare.thetaInt_smul, ← hP n Φ τ τ' hF] at k
  obtain ⟨b', hb'⟩ := ρ.onto_big i j (toTens a)
  obtain ⟨b, rfl⟩ := toTens_surjective b'
  have hΘ : IsMatched B t ρ i j (tensT W a τ) (tensT W b τ') := ⟨a, b, τ, τ', n, Φ, hb', hnat, hF, rfl, rfl⟩
  have z := h0 M hM a rfl n Φ τ τ' hnat hF g.1 g.2
  simp only [GlobalTheory.T.thetaGridRouteKernel_eq_detCharacters_mul_thetaKernel hL W t i j ωA hωA B ρ _ _ hΘ] at z
  rw [integral_const_mul, mul_eq_zero, mul_eq_zero] at z
  rcases z with (z | z) | z
  · exact Circle.coe_ne_zero _ z
  · exact Circle.coe_ne_zero _ z
  · exact hne (k.symm.trans (by rw [Pi.smul_apply]; exact smul_eq_zero_of_right _ z))

end Grid

section Null

open GlobalTheory.SquareComm GlobalTheory.SquareIdent GlobalTheory.SquareDict
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (alpha beta spV spW spW₁ spV₁)

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem exists_not_isNull (hSA : GlobalTheory.Published.StrongApproxSU) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree)
    (hLM : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching) {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T)
    (i j : Fin D.R.m) (hst : SquareStanding G t) : ∃ x, ¬ IsNull W B ρ t i j x := by
  obtain ⟨M, hM, a, τ, τ', n, Φ, hn, hF, g, g₁, h⟩ := exists_integral_ne_zero hSA hK hLM hL W B ρ t i j hst
  exact ⟨toTens a, fun h0 => h (h0 M hM a rfl n Φ τ τ' hn hF g g₁)⟩

set_option maxHeartbeats 1000000 in

theorem exists_nullSpace (hP : GlobalTheory.FunPr.Hypotheses₂) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree)
    (hLM : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching) {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (hst : ∀ t, SquareStanding G t)
    (i j : Fin D.R.m) {A : Fr (spW G i j)} {AV : Fr (spV G i j)} {AV₁ : Fr (spV₁ G i j)} (hA : IsGridFr W _ A)
    (hV : IsGridFr W _ AV) (hV₁ : IsGridFr W _ AV₁)
    (ι : PolRoute G (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid (i + 1) j) →ₗ[ℂ]
      PolF D (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).rank (spW G i j).rank)
    (hι : ∀ (t : T) (B : Frames G) (ρ : RealMatch W) n Φ (τ : TotT G (routeBig t i j)) τ', HasFlip B t ρ i j n Φ τ τ' →
      ∀ a : PolT G (routeBig t i j) →₀ ℂ,
        datumA W (tensT W a τ) = fockF W.ψ W.θ true A (frSum AV AV₁) (datumA W τ) (ι (toTens a))) :
    ∃ K : Submodule ℂ (PolRoute G (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid (i + 1) j)),
      (∀ B ρ t x, IsNull W B ρ t i j x ↔ x ∈ K) ∧
      (∀ x ∈ K, ∀ t ν 𝓕, IsHaarFD (spW G i j) ν 𝓕 → ∀ ωA : GlobalTheory.Grid.WRep (spW G i j) (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)),
        GlobalTheory.Grid.IsWeil W.ψ true _ _ (beta G i j) (beta G i j / alpha G t i j) ωA →
        ∀ f, IsFinF W.ψ W.θ true A (frSum AV AV₁) f → thetaInt ωA ν 𝓕 (fockF W.ψ W.θ true A (frSum AV AV₁) f (ι x)) = 0) ∧
      ∀ B (ρ : RealMatch W) t (M : Vol G), M.Is t → ∀ n Φ τ τ', (∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) →
        HasFlip B t ρ i j n Φ τ τ' → ∀ g g₁, ∃ l : PolRoute G (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid (i + 1) j) →ₗ[ℂ] ℂ,
          ∀ a, ∫ u in M.fd _, kerBig W (tensT W a τ) g g₁ u ∂M.ν _ = l (toTens a) := by
  obtain ⟨A₁, hA₁⟩ := exists_isGridFr W (X := .grid i j) ⟨i.2.le, j.2.le⟩
  have hD := fun t => dict hL W t i j A A₁ AV AV₁ hA hA₁ hV hV₁
  have hT := fun t => (hD t).1 (hst t) _ (exists_vol G hL t).choose_spec
  choose a b ha hb _ using (hT μ₀).gap
  obtain ⟨Pr, q, H⟩ := GlobalTheory.T.exists_square_commutativity_projection hP hK hLM D W.ψ W.θ W.ψ_std W.θ_is _ _ _ A A₁ (frSum AV AV₁) a b
  replace H := fun t => H _ _ (hT t) fun τ => ⟨GlobalTheory.SquareRel.hasInfExp_alpha G i j hL μ₀ t τ (ha τ), hb τ⟩
  choose ωA ωB hωA hωB using fun t => GlobalTheory.T.weil_representations_for_triple hP D W.ψ W.ψ_std _ _ _ _ _ (hT t)
  have hbig : Node.InRange D.R.m (.grid (i + 1) (j + 1)) := ⟨i.2, j.2⟩
  have form : ∀ B (ρ : RealMatch W) t (M : Vol G), M.Is t → ∀ n Φ τ τ',
      (∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) → HasFlip B t ρ i j n Φ τ τ' →
      ∃ (Pf : ModuleCat.{0} ℂ) (y : Pf) (J : Pr ⊗[ℂ] Pf →ₗ[ℂ] (GA D (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)) → ℂ))
        (κ : _ → ℂ), (J = 0 ∨ Function.Injective J) ∧
        (∀ P, thetaInt (ωA t) (M.ν _) (M.fd _) (fockF W.ψ W.θ true A (frSum AV AV₁) (datumA W τ) P) = J (q P ⊗ₜ y)) ∧
        ∀ g g₁ a, ∫ u in M.fd _, kerBig W (tensT W a τ) g g₁ u ∂M.ν _ = κ (g, g₁) * J (q (ι (toTens a)) ⊗ₜ y) (blk _ _ (g, g₁)) := by
    intro B ρ t M hM n Φ τ τ' hn hF
    obtain ⟨_, _, _, _, _, -, hc⟩ := core hP.howeDualityReal hP hLM hL W i j A A₁ AV AV₁ hA hA₁ hV hV₁ t B ρ M (hst t) hM (hT t)
      _ _ (hωA t) (hωB t)
    obtain ⟨_, hc⟩ := hc 0
    obtain ⟨Pf, y, J, h1, h2⟩ := H t _ _ (hM.vtx _ hbig).haar_fund _ (hωA t) _ (hc n Φ τ τ' hn hF).1
    obtain ⟨κ, hκ⟩ := (hD t).2 _ _ (hωA t) (hωB t)
    refine ⟨Pf, y, J, κ, h1, h2, fun g g₁ a => ?_⟩
    obtain ⟨b', hb'⟩ := ρ.onto_big i j (toTens a)
    obtain ⟨b, rfl⟩ := toTens_surjective b'
    rw [(hκ B ρ _ _ ⟨a, b, τ, τ', n, Φ, hb', hn, hF, rfl, rfl⟩).2.2.2.2.1 M g g₁, hι t B ρ n Φ τ τ' hF, h2]
  refine ⟨LinearMap.ker (q ∘ₗ ι), fun B ρ t x => ⟨fun h0 => ?_, fun hx M hM a ha n Φ τ τ' hn hF g g₁ => ?_⟩,
    fun x hx t ν 𝓕 hν ω hω f hf => ?_, fun B ρ t M hM n Φ τ τ' hn hF g g₁ => ?_⟩
  · obtain ⟨a, rfl⟩ := toTens_surjective x
    obtain ⟨M, hM, a₀, τ, τ', n, Φ, hn, hF, g, g₁, hne⟩ :=
      exists_integral_ne_zero hP.strongApproxSU hK hLM hL W B ρ t i j (hst t)
    obtain ⟨Pf, y, J, κ, h1, h2, h3⟩ := form B ρ t M hM n Φ τ τ' hn hF
    rw [h3] at hne
    have hy : y ≠ 0 := by rintro rfl; simp at hne
    have hJ : Function.Injective J := h1.resolve_left (by rintro rfl; simp at hne)
    have h4 := thetaInt_eq_zero hP.strongApproxSU hK hLM hL W B ρ t i j (hst t) hA hA₁ hV hV₁ (hωA t)
      (fun n Φ τ τ' hF => hι t B ρ n Φ τ τ' hF a) h0 hM hn hF
    rw [h2, ← map_zero J] at h4
    obtain ⟨c, hc⟩ := exists_scalar (Q := Pr) hy 0
    have h5 := congrArg (TensorProduct.comm ℂ Pr Pf) (hJ h4)
    rw [TensorProduct.comm_tmul, map_zero] at h5
    exact (hc _ 0 (h5.trans (TensorProduct.zero_tmul _ _).symm)).trans (smul_zero c)
  · obtain ⟨Pf, y, J, κ, -, -, h3⟩ := form B ρ t M hM n Φ τ τ' hn hF
    rw [h3, ha, show q (ι x) = 0 from hx, TensorProduct.zero_tmul, map_zero, Pi.zero_apply, mul_zero]
  · obtain ⟨Pf, y, J, -, h2⟩ := H t ν 𝓕 hν ω hω f hf
    rw [h2, show q (ι x) = 0 from hx, TensorProduct.zero_tmul, map_zero]
  · obtain ⟨Pf, y, J, κ, -, -, h3⟩ := form B ρ t M hM n Φ τ τ' hn hF
    exact ⟨κ (g, g₁) • (LinearMap.proj (blk _ _ (g, g₁)) ∘ₗ J ∘ₗ (TensorProduct.mk ℂ Pr Pf).flip y ∘ₗ q ∘ₗ ι), fun a => h3 g g₁ a⟩

theorem hasFlip_congr {W : G.Weil} {B : Frames G} {ρ ρ₀ : RealMatch W} (h1 : ρ₀.vX = ρ.vX) (h2 : ρ₀.vT = ρ.vT) {t : T}
    {i j : Fin D.R.m} {n Φ τ τ'} (h : HasFlip B t ρ i j n Φ τ τ') : HasFlip B t ρ₀ i j n Φ τ τ' := by
  unfold HasFlip at h ⊢
  rwa [h1, h2]

theorem exists_scalar_of_standing (hP : GlobalTheory.FunPr.Hypotheses₂) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree)
    (hLM : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching) {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (hst : ∀ t, SquareStanding G t)
    (B : Frames G) (ρ ρ₀ : RealMatch W) (h1 : ρ₀.vX = ρ.vX) (h2 : ρ₀.vT = ρ.vT) (i j : Fin D.R.m) :
    ∃ lam : ℂ, lam ≠ 0 ∧ ∀ t c' c₀, IsSquareConst W B ρ t i j c' → GlobalTheory.SqTower.RegConst W B ρ₀ t i j c₀ → c₀ ≠ 0 ∧ c' = lam * c₀ ∧
      ∀ a a₀ b, (a, b) ∈ ρ.rel i j → (a₀, b) ∈ ρ₀.rel i j → ∀ t', IsNull W B ρ t' i j (a - lam • a₀) := by
  obtain ⟨A, hA⟩ := exists_isGridFr W (X := .grid (i + 1) (j + 1)) ⟨i.2, j.2⟩
  obtain ⟨AV, hV⟩ := exists_isGridFr W (X := .grid i (j + 1)) ⟨i.2.le, j.2⟩
  obtain ⟨AV₁, hV₁⟩ := exists_isGridFr W (X := .grid (i + 1) j) ⟨i.2, j.2.le⟩
  obtain ⟨ι, -, hι⟩ := realA hL W i j A AV AV₁ hA hV hV₁
  obtain ⟨K, hN, -, hl⟩ := exists_nullSpace hP hK hLM hL W hst i j hA hV hV₁ ι hι
  obtain ⟨x, hx⟩ := exists_not_isNull hP.strongApproxSU hK hLM hL W B ρ μ₀ i j (hst μ₀)
  rw [hN] at hx
  have key : ∀ t c' c₀, IsSquareConst W B ρ t i j c' → GlobalTheory.SqTower.RegConst W B ρ₀ t i j c₀ →
      ∀ a a₀ b, (a, b) ∈ ρ.rel i j → (a₀, b) ∈ ρ₀.rel i j → (c₀ • a - c' • a₀ ∈ K) ∧ (c' = 0 → a ∈ K) ∧ (c₀ = 0 → a₀ ∈ K) := by
    intro t c' c₀ hc hc₀ a a₀ b hab hab₀
    obtain ⟨a, rfl⟩ := toTens_surjective a
    obtain ⟨a₀, rfl⟩ := toTens_surjective a₀
    obtain ⟨b, rfl⟩ := toTens_surjective b
    have H : ∀ M : Vol G, M.Is t → ∀ n Φ τ τ', (∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) →
        HasFlip B t ρ i j n Φ τ τ' → ∀ g g₁,
        ∃ (l : PolRoute G (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid (i + 1) j) →ₗ[ℂ] ℂ) (r : ℂ),
          (∀ a, ∫ u in M.fd _, kerBig W (tensT W a τ) g g₁ u ∂M.ν _ = l (toTens a)) ∧ l (toTens a) = c' * r ∧
            l (toTens a₀) = c₀ * r := by
      intro M hM n Φ τ τ' hn hF g g₁
      obtain ⟨l, e⟩ := hl B ρ t M hM n Φ τ τ' hn hF g g₁
      have hΘ : IsMatched B t ρ i j (tensT W a τ) (tensT W b τ') := ⟨a, b, τ, τ', n, Φ, hab, hn, hF, rfl, rfl⟩
      obtain ⟨z, z0, z1, z2⟩ := hc₀ M hM _ _ ⟨a₀, b, τ, τ', n, Φ, hab₀, hn, hasFlip_congr h1 h2 hF, rfl, rfl⟩ g g₁
      have z3 := hc M hM _ _ hΘ z g g₁ ⟨GlobalTheory.T.bigRoute_kernel_integrableOn_unitary_quotient (GlobalTheory.T.weil_convergence_of_siegel_set hP.siegelSetUnitary hP) hL W B ρ t i j
        (GlobalTheory.T.squareThetaTripleHypotheses_of_standing hL W t i j (hst t)) M hM _ _ hΘ g₁ g, z1.2⟩
      replace z2 := (congrArg (zdeg z * ·) (e a₀)).symm.trans z2
      replace z3 := (congrArg (zdeg z * ·) (e a)).symm.trans z3
      exact ⟨l, _ / zdeg z, e, by rw [← mul_div_assoc, ← z3, mul_div_cancel_left₀ _ z0],
        by rw [← mul_div_assoc, ← z2, mul_div_cancel_left₀ _ z0]⟩
    refine ⟨(hN B ρ t _).1 ?_, fun h => (hN B ρ t _).1 ?_, fun h => (hN B ρ t _).1 ?_⟩ <;>
    · intro M hM a' ha' n Φ τ τ' hn hF g g₁
      obtain ⟨l, r, e1, e2, e3⟩ := H M hM n Φ τ τ' hn hF g g₁
      rw [e1, ha']
      first
        | rw [map_sub, map_smul, map_smul, e2, e3, smul_eq_mul, smul_eq_mul]; ring
        | rw [e2, h, zero_mul]
        | rw [e3, h, zero_mul]
  obtain ⟨b, hb⟩ := ρ.onto_big i j x
  obtain ⟨x₀, hx₀⟩ := ρ₀.onto_small i j b
  obtain ⟨b₁, hb₁⟩ := ρ₀.onto_big i j x
  obtain ⟨x₁, hx₁⟩ := ρ.onto_small i j b₁
  by_cases hex : ∃ t c' c₀, IsSquareConst W B ρ t i j c' ∧ GlobalTheory.SqTower.RegConst W B ρ₀ t i j c₀
  swap
  · exact ⟨1, one_ne_zero, fun t c' c₀ h h₀ => absurd ⟨t, c', c₀, h, h₀⟩ hex⟩
  obtain ⟨s, d', d₀, hd, hd₀⟩ := hex
  have n₀ : ∀ t c' c₀, IsSquareConst W B ρ t i j c' → GlobalTheory.SqTower.RegConst W B ρ₀ t i j c₀ → c₀ ≠ 0 := fun t c' c₀ h h₀ e =>
    hx ((key t c' c₀ h h₀ _ _ _ hx₁ hb₁).2.2 e)
  have k : ∀ a a₀ b, (a, b) ∈ ρ.rel i j → (a₀, b) ∈ ρ₀.rel i j → a - (d' / d₀) • a₀ ∈ K := fun a a₀ b h h₀ => by
    have := K.smul_mem d₀⁻¹ (key s d' d₀ hd hd₀ a a₀ b h h₀).1
    rwa [smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ (n₀ _ _ _ hd hd₀), one_smul, ← div_eq_inv_mul] at this
  refine ⟨d' / d₀, div_ne_zero (fun e => hx ((key s d' d₀ hd hd₀ _ _ _ hb hx₀).2.1 e)) (n₀ _ _ _ hd hd₀),
    fun t c' c₀ h h₀ => ⟨n₀ t c' c₀ h h₀, ?_, fun a a₀ b h h₀ t' => (hN B ρ t' _).2 (k a a₀ b h h₀)⟩⟩
  by_contra hne
  have e := K.sub_mem (key t c' c₀ h h₀ _ _ _ hx₁ hb₁).1 (K.smul_mem c₀ (k _ _ _ hx₁ hb₁))
  rw [smul_sub, sub_sub_sub_cancel_left, smul_smul, ← sub_smul] at e
  exact hx ((K.smul_mem_iff (sub_ne_zero.2 fun e => hne (by rw [← e, mul_comm]))).1 e)

end Null

section Main

open GlobalTheory.SquareComm GlobalTheory.SquareIdent GlobalTheory.SquareDict GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (alpha beta spV spW spW₁ spV₁)

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem standing {large₂ : SizeData₂ D} (hS : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) {μ₀ : T} (hL : L.Is μ₀) (hx : 11 ≤ D.host.splitBound)
    (G : GridData L sc) (t : T) : SquareStanding G t := by
  classical
  obtain ⟨hq, hd, -⟩ := D.host.hyp
  have hcc : D.host.ccK = ⊤ := hS.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨⟨P, -, -⟩, -⟩ := hS
  have lev : ∀ p ∈ D.host.levelPrimes, p.Prime → Nat.Coprime p (D.host.QS * D.host.q * D.host.d) := fun p hp hpp => by
    have hd' : p ≠ D.host.d := fun e => by
      have h := P.level_split p hp
      rw [Host.cls, primeClass] at h
      split_ifs at h <;> contradiction
    have hq' : p ≠ D.host.q := fun e => by
      have h := P.level_split p hp
      rw [Host.cls, primeClass] at h
      split_ifs at h <;> contradiction
    exact ((D.host.level_coprimeS p hp).mul_right ((Nat.coprime_primes hpp hq).2 hq')).mul_right
      ((Nat.coprime_primes hpp hd).2 hd')
  refine ⟨hx, fun w hw => ?_⟩
  have e1 : ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) =
      ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) := by
    rw [hcc, Ideal.absNorm_top, mul_one]
  rw [e1]
  rcases Finset.mem_union.1 hw with hw | hw
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
    obtain ⟨p, hpv, hcop⟩ : ∃ p : ℕ, ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal ∧ Nat.Coprime p (D.host.QS * D.host.q * D.host.d) := by
      rcases G.pl.mem_S0_of_sum_eq.1 hv with rfl | hv1
      · refine ⟨q0 D, G.pl.basePlace_over_qZero, ?_⟩
        have hs := (leastSplitAuxiliaryPrimeThetaChain_spec D).2.1
        have hM : Nat.Coprime (Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D) (q0 D) := by
          rw [Nat.Coprime, Nat.gcd_rec, hs, Nat.gcd_one_left]
        have hdv : D.host.QS * D.host.q * D.host.d ∣ Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D := by
          unfold LevelStarExponents.condE
          exact Dvd.intro_left _ rfl
        exact (hM.coprime_dvd_left hdv).symm
      · rcases (S1_mem_OmF D).1 hv1 with h | h | h | h
        · exact ⟨_, h, lev _ (D.host.g_level 0) (D.host.g_prime 0)⟩
        · exact ⟨_, h, lev _ (D.host.g_level 1) (D.host.g_prime 1)⟩
        · exact ⟨_, h, lev _ D.host.pde_level.1 D.host.pde_prime⟩
        · exact ⟨_, h, lev _ D.host.pde_level.2 D.host.pde'_prime⟩
    have hpw : ((p : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal := by
      rw [← G.pl.under_w hv, HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast] at hpv
      exact hpv
    exact GlobalTheory.SquareConv.natCast_not_mem (G.pl.w v).isPrime.ne_top hcop hpw
  · intro hmem
    apply (hL.Q_off t w hw).1
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hmem

theorem real_matching : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (B : Frames G) (ρ ρ₀ : RealMatch W), ρ₀.vX = ρ.vX → ρ₀.vT = ρ.vT →
      ∀ i j : Fin D.R.m, ∃ lam : ℂ, lam ≠ 0 ∧ ∀ (t : T) (c' c₀ : ℂ), IsSquareConst W B ρ t i j c' →
        GlobalTheory.SqTower.RegConst W B ρ₀ t i j c₀ → c₀ ≠ 0 ∧ c' = lam * c₀ := by
  intro hP hK hLM
  refine ⟨0, fun ε CF _ => ⟨0, (12 : ℝ) ^ (5 / ε), fun C _ D large₂ he hx hR T Lc μ₀ hL G W B ρ ρ₀ h1 h2 i j => ?_⟩⟩
  have hst := standing hR.size hL hR.size.2.1.eleven_le G
  obtain ⟨lam, h0, H⟩ := exists_scalar_of_standing hP hK hLM hL W hst B ρ ρ₀ h1 h2 i j
  exact ⟨lam, h0, fun t c' c₀ hc hc₀ => ⟨(H t c' c₀ hc hc₀).1, (H t c' c₀ hc hc₀).2.1⟩⟩

end Main

end GlobalTheory.RealSep

end
