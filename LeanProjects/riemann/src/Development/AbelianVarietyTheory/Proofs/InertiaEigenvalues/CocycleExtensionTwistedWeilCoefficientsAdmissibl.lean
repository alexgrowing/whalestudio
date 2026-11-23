import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstOneMem
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.HasPresCutCocycleLocalCoefficient
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsAdmissibleExtensionLatticeTensor
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.HasPresOfInjectiveEquivariant
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsCyclicGeneratorLamPowerQuotient
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsEmbeddingAndEigenvectorsOfAdmissibleDecomp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodORingOfIntegers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralTensorTorsionCocycleOfTorsionLocal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBlochKatoReadOfTensorSelmerAddCoboundary
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

private theorem period_ring_generic_hodge {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [Algebra O LL] (hdom : IsDomain O) (hpid : IsPrincipalIdealRing O)
    (hfr : IsFractionRing O LL) {nn : ℕ}
    (emb : ZMod nn → (K₀ →ₐ[Qp] LL)) (lam : O) (jT : ZMod nn → ℤ → ℤ) (cT : G → Polynomial LL)
    {Xs : Type} {n k : ℕ}
    (hinj : Function.Injective (algebraMap O LL))
    (N : Xs → (G →* Matrix (Fin n) (Fin n) O)) (M : G →* Matrix (Fin k) (Fin k) O) (θ χ : G →* Oˣ) (p : Xs) (a : ℕ)
    (z : G → ↥(stdLatG hinj (twistM M θ)).T ⊗[O] ↥(Xq LL lam a)) (f : G → (Fin k → LL) ⧸ stdG O LL k)
    (hχ : χ = θ) (hlam : lam ≠ 0)
    (hfull : ∀ x, tableLineDegreeTwo.IsFull PD emb lam jT cT (matRep (mapM (algebraMap O LL) (twistM (N x) θ))))
    (hz : ∀ g, iotaW LL lam a k (z g) = f g)
    (hpres : UpperTheory.KN.HasPres LL N (Q := (Fin k → LL) ⧸ stdG O LL k) (fun g => actD (stdLatG hinj M) g) f)
    (hW : ∃ iW : (Fin k → LL) →ₗ[LL] (Fin n → LL), Function.Injective iW ∧
      ∀ g v, iW (((M g).map (algebraMap O LL)).mulVec v) = ((N p g).map (algebraMap O LL)).mulVec (iW v))
    (ψ : G →* Oˣ) (hψ : ∀ g, ψ g = 1)
    (he : ∃ e : Fin n → LL, e ≠ 0 ∧ ∀ g, ((N p g).map (algebraMap O LL)).mulVec e = ((ψ g : Oˣ) : O) • e) :
    tableLineDegreeTwo.IsAdmCoc PD emb lam jT cT (stdLatG hinj (twistM M θ)) ↥(Xq LL lam a) χ z := by
  subst hχ
  obtain ⟨iW, hW1, hW2⟩ := hW
  obtain ⟨e, he1, he2⟩ := he
  obtain ⟨x₀, hx⟩ := UpperTheory.KN.exists_cyclic_generator_lam_power_quotient LL hinj lam a (fun h0 => hlam (hinj (h0.trans (map_zero _).symm)))
  have h3 : UpperTheory.KN.HasPres LL N (fun g => tableLineDegreeTwo.actTw (stdLatG hinj (twistM M χ)) ↥(Xq LL lam a) χ g) z :=
    UpperTheory.KN.hasPres_of_injective_equivariant _ _ _ (iotaW LL lam a k) z f (LiftW.iotaW_injective LL lam a k)
      (fun g u => LiftW.iotaW_actTw hinj lam a M χ g u) hz hpres
  refine ⟨0, fun b _ hb => ?_⟩
  refine UpperTheory.KN.exists_admissible_extension_latticeTensor PD emb lam jT cT N χ χ p (stdLatG hinj (twistM M χ)) ↥(Xq LL lam a) z iW e x₀ rfl hlam
    hfull h3 hW1 (fun g v => ?_) he1 (fun g => ?_) hx b hb
  · refine (congrArg _ (matRep_twistM_apply M χ g v)).trans ?_
    rw [LinearMap.map_smul_of_tower]
    exact congrArg _ (hW2 g v)
  · rw [he2 g, hψ g, Units.val_one, one_smul]

private theorem chi_mul_inv_eq_one {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (g : Br.G D.nbr i w hw) :
    chiOC C (chiU D.nd i 1 * (chiU D.nd i 1)⁻¹) g = 1 := by
  simp [chiOC]

attribute [-instance] GlobalTheory.AdmLoc.modFun in
theorem _root_.GlobalTheory.T.cocycleExtension_twistedWeilCoefficients_admissible : ∀ (D : D7) (HW : HWOf D.loc) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
      (h w' η : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → ℕ)
      (typ : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Bool)
      (U : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Multiset ℤ),
    SetC HW r ρ π C hA lam θ h w' η typ U → GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π →
    TruncatedSeriesCountingIdentities.FamilyContinuous i r →
    ∀ z ∈ cutCoc i w hw r Set.univ (WpO D.nd i ρ π), ∀ (a : ℕ)
      (z' : Br.G D.nbr i w hw → ↥(latC C (twistM (locOC C (WpO D.nd i ρ π)) θ)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a)),
    tableLineDegreeTwo.IsCoc (latC C (twistM (locOC C (WpO D.nd i ρ π)) θ)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' →
    (∀ g, iotaW ↥C.LL.1 lam a D.R.r (z' g) = liftQ C.le D.R.r (z g)) →
    tableLineDegreeTwo.IsAdmCoc (Br.PD D.loc D.nbr i w hw) (embC HW C hA) lam (tableLineDegreeTwo.jTil U w' D.R.t)
      (tableLineDegreeTwo.resPoly (repV C (twistM (locOC C (WpO D.nd i ρ π)) θ)) (chiT C θ) D.R.t) (latC C (twistM (locOC C (WpO D.nd i ρ π)) θ)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' := by
  intro D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hSet _ _ hDec _ z hz a z' _ hz'
  have hG := GlobalTheory.Pass.goodO_ringOfIntegers (D.nd.l i) C.LL
  have hdom : IsDomain ↥(OL C.LL) := hG.1.1
  have hdvr : @IsDiscreteValuationRing ↥(OL C.LL) _ hdom := hG.1.2.1
  have hE := UpperTheory.KN.exists_embedding_and_eigenvectors_of_admissible_decomposition D i r ρ π w hw C hDec
  exact period_ring_generic_hodge (Br.PD D.loc D.nbr i w hw) hdom hdvr.toIsPrincipalIdealRing hG.1.2.2 (embC HW C hA) lam _ _
    Subtype.val_injective (fun x => locOC C (rTwO D.nd i r x)) (locOC C (WpO D.nd i ρ π)) θ (chiT C θ 1) π a z'
    (fun g => liftQ C.le D.R.r (z g)) (LiftW.chiT_one C θ) hlam.ne_zero hSet.2 hz'
    (UpperTheory.KN.hasPres_cutCocycle_localCoefficient D i r w hw C (WpO D.nd i ρ π) z hz) hE.1 _ (chi_mul_inv_eq_one C)
    (hE.2 1 (Finset.mem_Icc.2 ⟨le_rfl, hSet.1.1⟩))
