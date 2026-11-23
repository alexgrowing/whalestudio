import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstOneMem
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.HasPresCutCocycleLocalCoefficient
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsAdmissibleExtensionLatticeTensor
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.HasPresOfInjectiveEquivariant
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsCyclicGeneratorLamPowerQuotient
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsEmbeddingAndEigenvectorsOfAdmissibleDecomp
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.IotaCInjectiveAndEquivariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodORingOfIntegers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwistedCharacterCocycleOfTorsionLocalCocyc
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases
private theorem isAdmCoc_latOne_of_eigenvector_characters {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
      [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
      {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
      [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
      [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR)
      {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
      {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Algebra O LL] [IsFractionRing O LL] {nn : ℕ}
      (emb : ZMod nn → (K₀ →ₐ[Qp] LL)) (lam : O) (jT : ZMod nn → ℤ → ℤ) (cT : G → Polynomial LL)
      {Xs : Type} {n : ℕ} (N : Xs → (G →* Matrix (Fin n) (Fin n) O)) (θ χ ψ κ κ₁ : G →* Oˣ) (p : Xs)
      (hinj : Function.Injective (algebraMap O LL)) (M : G →* Matrix (Fin 1) (Fin 1) O) (a : ℕ)
      (z : G → ↥(latOne hinj ψ).T ⊗[O] ↥(Xq LL lam a)) (f : G → (Fin 1 → LL) ⧸ stdG O LL 1)
      (hχ : χ = θ) (hψ : ψ = κ * θ) (hκ : κ₁ = 1) (hlam : lam ≠ 0)
      (hM : ∀ g, (((χ g)⁻¹ * ψ g : Oˣ) : O) = M g 0 0)
      (hfull : ∀ x, tableLineDegreeTwo.IsFull PD emb lam jT cT (matRep (mapM (algebraMap O LL) (twistM (N x) θ))))
      (hpres : UpperTheory.KN.HasPres LL N (Q := (Fin 1 → LL) ⧸ stdG O LL 1) (fun g => actD (stdLatG hinj M) g) f)
      (hz : ∀ g, iotaC LL lam a (z g) = f g)
      (hu : ∃ u : Fin n → LL, u ≠ 0 ∧ ∀ g, ((N p g).map (algebraMap O LL)).mulVec u = ((κ g : Oˣ) : O) • u)
      (he : ∃ u : Fin n → LL, u ≠ 0 ∧ ∀ g, ((N p g).map (algebraMap O LL)).mulVec u = ((κ₁ g : Oˣ) : O) • u) :
      tableLineDegreeTwo.IsAdmCoc PD emb lam jT cT (latOne hinj ψ) ↥(Xq LL lam a) χ z := by
  obtain ⟨u, hu0, hu⟩ := hu
  obtain ⟨e, he0, he⟩ := he
  subst hκ
  have hI := UpperTheory.KN.iotaC_injective_and_equivariant hinj M χ ψ lam a hM
  have h3 : UpperTheory.KN.HasPres LL N (fun g => tableLineDegreeTwo.actTw (latOne hinj ψ) ↥(Xq LL lam a) χ g) z :=
    UpperTheory.KN.hasPres_of_injective_equivariant N _ _ (iotaC LL lam a) z f hI.1 hI.2 hz hpres
  obtain ⟨x₀, hx⟩ := UpperTheory.KN.exists_cyclic_generator_lam_power_quotient LL hinj lam a (fun h0 => hlam (hinj (h0.trans (map_zero _).symm)))
  refine ⟨0, fun b _ hb => ?_⟩
  refine UpperTheory.KN.exists_admissible_extension_latticeTensor PD emb lam jT cT N θ χ p (latOne hinj ψ) ↥(Xq LL lam a) z
    (LinearMap.toSpanSingleton LL _ u) e x₀ hχ hlam hfull h3
    (fun s t hst => smul_left_injective LL hu0 hst) (fun g v => ?_) he0 (fun g => ?_) hx b hb
  · rw [LinearMap.toSpanSingleton_apply, LinearMap.toSpanSingleton_apply, Matrix.mulVec_smul, hu g, hψ]
    funext m
    simp [Formalism.WeaklyAdmissibleFiltrations.charRep, tableLineDegreeTwo.charL, Algebra.smul_def]
    ring
  · rw [he g]
    simp

theorem _root_.GlobalTheory.T.cocycleExtension_conductorTwistedCharacter_admissible : ∀ (D : D7) (HW : HWOf D.loc) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
      (h w' η : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → ℕ)
      (typ : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Bool)
      (U : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Multiset ℤ),
    SetC HW r ρ π C hA lam θ h w' η typ U → GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π →
    TruncatedSeriesCountingIdentities.FamilyContinuous i r →
    ∀ c ∈ Finset.Icc 1 D.R.t, ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i c), ∀ (a : ℕ)
      (z' : Br.G D.nbr i w hw → ↥(latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a)),
    tableLineDegreeTwo.IsCoc (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' →
    (∀ g, iotaC ↥C.LL.1 lam a (z' g) = liftQ C.le 1 (z g)) →
    tableLineDegreeTwo.IsAdmCoc (Br.PD D.loc D.nbr i w hw) (embC HW C hA) lam (tableLineDegreeTwo.jTil U w' D.R.t)
      (tableLineDegreeTwo.resPoly (repV C (twistM (locOC C (WpO D.nd i ρ π)) θ)) (chiT C θ) D.R.t) (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c))
      ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' := by
  intro D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hSet _ _ hDec _ c hc z hz a z' _ hz'
  have hG := GlobalTheory.Pass.goodO_ringOfIntegers (D.nd.l i) C.LL
  have hdom : IsDomain ↥(OL C.LL) := hG.1.1
  have hdvr : @IsDiscreteValuationRing ↥(OL C.LL) _ hdom := hG.1.2.1
  have hfr : IsFractionRing ↥(OL C.LL) ↥C.LL.1 := hG.1.2.2
  have hpid : IsPrincipalIdealRing ↥(OL C.LL) := hdvr.toIsPrincipalIdealRing
  have h2 := UpperTheory.KN.hasPres_cutCocycle_localCoefficient D i r w hw C (chiRatO D.nd i c) z hz
  have hE := UpperTheory.KN.exists_embedding_and_eigenvectors_of_admissible_decomposition D i r ρ π w hw C hDec
  have hκ : chiOC C (chiU D.nd i 1 * (chiU D.nd i 1)⁻¹) = 1 := by simp [chiOC]
  have H := isAdmCoc_latOne_of_eigenvector_characters (Br.PD D.loc D.nbr i w hw) (embC HW C hA) lam (tableLineDegreeTwo.jTil U w' D.R.t)
    (tableLineDegreeTwo.resPoly (repV C (twistM (locOC C (WpO D.nd i ρ π)) θ)) (chiT C θ) D.R.t)
    (fun x => locOC C (rTwO D.nd i r x)) θ (chiT C θ 1) (chiT C θ c)
    (chiOC C (chiU D.nd i c * (chiU D.nd i 1)⁻¹)) (chiOC C (chiU D.nd i 1 * (chiU D.nd i 1)⁻¹)) π
    Subtype.val_injective (locOC C (chiRatO D.nd i c)) a z' (fun g => liftQ C.le 1 (z g))
    (chiT_one_eq_theta C θ) rfl hκ hlam.ne_zero (chiT_ratio C θ c) hSet.2 h2 hz' (hE.2 c hc)
    (hE.2 1 (Finset.mem_Icc.2 ⟨le_rfl, hSet.1.1⟩))
  exact H
