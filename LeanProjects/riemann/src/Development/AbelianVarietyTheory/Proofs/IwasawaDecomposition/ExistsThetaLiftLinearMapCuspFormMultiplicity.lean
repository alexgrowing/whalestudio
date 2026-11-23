import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqTopOfTranslates
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedHolomorphicFormEqMultiplicitySpaceValueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspFunOfTransvectionConstantTermsZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFiresIffThetaMultExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuotVolumeNeZeroNeTop
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VectorLevelCharacters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyCompactSecondCountableBorelCountable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicDiscreteSeriesLowestKTypeSmoothIrreduStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundedOfSmoothCuspidalUniformModerateStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicTypeAtExtremalOfKEquivariantLoweringKStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteThetaLiftContinuousInvariantHasDerivAtStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftDefiniteSmoothModerateGrowthAnnihilatedStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftDefiniteConstantTermEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestKTypeValuesKilledByLoweringPartStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsModelHolomorphicIntegralExtremalWeightStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockVectorMixedLaplacianKilledLoweringKilledStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MixedLaplacianKillsProductOfMinorsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilFiniteVectorFixedPrincipalLevelCoeffSpaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockVectorsKilledHeisenbergAverageIsotropicStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.DefLift.ThetaMap

open GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions

variable {D : D7}

open Classical in

theorem restrictsTo_of_eq {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} (h1 : LowSm M)
    (h2 : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M) {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T)
    {U : KMap M} (hU : KEquiv θ M U) (e : ∀ τ, lowT M τ) (he : ∀ τ, e τ ≠ 0)
    (h : T (fun τ => (e τ : M.sm τ)) = U e) : RestrictsTo M T U := by
  intro v
  have key := mem_of_translates h1 h2 (T.compLinearMap (fun τ => (lowT M τ).subtype) - U) ⊥ e he
    (by simpa [sub_eq_zero] using h) (fun τ k hk v u hu hv => ?_) v
  · simpa [sub_eq_zero] using key
  · have hv' : T (fun τ => (v τ : M.sm τ)) = U v := by simpa [sub_eq_zero] using hv
    have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
    have hg : (M.fr τ)⁻¹ * k * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
      have hk' : kᴴ * Formalism.REAL.Jm (M.ε τ) * k = Formalism.REAL.Jm (M.ε τ) := kset_uj hk
      have e1 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by
        rw [← conjTranspose_mul, mul_nonsing_inv _ hd, conjTranspose_one]
      change ((M.fr τ)⁻¹ * k * M.fr τ)ᴴ * gramAt D V τ * ((M.fr τ)⁻¹ * k * M.fr τ) = gramAt D V τ
      calc ((M.fr τ)⁻¹ * k * M.fr τ)ᴴ * gramAt D V τ * ((M.fr τ)⁻¹ * k * M.fr τ)
          = (M.fr τ)ᴴ * (kᴴ * (((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ) * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * k) *
              M.fr τ := by
            rw [← M.fr_gram τ]; simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = gramAt D V τ := by rw [e1, mul_nonsing_inv _ hd, Matrix.mul_one, Matrix.mul_one, hk', M.fr_gram]
    have e2 : M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹ = k := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_assoc,
        mul_nonsing_inv _ hd, Matrix.mul_one]
    have e3 := hT.equiv τ _ hg (fun τ => (v τ : M.sm τ)) (u : M.sm τ) (by
      rw [hu, DSModel.rep, e2])
    have e4 : (fun ρ => ((Function.update v τ u ρ : lowT M ρ) : M.sm ρ)) =
        Function.update (fun ρ => (v ρ : M.sm ρ)) τ (u : M.sm τ) :=
      funext fun ρ => Function.apply_update (fun ρ (y : lowT M ρ) => (y : M.sm ρ)) v τ u ρ
    have e5 : T (fun ρ => ((Function.update v τ u ρ : lowT M ρ) : M.sm ρ)) = U (Function.update v τ u) := by
      rw [e4, e3, hv', hU τ k hk v u hu]
    simpa [sub_eq_zero] using e5

theorem exists_extension (hP : GlobalTheory.Published.CuspRapidDecay) {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D}
    {S : D.what₂.Tau → SPar} {M : DSModel V S} (hM : HolShape M) {w : D.what₂.Tau → Fin V.rank → ℤ} (hw : WtIs M w)
    {J : Set (GA D V)} (hJ : J ⊆ (GfC V : Set (GA D V))) {χ : GA D V → ℂ} {U : KMap M} (ha : ∀ e, IsAutFun V (U e))
    (hl : ∀ e, ∀ k ∈ J, ∀ g, U e (g * k) = χ k * U e g) (hs : ∀ e, IsSmoothFn V θ (U e))
    (hg : ∀ e, IsUnifModGrowth V θ (U e)) (hz : ∀ e, ZCusp V (U e)) (hk : KEquiv θ M U)
    (hh : ∀ τ, ∀ Z ∈ pMinus M τ, ∀ e, RderC θ V τ Z (U e) = 0) :
    ∃ T : MMap M, IsMultMap θ M J χ T ∧ RestrictsTo M T U := by
  obtain ⟨h1, h2⟩ := GlobalTheory.T.holomorphicDiscreteSeries_lowestKType_smooth_irreducible D V S M hM
  obtain ⟨v, hv⟩ := exists_isExtVec M h1
  let e : ∀ τ, lowT M τ := fun τ => ⟨v τ, (hv τ).2.1⟩
  have he : ∀ τ, e τ ≠ 0 := fun τ h0 => by
    have h3 : v τ = 0 := congrArg Subtype.val h0
    have := (hv τ).1
    rw [h3] at this
    simp at this
  have hfin : ∃ μ 𝓕, FinPair V μ 𝓕 := by
    obtain ⟨_, _, _, _⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable V
    have : IsTopologicalGroup (GA D V) :=
      inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
    have hμ : (Measure.haar : Measure (GA D V)).IsHaarMeasure := inferInstance
    obtain ⟨hr, 𝓕, h𝓕⟩ := GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V _ hμ
    exact ⟨_, 𝓕, hμ, hr, h𝓕, (GlobalTheory.Mem.QuotVol.quot_volume_ne_zero_ne_top D V _ 𝓕 ⟨hμ, h𝓕⟩).2⟩
  obtain ⟨T, hT, hTe⟩ := GlobalTheory.T.boundedHolomorphicForm_eq_multiplicitySpace_value D θ V S M w v hθ hM hw hv hfin J χ (U e) hJ
    ⟨ha e, GlobalTheory.T.bounded_of_smooth_cuspidal_uniform_moderate hP D θ V hθ _ (ha e) (hs e) (hg e) (GlobalTheory.T.isCuspFun_of_transvection_constantTerms_zero D θ V hθ _ (ha e) (hz e)), hl e,
      GlobalTheory.T.holomorphicType_at_extremal_of_kEquivariant_loweringKilled D θ V S M w hθ hM hw h1 h2 U hs hk hh e hv⟩ (hz e)
  exact ⟨T, hT, restrictsTo_of_eq h1 h2 hT hk e he hTe⟩

open Classical in

theorem exists_member (hP : GlobalTheory.Published.CuspRapidDecay) {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
    {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om)
    {θ : InfFam D} (hθ : IsInfFam θ) (hpos : ∀ τ, (gramAt D S τ).PosDef)
    {Sp : D.what₂.Tau → SPar} {M : DSModel T Sp} (hM : HolShape M) {w : D.what₂.Tau → Fin T.rank → ℤ} (hw : WtIs M w)
    {c : CoefA S} (hc : c.Is) (pt : PolF D T.rank S.rank →ₗ[ℂ] (WO S T → ℂ)) (hpt : ∀ P, IsThetaFunO ψ S T (pt P))
    {Δ : PolF D T.rank S.rank} {io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D T.rank S.rank}
    (hio : IsIoW θ M c om (fun P => pt P) Δ io)
    (hΔ : ∀ τ, ∀ Z ∈ pMinus M τ, ∀ h, RderC θ T τ Z (fun g => thetaKO om h g (pt Δ)) = 0)
    {J : Set (GA D T)} (hJ : J ⊆ (GfC T : Set (GA D T)))
    (hJo : ∃ U : Subgroup (GA D T), IsOpen (U : Set (GA D T)) ∧ ∀ k ∈ U, k ∈ GfC T → k ∈ J)
    (hfix : ∀ k ∈ J, ∀ P, om (1, k) (pt P) = pt P) {χ : GA D T → ℂ} (hχ : ∀ k, χ k = 1)
    (hsupp : ∀ P h g ξ, IsoVec T ξ → ∃ n : ℕ, 0 < n ∧ ∃ a : Fin n → Fin S.rank → AE D,
      ∑ k, heisO ψ S T (along S T ξ (a k)) (om (h, g) (pt P)) = 0)
    {F : GA D S → c.W} (hF : Continuous F) (hFi : ∀ γ ∈ GQ S, ∀ h, F (γ * h) = F h)
    {ν : Measure (GA D S)} {𝓕 : Set (GA D S)} (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ S) 𝓕 ν) :
    ∃ Θ : MMap M, IsMultMap θ M J χ Θ ∧ ∀ v : ∀ ρ, lowT M ρ,
      Θ (fun ρ => (v ρ : M.sm ρ)) = lift om ν 𝓕 fun h => pt (io (PiTensorProduct.tprod ℂ v) (F h)) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.T.holomorphicDiscreteSeries_lowestKType_smooth_irreducible D T Sp M hM
  have hint : ∀ e g, IntegrableOn (fun h => thetaKO om h g (pt (io e (F h)))) 𝓕 ν := fun e g =>
    GlobalTheory.DefiniteQuotient.integrableOn_theta D ψ hom.std S T χS χT om hom hpos c.W (pt ∘ₗ io e)
      (fun _ => hpt _) _ hF hFi ν 𝓕 hν h𝓕 g
  let U₀ : LowT M →ₗ[ℂ] (GA D T → ℂ) :=
    { toFun := fun e => lift om ν 𝓕 fun h => pt (io e (F h))
      map_add' := fun e e' => by
        funext g
        simp only [lift, thetaKO, map_add, LinearMap.add_apply, Pi.add_apply]
        exact integral_add (hint e g) (hint e' g)
      map_smul' := fun a e => by
        funext g
        simp only [lift, thetaKO, map_smul, LinearMap.smul_apply, Pi.smul_apply, RingHom.id_apply]
        exact integral_smul a _ }
  let U : KMap M := U₀.compMultilinearMap (PiTensorProduct.tprod ℂ)
  have hU : ∀ v, U v = lift om ν 𝓕 fun h => (pt ∘ₗ io (PiTensorProduct.tprod ℂ v)) (F h) := fun _ => rfl
  have hmul : ∀ h g k φ, thetaKO om h (g * k) φ = thetaKO om h g (om (1, k) φ) := fun h g k φ => by
    unfold thetaKO
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have hlev : ∀ v, ∀ k ∈ J, ∀ g, U v (g * k) = U v g := fun v k hk g => by
    simp only [hU, lift, hmul, LinearMap.comp_apply, hfix k hk]
  have hd := fun v => GlobalTheory.T.definiteThetaLift_continuous_invariant_hasDerivAt D ψ S T χS χT om hom θ hθ hpos c.W (pt ∘ₗ io (PiTensorProduct.tprod ℂ v))
    (fun _ => hpt _) F hF hFi ν 𝓕 hν h𝓕
  have hs := fun v => GlobalTheory.T.thetaLift_definite_smooth_moderate_growth_annihilated D ψ S T χS χT om hom θ hθ hpos c.W (pt ∘ₗ io (PiTensorProduct.tprod ℂ v))
    (fun _ => hpt _) F hF hFi ν 𝓕 hν h𝓕
  have hz := fun v => GlobalTheory.T.thetaLift_definite_constantTerm_eq_zero D ψ S T χS χT om hom hpos c.W (pt ∘ₗ io (PiTensorProduct.tprod ℂ v))
    (fun _ => hpt _) F hF hFi ν 𝓕 hν h𝓕 fun x h g ξ hξ => hsupp _ h g ξ hξ
  obtain ⟨O, hO, hOJ⟩ := hJo
  exact exists_extension hP hθ hM hw hJ (U := U)
    (fun v => ⟨(hd v).1.2, ⟨O, hO, fun k hk hk' => hlev v k (hOJ k hk hk')⟩, (hd v).1.1⟩)
    (fun v k hk g => by rw [hχ, one_mul, hlev v k hk]) (fun v => (hs v).1) (fun v => (hs v).2.1) hz
    (fun τ k hk v u hu => by
      funext g
      simp only [hU, lift, rTr, hmul, LinearMap.comp_apply, hio.2.1 τ k hk v u hu])
    fun τ Z hZ v => (hs v).2.2 τ Z fun x h =>
      GlobalTheory.T.lowestKType_values_killed_by_loweringPart D ψ S T χS χT om hom θ hθ Sp M h1 h2 c hc pt hpt Δ io hio hΔ τ Z hZ v x h

theorem level_open (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → k ∈ levS V β L := by
  classical
  have : IsTopologicalGroup (GA D V) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  refine ⟨(lev D.sp.cm V.gram β L).comap (Lev.finE V), Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_, fun k hk hk' => ⟨hk', hk⟩⟩
  filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ V β (L.Pg ∪ L.Q)] with κ hh
  obtain ⟨h1, h2, h3⟩ := hh
  exact Kg_le_lev (D := L) (T := L.Pg ∪ L.Q) Finset.subset_union_left Finset.subset_union_right
      ⟨⟨h1, h2⟩, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_princAt.2 ⟨h2, h3 PP hP⟩⟩

theorem pureTensorO_one {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} sS sT BS BT (f : WO S T → ℂ) :
    pureTensorO ψ θ S T sS sT BS BT f 1 = f := by
  have : (1 : PolF D T.rank S.rank) = MvPolynomial.basisMonomials _ ℂ 0 := by simp
  rw [this, pureTensorO, pureTensorL, Module.Basis.constr_basis]
  simp [opPow]

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem firesAt (hP : GlobalTheory.Published.CuspRapidDecay) (R : RealDat D A Ks) (h0 : R.toLevCh.Is A.μ0) (hm : R.IsModels)
    (hω : R.thP_ωP) (hv : R.thP_vP) (hp : R.thP_pt_theta) (hio : R.thP_ioP) (i : Fin D.R.m) (t : T) (x : (R.HV i t).H) :
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelFiring.FiresAt R i t x := by
  have hx : (R.HV i t).e x ∈ Bridge.AdForms (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ
      (levEnv _ (R.βV i) (R.datVt i t)).J (levEnv _ (R.βV i) (R.datVt i t)).χ :=
    (hm.HV i t).2.1.le (LinearMap.mem_range_self _ x)
  have hpos : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ => by
    have := D.sp.V_sig ((i : ℕ) + 1) (tauE D τ)
    rw [hm.vpos i] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  have hth : ∀ i t, IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := fun i t => by
    have := hp i t 1
    rwa [RealDat.ptP, pureTensorO_one] at this
  obtain ⟨hM, w, hw⟩ := GlobalTheory.T.forms_model_holomorphic_integral_extremal_weight D G Pl0 T A Ks R hm.order i
  have hpq : ∀ τ, ((Wc D i).sig (tauE D τ)).1 + ((Wc D i).sig (tauE D τ)).2 ≤ (Vc D i).rank := fun τ => by
    have e := GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW_add_qW i τ
    have e' := rank_Wc i
    have := r_le_V i
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW, GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.qW] at e
    omega
  have hΔ := fun τ => GlobalTheory.T.fockVector_mixedLaplacianKilled_loweringKilled D R.ψ (Vc D i) (Wc D i) _ _ (R.ωP i t) (hω i t) R.θ hm.inf (D.sp.V_sig _) (D.sp.W_sig _)
    (R.BV i) (hm.BV i) _ (R.MW i (sg0 D A)) (fun τ => ((Wc D i).sig (tauE D τ)).1) (hm.order i) (R.vP i t) (hth i t)
    (GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hv i t) (hth i t)) (RealDat.Delta i) τ
    (GlobalTheory.T.mixed_laplacian_kills_product_of_minors D _ _ _ _ _ _ hpq τ)
  have key := exists_member hP (hω i t) hm.inf hpos hM hw (hm.cV i)
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A)))
      (R.vP i t)) (hp i t) (hio i t) hΔ (J := levS _ (R.βW i) (R.datWp i R.triv)) (fun _ hk => hk.1)
    (level_open _ _ _) (fun k hk P => by
      rw [GlobalTheory.OrientedHeis.om_fin_pureTensorO R.ψ _ _ _ _ _ (hω i t) R.θ hm.inf 1 (one_mem _) k hk.1 _ _ _ _ _ P (hth i t),
        GlobalTheory.T.weilFiniteVector_fixed_principalLevel_coeffSpace D G Pl0 T A Ks R h0 hω hv hth i t k hk])
    (GlobalTheory.IndefiniteRowSideFullHecke.VectorLevelCharacters.principalLevelCharacter_eq_one R i) (GlobalTheory.T.fock_vectors_killed_heisenberg_average_isotropic D G Pl0 T A Ks R h0 hm.inf hω hv hp i t)
    (GlobalTheory.ThetaIntegrand.ext_continuous (R.cV i) (hm.cV i) _ _ hx) (GlobalTheory.ThetaIntegrand.ext_invariant (R.cV i) hx)
    (hm.νV i t).1.1 (hm.νV i t).2
  obtain ⟨Θ, hΘ, hΘv⟩ := key
  refine ⟨fun e g => ?_, Θ, Submodule.subset_span hΘ, hΘv⟩
  exact GlobalTheory.ThetaIntegrand.integrableOn_form (hω i t) (D.sp.V_sig _) (hm.vpos i) (R.cV i) (hm.cV i) (R.βV i)
    (R.datVt i t) hx
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A)))
      (R.vP i t)) (hp i t) (R.ioP i e) (hm.νV i t) g

theorem exists_thetaMap : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.thP_ωP → R.thP_vP → R.thP_pt_theta → R.thP_ioP → ∃ th, ({ R with thF := th } : RealDat D A Ks).thP_thF_mem ∧ ({ R with thF := th } : RealDat D A Ks).thP_thF := by
  intro hP D G _ _ Pl0 T A Ks _ _ _ R h0 _ hm hω hv hp hio
  choose th hth using fun i t =>
    GlobalTheory.ThetaFiresOfMult.exists_isThetaMult_of_firesAt (firesAt hP R h0 hm hω hv hp hio i t)
  exact ⟨th, fun i t => (hth i t).1, fun i t => (hth i t).2⟩

end GlobalTheory.DefLift.ThetaMap

end
