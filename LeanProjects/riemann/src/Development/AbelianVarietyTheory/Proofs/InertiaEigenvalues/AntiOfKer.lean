import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Small2
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCConj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisTwistedSelmerAuxprimesOfMatrixAndBounds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAuxiliaryPrimesPrescribedFrobenius
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenNormalSubgroupUnderInertia
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevInductionGrowBoundOfPresentationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniversalSelmerCocycleMapAlgHomStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComparisonCocyclesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerUnramifiedOfVanishInertiaGeneratorsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedRepresentationKillsSmallSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetNeZeroOfLowestFormNeZeroPresentationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniversalCocycleRowsRelationNewPlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReciprocityRelaxedSelmerDualSelmerNewPlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNewPlaceFrobeniusConjugateModOpenNormalSubStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLambdaAlgebraHomEvaluationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalEqZeroOfLowCoeffOfNilpotentMultipleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteLocalRingPolyDividesVarPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetupOfFactorStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniversalSelmerCocycleBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PerfectPairingFiniteModuleRowsCriterionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoInvDualOfSetupStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDualSelmerClassNotKilledStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerOrderFormulaDualSelmerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalInvariantsKilledStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmallSubgroupCocycleFormNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenNormalSubgroupTwoCocyclesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaVanishingNoInvariantsFirstHalfPlacesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRingSqZeroNilpotentAugmentedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalEqZeroLowCoeffThreeNilpotentsStatement

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet

noncomputable section

namespace GlobalTheory.NewPrime

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {bkP : BKPh X}
  {i : X.Tw} {s : X.Sig i}

theorem small_inf {M : ℕ} {L : Subgroup (GE N)} {z : GE N} (hL : Small2 i s M L z) {ι C : Type} [Finite ι] [CommGroup C]
    (d : ι → (GE N →* C)) (ho : ∀ q, IsOpen ((d q).ker : Set (GE N))) (ha : ∀ q, AntiHom X.cc (d q)) :
    Small2 i s M (L ⊓ ⨅ q, (d q).ker) z := by
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, h6, h7⟩ := hL
  refine ⟨⟨?_, ?_, fun g g' hg => ?_, fun g => ⟨h4 g, ?_⟩, fun g hg => h5 g hg.1⟩, fun g hg => h6 g hg.1,
    fun g hg => h7 g hg.1⟩
  · refine h1.inter ?_
    show IsOpen ((⨅ q, (d q).ker : Subgroup (GE N)) : Set (GE N))
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite ho
  · have : (⨅ q, (d q).ker).Normal := Subgroup.normal_iInf_normal fun b => inferInstance
    infer_instance
  · simp only [Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker, h3 g g' hg]
    refine and_congr_right fun _ => forall_congr' fun q => ?_
    rw [ha q g g' hg, inv_eq_one]
  · refine Subgroup.mem_iInf.2 fun q => ?_
    simp [MonoidHom.mem_ker]

theorem anti_of_ker {ι C C' : Type} [CommGroup C] [CommGroup C'] (d : ι → (GE N →* C)) (ha : ∀ q, AntiHom X.cc (d q))
    (κ : GE N →* C') (h : ∀ g, (∀ q, d q g = 1) → κ g = 1) : AntiHom X.cc κ := fun g g' hg => by
  rw [eq_inv_iff_mul_eq_one, ← map_mul]
  exact h _ fun q => by rw [map_mul, ha q g g' hg, inv_mul_cancel]

theorem IsChar.eq_one {Λ : Type} [CommRing Λ] {κ : GE N →* Λˣ} {M : ℕ} {ι : Type} [Fintype ι] {ξ : ι → Λ}
    {d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))} (h : IsChar i κ ξ d) {g : GE N}
    (hg : ∀ q, ξ q = 0 ∨ d q g = 1) : κ g = 1 := by
  have e := h g
  rw [Finset.prod_eq_one, mul_one] at e
  · exact Units.ext e
  · intro q _
    rcases hg q with h0 | h0 <;> simp [h0]

theorem IsChar.single {Λ : Type} [CommRing Λ] {κ : GE N →* Λˣ} {M : ℕ} {ι : Type} [Fintype ι] {ξ : ι → Λ}
    {d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))} (h : IsChar i κ ξ d) {g : GE N} (q₀ : ι)
    (hg : ∀ q, q ≠ q₀ → ξ q = 0 ∨ d q g = 1) :
    ((κ g : Λˣ) : Λ) * (1 + ξ q₀) ^ (Multiplicative.toAdd (d q₀ g)).val = 1 := by
  have e := h g
  rwa [Finset.prod_eq_single q₀ (fun q _ hq => by rcases hg q hq with h0 | h0 <;> simp [h0]) (by simp)] at e

theorem det_ne_zero (hPT : PoitouTateTotallyComplex) (hT : TameLocal) (hl : 0 < nu X i) {M : ℕ} {L : Subgroup (GE N)} {z : GE N}
    {p : PlE D.host} {d : GE N →* Multiplicative (ZMod (X.l i ^ M))} {σ γ : GE N} (h3 : nu X i + 2 ≤ M) (hL : Small2 i s M L z)
    (hp : NewPl i M L p d σ γ) {A : Type} [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A]
    [TopologicalSpace A] [DiscreteTopology A] {κ : GE N →* Aˣ} {Q Q' : Finset (PlE D.host)}
    {ρ : GE N →* GL (Fin D.R.r) (X.O0 i)} (hS : Setup bkP i s κ Q) (hK : Kills i A) (hρ : IsDual i s ρ)
    (ha : AntiHom X.cc κ) (hκ : ∀ g ∈ DecV N p, κ g = 1) (hQ : ∀ v, v ∈ Q' ↔ v ∈ Q ∨ Over p v)
    {Y : Type} [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y]
    {β : Y →+ A →+ ZMod (X.l i ^ (nu X i + 1))} (hβ : Perf A β)
    (hcog : ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) A) (v : Fin a → A),
      (∀ x : Fin a → Y, matAct Φ x = 0 → ∑ j, v j • x j = 0) → v ∈ what₂ Φ)
    {a : ℕ} {Ψ : Matrix (Fin a) (Fin a) A} {Z : GE N → Matrix (Fin D.R.r) (Fin a) A} (hZ : Univ bkP i s κ Q Ψ Z)
    {y : Z1 (repOn ρ κ⁻¹ A)} (hy : DualSel bkP i s κ ρ β Q y) (l₀ : Fin a)
    (hB : bform (X := X) (fun g => rect (Z g) fun c => Ψ.adjugate c l₀) y.1 σ ≠ 0)
    {B : Type} [CommRing B] [Algebra (X.O0 i) B] (π : B →ₐ[X.O0 i] A) {x₁ x₂ : B} (hπ : Function.Surjective π)
    (hker : ∀ b, π b = 0 → b ∈ Ideal.span {x₁, x₂}) (h1 : π x₁ = 0) (h2 : π x₂ = 0) (h11 : x₁ * x₁ = 0)
    (h22 : x₂ ^ (2 * D.R.r) = 0) (h12 : ∀ f, x₁ * x₂ ^ (2 * D.R.r - 1) * f = 0 → π f = 0)
    {κ' : GE N →* Bˣ} (hκ' : ∀ g, ((κ g : Aˣ) : A) = π (κ' g : Bˣ)) (hK' : Kills i B) (ha' : AntiHom X.cc κ')
    (hI : ∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 p), ((κ' τ : Bˣ) : B) * (1 + x₁) ^ (Multiplicative.toAdd (d τ)).val = 1)
    (hσ : ((κ' σ : Bˣ) : B) * (1 + x₂) = 1) {a' : ℕ} {Φ' : Matrix (Fin a') (Fin a') B}
    {Z' : GE N → Matrix (Fin D.R.r) (Fin a') B} (hZ' : Univ bkP i s κ' Q' Φ' Z') : Φ'.det ≠ 0 := by
  have hZA := GlobalTheory.T.universalSelmerCocycle_map_algHom D N X bkP i s B A π κ' κ hκ' Q' a' Φ' Z' hZ'
  have hσD : σ ∈ DecV N p := hp.2.2.2.2.2.1.1
  have hσL : σ ∈ L := hp.2.2.2.1 hσD
  obtain ⟨E, hE1, hE2, hE3⟩ := GlobalTheory.T.comparison_cocycles_alt D N X bkP i s A κ Q Q' a a' Ψ (Φ'.map π) Z (fun g => (Z' g).map π) (two X γ) (two X σ)
    hZ hZA (GlobalTheory.T.selmer_unramified_of_vanish_inertia_generators hT D N X bkP i s hl M L z p d σ γ h3 hL hp A κ hK ha hκ Q Q' hQ) (fun W _ _ b m => by
      cases b
      · show repOn (Tgl i s) κ W σ m = m
        rw [(GlobalTheory.T.twisted_representation_kills_small_subgroup D N X i s hl M L z (by omega) hL A κ ρ hK hρ W σ hσL).1, hκ σ hσD, Units.val_one, one_smul]
      · show repOn (Tgl i s) κ W (cConj X σ) m = m
        rw [(GlobalTheory.T.twisted_representation_kills_small_subgroup D N X i s hl M L z (by omega) hL A κ ρ hK hρ W _
          ((hL.1.2.2.1 σ _ (cConj_apply X σ)).1 hσL)).1, antiHom_cConj X ha, hκ σ hσD, inv_one, Units.val_one, one_smul])
  have hcard : Fintype.card (Bool × Fin D.R.r) = 2 * D.R.r := by simp
  refine GlobalTheory.T.det_ne_zero_of_lowestForm_ne_zero_presentation A B (π : B →+* A) x₁ x₂ (Bool × Fin D.R.r) a a' Φ' (fun j => Z' (two X σ j.1) j.2)
    (fun j => Z' (two X γ j.1) j.2) (fun j => if j.1 then 1 else ((κ' σ : Bˣ) : B)) Ψ E (fun j => Z (two X σ j.1) j.2)
    (fun j => if j.1 then - y.1 (cConj X σ) j.2 else y.1 σ j.2) l₀ hπ hker h1 h2 h11 (hcard ▸ h22) (hcard ▸ h12)
    (fun j => ?_) (GlobalTheory.T.universal_cocycle_rows_relation_newPlace hT D N X bkP i s hl M L z p d σ γ h3 hL hp B κ' x₁ x₂ hK' ha' h11 hI hσ Q' a' Φ' Z' hZ')
    hE1 hE2 hE3 (hcog _ _ _ fun x hx => ?_) ?_
  · split_ifs
    · exact map_one _
    · show π _ = 1
      rw [← hκ', hκ σ hσD, Units.val_one]
  · refine hβ.2.1 _ fun c => ?_
    have hcx : matAct (Φ'.map π) (c • x) = 0 := by
      have hx' : matAct (Φ'.map π) x = 0 := hx
      rw [map_smul, hx', smul_zero]
    have e := GlobalTheory.T.reciprocity_relaxedSelmer_dualSelmer_newPlace hPT hT D N X bkP i s hl M L z p d σ γ h3 hL hp A κ Q Q' ρ hS hK hρ ha hκ hQ Y A β hβ.1 y _ hy
      ((hZA Y).1 _ hcx)
    have key : ∀ (g : GE N) (k : Fin D.R.r → A), vecPair D.R.r β (rect ((Z' g).map π) (c • x)) k =
        β (∑ j, (∑ u, k u * π (Z' g u j)) • x j) c := fun g k => by
      rw [vecPair_apply]
      simp only [rect, Finset.sum_smul, map_sum, AddMonoidHom.finsetSum_apply, Pi.smul_apply, Matrix.map_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun u _ => ?_
      rw [hβ.1, hβ.1, hβ.1, smul_eq_mul, smul_eq_mul, smul_eq_mul]
      congr 1
      ring
    rw [key, key, ← sub_eq_zero, ← AddMonoidHom.sub_apply, ← map_sub, ← Finset.sum_sub_distrib] at e
    rw [← e]
    congr 2
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← sub_smul, Finset.sum_apply, Fintype.sum_prod_type, Fintype.sum_bool, sub_eq_neg_add, ← Finset.sum_neg_distrib]
    simp only [← neg_mul]
    rfl
  · refine fun h0 => hB ?_
    rw [← h0, Fintype.sum_prod_type, Fintype.sum_bool, bform, sub_eq_neg_add, dotProduct_comm, dotProduct_comm _ (y.1 σ),
      ← neg_dotProduct]
    rfl

theorem step : Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → Gen.ArchimedeanSignatureMatching → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X), ThmS bkP → ∀ (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → Step bkP i s := by
  intro hC hPT _ hT hLF hLD hLE hGF hGE _ h4 D N X bkP hS i s hG hl M R n H S d A₀ L z P w e hn he hM h3 hAdm hLH hz hL hSt hFit
  classical
  have hM1 : 1 ≤ M := by omega
  have hMν : nu X i + 1 ≤ M := by omega
  have hp : (X.l i).Prime := (X.lPrime i).out
  by_cases hNF : NF bkP i s M d P (2 * (e + 1) * w + 2)
  · obtain ⟨P', hE, hSt', -⟩ := GlobalTheory.T.exists_newPlace_frobeniusConjugate_modOpenNormalSubgroup hC D N X i s M R n d A₀ L z P hM1 hz hL hSt hn H S hAdm hLH L 1 hL.1.1 hL.1.2.1
      le_rfl L.one_mem (fun _ _ => map_one _) (fun b _ => (hSt.2.1 b).1 _ (over_refl _) _ (N.plOm.2 _))
    exact ⟨P', hE, hSt', (GlobalTheory.T.chebotarevInductionGrowBound_of_presentation hT D N X bkP hS i s hG hl M R n d A₀ L z P P' _ hn hM h3 hz hL hSt' hE).1 hNF⟩
  unfold NF at hNF
  push Not at hNF
  obtain ⟨Q, hQ, a, Φ, hΦ, F₀, hF₀, hc₀⟩ := hNF
  rcases hFit Q hQ a Φ hΦ with rfl | ⟨b, b', hb⟩
  · exfalso
    have hK : Kills i (X.O0 i ⧸ idl i) := fun x hx => Ideal.Quotient.eq_zero_iff_mem.2 hx
    obtain ⟨φ, hφ, -⟩ := GlobalTheory.T.exists_lambda_algebra_hom_evaluation D N X i M (Fin R ⊕ Fin n) _ (fun _ => (0 : X.O0 i ⧸ idl i)) hl hMν hK
      (fun _ => zero_pow (pow_ne_zero _ hp.ne_zero))
    have e1 := hφ F₀
    rw [hF₀, Matrix.det_isEmpty, map_one, GlobalTheory.T.aeval_eq_zero_of_low_coeff_of_nilpotent_multiple _ _ _ (0 : X.O0 i ⧸ idl i) 1 (fun _ => 0) F₀ (pow_one _) (fun _ => dvd_rfl)
      (fun u hu => hK _ (hc₀ u (by omega)))] at e1
    have e2 : (1 : X.O0 i) ∈ Ideal.span {(X.l i : X.O0 i) ^ nu X i} * IsLocalRing.maximalIdeal (X.O0 i) :=
      Ideal.Quotient.eq_zero_iff_mem.1 e1
    exact (IsLocalRing.maximalIdeal.isMaximal (X.O0 i)).ne_top ((Ideal.eq_top_iff_one _).2 (Ideal.mul_le_inf e2).2)
  obtain ⟨F₁, hF₁⟩ := GlobalTheory.TwSys.toLam_surjective X i M (Fin R ⊕ Fin n) (Φ.adjugate b b')
  let K : Set (Fin R ⊕ Fin n) := {q | ∃ j : Fin R, n ≤ j.val ∧ q = .inl j}
  have := X.twistBaseCoefficientRing_residueField_finite i
  obtain ⟨A, _, _, _, _, t, a₀, hK, htK, ht2, haK, hau, hdvd⟩ := GlobalTheory.T.exists_finiteLocalRing_poly_divides_var_pow (X.O0 i) ((X.l i : X.O0 i) ^ nu X i) e w _ K F₁ he (by
    obtain ⟨m, h1, h2, h3⟩ := hb F₁ hF₁
    exact ⟨m, h1, by rintro q ⟨j, hj, rfl⟩; exact h2 j hj, h3⟩)
  change Kills i A at hK
  letI : TopologicalSpace A := ⊥
  haveI : DiscreteTopology A := ⟨rfl⟩
  have ht0 : t ^ X.l i ^ (M - nu X i - 1) = 0 := pow_eq_zero_of_le (by omega) htK
  obtain ⟨φ, hφ, hκ⟩ := GlobalTheory.T.exists_lambda_algebra_hom_evaluation D N X i M _ A (fun q => a₀ q * t) hl hMν hK (fun q => by rw [mul_pow, ht0, mul_zero])
  obtain ⟨κ, hκφ, hκ⟩ := hκ (fun q => d (P q))
  have hker : ∀ g, (∀ q ∉ K, d (P q) g = 1) → κ g = 1 := fun g hg => hκ.eq_one fun q => by
    by_cases hq : q ∈ K
    · exact Or.inl (by rw [haK q hq, zero_mul])
    · exact Or.inr (hg q hq)
  obtain ⟨hSet, hAnti, hκz⟩ := GlobalTheory.T.setup_and_antiHom_of_kills D N X bkP i s hG M _ P _ A₀ Q hSt.1 hQ A κ hK (fun g hg => hker g fun q _ => hg q)
  obtain ⟨Z, hZ⟩ := GlobalTheory.T.exists_universalSelmerCocycle_baseChange D N X bkP i s M _ _ Q a Φ hΦ A φ κ hκφ hK
  have hdet : (Φ.map φ).det = 0 := by
    have e1 := (φ : _ →+* A).map_det Φ
    rw [RingHom.coe_coe, ← hF₀, hφ, GlobalTheory.T.aeval_eq_zero_of_low_coeff_of_nilpotent_multiple _ _ _ t _ _ F₀ htK (fun _ => dvd_mul_left _ _)
      (fun u hu => hK _ (hc₀ u hu))] at e1
    exact e1.symm
  have hadj : (Φ.map φ).adjugate b b' ∣ t ^ ((e + 1) * w) := by
    have e1 := congrFun (congrFun ((φ : _ →+* A).map_adjugate Φ) b) b'
    rw [← hφ, hF₁] at hdvd
    exact e1 ▸ hdvd
  generalize Φ.map φ = Ψ at hZ hdet hadj
  obtain ⟨ρ, hρ⟩ := exists_isDual i s
  have hl0 : X.l i ^ (nu X i + 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
  obtain ⟨Y, _, _, _, β, hβ, hcog⟩ := GlobalTheory.T.perfect_pairing_finite_module_rows_criterion A (X.l i ^ (nu X i + 1)) hl0 (by
    have e1 := hK _ (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (GlobalTheory.ResSel.SmallSub.l_mem X i))
    rw [map_mul, map_pow, map_natCast] at e1
    rw [Nat.cast_pow, pow_succ, e1])
  letI : TopologicalSpace Y := ⊥
  haveI : DiscreteTopology Y := ⟨rfl⟩
  have hNI := GlobalTheory.T.noInvDual_of_setup_of_isDual_of_tame_inertia D N X bkP i s A κ Q ρ z hSet hρ hz
  obtain ⟨y, hy, hyc⟩ := GlobalTheory.T.exists_dual_selmer_class_not_killed D N X bkP i s A κ Q ρ hSet hK hρ hNI
    (GlobalTheory.T.selmer_order_formula_dual_selmer hPT hLF hLD hLE hGF hGE h4 D N X bkP i s A κ Q ρ hSet hK hρ hNI) Y β hβ a Ψ Z hZ ((X.l i : A) ^ nu X i * t ^ ((e + 1) * w)) t
    (Ψ.adjugate b) b'
    (GlobalTheory.T.local_invariants_killed_alt hT D N X bkP i s hl M R n d A₀ L z P hM1 hz hL hSt A κ Q ρ t a₀ hQ hSet hK hρ hκ
      (fun q => hau _ (by rintro ⟨j, -, h⟩; cases h)) A)
    (by
      have e1 := congrFun (Matrix.adjugate_mul Ψ) b
      rw [hdet, zero_smul] at e1
      exact e1)
    (fun h0 => ht2 (by
      obtain ⟨c, hc⟩ := hadj
      rw [map_pow, map_natCast]
      have e1 : t ^ (2 * (e + 1) * w + 1) = t ^ ((e + 1) * w) * t * t ^ ((e + 1) * w) := by ring
      rw [e1]
      nth_rewrite 2 [hc]
      linear_combination c * h0))
  let L' : Subgroup (GE N) := L ⊓ ⨅ q : {q // q ∉ K}, (d (P q.1)).ker
  have hL' : Small2 i s M L' z := small_inf hL (fun q : {q // q ∉ K} => d (P q.1)) (fun q => (hSt.1.2.2 q.1).1)
    (fun q => (hSt.1.2.2 q.1).2.1)
  have hmem : ∀ g, g ∈ L' ↔ g ∈ L ∧ ∀ q ∉ K, d (P q) g = 1 := fun g => by
    simp [L', Subgroup.mem_iInf, MonoidHom.mem_ker, -Sum.forall]
  have hκL : ∀ g ∈ L', κ g = 1 := fun g hg => hker g ((hmem g).1 hg).2
  have hx₀ : matAct Ψ (fun c => Ψ.adjugate c b') = 0 := by
    funext u
    have e1 := congrFun (congrFun (Matrix.mul_adjugate Ψ) u) b'
    rw [hdet, zero_smul] at e1
    exact e1
  obtain ⟨h, hh, hB⟩ := GlobalTheory.T.exists_smallSubgroup_cocycleForm_ne_zero D N X bkP i s hl M L' z hMν hz hL' A κ Q ρ hSet hK hρ hAnti (hκz z hz) hκL a Ψ Z hZ _ b _ y
    hx₀ hadj hyc
  obtain ⟨x, hx, -⟩ := (hZ A).1 _ hx₀
  rw [← hx] at hB
  obtain ⟨U, hUo, hUn, hUL, hUm, hUB⟩ := GlobalTheory.T.exists_open_normal_subgroup_two_cocycles D N X i s hl M L' z hMν hL' A κ ρ hK hρ hκL x y h hh hB
  obtain ⟨P', hE, hSt', σ, γ, g, hNew, hdσ, hg⟩ := GlobalTheory.T.exists_newPlace_frobeniusConjugate_modOpenNormalSubgroup hC D N X i s M R n d A₀ L z P hM1 hz hL hSt hn H S hAdm hLH U h
    hUo hUn (hUL.trans inf_le_left) hh.1
    (fun c hc => ((hmem h).1 hh).2 _ (by rintro ⟨j, hj, h⟩; cases h; omega))
    (fun c hc => by
      have hI : ∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 (P (.inl c))), τ ∈ L' := fun τ hτ =>
        (hmem τ).2 ⟨(hSt.2.1 c).1 _ (over_refl _) _ (N.plOm.2 _) hτ, fun q hq =>
          (hSt.1.2.2 q).2.2.2.1 _ (fun h => hq ⟨c, hc, hSt.1.2.1 _ _ h⟩) _ (N.plOm.2 _) τ hτ⟩
      intro τ hτ
      have e1 := (GlobalTheory.T.inertiaVanishing_noInvariants_firstHalfPlaces hT D N X bkP i s hG hl M R n d A₀ L z P hMν hz hL hSt A κ _ hK hSet.2.2.2.2.1 (Or.inl rfl) A c).2
        hAnti (fun τ hτ => hκL τ (hI τ hτ)) x τ hτ
      have e2 := (GlobalTheory.T.inertiaVanishing_noInvariants_firstHalfPlaces hT D N X bkP i s hG hl M R n d A₀ L z P hMν hz hL hSt A κ⁻¹ ρ hK
        (fun g => (hSet.2.2.2.2.1 g).imp fun k hk => by rw [MonoidHom.inv_apply, inv_pow, hk, inv_one]) (Or.inr hρ) A c).2
        (fun g g' hg => by rw [MonoidHom.inv_apply, MonoidHom.inv_apply, hAnti g g' hg])
        (fun τ hτ => by rw [MonoidHom.inv_apply, hκL τ (hI τ hτ), inv_one]) y τ hτ
      exact hUm τ (hI τ hτ) e1.1 e1.2 e2.1 e2.2)
  refine ⟨P', hE, hSt', fun Q' hQ' a' Φ' hΦ' F' hF' => ?_⟩
  by_contra hcon
  push Not at hcon
  have hr : 0 < 2 * D.R.r := by have := hG.2.2.2.2.2.2; omega
  obtain ⟨B, _, _, j, π, x₁, x₂, hπj, hπk, h1, h2, h11, h22, h12⟩ := GlobalTheory.T.exists_ring_sq_zero_nilpotent_augmented (X.O0 i) A _ hr
  have hK' : Kills i B := fun u hu => by rw [← j.commutes, hK u hu, map_zero]
  let q₀ : Fin R ⊕ Fin (n + 1) := .inr (Fin.last n)
  let q₁ : Fin R ⊕ Fin n := .inl ⟨n, hn⟩
  let em : Fin R ⊕ Fin n → Fin R ⊕ Fin (n + 1) := Sum.map id Fin.castSucc
  let ξ : Fin R ⊕ Fin (n + 1) → B := Sum.elim (fun c => if c = ⟨n, hn⟩ then x₂ else j (a₀ (.inl c) * t))
    (Fin.lastCases x₁ fun c => j (a₀ (.inr c) * t))
  have hcases : ∀ q', q' = q₀ ∨ ∃ q, q' = em q := by
    rintro (c | c)
    · exact Or.inr ⟨.inl c, rfl⟩
    · exact Fin.lastCases (Or.inl rfl) (fun c => Or.inr ⟨.inr c, rfl⟩) c
  have hne : ∀ q, em q ≠ q₀ := by
    rintro (c | c) h
    · exact Sum.inl_ne_inr h
    · exact Fin.castSucc_ne_last c (Sum.inr.inj h)
  have hξ0 : ξ q₀ = x₁ := by simp [ξ, q₀]
  have hξ1 : ξ (em q₁) = x₂ := by simp [ξ, q₁, em]
  have hξ : ∀ q, q ≠ q₁ → ξ (em q) = j (a₀ q * t) := by
    rintro (c | c) h
    · have : c ≠ ⟨n, hn⟩ := fun h' => h (congrArg _ h')
      simp [ξ, em, this]
    · simp [ξ, em]
  have hξ3 : ∀ q, j t ∣ ξ q ∨ ξ q = x₁ ∨ ξ q = x₂ := fun q' => by
    rcases hcases q' with rfl | ⟨q, rfl⟩
    · exact Or.inr (Or.inl hξ0)
    · by_cases hq : q = q₁
      · exact Or.inr (Or.inr (hq ▸ hξ1))
      · exact Or.inl (by rw [hξ q hq, map_mul]; exact dvd_mul_left _ _)
  obtain ⟨φ', hφ', hκ'⟩ := GlobalTheory.T.exists_lambda_algebra_hom_evaluation D N X i M _ B ξ hl hMν hK' (fun q => by
    rcases hξ3 q with ⟨c, hc⟩ | hc | hc <;> rw [hc]
    · rw [mul_pow, ← map_pow, ht0, map_zero, zero_mul]
    · exact pow_eq_zero_of_le (m := 2) (by omega) (by rw [sq, h11])
    · exact pow_eq_zero_of_le (by omega) h22)
  obtain ⟨κ', hκφ', hκ'⟩ := hκ' (fun q => d (P' q))
  obtain ⟨Z', hZ'⟩ := GlobalTheory.T.exists_universalSelmerCocycle_baseChange D N X bkP i s M _ _ Q' a' Φ' hΦ' B φ' κ' hκφ' hK'
  have hP' : ∀ q, P' (em q) = P q := hE
  have hσL : σ ∈ L' := by
    have e1 := hL'.1.2.1.conj_mem _ (L'.mul_mem (hUL hg) hh) g⁻¹
    rwa [show g⁻¹ * (g * σ * g⁻¹ * h⁻¹ * h) * g⁻¹⁻¹ = σ by group] at e1
  have hunr : ∀ q', q' ≠ q₀ → ∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 (P' q₀)), d (P' q') τ = 1 := fun q' hq' τ hτ =>
    (hSt'.1.2.2 q').2.2.2.1 _ (fun h => hq' (hSt'.1.2.1 _ _ h)) _ (N.plOm.2 _) τ hτ
  have hDec : DecV N (P' q₀) ≤ L' := GlobalTheory.ChosenPrimes.dec_le (N.plOm.2 _) hL'.1.1
    (fun τ hτ => (hmem τ).2 ⟨hNew.2.2.2.1 hτ.1, fun q _ => hP' q ▸ hunr _ (hne q) τ hτ⟩) hNew.2.2.2.2.2.1 hσL
  refine det_ne_zero hPT hT hl h3 hL hNew (Q' := Q') hSet hK hρ hAnti (fun g hg => hκL g (hDec hg)) (fun v => ?_) hβ hcog hZ hy b'
    (hx ▸ hUB σ g hg) π (fun u => ⟨j u, hπj u⟩) hπk h1 h2 h11 h22 h12 (κ' := κ') (fun g => ?_) hK'
    (anti_of_ker (fun q => d (P' q)) (fun q => (hSt'.1.2.2 q).2.1) κ' fun g hg => hκ'.eq_one fun q => Or.inr (hg q))
    (fun τ hτ => hξ0 ▸ hκ'.single q₀ fun q hq => Or.inr (hunr q hq τ hτ)) ?_ hZ' ?_
  · rw [hQ', hQ]
    constructor
    · rintro ⟨q', hq'⟩
      rcases hcases q' with rfl | ⟨q, rfl⟩
      · exact Or.inr hq'
      · exact Or.inl ⟨q, hP' q ▸ hq'⟩
    · rintro (⟨q, hq⟩ | hq)
      · exact ⟨em q, (hP' q).symm ▸ hq⟩
      · exact ⟨q₀, hq⟩
  · have e1 := congrArg π (hκ' g)
    have e2 := hκ g
    have hπξ : ∀ q, π (ξ (em q)) = a₀ q * t := fun q => by
      by_cases hq : q = q₁
      · rw [hq, hξ1, h2, haK q₁ ⟨_, le_rfl, rfl⟩, zero_mul]
      · rw [hξ q hq, hπj]
    have e3 : π (∏ q, (1 + ξ q) ^ (Multiplicative.toAdd (d (P' q) g)).val) =
        ∏ q, (1 + a₀ q * t) ^ (Multiplicative.toAdd (d (P q) g)).val := by
      simp only [map_prod, map_pow, map_add, map_one]
      rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fin.prod_univ_castSucc]
      have e4 : π (ξ (.inr (Fin.last n))) = 0 := by rw [← h1, ← hξ0]
      rw [e4, add_zero, one_pow, mul_one]
      congr 1 <;> refine Finset.prod_congr rfl fun c _ => ?_
      · rw [← hπξ, ← hP']; rfl
      · rw [← hπξ, ← hP']; rfl
    rw [map_mul, map_one, e3] at e1
    exact (left_inv_eq_right_inv e2 (by rw [mul_comm]; exact e1))
  · have e1 := hκ'.single (g := σ) (em q₁) fun q' hq' => by
      rcases hcases q' with rfl | ⟨q, rfl⟩
      · exact Or.inr hdσ
      · by_cases hq : q ∈ K
        · exact Or.inl (by rw [hξ q (fun h => hq' (congrArg em h)), haK q hq, zero_mul, map_zero])
        · exact Or.inr (by rw [hP']; exact ((hmem σ).1 hσL).2 q hq)
    have e2 : d (P' (em q₁)) σ = Multiplicative.ofAdd 1 := by
      have := (hSt'.2.2 (Fin.last n)).2 ⟨n, hn⟩ σ hNew.2.2.2.2.2.1
      rwa [if_pos (by simp)] at this
    have : Fact (1 < X.l i ^ M) := ⟨Nat.one_lt_pow (by omega) hp.one_lt⟩
    rwa [hξ1, e2, toAdd_ofAdd, ZMod.val_one, pow_one] at e1
  · have e1 := (φ' : _ →+* B).map_det Φ'
    rw [RingHom.coe_coe, ← hF', hφ', GlobalTheory.T.aeval_eq_zero_low_coeff_three_nilpotents _ _ _ (j t) x₁ x₂ (2 * (e + 1) * w + 2) (2 * D.R.r) ξ F'
      (by rw [← map_pow, htK, map_zero]) h11 h22 hξ3 (fun u hu => hK' _ (hcon u hu))] at e1
    exact e1.symm

end GlobalTheory.NewPrime
