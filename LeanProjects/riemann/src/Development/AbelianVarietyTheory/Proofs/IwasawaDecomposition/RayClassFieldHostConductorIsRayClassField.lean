import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOfFinOrderFbar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotDvdDiscrIffRamificationIdx
import Development.AbelianVarietyTheory.Proofs.HeightProofs.LeOfFiniteSplitNotSplitBauer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassFieldSplitsInOfIsRayPrimeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSpanEqOneModOfSplitsInRayClassFieldStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMulGaloisConjEqPrimeImagQuadraticStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitsCompletelyOverIntermediateOfSplitsOverRatStatement

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.ParRayMax

@[reducible] def algQb (D : D7) (jE : D.host.E →+* Qb) : Algebra D.host.K Qb :=
  (jE.comp (algebraMap D.host.K D.host.E)).toAlgebra

def toIF (D : D7) (jE : D.host.E →+* Qb) (L : Fld) (h : KQbar D jE ≤ L) :
    @IntermediateField D.host.K Qb _ _ (algQb D jE) :=
  letI := algQb D jE
  { L.toSubfield with algebraMap_mem' := fun x => h ⟨x.1, x.2, rfl⟩ }

set_option synthInstance.maxHeartbeats 400000 in

theorem exists_embedded (hray : GlobalTheory.Published.RayClassFieldSt) (D : D7) (jE : D.host.E →+* Qb) :
    ∃ (M : Fld) (h : KQbar D jE ≤ M) (hf : FiniteDimensional ℚ M),
      letI := GlobalTheory.ParRay.algK D jE h
      haveI := GlobalTheory.ParRay.nfOf hf
      GlobalTheory.Mem.Fld.IsRayField D.host.K M (GlobalTheory.Mem.RaySplit.condIdeal D.host) := by
  obtain ⟨M, _, _, _, hM⟩ := GlobalTheory.Published.rayClassFieldSt_iff_isRayField.1 hray D.host.K _
    (GlobalTheory.Mem.RaySplit.condIdeal_ne_bot D.host)
  letI := algQb D jE
  let ψ : M →ₐ[D.host.K] Qb := IsAlgClosed.lift
  let M1 : Fld := (ψ : M →+* Qb).toRatAlgHom.fieldRange
  have hψ : ∀ x : D.host.K, ψ (algebraMap D.host.K M x) = jE x := fun x => ψ.commutes x
  have hK : KQbar D jE ≤ M1 := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨algebraMap D.host.K M ⟨x, hx⟩, hψ ⟨x, hx⟩⟩
  let e₀ : M ≃ₐ[ℚ] M1 := AlgEquiv.ofInjectiveField (ψ : M →+* Qb).toRatAlgHom
  have hf : FiniteDimensional ℚ M1 := e₀.toLinearEquiv.finiteDimensional
  refine ⟨M1, hK, hf, ?_⟩
  letI := GlobalTheory.ParRay.algK D jE hK
  haveI := GlobalTheory.ParRay.nfOf hf
  exact hM.of_algEquiv (AlgEquiv.ofRingEquiv (f := e₀.toRingEquiv) fun x => Subtype.ext (hψ x))

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem le_of_rayAdm (D : D7) (jE : D.host.E →+* Qb) (M : Fld) (h : KQbar D jE ≤ M) (hf : FiniteDimensional ℚ M)
    (hM : letI := GlobalTheory.ParRay.algK D jE h; haveI := GlobalTheory.ParRay.nfOf hf;
      GlobalTheory.Mem.Fld.IsRayField D.host.K M (GlobalTheory.Mem.RaySplit.condIdeal D.host))
    (L : Fld) (hL : RayAdm (KQbar D jE) (D.host.QS * D.host.q * D.host.d) L) : L ≤ M := by
  have h2K := GlobalTheory.Mem.RaySplit.finrank_K D.host
  have h3K := GlobalTheory.Mem.RaySplit.isEmpty_real D.host
  letI := GlobalTheory.ParRay.algK D jE h
  haveI := GlobalTheory.ParRay.nfOf hf
  letI := algQb D jE
  obtain ⟨hKL, hfL, hspl⟩ := hL
  let mkE : ∀ (X : Fld) (hX : KQbar D jE ≤ X), X ≃+* toIF D jE X hX := fun X hX =>
    { toFun := fun x => ⟨x.1, x.2⟩, invFun := fun x => ⟨x.1, x.2⟩, left_inv := fun _ => rfl,
      right_inv := fun _ => rfl, map_mul' := fun _ _ => rfl, map_add' := fun _ _ => rfl }
  let R := toIF D jE M h
  let L' := toIF D jE L hKL
  let eR : M ≃ₐ[D.host.K] R := AlgEquiv.ofRingEquiv (f := mkE M h) fun x => rfl
  let eL : L ≃+* L' := mkE L hKL
  haveI : NumberField R := { to_finiteDimensional := (eR.toRingEquiv.toRatAlgEquiv).toLinearEquiv.finiteDimensional }
  haveI : NumberField L' := { to_finiteDimensional := eL.toRatAlgEquiv.toLinearEquiv.finiteDimensional }
  have hR : GlobalTheory.Mem.Fld.IsRayField D.host.K R (GlobalTheory.Mem.RaySplit.condIdeal D.host) := hM.of_algEquiv eR
  have hab : IsAbelianGalois D.host.K R := hR.1
  have key : ∀ 𝔭 : HeightOneSpectrum (𝓞 D.host.K), ¬ 𝔭.asIdeal ∣ GlobalTheory.Mem.RaySplit.condIdeal D.host →
      (𝔭.asIdeal.primesOver (𝓞 R)).ncard = Module.finrank D.host.K R →
        ∃ π : 𝓞 D.host.K, 𝔭.asIdeal = Ideal.span {π} ∧ π - 1 ∈ GlobalTheory.Mem.RaySplit.condIdeal D.host :=
    fun 𝔭 h1 h2 => GlobalTheory.T.exists_span_eq_one_mod_of_splits_in_rayClassField D.host.K R _ hR 𝔭 h1 h2
  have hle : L' ≤ R := by
    refine @GlobalTheory.Bauer.le_of_finite_split_not_split D.host.K Qb _ _ _ _ R L' _ _ hab.toIsGalois
      ((Ideal.finite_factors (GlobalTheory.Mem.RaySplit.condIdeal_ne_bot D.host)).subset ?_)
    rintro 𝔭 ⟨hpr, hRs, hLs⟩
    by_contra hnd
    apply hLs
    rw [GlobalTheory.Bauer.ncard_eq_ncard_primesOver] at hRs ⊢
    obtain ⟨π, hπ, hπ1⟩ := key 𝔭 hnd hRs
    obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_mul_galois_conj_eq_prime_imagQuadratic D.host.K h3K h2K
      (jE.comp (algebraMap D.host.K D.host.E)) π (Ideal.absNorm 𝔭.asIdeal) (congrArg Ideal.absNorm hπ).symm
    have hray : IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) (Ideal.absNorm 𝔭.asIdeal) := by
      refine ⟨hpr, jE ((π : D.host.K) : D.host.E), ⟨_, (π : D.host.K).2, rfl⟩, ?_, ?_, σ, hσ⟩
      · exact (RingOfIntegers.isIntegral_coe π).map (jE.comp (algebraMap D.host.K D.host.E)).toIntAlgHom
      · obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hπ1
        have hm0 : ((D.host.QS * D.host.q * D.host.d : ℕ) : Qb) ≠ 0 := by
          exact_mod_cast GlobalTheory.Mem.RaySplit.cond_ne_zero D.host
        have e : (jE ((π : D.host.K) : D.host.E) - 1) / ((D.host.QS * D.host.q * D.host.d : ℕ) : Qb) =
            (jE.comp (algebraMap D.host.K D.host.E)) (y : D.host.K) := by
          rw [div_eq_iff hm0]
          have e1 := congrArg ((jE.comp (algebraMap D.host.K D.host.E)).comp (algebraMap (𝓞 D.host.K) D.host.K)) hy
          simp only [map_mul, map_sub, map_one, map_natCast] at e1
          exact e1.symm
        rw [e]
        exact (RingOfIntegers.isIntegral_coe y).map (jE.comp (algebraMap D.host.K D.host.E)).toIntAlgHom
    have hsp := hspl _ hray
    have h1 : ((Ideal.span {((Ideal.absNorm 𝔭.asIdeal : ℕ) : ℤ)}).primesOver (𝓞 L')).ncard = Module.finrank ℚ L' := by
      rw [← GlobalTheory.HostSplit.ncard_placesOver L' hpr, ← finrank_eq_of_equiv eL]
      exact (ncard_places_of_equiv eL _).symm.trans hsp
    exact GlobalTheory.T.splits_completely_over_intermediate_of_splits_over_rat D.host.K L' _ hpr h1 𝔭 (Ideal.absNorm_mem 𝔭.asIdeal)
  exact fun x hx => hle hx

theorem rayField_isRay : GlobalTheory.Published.RayClassFieldSt → ∀ (D : D7) (jE : D.host.E →+* Qb),
    ∃ (h : KQbar D jE ≤ MrayC D jE) (hf : FiniteDimensional ℚ (MrayC D jE)),
      letI := GlobalTheory.ParRay.algK D jE h
      haveI := GlobalTheory.ParRay.nfOf hf
      IsGalois D.host.K (MrayC D jE) ∧ (∀ σ τ : MrayC D jE ≃ₐ[D.host.K] MrayC D jE, σ * τ = τ * σ) ∧
      (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr (MrayC D jE) → p ∣ D.host.QS * D.host.q * D.host.d) ∧
      ∀ p, IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) p → SplitsIn (MrayC D jE) p := by
  intro hray D jE
  obtain ⟨M, h, hf, hM⟩ := exists_embedded hray D jE
  have hsplit := GlobalTheory.T.rayClassField_splitsIn_of_isRayPrime D jE M h hf hM
  have heq : MrayC D jE = M :=
    le_antisymm (iSup₂_le fun L hL => le_of_rayAdm D jE M h hf hM L hL) (le_rayField ⟨h, hf, hsplit⟩)
  generalize MrayC D jE = X at heq ⊢
  subst heq
  refine ⟨h, hf, ?_⟩
  letI := GlobalTheory.ParRay.algK D jE h
  haveI := GlobalTheory.ParRay.nfOf hf
  exact ⟨GlobalTheory.Mem.RaySplit.isGalois_of_ray hM, GlobalTheory.Mem.RaySplit.comm_of_ray hM, GlobalTheory.Mem.RaySplit.unr_of_ray hM, hsplit⟩

end GlobalTheory.ParRayMax

end
