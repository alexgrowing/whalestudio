import Mathlib
import Development.AutomorphicArithmetic.PrimeDiscriminants.RamDiscr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetHypOfIsTripleOfGalHodge
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSetup
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardPadicAlgClPadicComplexEqComplex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimeDvdAbsNormHalfDifferent
import Formalism.LocalToGlobal.NormalizedHeckeFactors.WittCoreInclusionMulVecMemLatticeCompletionAtPla
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharpolySmulOfProd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin IsAlgPos)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TwInputs.SetupPin

variable {D : D7}

theorem goodSetup_badPlaces_conj (F : TwFrameC D) {low : Finset ℕ} (T : TwistFrameLowIndexCompatibility D F low) :
    ∀ i, ∀ P ∈ D.ntw.S0 i, ∀ P', Formalism.BasicNotions.IsConjPl D.host P P' → P' ∈ D.ntw.S0 i := by
  intro i P hP P' hc
  have hP' : P ∈ (D.ntw.S0 i : Set (HeightOneSpectrum (𝓞 D.host.E))) := hP
  rw [T.ringSpec_excludedPlaces_eq i] at hP'
  show P' ∈ (D.ntw.S0 i : Set (HeightOneSpectrum (𝓞 D.host.E)))
  rw [T.ringSpec_excludedPlaces_eq i]
  rcases hP' with (((h | h) | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Formalism.L2.placesOver_conj D _ h hc))))
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.1 h
    exact Or.inl (Or.inl (Or.inl (Or.inr (Set.mem_iUnion.2 ⟨k, Formalism.L2.placesOver_conj D _ hk hc⟩))))
  · exact Or.inl (Or.inl (Or.inr (Formalism.L2.placesOver_conj D _ h hc)))
  · exact Or.inl (Or.inr (Formalism.L2.placesOver_conj D _ h hc))
  · exact Or.inr (T.concreteTwistFrame_extraExcludedPlaces_conj i P P' h hc)

theorem goodSetup_placesOverTwo_subset (F : TwFrameC D) {low : Finset ℕ} (T : TwistFrameLowIndexCompatibility D F low) (h2 : 2 ∈ low) :
    ∀ i, placesOver D.host.E 2 ⊆ ↑(D.ntw.S0 i) := by
  intro i P hP
  show P ∈ (D.ntw.S0 i : Set (HeightOneSpectrum (𝓞 D.host.E)))
  rw [T.ringSpec_excludedPlaces_eq i]
  exact Or.inr (T.concreteTwistFrame_extraExcluded_over_smallPrimes i 2 h2 hP)

theorem q_dvd_discr (D : D7) : D.host.q ∣ (NumberField.discr D.host.E).natAbs :=
  Int.natCast_dvd.1 D.host.q_dvd_discr

theorem goodSetup_count_eq_zero_off_badPlaces (F : TwFrameC D) {low : Finset ℕ} (T : TwistFrameLowIndexCompatibility D F low) (h2 : 2 ∈ low)
    (hd : (NumberField.discr D.host.E).natAbs.primeFactors ⊆ low) (hc : (Ideal.absNorm D.host.ccK).primeFactors ⊆ low) :
    ∀ i P, P ∉ D.ntw.S0 i → FractionalIdeal.count D.host.E P D.host.AA = 0 := by
  intro i P hP
  by_contra hA
  have hb : ((GlobalTheory.HalfCompare.badInt D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    by_contra hb
    exact hA (GlobalTheory.HalfCompare.primeToAA_of_not_mem hb)
  obtain ⟨p, hp, hpP⟩ := GlobalTheory.HalfCompare.exists_prime_under P
  have hdiv : p ∣ GlobalTheory.HalfCompare.badInt D := (hpP _).1 hb
  have hlow : p ∈ low := by
    unfold GlobalTheory.HalfCompare.badInt at hdiv
    rcases hp.dvd_mul.1 hdiv with h | h
    · exact hd (Nat.mem_primeFactors.2 ⟨hp,
        Int.natCast_dvd.1 ((D.host.dvd_discr_iff_dvd_condN hp).2 (h.mul_right D.host.d)),
        Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero _)⟩)
    · exact hc (Nat.mem_primeFactors.2 ⟨hp, h, by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact D.host.ccK_ne_bot⟩)
  apply hP
  show P ∈ (D.ntw.S0 i : Set (HeightOneSpectrum (𝓞 D.host.E)))
  rw [T.ringSpec_excludedPlaces_eq i]
  exact Or.inr (T.concreteTwistFrame_extraExcluded_over_smallPrimes i p hlow ((hpP p).2 dvd_rfl))

theorem mk_fractionRing_le {R : Type} [CommRing R] [IsDomain R] (h : Cardinal.mk R ≤ Cardinal.continuum) :
    Cardinal.mk (FractionRing R) ≤ Cardinal.continuum := by
  have hs : Function.Surjective
      (fun p : R × nonZeroDivisors R => IsLocalization.mk' (FractionRing R) p.1 p.2) := fun z => by
    obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) z
    exact ⟨(x, y), hxy⟩
  refine (Cardinal.mk_le_of_surjective hs).trans ?_
  rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
  calc Cardinal.mk R * Cardinal.mk (nonZeroDivisors R) ≤ Cardinal.continuum * Cardinal.continuum :=
        mul_le_mul' h ((Cardinal.mk_subtype_le _).trans h)
    _ = Cardinal.continuum := Cardinal.continuum_mul_self

theorem mk_frac_Ok (F : TwFrameC D) : ∀ i k, Cardinal.mk (FractionRing (D.ntw.Ok i k)) ≤ Cardinal.continuum := by
  intro i k
  haveI := D.ntw.lPrime i
  apply mk_fractionRing_le
  have hinj : Function.Injective (fun x : D.ntw.Ok i k => ((F.eOk i k x : _) : ℂ_[D.ntw.l i])) :=
    Subtype.val_injective.comp (F.eOk i k).injective
  refine (Cardinal.mk_le_of_injective hinj).trans ?_
  rw [(GlobalTheory.PadicCard.card_padicAlgCl_padicComplex (D.ntw.l i)).2, Cardinal.mk_complex]

theorem continuous_comp_of_isOpen_ker {Γ B Y : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group B]
    [TopologicalSpace Y] (φ : Γ →* B) (f : B → Y) (h : IsOpen (φ.ker : Set Γ)) : Continuous (f ∘ φ) := by
  have hloc : IsLocallyConstant (f ∘ φ) := by
    intro s
    rw [isOpen_iff_forall_mem_open]
    intro g hg
    refine ⟨(fun g' => g⁻¹ * g') ⁻¹' (φ.ker : Set Γ), fun g' hg' => ?_,
      h.preimage (continuous_const.mul continuous_id), ?_⟩
    · have h1 : φ (g⁻¹ * g') = 1 := hg'
      rw [map_mul, map_inv, inv_mul_eq_one] at h1
      show f (φ g') ∈ s
      rw [← h1]
      exact hg
    · show φ (g⁻¹ * g) = 1
      rw [inv_mul_cancel, map_one]
  exact hloc.continuous

theorem delAt_alg (C : CharFrame D) (l : ℕ) : IsAlgPos (C.delAt l) 0 := by
  unfold CharFrame.delAt
  split_ifs
  · obtain ⟨n, h0, h⟩ := C.isDel'.fin
    exact GlobalTheory.HeckeGal.isAlgPos_zero_of_orderDvd h0 h
  · obtain ⟨n, h0, h⟩ := C.isDel.fin
    exact GlobalTheory.HeckeGal.isAlgPos_zero_of_orderDvd h0 h

end GlobalTheory.TwInputs.SetupPin

namespace GlobalTheory.TwInputs.SetupPin

variable {D : D7}

theorem exists_art_gal (hA : GlobalTheory.Published.GlobalArtinReciprocity) (cf : CharFrame D) (hR : DeltaRead D cf) :
    ∃ art : Ideles D.host.E →* Gab D.host.E D.nd.Om, IsGlobalArtin art ∧ ∀ i b,
      ∃ (κ : FractionRing (D.ntw.O0 i) →+* Qbar (D.ntw.l i)) (ι : Qbar (D.ntw.l i) ≃+* ℂ),
        (∀ x, ι (κ ((if b then D.ntw.emb0 i else D.ntw.emb0b i) x)) = embLL0 D x) ∧
        GlobalTheory.GalChar.IsGal art κ ι (cf.delAt (D.ntw.l i)) (fun _ => 0) (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)) := by
  obtain ⟨art, hart⟩ := hA D.host.E D.nd.Om
  refine ⟨art, hart, fun i b => ?_⟩
  haveI := D.ntw.lPrime i
  obtain ⟨ρ⟩ := GlobalTheory.Triple.Reading.nonempty (X := D.ntw) i b
  have hker : IsOpen ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker : Set (G D.host.E D.nd.Om)) := by
    have e : ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker : Set (G D.host.E D.nd.Om)) = (D.ntw.delta i).ker := by
      ext g
      cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
    rw [e]
    exact D.ntw.delta_open i
  have hχ : IsAlgPos (cf.delAt (D.ntw.l i)) 0 := delAt_alg cf _
  obtain ⟨r0, hr0, hL⟩ := hart.exists_isLAdicOf ρ.ι hχ
  have hc : Continuous (GlobalTheory.GalChar.inQ ρ.κ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i))) :=
    continuous_comp_of_isOpen_ker (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i))
      (Units.map (GlobalTheory.GalChar.toQ ρ.κ).toMonoidHom) hker
  have hz : ∀ v, ‖(((cf.delAt (D.ntw.l i)).val v : ℂˣ) : ℂ)‖ = 1 := fun v => cf.delAt_unitary _ _
  have heq : GlobalTheory.GalChar.inQ ρ.κ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)) = r0 := by
    refine GlobalTheory.GalChar.eq_of_frob hart hc hr0 ?_
    filter_upwards [GlobalTheory.GalChar.away_ae (E := D.host.E) (D.ntw.l i) (Fact.out : (D.ntw.l i).Prime).ne_zero,
      GlobalTheory.GalChar.unr_ae (cf.delAt (D.ntw.l i))] with v hv hu A hA σ hσ
    obtain ⟨x, hx, hd⟩ := hR i v hv hu A σ hA hσ
    have hx' : D.what₂.embLL (x : D.what₂.LL) = (((cf.delAt (D.ntw.l i)).val v : ℂˣ) : ℂ)⁻¹ := by
      rw [hx, Units.val_inv_eq_inv_val]
    apply Units.ext
    rw [hL.frob_unr hart (Or.inr rfl) hu hA hσ, GlobalTheory.GalChar.inQ_val]
    cases b
    · have hstar : (x : D.what₂.LL) = star ((x⁻¹ : D.LL0) : D.what₂.LL) := by
        apply D.what₂.embLL.injective
        rw [D.starLL_cx, IntermediateField.coe_inv, map_inv₀, hx', inv_inv, ← Complex.inv_eq_conj (hz v)]
      have h1 : ρ.ι (ρ.κ (D.ntw.emb0 i x)) = (((cf.delAt (D.ntw.l i)).val v : ℂˣ) : ℂ) := by
        rw [← D.ntw.restX_coefficientEmbedding_conj i x⁻¹ x hstar]
        have := ρ.read x⁻¹
        simp only [GlobalTheory.Triple.embSide, Bool.false_eq_true, if_false] at this
        rw [this]
        show D.what₂.embLL ((x⁻¹ : D.LL0) : D.what₂.LL) = _
        rw [IntermediateField.coe_inv, map_inv₀, hx', inv_inv]
      show GlobalTheory.GalChar.toQ ρ.κ (((D.ntw.delta i)⁻¹ σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) = _
      rw [MonoidHom.inv_apply, map_units_inv]
      congr 1
      show ρ.κ (algebraMap _ _ _) = _
      rw [hd, ← h1, ρ.ι.symm_apply_apply]
    · have h1 : ρ.ι (ρ.κ (D.ntw.emb0 i x)) = (((cf.delAt (D.ntw.l i)).val v : ℂˣ) : ℂ)⁻¹ := by
        have := ρ.read x
        simp only [GlobalTheory.Triple.embSide, if_true] at this
        rw [this]
        exact hx'
      show ρ.κ (algebraMap _ _ ((D.ntw.delta i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)) = _
      rw [hd, ← map_inv₀, ← h1, ρ.ι.symm_apply_apply]
  refine ⟨ρ.κ, ρ.ι, fun x => ?_, hχ, ?_, ?_⟩
  · have := ρ.read x
    cases b <;> simpa [GlobalTheory.Triple.embSide] using this
  · exact continuous_comp_of_isOpen_ker (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)) Units.val hker
  · rw [heq]
    exact hL

end GlobalTheory.TwInputs.SetupPin

namespace GlobalTheory.TwInputs.SetupPin

end GlobalTheory.TwInputs.SetupPin
