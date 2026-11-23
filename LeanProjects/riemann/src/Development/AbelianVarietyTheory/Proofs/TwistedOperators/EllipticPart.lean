import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsInertPlOfInertOff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePreimageOfNhdsZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyUnitaryTorusOrbitalClassTrivialLocalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalStableOrbitalIntegralsWellDefinedStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCharpolyKernelEqStableOrbitalIntegralsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTorusClassOfIrreducibleCharpolyUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryTorusCompactQuotientFiniteVolumeStatement
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrEllSum

open Classical in

theorem finsum_subtype_ite {G : Type} (p : G → Prop) {u : G → ℂ} (hu : (Function.support u).Finite) :
    ∑ᶠ δ : {δ // p δ}, u δ.1 = ∑ δ ∈ hu.toFinset, if p δ then u δ else 0 := by
  rw [finsum_subtype_eq_finsum_cond (f := u) (p := p), finsum_eq_sum_of_support_subset (s := hu.toFinset)]
  · exact Finset.sum_congr rfl fun δ _ => finsum_eq_if
  · intro δ hδ
    simp only [Finite.coe_toFinset]
    intro h0
    exact hδ (by simp [h0])

theorem finsum_group {G Q I : Type} (c : G → Q) (ι : I → Q) (hι : Function.Injective ι) (p : G → Prop)
    (hp : ∀ g, p g ↔ ∃ i, c g = ι i) {u : G → ℂ} (hu : (Function.support u).Finite) (S : Finset I)
    (hS : ∀ g i, u g ≠ 0 → c g = ι i → i ∈ S) :
    ∑ᶠ δ : {δ // p δ}, u δ.1 = ∑ i ∈ S, ∑ᶠ δ : {δ // c δ = ι i}, u δ.1 := by
  classical
  rw [finsum_subtype_ite p hu, Finset.sum_congr rfl fun i _ => finsum_subtype_ite (fun δ => c δ = ι i) hu,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun g hg => ?_
  have hg' : u g ≠ 0 := by simpa using hg
  by_cases h : p g
  · obtain ⟨i, hi⟩ := (hp g).1 h
    rw [if_pos h, Finset.sum_eq_single_of_mem i (hS g i hg' hi) fun j _ hj =>
      if_neg fun e => hj (hι (e.symm.trans hi)), if_pos hi]
  · rw [if_neg h]
    exact (Finset.sum_eq_zero fun i _ => if_neg fun e => h ((hp g).2 ⟨i, e⟩)).symm

theorem elliptic_expansion {E : Type} [Field E] [NumberField E] {F : Subfield E} [NumberField F] {σ : E →ₐ[F] E}
    (hcm : IsCMExt F E σ) (hun : Algebra.Unramified (𝓞 F) (𝓞 E)) {r : ℕ} {J : Matrix (Fin r) (Fin r) E}
    (hJ : IsHermND σ J) (L : Submodule (𝓞 E) (Fin r → E)) [Submodule.IsLattice E L]
    {μa : ∀ w, Measure (GArch σ J w)} {μf : ∀ v, Measure (GLoc σ J v)} {μ : Measure (GAd σ J)}
    (hμ : IsRestrictedProd σ J L μa μf μ) {fa : ∀ w, GArch σ J w → ℂ} {ff : ∀ v, GLoc σ J v → ℂ}
    (ha : ∀ w, fa w ∈ CcArch σ J w) (hf : IsFinFamily σ J L ff)
    (dta : ∀ (P : PPol σ r) (w : InfinitePlace F), Measure (Tor P w.Completion))
    (dtf : ∀ (P : PPol σ r) (v : HeightOneSpectrum (𝓞 F)), Measure (Tor P (Fv F v)))
    (dt : ∀ P : PPol σ r, Measure (Tor P (AF F))) (ht : ∀ P, IsTorusMeas P (dta P) (dtf P) (dt P))
    (K : GAd σ J → ℂ)
    (hK : K = fun x => ∑ᶠ δ : {δ : GRat σ J // Irreducible δ.1.1.charpoly}, tensor σ J fa ff (x⁻¹ * ratEmb σ J δ.1 * x))
    (t : PPol σ r → ℂ)
    (hterm : t = fun P => ((torVol P (dt P)).toReal : ℂ) * (∏ᶠ v, Phi (J := J) (μf v) (dtf P v) (ff v)) *
      ∏ w, Phi (J := J) (μa w) (dta P w) (fa w)) :
    (∀ P, (torVol P (dt P) ≠ ⊤ ∧ (∀ v, PhiOK (J := J) (μf v) (dtf P v) (ff v)) ∧
      ∀ᶠ v in cofinite, Phi (J := J) (μf v) (dtf P v) (ff v) = 1) ∧ ∀ w, PhiOK (J := J) (μa w) (dta P w) (fa w)) ∧
    (Function.support t).Finite ∧ Integrable (descend (ratPts σ J) K) (quotMeasure (ratPts σ J) μ) ∧
      ∫ q, descend (ratPts σ J) K q ∂quotMeasure (ratPts σ J) μ = ∑ᶠ P, t P := by
  have ha' : ∀ w, Continuous (fa w) ∧ HasCompactSupport (fa w) := fun w =>
    ⟨continuous_of_mem_ccSmooth (continuous_archCoord σ J w) (ha w), (ha w).1⟩
  have hc := (continuous_of_mem_ccAd (tensor_mem_ccAd ha hf)).2
  obtain ⟨hfin, hfinx⟩ := GlobalTheory.TrFinite.finite_charpoly_and_ratPts F E σ hcm r J _ hc
  have hpol := fun P => GlobalTheory.T.integral_charpolyKernel_eq_stableOrbitalIntegrals E F σ hcm hun r P J hJ L μa μf μ hμ fa ff ha' hf (dta P) (dtf P) (dt P) (ht P)
  have hinj : Function.Injective (Subtype.val : PPol σ r → E[X]) := Subtype.val_injective
  set S : Finset (PPol σ r) := (hfin.preimage (f := fun P : PPol σ r => P.1) hinj.injOn).toFinset with hSdef
  have hS : ∀ (x : GAd σ J) (γ : GRat σ J) (P : PPol σ r), tensor σ J fa ff (x⁻¹ * ratEmb σ J γ * x) ≠ 0 →
      γ.1.1.charpoly = P.1 → P ∈ S := fun x γ P h e =>
    (Finite.mem_toFinset _).2 ⟨γ, e, x, subset_tsupport _ h⟩
  have hsum : descend (ratPts σ J) K = fun q => ∑ P ∈ S, descend (ratPts σ J) (polKernel P J (tensor σ J fa ff)) q := by
    funext q
    rw [hK]
    refine finsum_group (fun γ : GRat σ J => γ.1.1.charpoly) _ hinj _ (fun γ => ⟨fun h => ?_, ?_⟩)
      (u := fun γ => tensor σ J fa ff ((Quotient.out q)⁻¹ * ratEmb σ J γ * Quotient.out q))
      ((hfinx (Quotient.out q)).subset fun γ h => subset_tsupport _ h) S (hS _)
    · obtain ⟨P, hP, -⟩ := (GlobalTheory.T.exists_torusClass_of_irreducible_charpoly_unitary F E σ hcm r J hJ).2 γ h
      exact ⟨P, hP⟩
    · rintro ⟨P, hP⟩
      rw [hP]
      exact P.2.2.1
  have hsupp : Function.support t ⊆ S := fun P hP => by
    by_contra hn
    refine hP ?_
    rw [hterm]
    refine (hpol P).2.symm.trans (integral_eq_zero_of_ae (.of_forall fun q => ?_))
    refine finsum_eq_zero_of_forall_eq_zero fun δ => ?_
    by_contra h
    exact hn (hS _ δ.1 P h δ.2)
  refine ⟨fun P => ⟨⟨(GlobalTheory.T.unitaryTorus_compact_quotient_finite_volume F E σ hcm r P).2 _ (ht P).haar, fun v => ?_, ?_⟩, fun w => ?_⟩,
    S.finite_toSet.subset hsupp, ?_, ?_⟩
  · exact (GlobalTheory.T.local_stable_orbital_integrals_well_defined F E σ hcm r r P J hJ).1 v _ _ _ (hμ.haar_loc v) ((ht P).haar_loc v) (hf.1 v).1.continuous
      (hf.1 v).2
  · have := isLattice_stdLattice (E := Fld P) (n := 1)
    filter_upwards [GlobalTheory.T.eventually_unitaryTorus_orbitalClass_trivial_local F E σ hcm r P J hJ L, hf.2, hμ.eventually_eq_one,
      IsRestrictedProd.eventually_eq_one (ht P)] with v h1 h2 h3 h4
    have h5 := h1.2.2.2 (μf v) (dtf P v) (hμ.haar_loc v) ((ht P).haar_loc v) h3 h4
    rw [h2, Phi, finsum_eq_single _ ⟨1, h1.1⟩ fun q hq => (h5 q).2 fun e => hq (Subtype.ext e)]
    exact (h5 _).1 rfl
  · exact (GlobalTheory.T.local_stable_orbital_integrals_well_defined F E σ hcm r r P J hJ).2 w _ _ _ (hμ.haar_arch w) ((ht P).haar_arch w) (ha' w).1 (ha' w).2
  · rw [hsum]
    exact integrable_finsetSum _ fun P _ => (hpol P).1
  · rw [hsum, integral_finsetSum _ fun P _ => (hpol P).1, finsum_eq_sum_of_support_subset _ hsupp, hterm]
    exact Finset.sum_congr rfl fun P _ => (hpol P).2

theorem ellipticPart : GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.EllipticPart := by
  intro D V lam S M T U μa μf μ fa ff h dta dtf dt ht
  obtain ⟨-, -, -, -, hμ, ha, hf⟩ := h
  exact elliptic_expansion (isCMExt_host D) (GlobalTheory.InertOfConj.unram D) (isHermND_gram V) (frameLat V) hμ ha.mem hf.isFinFamily
    dta dtf dt ht _ rfl _ rfl

end GlobalTheory.TrEllSum
