import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec

noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

namespace GlobalTheory.ChiLocGal

section General

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

open Pointwise in

theorem isFrob_conj {A : ValuationSubring Ω} {q : ℕ} {g σ : G E Ω} (hσ : IsFrob (F := E) (g • A) q σ) :
    IsFrob (F := E) A q (g⁻¹ * σ * g) := by
  have hm : ∀ x, g x ∈ g • A ↔ x ∈ A := fun x => ValuationSubring.smul_mem_pointwise_smul_iff
  refine ⟨?_, fun x hx => ?_⟩
  · have h1 : σ • g • A = g • A := hσ.1
    show (g⁻¹ * σ * g) • A = A
    rw [mul_smul, mul_smul, h1, inv_smul_smul]
  · have h1 := hσ.2 (g x) (by rwa [ValuationSubring.valuation_le_one_iff, hm,
      ← ValuationSubring.valuation_le_one_iff])
    have e : σ (g x) - g x ^ q = g ((g⁻¹ * σ * g) x - x ^ q) := by
      rw [map_sub, map_pow, AlgEquiv.mul_apply, AlgEquiv.mul_apply, mul_inv_apply]
    rwa [e, valuation_lt_one_iff', ← map_inv₀, hm, hm, map_eq_zero_iff _ g.injective,
      ← valuation_lt_one_iff'] at h1

theorem frob_any [IsAlgClosure E Ω] {B : Type} [CommGroup B] {r r' : G E Ω →* B}
    {v : HeightOneSpectrum (𝓞 E)} {A₀ A : ValuationSubring Ω} (h0 : IsPlaceOver A₀ v) (hA : IsPlaceOver A v)
    (h : ∀ σ : G E Ω, IsFrob (F := E) A₀ (normV v) σ → r σ = r' σ) {σ : G E Ω}
    (hσ : IsFrob (F := E) A (normV v) σ) : r σ = r' σ := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver h0 hA
  have e : ∀ f : G E Ω →* B, f (g⁻¹ * σ * g) = f σ := fun f => by
    rw [map_mul, map_mul, map_inv, mul_comm (f g)⁻¹ (f σ), mul_assoc, inv_mul_cancel, mul_one]
  rw [← e r, ← e r']
  exact h _ (isFrob_conj hσ)

theorem locM_eq (P : HeightOneSpectrum (𝓞 E)) (x : (P.adicCompletion E)ˣ) :
    Units.map (Formalism.L2.NC.locM P) x = localIdele E P x := by
  rfl

end General

section Values

variable {E : Type} [Field E] [NumberField E]

theorem val_of_at {χ : HChar E} {ψ : Formalism.L2.NC.HC E} (h : ∀ x, ψ.χ x = χ.1 x) {P : HeightOneSpectrum (𝓞 E)} {α : ℂ}
    (hα : ψ.At P α) : ((χ.val P : ℂˣ) : ℂ) = α := by
  rw [← hα.2 _ (unif_spec P), h, locM_eq]
  rfl

theorem normV_eq_absNorm (P : HeightOneSpectrum (𝓞 E)) : normV P = Ideal.absNorm P.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rfl

theorem val_block {μ η : HChar E} {r : ℕ} {P : HeightOneSpectrum (𝓞 E)} {α z : ℂ}
    (hα : (((μ * η⁻¹).val P : ℂˣ) : ℂ) = α) (hz : z = α⁻¹ * (Real.sqrt (normV P) : ℂ) ^ (-(r : ℤ))) :
    (((GlobalTheory.GalChar.block μ η r).val P : ℂˣ) : ℂ) = z⁻¹ := by
  rw [GlobalTheory.GalChar.block_val, hα, hz, mul_inv, inv_inv, zpow_neg, inv_inv, zpow_natCast, ← normV_eq_absNorm]
  congr 1
  have h0 : (0 : ℝ) ≤ (normV P : ℝ) := Nat.cast_nonneg _
  rw [show ((normV P : ℕ) : ℂ) = ((normV P : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_cpow h0,
    Real.sqrt_eq_rpow, ← Complex.ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul h0]
  congr 2
  ring

end Values

theorem chi1_loc_isGal : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T), ∀ (Y : LocAut X) (Cb : LocBC Y), AutSpec A M tp.tup Sp.iq Y Cb → ∀ (art : Ideles D.host.E →* Gab D.host.E D.nd.Om), IsGlobalArtin art → ∀ (i : X.nd.Loc) (j' : Fin D.R.m), j'.1 + 1 = X.nd.j i → ∃ n, GlobalTheory.GalChar.IsGal art (Sp.iq i) (Y.naut.iotaQC i) (GlobalTheory.GalChar.block (cf.mu0 j' * cf.delAt (X.nd.l i)) cf.eta D.R.r) n ((Units.map (T.twist₂ i).toMonoidHom).comp (D.ntw.chi1 (T.twOf i) (X.nd.j i) (T.twSide i))) := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp _ _ _ he _ _ big X T Sp Y Cb hAu art ha i j' hj
  letI := D.ntw.crO0 (T.twOf i)
  haveI := D.ntw.twistBaseCoefficientRing_isDomain (T.twOf i)
  haveI := D.ntw.twistBaseCoefficientRing_isDVR (T.twOf i)
  letI := D.ntw.topO0 (T.twOf i)
  haveI := D.ntw.twistBaseCoefficientRing_topologicalRing (T.twOf i)

  let C' : GlobalTheory.Mem.Chr.HFrame D.host (eExp D) :=
    ⟨cf.P, cf.W, cf.mu0, cf.eta, cf.chiPsi, cf.del, cf.del', cf.isMu0, cf.isEta, cf.isChi, cf.isDel, cf.isDel'⟩
  obtain ⟨n0, h0⟩ := GlobalTheory.GalChar.exists_isAlgPos_mu0 C' he j'
  obtain ⟨n, hn⟩ := GlobalTheory.GalChar.block_alg C' ⟨_, GlobalTheory.GalChar.isAlgPos_mul h0 (GlobalTheory.GalChar.del_alg C' (X.nd.l i))⟩
  have hn' : IsAlgPos (GlobalTheory.GalChar.block (cf.mu0 j' * cf.delAt (X.nd.l i)) cf.eta D.R.r) n := hn

  have hj1 := X.nd.j_range i
  obtain ⟨B1, hB1⟩ := Bs.chi.chi1 (T.twOf i) (X.nd.j i) (T.twSide i) hj1.1 hj1.2
  have hχ : ∀ x, (Bs.chiD.firstHeckeCharacter (T.twOf i) (X.nd.j i)).χ x = (cf.mu0 j' * cf.delAt (X.nd.l i) * cf.eta⁻¹).1 x := by
    intro x
    have h1 := Bs.ringSpec_normalisedCharacter_eq j' x
    have h2 := Bs.del_eq (T.twOf i) x
    have h3 := Bs.eta_eq x
    rw [hj] at h1
    have h4 : D.ntw.l (T.twOf i) = X.nd.l i := T.twOf_l i
    rw [h4] at h2
    simp only [Formalism.L2.NC.NChiData.firstHeckeCharacter, Formalism.L2.NC.HC.mul_χ, Formalism.L2.NC.HC.inv_χ, MonoidHom.mul_apply,
      MonoidHom.inv_apply, h1, h2, h3]
    rfl
  set χb := GlobalTheory.GalChar.block (cf.mu0 j' * cf.delAt (X.nd.l i)) cf.eta D.R.r with hχb

  have key : ∀ P ∉ B1, ∃ x : ↥D.LL0, Formalism.L2.NC.complexEmbeddingRestrictedToSubfield D x = ((χb.val P : ℂˣ) : ℂ)⁻¹ ∧
      ∀ σ : G D.host.E D.nd.Om, IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) σ →
        X.nd.embK i (x : D.what₂.LL) = algebraMap (X.nd.O i) (FractionRing (X.nd.O i))
          (T.twist₂ i (Units.val (D.ntw.chi1 (T.twOf i) (X.nd.j i) (T.twSide i) σ))) := by
    intro P hP
    obtain ⟨α, hα, x, hx, hσ⟩ := hB1 P hP
    refine ⟨x, ?_, fun σ hσ' => T.twO_emb i x _ (hσ σ hσ')⟩
    rw [val_block (val_of_at hχ hα) hx, inv_inv]
  have hev : ∀ᶠ P in Filter.cofinite, P ∉ B1 := Filter.eventually_cofinite.2 (by simpa using B1.finite_toSet)
  have hAlm : GlobalTheory.GalChar.AlmostIn (Formalism.L2.NC.complexEmbeddingRestrictedToSubfield D) χb := by
    filter_upwards [hev] with P hP
    obtain ⟨x, hx, -⟩ := key P hP
    exact ⟨x⁻¹, by rw [map_inv₀, hx, inv_inv]⟩
  have hf : ∀ x : ↥D.LL0, Y.naut.iotaQC i (Sp.iq i (((X.nd.embK i).comp D.LL0.val.toRingHom) x)) =
      Formalism.L2.NC.complexEmbeddingRestrictedToSubfield D x := by
    intro x
    rw [← hAu.iotaQ i]
    exact Y.iota_LL i x
  have hO := X.nd.O_adic i
  have hκ := Sp.iq_alg i
  obtain ⟨r0, hr0⟩ := GlobalTheory.GalChar.exists_isGal hO hκ ha hn' hf hAlm

  haveI : T2Space (X.nd.O i) := (GlobalTheory.GalChar.isEmbedding_toQ hO hκ).t2Space
  have hlO := (GlobalTheory.CoefEmbed.embedding_closed_integral (X.nd.l i) (X.nd.O i) hO (Sp.iq i) hκ).2.2.2
  have hl0 : ((X.nd.l i : ℕ) : D.ntw.O0 (T.twOf i)) ≠ 0 := fun h => by
    have h' := congrArg (algebraMap (D.ntw.O0 (T.twOf i)) (FractionRing (D.ntw.O0 (T.twOf i)))) h
    rw [map_natCast, map_zero, ← map_natCast (D.ntw.emb0 (T.twOf i))] at h'
    have h'' := (D.ntw.emb0 (T.twOf i)).injective (h'.trans (map_zero _).symm)
    exact (Fact.out : (X.nd.l i).Prime).ne_zero (by exact_mod_cast h'')
  have hc1 : Continuous ((Units.map (T.twist₂ i).toMonoidHom).comp (D.ntw.chi1 (T.twOf i) (X.nd.j i) (T.twSide i))) :=
    GlobalTheory.GalChar.continuous_units _ ((GlobalTheory.GalChar.continuous_ringHom (D.ntw.twistBaseCoefficientRing_isAdic (T.twOf i)) hO hl0 hlO (T.twist₂ i)).comp
      (D.ntw.twistCharacterFamily_continuous (T.twOf i) (X.nd.j i) (T.twSide i)))
  have hlne : X.nd.l i ≠ 0 := (Fact.out : (X.nd.l i).Prime).ne_zero
  have heq : r0 = (Units.map (T.twist₂ i).toMonoidHom).comp (D.ntw.chi1 (T.twOf i) (X.nd.j i) (T.twSide i)) := by
    refine GlobalTheory.GalChar.eq_of_frob ha (GlobalTheory.GalChar.continuous_units r0 hr0.2.1) hc1 ?_
    filter_upwards [hev, GlobalTheory.GalChar.unr_ae χb, GlobalTheory.GalChar.away_ae (E := D.host.E) (X.nd.l i) hlne]
      with v hv hu hl A' hA' σ hσ
    refine frob_any (D.nd.plOm.2 v) hA' (fun σ' hσ' => ?_) hσ
    obtain ⟨x, hx1, hx2⟩ := key v hv
    apply Units.ext
    apply GlobalTheory.GalChar.toQ_injective (Sp.iq i)
    apply (Y.naut.iotaQC i).injective
    rw [hr0.frob ha (Or.inl hl) hu (D.nd.plOm.2 v) hσ', ← hx1]
    show _ = Y.naut.iotaQC i (Sp.iq i (algebraMap (X.nd.O i) (FractionRing (X.nd.O i))
      (T.twist₂ i (Units.val (D.ntw.chi1 (T.twOf i) (X.nd.j i) (T.twSide i) σ')))))
    rw [← hx2 σ' hσ']
    exact (hf x).symm
  exact ⟨n, heq ▸ hr0⟩

end GlobalTheory.ChiLocGal
