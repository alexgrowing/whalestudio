import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSameData
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.TwInputs.Move GlobalTheory.HeightCounting.SideCopy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

private theorem readMove {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {A K L L' : Type} [CommRing A] [CommRing K]
    [CommRing L] [CommRing L'] {pl : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω} {φ : G E Ω →* Aˣ} {rd : A →+* K} {eL : L →+* K}
    {c : L →+* ℂ} {χ : NC.HC E} {w : ℤ} (h : NC.Read pl φ rd eL c χ w) (e : L' ≃+* L) (eL' : L' →+* K) (c' : L' →+* ℂ)
    (h1 : ∀ x, eL (e x) = eL' x) (h2 : ∀ x, c (e x) = c' x) : NC.Read pl φ rd eL' c' χ w := by
  obtain ⟨B, hB⟩ := h
  refine ⟨B, fun P hP => ?_⟩
  obtain ⟨α, hα, x, hx, hσ⟩ := hB P hP
  refine ⟨α, hα, e.symm x, ?_, fun σ hs => ?_⟩
  · rw [← h2, e.apply_symm_apply, hx]
  · rw [← h1, e.apply_symm_apply]; exact hσ σ hs

private theorem plMove {L L' K : Type} [Field L] [Field L'] [CommRing K] (e : L' ≃+* L) (f : L →+* K) (f' : L' →+* K)
    (h1 : ∀ x, f (e x) = f' x) (l : ℕ) (p : K → Prop)
    (h : ∃ w : HeightOneSpectrum (𝓞 L), (l : 𝓞 L) ∈ w.asIdeal ∧ ∀ x : 𝓞 L, x ∈ w.asIdeal ↔ p (f (x : L))) :
    ∃ w : HeightOneSpectrum (𝓞 L'), (l : 𝓞 L') ∈ w.asIdeal ∧ ∀ x : 𝓞 L', x ∈ w.asIdeal ↔ p (f' (x : L')) := by
  obtain ⟨w, hl, hw⟩ := h
  let g : 𝓞 L' ≃+* 𝓞 L := RingOfIntegers.mapRingEquiv e
  have hp := w.isPrime
  refine ⟨⟨w.asIdeal.comap (g : 𝓞 L' →+* 𝓞 L), Ideal.comap_isPrime _ _, fun hb => w.ne_bot ?_⟩, ?_, fun x => ?_⟩
  · rw [eq_bot_iff]
    intro y hy
    have : g.symm y ∈ w.asIdeal.comap (g : 𝓞 L' →+* 𝓞 L) := by
      rw [Ideal.mem_comap]
      simpa using hy
    rw [hb, Ideal.mem_bot] at this
    simpa using this
  · simpa using hl
  · rw [← h1]
    exact hw (g x)

private theorem mid {D : D7} {cf : CharFrame D} {low : Finset ℕ} (B : RingPart D cf low) {L' : Type} [Field L'] (e : L' ≃+* ↥D.LL0)
    (m mb : ∀ i, L' →+* FractionRing (D.ntw.O0 i)) (c : L' →+* ℂ)
    (hm : ∀ i x, D.ntw.emb0 i (e x) = m i x) (hmb : ∀ i x, D.ntw.emb0b i (e x) = mb i x) (hc : ∀ x, embLL0 D (e x) = c x)
    (jL : ∀ i, D.ntw.abelian₂ i → ℕ) (hjL : D.ntw.jL = jL) (s2 : ∀ i, D.ntw.abelian₂ i → ℤ) (hs2 : D.ntw.s2 = s2)
    (lamG : ∀ i, D.ntw.abelian₂ i → (G D.host.E D.nd.Om →* (D.ntw.O i)ˣ)) (hlamG : D.ntw.lamG = lamG)
    (qs : ∀ i, D.ntw.abelian₂ i → HeightOneSpectrum (𝓞 D.host.E) → FractionRing (D.ntw.O i)) (hqs : D.ntw.qs = qs)
    (mu0 : Fin D.R.m → HChar D.host.E) (hmu0 : cf.mu0 = mu0) (eta : HChar D.host.E) (heta : cf.eta = eta)
    (del : HChar D.host.E) (hdel : cf.del = del) (del' : HChar D.host.E) (hdel' : cf.del' = del') :
    (∀ i, ∃ w : HeightOneSpectrum (𝓞 L'), ((D.ntw.l i : ℕ) : 𝓞 L') ∈ w.asIdeal ∧
      ∀ x : 𝓞 L', x ∈ w.asIdeal ↔ ∃ y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i),
        algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y = m i (x : L')) ∧
    (∀ i (x : L') (y z : D.ntw.O0 i), z ≠ 0 →
      (m i x * algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) z =
          algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y ↔
        ((B.twF.j0 i).comp e.toRingHom) x * (B.twF.eO0 i z : PadicAlgCl (D.ntw.l i)) = (B.twF.eO0 i y : PadicAlgCl (D.ntw.l i)))) ∧
    (∀ i lam P, P ∉ D.ntw.S0 i →
      B.twF.iCq i (qs i lam P) = ((((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-(s2 i lam : ℝ) / 2) : ℝ) : ℂ)) ∧
    (∀ s, NC.Read D.nd.plOm.1 (D.ntw.delta s) (algebraMap (D.ntw.O0 s) (FractionRing (D.ntw.O0 s))) (m s) c (B.chiD.del s) 0) ∧
    (∀ s j (b : Bool), 1 ≤ j → j ≤ D.R.m → NC.Read D.nd.plOm.1 (D.ntw.chi1 s j b) (algebraMap (D.ntw.O0 s) (FractionRing (D.ntw.O0 s)))
      (if b then m s else mb s) c (B.chiD.firstHeckeCharacter s j) (-(D.R.r : ℤ))) ∧
    (∀ s (b : Bool) (x : L') (y : D.ntw.O0 s),
      algebraMap (D.ntw.O0 s) (FractionRing (D.ntw.O0 s)) y = (if b then m s else mb s) x →
      ((B.chiD.embO s b).comp e.toRingHom) x = algebraMap (D.ntw.O s) (FractionRing (D.ntw.O s)) (algebraMap (D.ntw.O0 s) (D.ntw.O s) y)) ∧
    (∀ s lam, NC.Read D.nd.plOm.1 (lamG s lam) (algebraMap (D.ntw.O s) (FractionRing (D.ntw.O s)))
      ((B.chiD.embO s (D.ntw.sideL s lam)).comp e.toRingHom) c (B.chiD.mu0 (jL s lam) * B.chiD.del s * (B.chiD.chiI s lam)⁻¹) 0) ∧
    (∀ x, B.chiD.etaT.χ x = eta.1 x) ∧
    (∀ (j : Fin D.R.m) x, (B.chiD.mu0 (j.1 + 1)).χ x = (mu0 j).1 x) ∧
    (∀ s x, (B.chiD.del s).χ x = (if D.ntw.l s = D.host.pde then del' else del).1 x) ∧
    (∀ s (x : L'), B.twF.iCq s (((B.chiD.embO s true).comp e.toRingHom) x) = c x) ∧
    (∀ s (x y : L'), c y = starRingEnd ℂ (c x) →
      ((B.chiD.embO s false).comp e.toRingHom) x = ((B.chiD.embO s true).comp e.toRingHom) y) ∧
    (∀ (s : D.ntw.Tw) (w : PlE D.host), w ∉ placesOver D.host.E (D.ntw.l s) → (if D.ntw.l s = D.host.pde then del' else del).UnrAt w →
      ∀ (A : ValuationSubring D.nd.Om) (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om), IsPlaceOver (F := D.host.E) A w →
        IsFrob (F := D.host.E) A (normV w) σ →
        ∃ x : L', c x = (((if D.ntw.l s = D.host.pde then del' else del).val w)⁻¹ : ℂˣ).1 ∧
          algebraMap (D.ntw.O0 s) (FractionRing (D.ntw.O0 s)) ((D.ntw.delta s σ : (D.ntw.O0 s)ˣ) : D.ntw.O0 s) = m s x) := by
  subst hjL hs2 hlamG hqs hmu0 heta hdel hdel'
  have hb : ∀ s (b : Bool) x, (if b then D.ntw.emb0 s else D.ntw.emb0b s) (e x) = (if b then m s else mb s) x := by
    intro s b x
    cases b
    · exact hmb s x
    · exact hm s x
  refine ⟨fun i => ?_, fun i x y z hz => ?_, B.tw.qs_pos, fun s => readMove (B.chi.delta s) e _ _ (hm s) hc,
    fun s j b h1 h2 => readMove (B.chi.chi1 s j b h1 h2) e _ _ (hb s b) hc, fun s b x y hy => ?_,
    fun s lam => readMove (B.chi.lamG s lam) e _ _ (fun _ => rfl) hc, B.eta_eq, B.ringSpec_normalisedCharacter_eq, B.del_eq, fun s x => ?_,
    fun s x y hy => ?_, fun s w h1 h2 A σ h3 h4 => ?_⟩
  · exact plMove e (D.ntw.emb0 i) (m i) (hm i) (D.ntw.l i) (fun k => ∃ y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i),
      algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y = k) (B.tw.pl_emb i)
  · rw [← hm]
    exact B.tw.ringSpec_baseEmbedding_compatible i (e x) y z hz
  · rw [← hb] at hy
    exact B.chi.ringSpec_sidedEmbedding_fixedField s b (e x) y hy
  · rw [← hc]
    exact B.iCq_embO s (e x)
  · refine B.embO_star s (e x) (e y) (D.what₂.embLL.injective ?_)
    rw [← hc, ← hc] at hy
    rw [D.starLL_cx]
    exact hy
  · obtain ⟨x, hx, hx'⟩ := B.deltaRead s w h1 h2 A σ h3 h4
    refine ⟨e.symm x, ?_, ?_⟩
    · rw [← hc, e.apply_symm_apply]
      exact hx
    · rw [← hm, e.apply_symm_apply]
      exact hx'

theorem UpperTheory.nonempty_coefficientRingData_of_isomorphic_CMDatum :
    ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}, CopyAll D D' ι e → ∀ {cf : CharFrame D} {cf' : CharFrame D'}, SameFrame cf cf' → IsEmpty D'.nd.Loc → ∀ low : Finset ℕ, RingPart D cf low → Nonempty (RingPart D' cf' low) := by
  intro D D' ι e h cf cf' hf hE low B
  have hst : ∀ x y : ↥D'.LL0, (y : D'.what₂.LL) = star (x : D'.what₂.LL) → embLL0 D' y = starRingEnd ℂ (embLL0 D' x) :=
    fun x y hy => (congrArg D'.what₂.embLL hy).trans (D'.starLL_cx _)
  obtain ⟨r, rfl⟩ := h.cp.exists_rest
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13⟩ := mid B e ((by with_unfolding_all exact ((overD D r).ntw.emb0 :)))
    ((by with_unfolding_all exact ((overD D r).ntw.emb0b :))) (embLL0 (overD D r))
    (fun i x => eq_of_heq ((by with_unfolding_all exact ((h.cp.emb0 i ((i)) (((HEq.refl i))) x) : _))))
    (fun i x => eq_of_heq ((by with_unfolding_all exact ((h.cp.emb0b i ((i)) (((HEq.refl i))) x) : _)))) h.cp.embLL0_eq
    ((by with_unfolding_all exact ((overD D r).ntw.jL :))) (eq_of_heq ((by with_unfolding_all exact (h.jL :)))) ((by with_unfolding_all exact ((overD D r).ntw.s2 :))) (eq_of_heq ((by with_unfolding_all exact (h.s2 :))))
    ((by with_unfolding_all exact ((overD D r).ntw.lamG :))) (eq_of_heq ((by with_unfolding_all exact (h.lamG :)))) ((by with_unfolding_all exact ((overD D r).ntw.qs :))) (eq_of_heq ((by with_unfolding_all exact (h.qs :))))
    ((by with_unfolding_all exact (cf'.mu0 :))) (eq_of_heq ((by with_unfolding_all exact (hf.mu0 :)))) ((by with_unfolding_all exact (cf'.eta :))) (eq_of_heq ((by with_unfolding_all exact (hf.eta :))))
    ((by with_unfolding_all exact (cf'.del :))) (eq_of_heq ((by with_unfolding_all exact (hf.del :)))) ((by with_unfolding_all exact (cf'.del' :))) (eq_of_heq ((by with_unfolding_all exact (hf.del' :))))
  exact ⟨⟨⟨(by with_unfolding_all exact (B.twF.K0 :)), (by with_unfolding_all exact (B.twF.eO0 :)), (by with_unfolding_all exact ((fun i => (B.twF.j0 i).comp e.toRingHom) :)), (by with_unfolding_all exact (B.twF.Lw :)),
      (by with_unfolding_all exact (B.twF.eO :)), (by with_unfolding_all exact (B.twF.eOk :)), (by with_unfolding_all exact (B.twF.iCq :)), (by with_unfolding_all exact (B.twF.S0x :))⟩,
    ⟨(by with_unfolding_all exact (m1 :)), (by with_unfolding_all exact (B.tw.ringSpec_baseIntegersEquiv_algebraMap :)), (by with_unfolding_all exact (m2 :)), (by with_unfolding_all exact (B.tw.eO_alg :)), (by with_unfolding_all exact (B.tw.eOk_alg :)), (by with_unfolding_all exact (B.tw.mu_g :)),
      (by with_unfolding_all exact (B.tw.hk_split :)), (by with_unfolding_all exact (B.tw.ringSpec_excludedPlaces_eq :)), (by with_unfolding_all exact (B.tw.concreteTwistFrame_extraExcludedPlaces_conj :)), (by with_unfolding_all exact (B.tw.B_range :)), (by with_unfolding_all exact (B.tw.sig_inj :)),
      (by with_unfolding_all exact (m3 :)), (by with_unfolding_all exact (B.tw.concreteTwistFrame_extraExcluded_over_smallPrimes :))⟩,
    ⟨(by with_unfolding_all exact (B.chiD.mu0 :)), (by with_unfolding_all exact (B.chiD.etaT :)), (by with_unfolding_all exact (B.chiD.del :)), fun a => hE.elim a, (by with_unfolding_all exact (B.chiD.chiI :)),
      (by with_unfolding_all exact ((fun s b => (B.chiD.embO s b).comp e.toRingHom) :))⟩,
    ⟨fun a => hE.elim a, (by with_unfolding_all exact (B.chi.del_fix :)), (by with_unfolding_all exact (m4 :)), (by with_unfolding_all exact (m5 :)), (by with_unfolding_all exact (m6 :)), (by with_unfolding_all exact (B.chi.etaT_unr :)),
      (by with_unfolding_all exact (B.chi.etaT_inf :)), (by with_unfolding_all exact (m7 :))⟩,
    (by with_unfolding_all exact (m8 :)), (by with_unfolding_all exact (m9 :)), (by with_unfolding_all exact (m10 :)), (by with_unfolding_all exact (m11 :)),
    (by with_unfolding_all exact ((fun s x y hy => m12 s x y (hst x y hy)) :)), (by with_unfolding_all exact (m13 :))⟩⟩
