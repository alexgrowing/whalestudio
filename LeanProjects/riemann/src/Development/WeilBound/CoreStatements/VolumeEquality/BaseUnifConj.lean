import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifConjA
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConjugateUniversalFamilyStatement

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory Limits NumberField MeasureTheory Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l}

theorem vecAt_conj {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K]
    {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y) {n g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
    (R R' : (Fin n → ℂ) → RiemLat E g Λ) (z : (Fin n → ℂ) → (Sp ℂ ⟶ 𝔐.X)) (t₀ : Fin n → ℂ)
    (hR : ∀ t, (∀ x, (R' t).P x = star ((R (star t)).P x)) ∧ (R' t).Hm = (R (star t)).Hm.map (starRingEnd ℂ) ∧
      ∀ a x, (R' t).B a x = star ((R (star t)).B a (star x)))
    (h : VecAt 𝔐 R (fun t => spMap (starRingEnd ℂ) ≫ z (star t)) (star t₀)) : VecAt 𝔐 R' z t₀ := by
  intro m s hs
  obtain ⟨x, hx, hev⟩ := h m s fun a => by
    obtain ⟨v, hv⟩ := hs a
    show ∃ v, 𝔐.M.ValAt (spMap (starRingEnd ℂ) ≫ z (star (star t₀))) (s a) v
    rw [star_star]
    exact ⟨_, Cj.valAt_conj 𝔐.M _ _ v hv⟩
  refine ⟨fun a t => star (x a (star t)), fun a => Cj.analyticAt_star_star (hx a), ?_⟩
  filter_upwards [(continuous_star.continuousAt (x := t₀)).tendsto.eventually hev] with t ht
  obtain ⟨v, hv, hF⟩ := ht
  have key : ∀ (w w' : Sp ℂ ⟶ 𝔐.X) (v : Fin m → (epsAt w ⟶ 𝔐.t.G)), w' = spMap (starRingEnd ℂ) ≫ w →
      (∀ a, 𝔐.M.ValAt w (s a) (v a)) → FibreLatVec 𝔐.t w (R (star t)) (fun a => x a (star t)) v →
      ∃ v' : Fin m → (epsAt w' ⟶ 𝔐.t.G), (∀ a, 𝔐.M.ValAt w' (s a) (v' a)) ∧
        FibreLatVec 𝔐.t w' (R' t) (fun a => star (x a (star t))) v' := by
    rintro w _ v rfl hv hF
    exact ⟨fun a => Cj.cjVec w (v a), fun a => Cj.valAt_conj 𝔐.M w _ _ (hv a),
      Cj.fibreLatVec_conj 𝔐.t w _ _ _ v (hR t).1 (hR t).2.1 (hR t).2.2 (fun a => (hv a).isTanAt) hF⟩
  exact key _ _ v (by rw [Cj.cj_cj, star_star]) hv hF

theorem kUnifConj : KUnifConj := by
  rintro E _ _ _ H D l Xo c Y sm j j' n g q κ ⟨U⟩
  choose F' hq hσ hform hR using fun k => GlobalTheory.T.conjugate_universal_family E (CMType H) j j' n g (U.Di k).La (U.F k)
  have hcanc : ∀ {X : Scheme.{0}} {a b : Sp ℂ ⟶ X}, spMap (starRingEnd ℂ) ≫ a = spMap (starRingEnd ℂ) ≫ b → a = b :=
    fun {X a b} e => by rw [← Cj.cj_cj a, e, Cj.cj_cj]
  have hs : spMap (((starRingEnd ℂ).comp κ).comp (algebraMap (𝓞 c.F) c.F)) =
      spMap (starRingEnd ℂ) ≫ spMap (κ.comp (algebraMap (𝓞 c.F) c.F)) :=
    Spec.map_comp (CommRingCat.ofHom (κ.comp (algebraMap (𝓞 c.F) c.F))) (CommRingCat.ofHom (starRingEnd ℂ))
  refine ⟨{
    ι := U.ι
    fin := U.fin
    Di := U.Di
    sig := U.sig
    F := F'
    q_eq := fun k => (hq k).trans (U.q_eq k)
    form_eq := fun k => ?_
    σ_eq := fun k τ => ?_
    Γ := U.Γ
    mem_Γ := U.mem_Γ
    arith := fun k => ?_
    pt := fun k t => spMap (starRingEnd ℂ) ≫ U.pt k (star t)
    hol := fun k => ?_
    comp_s_eq_spMap_of_isOver := fun k t ht => ?_
    interior := fun k t ht => ?_
    disj := fun k k' t ht t' ht' e =>
      U.disj k k' _ (Cj.star_mem_ballDom ht) _ (Cj.star_mem_ballDom ht') (hcanc e)
    fibre := fun k t ht t' ht' => ?_
    onto := fun p hp hps => ?_
    lat := fun k t ht => ?_
    vec := fun S Ω _ K _ J _ y 𝔐 k V z hV hVs hz hzf t₀ ht₀ => ?_
    locc := fun m T y hT hTc hy hyi hys b hb b' hb' k k' t ht t' ht' e e' => ?_ }⟩
  · rw [hform]
    rcases U.form_eq k with h | h <;> rw [h]
    · exact Or.inr rfl
    · exact Or.inl (neg_neg _)
  · rw [hσ, U.σ_eq]
    rfl
  · have h := U.arith k
    unfold UnivFam.IsArith at h ⊢
    rwa [hform, Cj.autGrp_neg]
  · have h := GlobalTheory.T.holomorphic_family_conjugate _ _ _ _ (U.hol k)
    rwa [Cj.preimage_star_ballDom] at h
  · rw [Category.assoc, U.comp_s_eq_spMap_of_isOver k _ (Cj.star_mem_ballDom ht), hs]
  · rw [Cj.centre_conj]
    exact U.interior k _ (Cj.star_mem_ballDom ht)
  · have h := U.fibre k _ (Cj.star_mem_ballDom ht) _ (Cj.star_mem_ballDom ht')
    constructor
    · intro e
      obtain ⟨γ, hγ, he⟩ := h.1 (hcanc e)
      exact ⟨γ, hγ, Cj.eqvBy_conj (hR k t).1 (hR k t').1 he⟩
    · rintro ⟨γ, hγ, he⟩
      have e := h.2 ⟨γ, hγ, Cj.eqvBy_conj (fun x => by rw [(hR k t).1, star_star])
        (fun x => by rw [(hR k t').1, star_star]) he⟩
      show spMap (starRingEnd ℂ) ≫ U.pt k (star t) = spMap (starRingEnd ℂ) ≫ U.pt k (star t')
      rw [e]
  · obtain ⟨k, t, ht, e⟩ := U.onto (spMap (starRingEnd ℂ) ≫ p) (by rwa [Cj.centre_conj])
      (by rw [Category.assoc, hps, hs, Cj.cj_cj])
    refine ⟨k, star t, Cj.star_mem_ballDom ht, ?_⟩
    show spMap (starRingEnd ℂ) ≫ U.pt k (star (star t)) = p
    rw [star_star, e, Cj.cj_cj]
  · have h := Cj.fibreLatVec_conj Y.t _ _ ((F' k).R t) _ _ (hR k t).1 (hR k t).2.1 (hR k t).2.2 (fun a => a.elim)
      (U.lat k _ (Cj.star_mem_ballDom ht))
    obtain ⟨A, i, φ, u, χ, h1, h2, h3, h4, h5, -⟩ := h
    exact ⟨A, i, φ, u, χ, h1, h2, h3, h4, h5, fun a => a.elim⟩
  · refine vecAt_conj 𝔐 (U.F k).R (F' k).R z t₀ (hR k) ?_
    refine U.vec S Ω K J y 𝔐 k (star ⁻¹' V) _ (hV.preimage continuous_star) (fun t ht => ?_)
      (GlobalTheory.T.holomorphic_family_conjugate _ _ _ _ hz) (fun t ht => ?_) _ (by simpa using ht₀)
    · simpa using Cj.star_mem_ballDom (hVs ht)
    · rw [Category.assoc, hzf _ ht, Cj.cj_cj, star_star]
  · have hpre : IsPreconnected (star ⁻¹' T : Set (Fin m → ℂ)) := by
      have e₀ : (star ⁻¹' T : Set (Fin m → ℂ)) = star '' T := by
        ext x
        constructor
        · intro h
          exact ⟨star x, h, star_star x⟩
        · rintro ⟨a, ha, rfl⟩
          show star (star a) ∈ T
          rwa [star_star]
      rw [e₀]
      exact hTc.image _ continuous_star.continuousOn
    refine U.locc m (star ⁻¹' T) _ (hT.preimage continuous_star) hpre (GlobalTheory.T.holomorphic_family_conjugate _ _ _ _ hy) (fun a ha => ?_)
      (fun a ha => ?_) (star b) (by simpa using hb) (star b') (by simpa using hb') k k' _ (Cj.star_mem_ballDom ht) _
      (Cj.star_mem_ballDom ht') ?_ ?_
    · rw [Cj.centre_conj]
      exact hyi _ ha
    · rw [Category.assoc, hys _ ha, hs, Cj.cj_cj]
    · show spMap (starRingEnd ℂ) ≫ y (star (star b)) = _
      rw [star_star, e, Cj.cj_cj]
    · show spMap (starRingEnd ℂ) ≫ y (star (star b')) = _
      rw [star_star, e', Cj.cj_cj]

end SheetDecomposition
