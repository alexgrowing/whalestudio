import Development.WeilBound.CoreStatements.FlagImmersions.Transport
import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnif
import Development.WeilBound.CoreStatements.VolumeEquality.Pieces
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConjugateUniversalFamily

noncomputable section

namespace RootFieldNumerics

open AlgebraicGeometry CategoryTheory Limits NumberField Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp SheetDecomposition

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K]
  {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)

def HasPer {n : ℕ} (V : Set (Fin n → ℂ)) (z : (Fin n → ℂ) → (Sp ℂ ⟶ 𝔐.X)) (t₀ : Fin n → ℂ) : Prop :=
  ∃ (g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (R : (Fin n → ℂ) → RiemLat E g Λ) (V' : Set (Fin n → ℂ)),
    IsOpen V' ∧ t₀ ∈ V' ∧ V' ⊆ V ∧ IsHolFam V' R ∧ VecAt 𝔐 R z t₀

theorem hasPer_good {g : ℕ} (κ : c.F →+* ℂ) (ty : Fin g → (E →+* ℂ)) (hty : IsTypeFn H D.p D.q ty)
    (FU : FamilyUnif Xo (κ.comp (IntermediateField.inclusion c.le).toRingHom) ty) {n : ℕ} {V : Set (Fin n → ℂ)}
    {z : (Fin n → ℂ) → (Sp ℂ ⟶ 𝔐.X)} (hV : IsOpen V) (hz : IsHolTo V z) (hi : ∀ t ∈ V, 𝔐.Interior (z t))
    (hs : ∀ t ∈ V, (z t ≫ 𝔐.f) ≫ Y.s = spMap (κ.comp (algebraMap (𝓞 c.F) c.F))) {t₀ : Fin n → ℂ} (ht₀ : t₀ ∈ V) :
    HasPer 𝔐 V z t₀ := by
  classical
  have hx : ∀ a, ∃ x : Sp ℂ ⟶ Xo.XF c, x ≫ pullback.snd _ _ = spMap κ ∧ (a ∈ V → x ≫ Y.j = z a ≫ 𝔐.f) := fun a => by
    by_cases ha : a ∈ V
    · obtain ⟨x, h₁, h₂⟩ := exists_j Y κ _ ((interior_iff 𝔐 _).2 (hi a ha)) (hs a ha)
      exact ⟨x, h₂, fun _ => h₁⟩
    · obtain ⟨x, -, h₂⟩ := exists_j Y κ _ ((interior_iff 𝔐 _).2 (hi t₀ ht₀)) (hs t₀ ht₀)
      exact ⟨x, h₂, fun h => absurd h ha⟩
  choose x hxs hxj using hx
  have hol := isHolTo_of_j Y κ hV hxs (GlobalTheory.HolPeriods.isHolTo_congr (PullbackSections.isHolTo_comp hz 𝔐.f) hxj)
  obtain ⟨V', i, P, hV', hm, hsub, hP, hu⟩ := FU.lift n V (fun a => x a ≫ pullback.fst _ _) hV
    (fun a _ => by rw [Category.assoc, pullback.condition, ← Category.assoc, hxs, spMap_comp]) (PullbackSections.isHolTo_comp hol _) t₀ ht₀
  have htyi : IsTypeFn H (FU.Di i).p (FU.Di i).q ty := by
    rw [(FU.sig i).1, (FU.sig i).2]
    exact hty
  have hR : ∀ t, ∃ R : RiemLat E g (FU.Di i).La, R.form = (FU.Di i).EF ∧ (t ∈ V' → R.P = P t) := fun t => by
    by_cases ht : t ∈ V'
    · obtain ⟨R, h₁, h₂, -⟩ := GlobalTheory.T.exists_riemann_lattice_of_period E H (FU.Di i) g ty _ htyi (hP.1 t ht)
      exact ⟨R, h₂, fun _ => h₁⟩
    · obtain ⟨R, -, h₂, -⟩ := GlobalTheory.T.exists_riemann_lattice_of_period E H (FU.Di i) g ty _ htyi (hP.1 t₀ hm)
      exact ⟨R, h₂, fun h => absurd h ht⟩
  choose R hf hRP using hR
  refine ⟨g, _, inferInstance, inferInstance, R, V', hV', hm, hsub,
    ⟨fun t _ t' _ => (hf t).trans (hf t').symm, fun a => (hP.2 a).congr fun t ht => by rw [hRP t ht]⟩, ?_⟩
  refine vecOfPeriods_of holCoord E H D l Xo c Y S Ω K J y 𝔐 κ _ g ty FU i n V' z x R P (fun _ => 1) hV'
    (vecMono hz hV' hsub) (vecMono hol hV' hsub) hP (fun _ _ => differentiableOn_const _) (fun t ht => ?_) t₀ hm
  exact ⟨hf t, by simp, fun a => by rw [hRP t ht, Matrix.one_mulVec], hxj t (hsub ht), (hu t ht).symm, hxs t⟩

theorem hasPer_conj {n : ℕ} {V : Set (Fin n → ℂ)} {z : (Fin n → ℂ) → (Sp ℂ ⟶ 𝔐.X)} {t₀ : Fin n → ℂ}
    (h : HasPer 𝔐 (star ⁻¹' V) (fun t => spMap (starRingEnd ℂ) ≫ z (star t)) (star t₀)) : HasPer 𝔐 V z t₀ := by
  obtain ⟨g, Λ, _, _, R, V', hV', hm, hsub, hR, hv⟩ := h
  refine ⟨g, Λ, inferInstance, inferInstance, fun t => GlobalTheory.CompanionTheory.Ar.Cusp.ConjFam.conjLat (R (star t)), star ⁻¹' V', hV'.preimage continuous_star, hm,
    fun t ht => by simpa using hsub ht, ⟨fun t ht t' ht' => ?_, fun a => ?_⟩, ?_⟩
  · show -(R (star t)).form = -(R (star t')).form
    rw [hR.1 _ ht _ ht']
  · exact GlobalTheory.CompanionTheory.Ar.Cusp.ConjFam.differentiableOn_conj (hR.2 a) fun t ht => ht
  · exact vecAt_conj 𝔐 R _ z t₀ (fun t => ⟨fun _ => rfl, rfl, fun _ _ => rfl⟩) hv

theorem locPer : LocPer := by
  intro hG E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 n V z h1 hV hz hi t₀ ht₀
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  obtain ⟨ε, hε, hB⟩ := Metric.isOpen_iff.1 hV t₀ ht₀
  have hBo : IsOpen (Metric.ball t₀ ε) := Metric.isOpen_ball
  have hz' := vecMono hz hBo hB
  have hemb : ∀ p : Sp ℂ ⟶ Y.X, ∃ κ : c.F →+* ℂ, p ≫ Y.s = spMap (κ.comp (algebraMap (𝓞 c.F) c.F)) := fun p => by
    obtain ⟨κ, hκρ⟩ := FamEx.exists_ringHom_extend (Spec.preimage (p ≫ Y.s)).hom
    refine ⟨κ, ?_⟩
    rw [hκρ]
    unfold spMap
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  choose κ hκy using fun b => hemb (z b ≫ 𝔐.f)
  have hd : ∀ r : 𝓞 c.F, DifferentiableOn ℂ (fun b => κ b (r : c.F)) (Metric.ball t₀ ε) := fun r => by
    have h3 := (PullbackSections.isHolTo_comp (PullbackSections.isHolTo_comp hz' 𝔐.f) Y.s ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 c.F))).inv r)).2
    have hset : Metric.ball t₀ ε ⊆ {b ∈ Metric.ball t₀ ε | ⊤ ≤ ((z b ≫ 𝔐.f) ≫ Y.s) ⁻¹ᵁ ⊤} := fun b hb => ⟨hb, le_top⟩
    refine (h3.mono hset).congr fun b _ => ?_
    show κ b (r : c.F) = valAt' ((z b ≫ 𝔐.f) ≫ Y.s) ⊤ _
    rw [hκy b]
    exact (PullbackSections.valAt'_spMap ((κ b).comp (algebraMap (𝓞 c.F) c.F)) r).symm
  have h0 : t₀ ∈ Metric.ball t₀ ε := Metric.mem_ball_self hε
  have hc : ∀ b ∈ Metric.ball t₀ ε, (z b ≫ 𝔐.f) ≫ Y.s = spMap ((κ t₀).comp (algebraMap (𝓞 c.F) c.F)) := fun b hb => by
    rw [hκy, FamEx.embedding_const_preconnected (convex_ball t₀ ε).isPreconnected κ hd hb h0]
  have hi' : ∀ t ∈ Metric.ball t₀ ε, 𝔐.Interior (z t) := fun t ht => hi t (hB ht)
  have hN : N1c := hG.1.2.2.1
  obtain ⟨g, ty, hty⟩ := GlobalTheory.AllClasses.exists_isTypeFn H D.p D.q
  let ρ : c.F := (IntermediateField.inclusion c.le).toRingHom (baseKA l).ρ
  have key : HasPer 𝔐 (Metric.ball t₀ ε) z t₀ := by
    have e : ρ ^ 2 = -(H.d : c.F) := Subtype.ext (by show (ρ : ℂ) ^ 2 = -(H.d : ℂ); exact H.sqrt_neg_disc_sq)
    have e2 : (κ t₀ ρ) ^ 2 = H.rt0 ^ 2 := by
      rw [← map_pow, e, H.sqrt_neg_disc_sq]
      simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 e2 with h | h
    · obtain ⟨FU⟩ := hN E H D l Xo ((κ t₀).comp (IntermediateField.inclusion c.le).toRingHom) g ty h1 h hty
      exact hasPer_good 𝔐 _ ty hty FU hBo hz' hi' hc h0
    · obtain ⟨FU⟩ := hN E H D l Xo (((starRingEnd ℂ).comp (κ t₀)).comp (IntermediateField.inclusion c.le).toRingHom) g ty h1
        (by
          show starRingEnd ℂ (κ t₀ ρ) = _
          rw [h, map_neg, FamEx.rt0_conj_neg_ne_zero, neg_neg]) hty
      have hs : spMap (((starRingEnd ℂ).comp (κ t₀)).comp (algebraMap (𝓞 c.F) c.F)) =
          spMap (starRingEnd ℂ) ≫ spMap ((κ t₀).comp (algebraMap (𝓞 c.F) c.F)) :=
        Spec.map_comp (CommRingCat.ofHom ((κ t₀).comp (algebraMap (𝓞 c.F) c.F))) (CommRingCat.ofHom (starRingEnd ℂ))
      refine hasPer_conj 𝔐 (hasPer_good 𝔐 _ ty hty FU (hBo.preimage continuous_star) (GlobalTheory.T.holomorphic_family_conjugate _ _ _ _ hz')
        (fun t ht => ?_) (fun t ht => ?_) (by simpa using hε))
      · have h := hi' _ ht
        unfold HodgeCpt.Interior at h ⊢
        rwa [Cj.centre_conj]
      · rw [hs, ← hc _ ht]
        simp only [Category.assoc]
  obtain ⟨g, Λ, i₁, i₂, R, V', hV', hm, hsub, hR, hv⟩ := key
  refine ⟨g, Λ, i₁, i₂, R, V', fun s => (κ t₀).comp (labelEmb c s), hV', hm, hsub.trans hB, hR, fun t ht s => ?_, hv⟩
  have h := hc t (hsub ht)
  rw [Category.assoc] at h
  cases s with
  | inl τ => exact labVal_of_over 𝔐 (hi' t (hsub ht)) h Sum.inl τ
  | inr τ => exact labVal_of_over 𝔐 (hi' t (hsub ht)) h Sum.inr τ

end RootFieldNumerics
