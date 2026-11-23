import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkClosedPointToGermTop
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsUnitIffUnitAt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinrankFiniteFlatTorsionSubschemeEqCardPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace GlobalTheory.CompanionTheory.Ar.Cusp.LabPt

theorem valAt_of_const {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    {O : Type} [CommRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O))
    (hs : ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω))) {R : Type} [CommRing R] [IsLocalRing R]
    (z : Spec (CommRingCat.of R) ⟶ X) (ρ : O →+* R) (hz : z ≫ s = Spec.map (CommRingCat.ofHom ρ))
    (h : genPt ξ ⤳ centre z) (o : O) : ValAt ξ z (algebraMap O Ω o) (ρ o) := by
  refine ⟨h, (X.presheaf.germ ⊤ (centre z) trivial).hom
    (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o)),
    Flat.ConstReg.genMap_germ_const ξ s hs ⟨centre z, h⟩ o, ?_⟩
  have h1 : X.presheaf.germ ⊤ (centre z) trivial ≫ Scheme.stalkClosedPointTo z =
      z.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
    refine (Scheme.germ_stalkClosedPointTo z ⊤ trivial).trans ?_
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Scheme.Hom.appTop]
    congr 1
  have h1' := congrArg (fun q => q.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) h1
  refine h1'.trans ?_
  have h2 : z.appTop.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o)) =
      (Spec.map (CommRingCat.ofHom ρ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o) := by
    rw [← hz]; simp only [Scheme.Hom.comp_appTop]; rfl
  have h3 := congrArg (fun q => q.hom o) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ρ))
  have h3' : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (ρ o) =
      (Spec.map (CommRingCat.ofHom ρ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o) := h3
  show (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (z.appTop.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) = ρ o
  rw [h2, ← h3']
  simp

theorem valAt_unique {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (hξ : IsCptGen ξ)
    {R : Type} [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X)
    (h : genPt ξ ⤳ centre z) {a : Ω} {r r' : R} (h₁ : ValAt ξ z a r) (h₂ : ValAt ξ z a r') : r = r' := by
  obtain ⟨φ, hφ, -⟩ := ValHom.exists_valAt_hom X Ω ξ R z h hξ
  obtain ⟨_, e₁⟩ := (hφ a r).1 h₁
  obtain ⟨_, e₂⟩ := (hφ a r').1 h₂
  exact e₁.symm.trans e₂

theorem injective_of_charZero {A : Type} [CommRing A] [IsDomain A] [Algebra.IsIntegral ℤ A] {L : Type} [Field L]
    [CharZero L] (t : A →+* L) : Function.Injective t := by
  have hk : RingHom.ker t = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    ext n
    simp [Ideal.mem_comap, RingHom.mem_ker]
  exact (RingHom.injective_iff_ker_eq_bot t).2 hk

theorem card_hom_le (E : Type) [Field E] [NumberField E] (L : Type) [Field L] [CharZero L] :
    Finite (𝓞 E →+* L) ∧ Nat.card (𝓞 E →+* L) ≤ Module.finrank ℚ E := by
  let f : (𝓞 E →+* L) → (E →ₐ[ℚ] AlgebraicClosure L) := fun t =>
    ((algebraMap L (AlgebraicClosure L)).comp
      (IsFractionRing.lift (K := E) (injective_of_charZero t))).toRatAlgHom
  have hf : Function.Injective f := by
    intro t t' h
    refine RingHom.ext fun a => (algebraMap L (AlgebraicClosure L)).injective ?_
    have := DFunLike.congr_fun h (algebraMap (𝓞 E) E a)
    simpa [f] using this
  have hc : Nat.card (E →ₐ[ℚ] AlgebraicClosure L) = Module.finrank ℚ E := by
    rw [Nat.card_eq_fintype_card, AlgHom.card]
  haveI : Finite (𝓞 E →+* L) := Finite.of_injective f hf
  exact ⟨inferInstance, (Nat.card_le_card_of_injective f hf).trans hc.le⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem bijective_of_injective (H : Host E) {L : Type} [Field L] [CharZero L]
    (f : CMType H ⊕ CMType H → (𝓞 E →+* L)) (hf : Function.Injective f) : Function.Bijective f := by
  obtain ⟨hfin, hle⟩ := card_hom_le E L
  refine hf.bijective_of_nat_card_le (hle.trans ?_)
  rw [Nat.card_eq_of_bijective _ (LabelCount.labelCx_bijective H), Nat.card_eq_fintype_card,
    NumberField.Embeddings.card]

theorem isCMFam_of_bijective {A : Type} [Fintype A] (f g : A → (𝓞 E →+* ℂ))
    (hb : Function.Bijective (Sum.elim f g)) (hc : ∀ τ, g τ = (starRingEnd ℂ).comp (f τ)) :
    IsCMFam f ∧ IsCMFam g := by
  have cc : ∀ s : 𝓞 E →+* ℂ, (starRingEnd ℂ).comp ((starRingEnd ℂ).comp s) = s :=
    fun s => RingHom.ext fun a => by simp
  have hf : Function.Injective f := fun a b h =>
    Sum.inl_injective (hb.1 (a₁ := .inl a) (a₂ := .inl b) h)
  have hg : Function.Injective g := fun a b h =>
    Sum.inr_injective (hb.1 (a₁ := .inr a) (a₂ := .inr b) h)
  have hd : ∀ a b, f a ≠ g b := fun a b h => by
    have := hb.1 (a₁ := .inl a) (a₂ := .inr b) h
    simp at this
  refine ⟨⟨hf, fun s => ⟨?_, fun hn => ?_⟩⟩, ⟨hg, fun s => ⟨?_, fun hn => ?_⟩⟩⟩
  · rintro ⟨τ, rfl⟩ ⟨τ', h⟩
    exact hd τ' τ (h.trans (hc τ).symm)
  · obtain ⟨x, hx⟩ := hb.2 s
    rcases x with τ | τ
    · exact ⟨τ, hx⟩
    · have hx' : g τ = s := hx
      exact absurd ⟨τ, by rw [← hx', hc, cc]⟩ hn
  · rintro ⟨τ, rfl⟩ ⟨τ', h⟩
    refine hd τ τ' (Eq.symm (h.trans ?_))
    rw [hc, cc]
  · obtain ⟨x, hx⟩ := hb.2 s
    rcases x with τ | τ
    · have hx' : f τ = s := hx
      exact absurd ⟨τ, by rw [← hx', hc]⟩ hn
    · exact ⟨τ, hx⟩

theorem exists_labVal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L : Type) [Field L] [CharZero L] (z : Sp L ⟶ 𝔐.X), ∃ σ : CMType H ⊕ CMType H → (𝓞 E →+* L), 𝔐.LabVal z id σ ∧ (∀ σ', 𝔐.LabVal z id σ' → σ' = σ) ∧ Function.Bijective σ ∧ (∀ s, Function.Injective (σ s)) ∧ 2 * Fintype.card (CMType H) = Module.finrank ℚ E ∧ ∀ e : L →+* ℂ, IsCMFam (fun τ => e.comp (σ (.inl τ))) ∧ IsCMFam (fun τ => e.comp (σ (.inr τ))) ∧ ∀ τ, e.comp (σ (.inr τ)) = (starRingEnd ℂ).comp (e.comp (σ (.inl τ))) := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 L _ _ z
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := { }
  obtain ⟨ρ, hρ⟩ : ∃ ρ : 𝓞 c.F →+* L, spMap ρ = z ≫ 𝔐.f ≫ Y.s :=
    ⟨(Spec.preimage (z ≫ 𝔐.f ≫ Y.s)).hom, by simp [spMap]⟩
  let κ : c.F →+* L := IsFractionRing.lift (injective_of_charZero ρ)
  have hκ : ∀ o, κ (algebraMap (𝓞 c.F) c.F o) = ρ o := fun o => IsFractionRing.lift_algebraMap _ o
  letI : Algebra (𝓞 c.F) Ω := (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)).toAlgebra
  have hsp : genPt 𝔐.ξ ⤳ centre z := 𝔐.all _
  have hval : ∀ (s : CMType H ⊕ CMType H) (a : 𝓞 E), ValAt 𝔐.ξ z (𝔐.emb s a) (κ (labelEmb c s a)) := by
    intro s a
    have hint : IsIntegral ℤ (labelEmb c s a) :=
      (NumberField.RingOfIntegers.isIntegral a).map (labelEmb c s).toIntAlgHom
    have hm : algebraMap (𝓞 c.F) c.F (IsIntegralClosure.mk' (𝓞 c.F) _ hint) = labelEmb c s a :=
      IsIntegralClosure.algebraMap_mk' _ _ hint
    have h := valAt_of_const 𝔐.ξ (𝔐.f ≫ Y.s) 𝔐.cst_over z ρ hρ.symm hsp (IsIntegralClosure.mk' (𝓞 c.F) _ hint)
    have he : algebraMap (𝓞 c.F) Ω (IsIntegralClosure.mk' (𝓞 c.F) _ hint) = 𝔐.emb s a := by
      show 𝔐.cst (algebraMap (𝓞 c.F) c.F (IsIntegralClosure.mk' (𝓞 c.F) _ hint)) = 𝔐.cst (labelEmb c s a)
      rw [hm]
    rw [he, ← hκ, hm] at h
    exact h
  let σ : CMType H ⊕ CMType H → (𝓞 E →+* L) := fun s => κ.comp (labelEmb c s)
  have hinj : ∀ {L' : Type} [Field L'] (κ' : c.F →+* L'),
      Function.Injective fun s : CMType H ⊕ CMType H => κ'.comp (labelEmb c s) := fun κ' s t h =>
    LabelCount.labelEmb_injective c (RingHom.ext fun a => κ'.injective (RingHom.congr_fun h a))
  have hconj : ∀ (e : L →+* ℂ) (τ : CMType H),
      e.comp (σ (.inr τ)) = (starRingEnd ℂ).comp (e.comp (σ (.inl τ))) := by
    intro e τ
    refine RingHom.ext fun a => ?_
    let ψ : E →+* ℂ := (e.comp κ).comp (τ.1.codRestrict c.F (c.conj τ.1))
    show ψ ((H.bar a : 𝓞 E) : E) = starRingEnd ℂ (ψ (a : E))
    rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]
  refine ⟨σ, hval, fun σ' h' => ?_, bijective_of_injective H σ (hinj κ), fun s => injective_of_charZero _, ?_,
    fun e => ?_⟩
  · funext s
    refine RingHom.ext fun a => ?_
    exact valAt_unique 𝔐.ξ 𝔐.tie.gen z hsp (h' s a) (hval s a)
  · have h := (LabelCount.labels_injective_card E H l c c.F (RingHom.id _)).2
    rw [Fintype.card_sum] at h
    omega
  · have hb : Function.Bijective (fun s => e.comp (σ s)) :=
      bijective_of_injective H _ (hinj (e.comp κ))
    have hb' : Function.Bijective (Sum.elim (fun τ => e.comp (σ (.inl τ))) fun τ => e.comp (σ (.inr τ))) := by
      convert hb using 1
      funext s
      rcases s with τ | τ <;> rfl
    obtain ⟨h1, h2⟩ := isCMFam_of_bijective _ _ hb' (hconj e)
    exact ⟨h1, h2, hconj e⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.LabPt
