import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPullWedge
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericCoordsDescendSubfield
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelConstantsExtension
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkClosedPointToGermTop
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CptStalk

theorem isIntegrallyClosed_regAt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (hg : IsCptGen ξ) (q : Cpt ξ) : IsIntegrallyClosed (regAt ξ q) := by
  let e : X.presheaf.stalk q.1 ≃+* regAt ξ q :=
    RingEquiv.ofBijective (genMap ξ q).rangeRestrict
      ⟨fun x y hxy => hg.inj q (congrArg Subtype.val hxy), (genMap ξ q).rangeRestrict_surjective⟩
  haveI := (hn q.1).1
  haveI := (hn q.1).2
  exact IsIntegrallyClosed.of_equiv e

theorem asIdeal_eq_bot {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hg : IsCptGen ξ)
    {F : Type} [Field F] [NumberField F] (s : X ⟶ Spec (CommRingCat.of (𝓞 F))) (b : 𝓞 F →+* Ω)
    (hs : ξ ≫ s = Spec.map (CommRingCat.ofHom b)) {p : Cpt ξ} (hp : p ∈ genFibre ℤ ξ) :
    (s p.1).asIdeal = ⊥ := by
  letI : Algebra (𝓞 F) Ω := b.toAlgebra
  have hreg := ConstReg.regular_const X Ω ξ (𝓞 F) s hs p
  refine (Submodule.eq_bot_iff _).2 fun o ho => ?_
  by_contra h0
  have hn : Ideal.absNorm (Ideal.span {o}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact h0
  have hmem : ((Ideal.absNorm (Ideal.span {o}) : ℕ) : 𝓞 F) ∈ (s p.1).asIdeal :=
    (Ideal.span_singleton_le_iff_mem _).2 ho (Ideal.absNorm_mem _)
  have hu := hp ((Ideal.absNorm (Ideal.span {o}) : ℕ) : ℤ) (by exact_mod_cast hn)
  have hu' : unitAt ξ p (algebraMap (𝓞 F) Ω ((Ideal.absNorm (Ideal.span {o}) : ℕ) : 𝓞 F)) := by
    simpa using hu
  exact ((hreg _).2 hg).1 hu' hmem

section Eig

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
  {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {f : X' ⟶ X} (m : SABMap t' t f)
  {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] {ξ : Spec (CommRingCat.of Ω₀) ⟶ X} {ξ' : Spec (CommRingCat.of Ω) ⟶ X'}
  {i : Ω₀ →+* Ω} {V V' : Type} [AddCommGroup V] [Module Ω₀ V] [AddCommGroup V'] [Module Ω V']
  {M : LieModel t.G ξ V} {M' : LieModel t'.G ξ' V'} {ρ : 𝓞 E →+* Module.End Ω₀ V}
  {ρ' : 𝓞 E →+* Module.End Ω V'} {j : V →+ V'}

include m in

theorem map_act (hact : M.IsActOf t.act.act ρ) (hact' : M'.IsActOf t'.act.act ρ')
    (hj : ∀ e, (M'.pt (j e)).left ≫ m.φ = spMap (dualMap i) ≫ (M.pt e).left) (a : 𝓞 E) (e : V) :
    j (ρ a e) = ρ' a (j e) := by
  have hcanc : ∀ v w : epsAt ξ' ⟶ t'.G, v.left ≫ m.φ = w.left ≫ m.φ → v = w := by
    intro v w h
    apply Over.OverMorphism.ext
    refine m.cart.1.hom_ext h ?_
    rw [Over.w v, Over.w w]
  refine M'.inj (hcanc _ _ ?_)
  rw [hj, hact a e, hact' a (j e), Over.comp_left, Over.comp_left, Category.assoc, m.act a,
    ← Category.assoc (M'.pt (j e)).left]
  exact congrArg (· ≫ _) (hj e).symm

include m in

theorem map_mem_eigSp (hact : M.IsActOf t.act.act ρ) (hact' : M'.IsActOf t'.act.act ρ')
    (hj : ∀ e, (M'.pt (j e)).left ≫ m.φ = spMap (dualMap i) ≫ (M.pt e).left)
    (hsl : ∀ (a : Ω₀) (e : V), j (a • e) = i a • j e) (σ : 𝓞 E →+* Ω₀) {e : V} (he : e ∈ eigSp ρ σ) :
    j e ∈ eigSp ρ' (i.comp σ) := by
  simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero] at he ⊢
  intro a
  rw [← map_act m hact hact' hj, he a, hsl]
  rfl

theorem eigLat_eq_pull [CharZero Ω₀] [CharZero Ω] (cst : c.F →+* Ω₀) (hg : IsCptGen ξ) (hg' : IsCptGen ξ')
    (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i) (hact : M.IsActOf t.act.act ρ) (hact' : M'.IsActOf t'.act.act ρ')
    (hint : ∀ q : Cpt ξ, IsIntegrallyClosed (regAt ξ q)) (hint' : ∀ q : Cpt ξ', IsIntegrallyClosed (regAt ξ' q))
    (hj : ∀ e, (M'.pt (j e)).left ≫ m.φ = spMap (dualMap i) ≫ (M.pt e).left)
    (s : CMType H ⊕ CMType H) (q : Cpt ξ') (hq : ∀ r : ℕ, r.Prime → ¬ InFibre ξ' r q) :
    M'.eigLat ρ' ((i.comp cst).comp (labelEmb c s)) q =
      (M.eigLat ρ (cst.comp (labelEmb c s))).pull ξ' f j q := by
  obtain ⟨j₂, hj₂, hsl₂, -, -, hlat₂⟩ := GlobalTheory.T.lie_model_dominant_hodge E H X t X' t' f m Ω₀ Ω ξ ξ' i V V' M M' hg hg' hd
  have hcanc : ∀ v w : epsAt ξ' ⟶ t'.G, v.left ≫ m.φ = w.left ≫ m.φ → v = w := by
    intro v w h
    apply Over.OverMorphism.ext
    refine m.cart.1.hom_ext h ?_
    rw [Over.w v, Over.w w]
  have hjj : j₂ = j := by
    ext e
    exact M'.inj (hcanc _ _ ((hj₂ e).trans (hj e).symm))
  subst hjj
  have hlat := hlat₂
  have hsl := hsl₂
  obtain ⟨h, -, h2⟩ := RegAtDom.regAt_dominates X Ω₀ ξ X' Ω ξ' f i hd q
  have hp : ∀ r : ℕ, r.Prime → ¬ InFibre ξ r ⟨f q.1, h⟩ := fun r hr hn =>
    hn (by
      have := h2 hg' _ (natCast_mem _ r) (by rw [map_natCast]; exact not_not.1 (hq r hr))
      exact this)
  have hsum := (SatModel.lat_eq_iSup_of_char0 c t ξ hg cst M ρ hact (fun q _ => hint q)).2 _ hp
  have hind := (SatModel.lat_eq_iSup_of_char0 c t' ξ' hg' (i.comp cst) M' ρ' hact' (fun q _ => hint' q)).1
  have hle : ∀ u, ((M.eigLat ρ (cst.comp (labelEmb c u))).pull ξ' f j₂) q ≤ M'.lat q ⊓
      (eigSp ρ' ((i.comp cst).comp (labelEmb c u))).restrictScalars (regAt ξ' q) := by
    intro u
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h', e, he, rfl⟩
    have he2 : e ∈ eigSp ρ (cst.comp (labelEmb c u)) := he.2
    have h3 : j₂ e ∈ eigSp ρ' ((i.comp cst).comp (labelEmb c u)) := by
      rw [RingHom.comp_assoc]
      exact map_mem_eigSp m hact hact' hj₂ hsl _ he2
    refine ⟨?_, h3⟩
    show j₂ e ∈ M'.lat q
    rw [hlat]
    exact Submodule.subset_span ⟨h, e, he.1, rfl⟩
  have hall : M'.lat q ≤ ⨆ u, ((M.eigLat ρ (cst.comp (labelEmb c u))).pull ξ' f j₂) q := by
    rw [hlat]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h', e, he, rfl⟩
    have he1 : e ∈ ⨆ u, M.lat.inter (eigSp ρ (cst.comp (labelEmb c u))) ⟨f q.1, h⟩ := by
      rw [← hsum]
      exact he
    refine Submodule.iSup_induction _ (motive := fun e =>
      j₂ e ∈ ⨆ u, ((M.eigLat ρ (cst.comp (labelEmb c u))).pull ξ' f j₂) q) he1 (fun u e he => ?_) ?_
      (fun x y hx hy => ?_)
    · exact Submodule.mem_iSup_of_mem u (Submodule.subset_span ⟨h, e, he, rfl⟩)
    · simp only [map_zero]
      exact zero_mem _
    · simp only [map_add]
      exact add_mem hx hy
  refine le_antisymm ?_ (hle s)
  rintro x ⟨hx1, hx2⟩
  exact FlagStep.mem_of_mem_iSup_of_indep (regAt ξ' q) hind (fun u => (hle u).trans inf_le_right) s (hall hx1) hx2

end Eig

section Labels

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)

theorem labelEmb_inl (τ : CMType H) : labelEmb c (.inl τ) = tauIn c τ.1 := rfl

theorem labelEmb_inr (τ : CMType H) : labelEmb c (.inr τ) = tauIn c (ComplexEmbedding.conjugate τ.1) := by
  refine RingHom.ext fun a => Subtype.ext ?_
  change τ.1 ((H.bar a : 𝓞 E) : E) = (ComplexEmbedding.conjugate τ.1) (a : E)
  rw [H.bar_eq, ComplexEmbedding.conjugate_coe_eq, IsCMField.complexEmbedding_complexConj]

end Labels

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (U : Set (Xo.XF c)) (Z : CptOver Y U) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (τ : CMType H) (i : Z.Ω →+* Ω) (j : Z.V →+ 𝔐.Li), CptIn.IsTie Z 𝔐 i j → ∀ p ∈ genFibre ℤ 𝔐.ξ, 𝔐.f p.1 ∈ Subtype.val '' Z.genFib ∧ 𝔐.V (.inl τ) p = (Z.eig τ.1).pull 𝔐.ξ 𝔐.f j p ∧ 𝔐.V (.inr τ) p = (Z.eig (ComplexEmbedding.conjugate τ.1)).pull 𝔐.ξ 𝔐.f j p := by
  intro E _ _ _ H D l Xo c _ Y U Z S Ω _ K _ J _ y 𝔐 τ i j hT p hp
  obtain ⟨hd, hi, -, hpt⟩ := hT
  have hg' := 𝔐.tie.gen
  have hg := Z.gen
  haveI : CharZero Z.Ω := (RingHom.charZero_iff Z.inc.injective).1 inferInstance
  haveI : CharZero Ω := (RingHom.charZero_iff 𝔐.cst.injective).1 inferInstance
  have hq : ∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r p := fun r hr hf =>
    hf (by simpa using hp (r : ℤ) (by exact_mod_cast hr.ne_zero))
  have hcore : ∀ s, 𝔐.V s p = (Z.M.eigLat Z.ρ (Z.inc.comp (labelEmb c s))).pull 𝔐.ξ 𝔐.f j p := by
    intro s
    have h1 : 𝔐.V s p = 𝔐.M.eigLat 𝔐.ρ (𝔐.cst.comp (labelEmb c s)) p :=
      Lat.patch_of_not S _ _ fun r hr => hq r (𝔐.S_prime r hr)
    rw [h1, ← hi]
    exact eigLat_eq_pull c 𝔐.m Z.inc hg hg' hd Z.act 𝔐.act (isIntegrallyClosed_regAt Y.normal hg)
      (isIntegrallyClosed_regAt 𝔐.normal hg') hpt s p hq
  refine ⟨?_, ?_, ?_⟩
  · have hb : (Y.s (𝔐.f p.1)).asIdeal = ⊥ := by
      have := asIdeal_eq_bot hg' (𝔐.f ≫ Y.s) (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)) 𝔐.cst_over hp
      rwa [Scheme.Hom.comp_apply] at this
    refine ⟨⟨𝔐.f p.1, hd.specializes p⟩, ?_, rfl⟩
    show 𝔐.f p.1 ∈ Set.range (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F)))
    obtain ⟨w⟩ : Nonempty (Sp c.F) := inferInstance
    have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := IsFractionRing.injective _ _
    have e : Y.s (𝔐.f p.1) = spMap (algebraMap (𝓞 c.F) c.F) w := by
      refine PrimeSpectrum.ext ?_
      rw [hb]
      refine ((Submodule.eq_bot_iff _).2 fun o ho => ?_).symm
      have h1 : algebraMap (𝓞 c.F) c.F o ∈ w.asIdeal := ho
      by_contra h0
      have h2 : algebraMap (𝓞 c.F) c.F o ≠ 0 := fun e0 => h0 (hβ (by rw [e0, map_zero]))
      exact w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 (isUnit_iff_ne_zero.2 h2))
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback _ _ e
    exact ⟨z, hz⟩
  · rw [hcore, labelEmb_inl]
    rfl
  · rw [hcore, labelEmb_inr]
    rfl

end GlobalTheory.CompanionTheory.Ar.Flat.CptStalk
