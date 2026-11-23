import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ScaledTwistingSheafSpec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPullbackOfNormalFlatProj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemBasesNonempty
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ExistsGoodLevel

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam.Pad.BCEx

theorem isPullback_open {A T B : Scheme.{0}} (b : T ⟶ B) (jT : A ⟶ T) (jB : A ⟶ B)
    [IsOpenImmersion jT] [IsOpenImmersion jB] (w : jT ≫ b = jB) (hb : ∀ x, b x ∈ Set.range jB ↔ x ∈ Set.range jT) :
    IsPullback jT (𝟙 _) b jB :=
  (IsOpenImmersion.isPullback (𝟙 _) _ _ _ (w.trans (Category.id_comp _).symm) (by ext x; exact hb x)).flip

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {p : ℕ} {W : ValuationSubring ℂ}

section Local

variable {Xo : ∀ l : Level H, Moduli Dw l} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem exists_mdl (Z : Mdl Y i₀) [IsIso Z.π] {i : Idx H p} (hi : Z.i = i) {X' : Scheme.{0}} (f : X' ⟶ (Y i).X)
    (a : (Xo i.l).XF i.c ⟶ X') [IsOpenImmersion (Y i).j] (hp : IsPullback a (𝟙 _) f (Y i).j)
    (hs : IsProjOver (f ≫ (Y i).s)) (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X') (hf : Flat (f ≫ (Y i).s))
    (hd : Dense (Set.range a)) : ∃ (Z' : Mdl Y i₀) (h : Z'.i = i) (e : Z'.X ≅ X'), Z'.ty = Z.ty ∧
      Z'.π ≫ eqToHom (congrArg (fun j => (Y j).X) h) = e.hom ≫ f := by
  subst hi
  let U : Z.X.Opens := Z.π ⁻¹ᵁ (Y Z.i).j.opensRange
  have hU : (U : Set Z.X) = Z.opn := rfl
  let u : U.toScheme ≅ (Xo Z.i.l).XF Z.i.c := IsOpenImmersion.isoOfRangeEq (U.ι ≫ Z.π) (Y Z.i).j (by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι, hU]
    exact Set.image_preimage_eq _ Z.π.surjective)
  have hu : u.hom ≫ (Y Z.i).j = U.ι ≫ Z.π := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  obtain ⟨n, ι, hι, hs⟩ := hs
  have hiso : IsIso ι.toImage := inferInstance
  let e : ι.ker.subscheme ≅ X' := (asIso ι.toImage).symm
  have he : e.inv ≫ ι.ker.subschemeι = ι := ι.toImage_imageι
  have hp' : IsPullback (u.hom ≫ a ≫ e.inv) (𝟙 U.toScheme) (e.hom ≫ f ≫ inv Z.π) U.ι :=
    hp.of_iso u.symm e.symm u.symm (asIso Z.π).symm (by simp) (by simp) (by simp)
      (by simp [Iso.eq_inv_comp, ← Category.assoc, hu])
  have h₀ : (e.hom ≫ f ≫ inv Z.π) ≫ Z.s = e.hom ≫ f ≫ (Y Z.i).s := by
    rw [← Z.π_s]; simp
  have hs' : (e.hom ≫ f ≫ inv Z.π) ≫ Z.s = ι.ker.subschemeι ≫ PSpace.str _ n := by
    rw [h₀, ← hs, ← Category.assoc]
    congr 1
    exact ((Iso.inv_comp_eq e).1 he).symm
  have hn₀ := BaseMdl.normal_of_iso e.hom hn
  have hn' : GlobalTheory.IsNormalScheme ι.ker.subscheme := ⟨fun x => (hn₀ x).1, fun x => (hn₀ x).2⟩
  have hf' : Flat ((e.hom ≫ f ≫ inv Z.π) ≫ Z.s) := by rw [h₀]; infer_instance
  have hd' : Dense (Set.range (u.hom ≫ a ≫ e.inv)) := by
    have : DenseRange e.inv := e.inv.surjective.denseRange
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, u.hom.surjective.range_comp, Scheme.Hom.comp_base, TopCat.coe_comp]
    exact this.comp hd e.inv.continuous
  refine ⟨Recode.mdl Z ι.ker _ hU hp' hs' hn' hf' hd', rfl, e, rfl, (Category.comp_id _).trans ?_⟩
  change (e.hom ≫ f ≫ inv Z.π) ≫ Z.π = e.hom ≫ f
  simp

theorem compat (Z : Mdl Y i₀) {i : Idx H p} (hi : Z.i = i) {O : Type} [CommRing O] {X : Scheme.{0}} (s : X ⟶ Sp O)
    (j : (Xo i.l).XF i.c ⟶ X) (β : O → ℂ) (b : O →+* i.c.V W) (hb : ∀ x, (((b x : i.c.V W) : i.c.F) : ℂ) = β x)
    {X' : Scheme.{0}} (e : Z.X ≅ X') (f : X' ⟶ (Y i).X) (a : (Xo i.l).XF i.c ⟶ X') (hp : IsPullback a (𝟙 _) f (Y i).j)
    (hπ : Z.π ≫ eqToHom (congrArg (fun j => (Y j).X) hi) = e.hom ≫ f) (q : X' ⟶ pullback s (spMap b)) [IsIso q]
    (q₁ : a ≫ q ≫ pullback.fst _ _ = j) (q₂ : q ≫ pullback.snd _ _ = f ≫ (Y i).s) :
    ∃ (b' : O →+* Z.i.c.V W) (ν : Z.X ⟶ pullback s (spMap b')),
      (∀ x, (((b' x : Z.i.c.V W) : Z.i.c.F) : ℂ) = β x) ∧ IsFinite ν ∧ ν ≫ pullback.snd _ _ = Z.s ∧
      pullback.fst Z.π (Y Z.i).j ≫ ν ≫ pullback.fst _ _ =
        pullback.snd Z.π (Y Z.i).j ≫ eqToHom (congrArg (fun i : Idx H p => (Xo i.l).XF i.c) hi) ≫ j := by
  subst hi
  replace hπ : Z.π = e.hom ≫ f := (Category.comp_id _).symm.trans hπ
  refine ⟨b, e.hom ≫ q, hb, inferInstance, by rw [Category.assoc, q₂, ← Category.assoc, ← hπ, Z.π_s], ?_⟩
  have w : (pullback.fst Z.π (Y Z.i).j ≫ e.hom) ≫ f = pullback.snd Z.π (Y Z.i).j ≫ (Y Z.i).j := by
    rw [Category.assoc, ← hπ, pullback.condition]
  have h₁ := hp.lift_fst _ _ w
  have h₂ := hp.lift_snd _ _ w
  rw [Category.comp_id] at h₂
  rw [h₂] at h₁
  rw [eqToHom_refl, Category.id_comp, ← q₁, ← Category.assoc _ a, h₁]
  simp only [Category.assoc]

end Local

section Global

variable {l : Level H} {c : Coeff l}

theorem exists_isLocalization (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (b : 𝓞 c.F →+* c.V W)
    (hb : ∀ x, ((b x : c.V W) : c.F) = (x : c.F)) :
    ∃ M : Submonoid (𝓞 c.F), letI := b.toAlgebra; IsLocalization M (c.V W) := by
  haveI := c.fin
  haveI : NumberField c.F := {}
  obtain ⟨v, -, hv⟩ := GlobalModelGuards.exists_prime_eq c W p hp hW
  haveI hl : IsLocalization v.asIdeal.primeCompl (v.valuationSubringAtPrime c.F) :=
    Localization.subalgebra.isLocalization_ofField c.F v.asIdeal.primeCompl v.asIdeal.primeCompl_le_nonZeroDivisors
  letI := b.toAlgebra
  refine ⟨v.asIdeal.primeCompl, IsLocalization.isLocalization_of_algEquiv _ (S := v.valuationSubringAtPrime c.F)
    (AlgEquiv.ofRingEquiv (f := RingEquiv.subringCongr (congrArg ValuationSubring.toSubring hv)) fun x => ?_)⟩
  exact Subtype.ext (hb x).symm

variable {Xo : Moduli Dw l}

theorem normal_bc (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (b : 𝓞 c.F →+* c.V W) (hb : ∀ x, ((b x : c.V W) : c.F) = (x : c.F)) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (pullback Y.s (spMap b)) := by
  obtain ⟨M, hM⟩ := exists_isLocalization hp hW b hb
  letI := b.toAlgebra
  have h₁ : IsPreimmersion (spMap b) := IsPreimmersion.of_isLocalization (R := CommRingCat.of (𝓞 c.F)) (S := c.V W) M
  have h₂ : Flat (spMap b) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (c.V W) M)
  have : IsPreimmersion (pullback.fst Y.s (spMap b)) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip h₁
  intro x
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks (pullback.fst Y.s (spMap b)) x
  have i := (asIso ((pullback.fst Y.s (spMap b)).stalkMap x)).commRingCatIsoToRingEquiv
  obtain ⟨_, _⟩ := Y.normal (pullback.fst Y.s (spMap b) x)
  exact ⟨i.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv i⟩

theorem exists_map (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (Y' : Model Xo c (c.V W).subtype) (b : 𝓞 c.F →+* c.V W) (hb : ∀ x, ((b x : c.V W) : c.F) = (x : c.F))
    (h : Dominates Y Y' b) : ∃ (f : pullback Y.s (spMap b) ⟶ Y'.X) (a : Xo.XF c ⟶ pullback Y.s (spMap b)),
      f ≫ Y'.s = pullback.snd _ _ ∧ a ≫ pullback.fst _ _ = Y.j ∧ IsPullback a (𝟙 _) f Y'.j ∧ Dense (Set.range a) := by
  obtain ⟨f, t, m₁, m₂, hf, hj, -⟩ := h
  have hc : spMap (c.V W).subtype ≫ spMap b = spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [← spMap_comp]; exact congrArg spMap (RingHom.ext hb)
  let g : pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F)) ⟶ pullback Y.s (spMap b) :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap (c.V W).subtype)
      (by rw [Category.assoc, hc, pullback.condition])
  have g₁ : g ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have hg : IsPullback g (pullback.snd _ _) (pullback.snd _ _) (spMap (c.V W).subtype) :=
    IsPullback.of_right (by rw [g₁, hc]; exact IsPullback.of_hasPullback _ _) (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback _ _)
  have := c.fin
  have hV : (p : c.F) ∈ (c.V W).nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_or] at hW ⊢
    refine Or.inr fun h => hW.elim (Nat.cast_ne_zero.2 hp.ne_zero) fun h' => h' ?_
    have h2 : c.F.val.toRingHom (p : c.F)⁻¹ ∈ W := h
    simpa using h2
  have := BaseMdl.away_of_valuation c.F (c.V W) p hp hV
  have ho : IsOpenImmersion (spMap (c.V W).subtype) := IsOpenImmersion.of_isLocalization (S := c.F) ((p : ℕ) : c.V W)
  have : IsOpenImmersion g := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hg.flip ho
  have := Y.jQ_open
  have := BaseMdl.isOpenImmersion_j hp hW Y'
  have ha : (Y.jQ ≫ g) ≫ pullback.fst _ _ = Y.j := by rw [Category.assoc, g₁]; rfl
  have hgen : ∀ x, pullback.snd Y.s (spMap b) x ∈ Set.range (spMap (c.V W).subtype) → x ∈ Set.range g :=
    fun x ⟨z, hz⟩ => (Scheme.exists_preimage_of_isPullback hg x z hz.symm).imp fun _ h => h.1
  refine ⟨f, Y.jQ ≫ g, hf, ha, isPullback_open _ _ _ (hj _ ha) fun x => ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨z, hz⟩
    obtain ⟨y, rfl⟩ := hgen x ⟨pullback.snd Xo.s _ z, by
      rw [← Scheme.Hom.comp_apply, ← BaseMdl.j_s Y', Scheme.Hom.comp_apply, hz, ← Scheme.Hom.comp_apply, hf]⟩
    have h₁ : Y'.j z ∈ abLocus Y'.t.G := by
      have : Y'.jQ z ∈ pullback.fst Y'.s (spMap (c.V W).subtype) ⁻¹' abLocus Y'.t.G := Y'.ab_gen.ge ⟨z, rfl⟩
      rwa [Set.mem_preimage, ← Scheme.Hom.comp_apply] at this
    rw [hz] at h₁
    have h₂ := (abLocus_pullback abLocusOne Y.t.semi m₁.cart.1 _).2
      ((abLocus_pullback abLocusOne Y'.t.semi m₂.cart.1 _).1 h₁)
    rw [← Scheme.Hom.comp_apply, g₁] at h₂
    obtain ⟨w, rfl⟩ := Y.ab_gen.le h₂
    exact ⟨w, Scheme.Hom.comp_apply _ _ w⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, by rw [← Scheme.Hom.comp_apply, hj _ ha]⟩
  · have := Y.flat
    have h1 : DenseRange g := by
      intro x
      let q : Sp c.F := (⊥ : PrimeSpectrum c.F)
      have hs : spMap (c.V W).subtype q ⤳ pullback.snd Y.s (spMap b) x := by
        refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
        show Ideal.comap (c.V W).subtype ⊥ ≤ _
        rw [Ideal.comap_bot_of_injective _ Subtype.val_injective]
        exact bot_le
      obtain ⟨x', hx', e⟩ := Flat.generalizingMap (pullback.snd Y.s (spMap b)) hs
      refine closure_mono ?_ (specializes_iff_mem_closure.1 hx')
      exact Set.singleton_subset_iff.2 (hgen _ ⟨q, e.symm⟩)
    rw [Scheme.Hom.comp_base, TopCat.coe_comp]
    exact h1.comp Y.jQ_dense g.continuous

end Global

theorem exists_isBC {Xo : ∀ l : Level H, Moduli Dw l} {Y : LocFam Xo} {l : Level H} {c : Coeff l}
    {hg : ∀ p : ℕ, p.Prime → l.GoodAt p} (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Code Y c hg)
    (Z₀ : Mdl (Y p W hp hW) ⟨l, c, hg p hp⟩) (hi : Z₀.i = ⟨l, c, hg p hp⟩) [IsIso Z₀.π] (hty : ∀ σ, Z₀.ty σ = ∅) :
    ∃ Z', Z.IsBC (hp := hp) (hW := hW) Z' := by
  obtain ⟨Y', e, he, hd⟩ := Z.ex
  obtain ⟨b, hb, -⟩ := GlobalModelGuards.exists_incl c W
  obtain ⟨f, a, hf, ha, hP, hD⟩ := exists_map hp hW Y' _ b hb (hd p W hp hW b hb)
  have := BaseMdl.isOpenImmersion_j hp hW (Y p W hp hW ⟨l, c, hg p hp⟩)
  have := Y'.flat
  obtain ⟨Z', h, e', h₁, h₂⟩ := exists_mdl Z₀ hi f a hP
    (by rw [hf]; exact ProjSpace.isProjOver_pullback_snd b Y'.proj) (normal_bc hp hW Y' b hb)
    (by rw [hf]; infer_instance) hD
  let q : pullback Y'.s (spMap b) ⟶ pullback Z.s (spMap b) :=
    pullback.map _ _ _ _ e.hom (𝟙 _) (𝟙 _) (by rw [he.1, Category.comp_id]) (by simp)
  refine ⟨Z', h, fun σ => by rw [h₁, hty], compat Z' h Z.s Z.j (fun x => ((x : c.F) : ℂ)) b
    (fun x => congrArg _ (hb x)) e' f a hP h₂ q ?_ ?_⟩
  · rw [pullback.lift_fst, ← Category.assoc, ha, he.2]
  · rw [pullback.lift_snd, Category.comp_id, hf]

theorem exists_isBCAt : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (p : ℕ) (ct : At S κ p) (Z : CodeAt S κ), ∃ Z', IsBCAt ct Z Z' := by
  intro D A N j S κ p ct Z
  have := ct.B.iso none
  exact exists_isBC ct.hp ct.hW Z (ct.B.X none) (ct.B.lvl none) (ct.B.ty none)

end GlobalTheory.ShFam.Pad.BCEx
