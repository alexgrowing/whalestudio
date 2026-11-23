import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
import Development.AutomorphicArithmetic.DivisorFrames.FlagTorusGenericPoint
import Development.AutomorphicArithmetic.DivisorFrames.LevelFlagCompactPoint
import Development.AutomorphicArithmetic.DivisorFrames.LevelUnfoldingFlag
import Development.AutomorphicArithmetic.DivisorFrames.LevelUnfoldingMetric
import Development.AutomorphicArithmetic.DivisorFrames.LevelFlagMultiplicity
import Development.AutomorphicArithmetic.DivisorFrames.LevelPointCount
import Development.AutomorphicArithmetic.DivisorFrames.DegreeMatchingFamilies
import Development.AutomorphicArithmetic.DivisorFrames.GenericFibreOpenProjective
import Development.AutomorphicArithmetic.DivisorFrames.PointsGenericFibreComponents
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartCocycleHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimComponent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CardLiesOverEqIndex
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp
open scoped Classical

private theorem spread {X S Y : Scheme.{0}} [IsIntegral X] (V : X.Opens) (x : X) (hx : x ∈ V) (sV : V.toScheme ⟶ S)
    (sY : Y ⟶ S) [LocallyOfFiniteType sY] (q : Spec (X.presheaf.stalk x) ⟶ Y)
    (hq : q ≫ sY = V.fromSpecStalkOfMem x hx ≫ sV) :
    ∃ (U : X.Opens) (hU : x ∈ U) (k : U.toScheme ⟶ V.toScheme) (h : U.toScheme ⟶ Y), U ≤ V ∧ k ≫ V.ι = U.ι ∧
      U.fromSpecStalkOfMem x hU ≫ h = q ∧ h ≫ sY = k ≫ sV := by
  haveI : Nonempty V := ⟨⟨x, hx⟩⟩
  haveI : IsIntegral V.toScheme := inferInstance
  let x' : V.toScheme := ⟨x, hx⟩
  let σ : Spec (V.toScheme.presheaf.stalk x') ⟶ Spec (X.presheaf.stalk x) := Spec.map (V.ι.stalkMap x')
  haveI : IsIso σ := inferInstanceAs (IsIso (Spec.map (V.ι.stalkMap x')))
  have hσ : σ ≫ X.fromSpecStalk x = V.toScheme.fromSpecStalk x' ≫ V.ι :=
    Scheme.SpecMap_stalkMap_fromSpecStalk V.ι
  have hσ' : σ ≫ V.fromSpecStalkOfMem x hx = V.toScheme.fromSpecStalk x' := by
    rw [← cancel_mono V.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, hσ]
  obtain ⟨U', hU', h', h₁, h₂⟩ := spread_out_of_isGermInjective' sV sY (σ ≫ q)
    (by rw [Category.assoc, hq, reassoc_of% hσ'])
  let U : X.Opens := V.ι ''ᵁ U'
  have hU : x ∈ U := ⟨x', hU', rfl⟩
  let k : U.toScheme ⟶ U'.toScheme := IsOpenImmersion.lift (U'.ι ≫ V.ι) U.ι (by
    rintro _ ⟨⟨_, y, hy, rfl⟩, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩)
  have hk : k ≫ U'.ι ≫ V.ι = U.ι := IsOpenImmersion.lift_fac _ _ _
  refine ⟨U, hU, k ≫ U'.ι, k ≫ h', ?_, by rw [Category.assoc, hk], ?_, by rw [Category.assoc, h₂, Category.assoc]⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · have : σ ≫ U.fromSpecStalkOfMem x hU ≫ k = U'.fromSpecStalkOfMem x' hU' := by
      rw [← cancel_mono (U'.ι ≫ V.ι), Category.assoc, Category.assoc, hk, Scheme.Opens.fromSpecStalkOfMem_ι, hσ,
        Scheme.Opens.fromSpecStalkOfMem_ι_assoc]
    rw [← cancel_epi σ, reassoc_of% this, h₁]

section
open GlobalTheory.ShFam.Pad.Pull GlobalTheory.LieMet
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv actR)
open GlobalTheory.ConsGeo (Lev incl gpt)

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {O : Type} [CommRing O] {β : O →+* i₀.c.F}

private theorem exists_lev (Z : LocM.Mdl Y i₀) (T : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model (Xo i₀.l) i₀.c β)
    (hpq : 1 ≤ Dw.p + Dw.q) {τ : (Y Z.i).X ⟶ (Y i₀).X} {mu : SABMap (Y Z.i).t (Y i₀).t τ}
    (h : IsTrans i₀ Z.i τ mu) : ∃ (L : Lev Z T) (ν : SABMap (Y Z.i).oF.t (Y i₀).oF.t L.r),
      (Y Z.i).j ≫ τ = L.r ≫ (Y i₀).j ∧ ν.φ ≫ (Y i₀).m.φ = (Y Z.i).m.φ ≫ mu.φ ∧
      L.ν.φ ≫ T.m0.toSABMap.φ = ν.φ ≫ (Y i₀).m0.toSABMap.φ := by
  obtain ⟨b, r, ν, hb, hj, hs, hν, hl⟩ := GlobalTheory.LocM.Cocycle.exists_sab_of_isTrans h
  obtain ⟨π, hπ, hpb, -⟩ :=
    (GlobalTheory.LevelCompare.levelMaps_iff hpq).1 (GlobalTheory.moduliScheme_levelMaps_heckePoints.2 E H Dw hpq).1 _ _ Z.dvd
      (Xo i₀.l) (Xo Z.i.l)
  have w : (pullback.fst _ _ ≫ π : (Xo Z.i.l).XF Z.i.c ⟶ _) ≫ (Xo i₀.l).s =
      (pullback.snd _ _ ≫ spMap (incl Z)) ≫ spMap (IntermediateField.inclusion i₀.c.le).toRingHom := by
    rw [Category.assoc, hπ, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc,
      GlobalTheory.IndefiniteRowSideFullHecke.RelativeGroupHatForm.spMap_inclusion_comp]
    exact congrArg _ (GlobalTheory.IndefiniteRowSideFullHecke.RelativeGroupHatForm.spMap_inclusion_comp _ _).symm
  let r₀ : (Xo Z.i.l).XF Z.i.c ⟶ (Xo i₀.l).XF i₀.c := pullback.lift _ _ w
  have hr : r₀ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ π := pullback.lift_fst _ _ _
  have hr' : r₀ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (incl Z) := pullback.lift_snd _ _ _
  obtain ⟨m, hm⟩ := hpb
  obtain ⟨n, hn⟩ := LevelCover.sab_comp (Y Z.i).m0.toSABMap m hr.symm
  obtain ⟨ν₀, hν₀⟩ := LevelCover.sab_cancel (Y i₀).m0.toSABMap n r₀ rfl
  have hsnd : r ≫ pullback.snd _ _ = r₀ ≫ pullback.snd _ _ := by
    have := mono_spMap_subtype (i₀.c.V W)
    rw [hr', ← cancel_mono (spMap (i₀.c.V W).subtype), Category.assoc, Category.assoc,
      ← ModelRelProbe.j_over (Y i₀), ← reassoc_of% hj, hs, reassoc_of% ModelRelProbe.j_over (Y Z.i),
      ModelRelProbe.spMap_comp, ModelRelProbe.spMap_comp]
    congr 2
    ext x
    exact hb x
  have hS := TransitionUnique.isReduced_XF (Xo Z.i.l) Z.i.c
  have hrr : r = r₀ := TransitionUnique.map_unique (Y i₀) ν ν₀ hsnd
    (fun a => ⟨_, hl.1 a, LevelCover.sec_cancel ν₀ (Y i₀).m0.toSABMap _ _ (by
      rw [hν₀, hn, ← Category.assoc, LevelCover.sec_pow _ _ _ ((Y Z.i).m0.eta a), Category.assoc, hm.1 a,
        (Y i₀).m0.eta a, reassoc_of% hr])⟩)
    (fun a => ⟨_, hl.2 a, LevelCover.sec_cancel ν₀ (Y i₀).m0.toSABMap _ _ (by
      rw [hν₀, hn, ← Category.assoc, LevelCover.sec_pow _ _ _ ((Y Z.i).m0.etaA a), Category.assoc, hm.2 a,
        (Y i₀).m0.etaA a, reassoc_of% hr])⟩)
  subst hrr
  obtain ⟨n', hn'⟩ := LevelCover.sab_comp ν (Y i₀).m0.toSABMap rfl
  obtain ⟨ν', hν'⟩ := LevelCover.sab_cancel T.m0.toSABMap n' r₀ rfl
  exact ⟨⟨r₀, ν', hr', π, hπ, ⟨m, hm⟩, hr⟩, ν, hj, hν, hν'.trans hn'⟩

set_option maxHeartbeats 1000000 in

private theorem generic_match (Z : LocM.Mdl Y i₀) [IsDiscreteValuationRing (Z.i.c.V W)]
    {T : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model (Xo i₀.l) i₀.c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* i₀.c.F}
    {σ : i₀.c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf (Xo i₀.l) i₀.c σ N} (Φ : FlagTor T e U) (L : Lev Z T)
    (hpq : 1 ≤ Dw.p + Dw.q) (hfull : ∀ τ k, k ≤ Dw.mult τ → k ∈ Z.ty τ) (d : ℕ)
    (hZ : ∀ C, ((nmodel Z).comp C).relDim = d) (hΦ : ∀ c, (Φ.C c).Y.dim = d)
    (hgen : ∀ C, (nmodel Z).compι C (genericPoint _) ∈ Z.opn) (hopn : Z.opn ⊆ (nmodel Z).gen)
    (C : (nmodel Z).Comp) :
    ∃ (c : U.Comp) (θ : (Φ.C c).Y.X.functionField →+* ((nmodel Z).comp C).X.functionField),
      ConsGeo.Match L (Φ.C c) (gpt _ ≫ (nmodel Z).compι C) (spMap θ ≫ gpt _) := by
  haveI := Z.i.c.fin
  haveI := i₀.c.fin
  have hG := fun C : (nmodel Z).Comp => UpperTheory.generic_fibre_open_projective (Z.i.c.V W) Z.i.c.F ((nmodel Z).comp C)
  choose hI hO hR hP hD ε hε using hG
  let X : (nmodel Z).Comp → Scheme.{0} := fun C => ((nmodel Z).comp C).toBase.genFibre
  let ι : ∀ C, X C ⟶ Z.X := fun C => ((nmodel Z).comp C).toBase.genFibreι ≫ (nmodel Z).compι C
  let sX : ∀ C, X C ⟶ Sp F := fun C => ((nmodel Z).comp C).toBase.genFibreStr ≫
    spMap ((ε C).toRingHom.comp ((incl Z).comp e.toRingHom))
  haveI : ∀ C, IsIntegral (X C) := hI
  have hfin : (incl Z).Finite := RingHom.Finite.of_comp_finite (f := algebraMap ℚ i₀.c.F) (by
    rw [Subsingleton.elim ((incl Z).comp (algebraMap ℚ i₀.c.F)) (algebraMap ℚ Z.i.c.F)]
    exact RingHom.finite_algebraMap.2 inferInstance)
  haveI : ∀ C, LocallyOfFiniteType (sX C) := fun C => by
    haveI := (isProper_and_exists_isAmpleLB_of_isProjOver (hP C)).1
    haveI : LocallyOfFiniteType (spMap ((ε C).toRingHom.comp ((incl Z).comp e.toRingHom))) :=
      (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2
        ((RingHom.Finite.comp (RingHom.Finite.of_surjective _ (ε C).surjective)
          (RingHom.Finite.comp hfin (RingHom.Finite.of_surjective _ e.surjective))).finiteType)
    exact inferInstanceAs (LocallyOfFiniteType (_ ≫ _))
  have hgp : ∀ C, ((nmodel Z).comp C).toBase.genFibreι (genericPoint (X C)) = genericPoint _ := fun C =>
    haveI := hO C
    genericPoint_eq_of_isOpenImmersion _
  have hcl : ∀ {k : Type} [Field k] (x : Sp k), x = closedPoint k := fun x => Subsingleton.elim (α := PrimeSpectrum _) _ _
  have hpos : 0 < ConsGeo.embDeg (incl Z) := by
    letI := (incl Z).toAlgebra
    haveI : Module.Finite i₀.c.F Z.i.c.F := hfin
    exact Module.finrank_pos
  obtain ⟨b, θ, hb, -⟩ := UpperTheory.degree_matching_families F (i₀.c.F.val.toRingHom.comp e.toRingHom) (nmodel Z).Comp U.Comp X
    (fun c => (Φ.C c).Y.X) sX (fun c => (Φ.C c).Y.str) d
    (levDeg Z.dvd (Xo i₀.l) i₀.c (Xo Z.i.l) Z.i.c * ConsGeo.embDeg (incl Z))
    (fun C => ι C ⁻¹' Z.opn) (fun c => (Φ.C c).π ⁻¹' Set.range T.jQ)
    (fun k _ C c w q => ConsGeo.Match L (Φ.C c) (w ≫ ι C) q)
    (fun C => (hD C).trans (by rw [hZ])) (fun c => by rw [Var.topologicalKrullDim_eq, hΦ])
    (Nat.mul_pos (levDeg_pos _ _ _ _ _) hpos)
    (fun C => by
      change ι C _ ∈ Z.opn
      rw [Scheme.Hom.comp_apply, hgp]
      exact hgen C)
    (fun c => by
      have h := congrArg (fun u => u (closedPoint _)) (Φ.C c).y0_x
      exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm.trans (h.trans ((Scheme.Hom.comp_apply _ _ _).trans
        (congrArg (Φ.C c).π Scheme.fromSpecStalk_closedPoint)))⟩)
    (fun k _ C c w q h => by
      obtain ⟨h₁, h₂, ⟨f, h₃, h₄⟩, -⟩ := UpperTheory.level_flag_compact_point L (Φ.C c) _ q h
      refine ⟨?_, h₁, h₂⟩
      have := mono_spMap_subtype (Z.i.c.V W)
      have h₅ : w ≫ ((nmodel Z).comp C).toBase.genFibreStr ≫ spMap (ε C).toRingHom = spMap f := by
        rw [← cancel_mono (spMap (Z.i.c.V W).subtype), ← h₃, Category.assoc, Category.assoc, Category.assoc]
        exact congrArg (w ≫ ·) ((hε C).trans (Category.assoc _ _ _).symm)
      rw [← (Φ.C c).π_str, reassoc_of% h₄, ← h₅]
      simp only [sX, ← ModelRelProbe.spMap_comp, Category.assoc])
    (fun k _ C w hw => UpperTheory.level_unfolding_flag Φ L _ hw)
    (fun k _ C c c' w q q' h h' => UpperTheory.level_unfolding_metric Φ L hfull _ c c' q q' h h')
    (fun k k' _ _ ψ C c w q h => by
      rw [Category.assoc]
      exact (UpperTheory.level_flag_compact_point L (Φ.C c) _ q h).2.2.2 k' ψ)
    (fun c q hq hQ => by
      haveI := T.jQ_open
      let y := IsOpenImmersion.lift T.jQ (q ≫ (Φ.C c).π) (by
        rintro _ ⟨x, rfl⟩
        rw [hcl x]
        exact hQ)
      have hy : q ≫ (Φ.C c).π = y ≫ T.jQ := (IsOpenImmersion.lift_fac _ _ _).symm
      have hys : y ≫ pullback.snd _ _ = spMap i₀.c.F.val.toRingHom := by
        have h1 : T.jQ ≫ genStr T = pullback.snd _ _ := T.jQ_over
        haveI : IsIso (spMap e.toRingHom) := inferInstanceAs (IsIso (Spec.map e.toCommRingCatIso.hom))
        rw [← cancel_mono (spMap e.toRingHom), ← h1, Category.assoc, Category.assoc, ← reassoc_of% hy, (Φ.C c).π_str, hq,
          ModelRelProbe.spMap_comp]
      obtain ⟨e₁⟩ := UpperTheory.level_flag_multiplicity L (Φ.C c) hfull q y hy
      rw [← UpperTheory.level_point_count L hpq ⟨y, hys⟩, ← Nat.card_congr e₁]
      obtain ⟨hinj, hsurj⟩ := UpperTheory.points_generic_fibre_components _ (nmodel Z) ℂ
      refine Nat.card_eq_of_bijective (fun w => ⟨w.1.2 ≫ ι w.1.1, w.2⟩)
        ⟨fun w w' h => Subtype.ext (hinj (congrArg Subtype.val h)), fun w => ?_⟩
      obtain ⟨C, w', hw⟩ := hsurj w.1 (hopn (UpperTheory.level_flag_compact_point L (Φ.C c) _ q w.2).1)
      exact ⟨⟨⟨C, w'⟩, by
        change ConsGeo.Match L (Φ.C c) (w' ≫ _ ≫ _) q
        rw [hw]; exact w.2⟩, Subtype.ext hw⟩)
  haveI := hO C
  obtain ⟨ρ, hρ⟩ : ∃ ρ : (X C).functionField →+* ((nmodel Z).comp C).X.functionField,
      spMap ρ ≫ gpt (X C) ≫ ((nmodel Z).comp C).toBase.genFibreι = gpt _ := by
    have key : ∀ {A B : Scheme.{0}} (j : A ⟶ B) [IsOpenImmersion j] (x : A) (y : B), j x = y →
        ∃ ρ : A.presheaf.stalk x ⟶ B.presheaf.stalk y, Spec.map ρ ≫ A.fromSpecStalk x ≫ j = B.fromSpecStalk y := by
      rintro A B j _ x _ rfl
      exact ⟨inv (j.stalkMap x), by
        rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id,
          Category.id_comp]⟩
    obtain ⟨ρ, hρ⟩ := key _ _ _ (hgp C)
    exact ⟨ρ.hom, hρ⟩
  refine ⟨b C, ρ.comp (θ C), ?_⟩
  have := (UpperTheory.level_flag_compact_point L (Φ.C (b C)) _ _ (hb C)).2.2.2 _ ρ
  rwa [← Category.assoc (spMap ρ) (spMap _), ModelRelProbe.spMap_comp, reassoc_of% hρ] at this

private theorem frame_pull {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {l : Level H} {c : Coeff l}
    {g : X' ⟶ X} (mu : SABMap t' t g) {R : Type} [CommRing R] {x' : Sp R ⟶ X'} {x : Sp R ⟶ X} (hx : x' ≫ g = x)
    {f : c.F →+* R} {u : Vecs Dw t R} (h : GlobalTheory.LocM.IsFrame t f x u) :
    ∃ v : Vecs Dw t' R, GlobalTheory.LocM.IsFrame t' f x' v ∧ ∀ τ i, v τ i ≫ mu.φ = u τ i := by
  have ex : ∀ τ i, ∃ V : TanM x' t'.G, pushE mu x' hx V = tanOf (h.1 τ i).1 := fun τ i =>
    (pushE mu x' hx).surjective _
  choose V hV using ex
  have e : ∀ τ i, (tv (V τ i)).left ≫ mu.φ = u τ i := fun τ i => congrArg (fun z => (tv z).left) (hV τ i)
  refine ⟨fun τ i => (tv (V τ i)).left, ⟨fun τ i => ⟨isTan_tv _, fun a => ?_⟩, fun τ w hw he => ?_⟩, e⟩
  · refine (eig_iff (V τ i) a _).2 ((pushE mu x' hx).injective ?_)
    rw [pushE_act, map_smul, hV]
    exact (eig_iff _ a _).1 ((h.1 τ i).2 a)
  · have := h.2 τ (w ≫ mu.φ) (isTan_push mu x' hx hw) fun a => by
      rw [Category.assoc, ← mu.act, ← Category.assoc, he, Category.assoc]
    refine (existsUnique_congr fun cf => comb_push mu hx (fun i => isTan_tv (V τ i)) hw cf).1 ?_
    simpa only [e] using this

private theorem link_of_match {Z : LocM.Mdl Y i₀} {T : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model (Xo i₀.l) i₀.c β} {F : Type} [Field F]
    {e : F ≃+* i₀.c.F} {σ : i₀.c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf (Xo i₀.l) i₀.c σ N} (Φ : FlagTor T e U)
    (L : Lev Z T) (hfull : ∀ τ k, k ≤ Dw.mult τ → k ∈ Z.ty τ) {τ : (Y Z.i).X ⟶ (Y i₀).X}
    {mu : SABMap (Y Z.i).t (Y i₀).t τ} {ν : SABMap (Y Z.i).oF.t (Y i₀).oF.t L.r}
    (hν : ν.φ ≫ (Y i₀).m.φ = (Y Z.i).m.φ ≫ mu.φ)
    (hν' : L.ν.φ ≫ T.m0.toSABMap.φ = ν.φ ≫ (Y i₀).m0.toSABMap.φ) {k : Type} [Field k] {w : Sp k ⟶ Z.X} {a : Fin Z.m}
    {φ : Γ(Z.X, (Z.U a).1) →+* k} (hφ : spMap φ ≫ Z.chart a = w) {y : Sp k ⟶ (Xo Z.i.l).XF Z.i.c}
    (hy : y ≫ (Y Z.i).j = w ≫ Z.π) {c : U.Comp} {q : Sp k ⟶ (Φ.C c).Y.X} (hM : ConsGeo.Match L (Φ.C c) w q) :
    q ≫ (Φ.C c).π = y ≫ L.r ≫ T.jQ ∧ y ≫ pullback.snd _ _ = spMap (φ.comp (Z.alg a)) ∧
      ∃ (f : i₀.c.F →+* k) (g : EigFrame T f (q ≫ (Φ.C c).π ≫ genι T)),
      (∀ σ i, Transp T (Y i₀) (y ≫ L.r) (g.v σ i) ((Z.fr a).bc φ σ i ≫ mu.φ)) ∧ (Φ.C c).Carries q g := by
  have hys : y ≫ pullback.snd _ _ = spMap (φ.comp (Z.alg a)) := by
    have := mono_spMap_subtype (Z.i.c.V W)
    have hjs : (Y Z.i).j ≫ (Y Z.i).s = pullback.snd _ _ ≫ spMap (Z.i.c.V W).subtype := by
      unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j
      rw [Category.assoc, pullback.condition, ← Category.assoc, (Y Z.i).jQ_over]
    rw [← cancel_mono (spMap (Z.i.c.V W).subtype), Category.assoc, ← hjs, reassoc_of% hy, affineOpenChart_comp_structure_eq_spMap Z hφ]
  have hu := chart_frame Z hφ
  obtain ⟨v, hv, hvu⟩ := frame_pull (Y Z.i).m hy hu
  let φ' : i₀.c.F →+* k := (φ.comp (Z.alg a)).comp (incl Z)
  have h1 := frame_push (c := i₀.c) (f := φ') L.ν (x := y ≫ L.r) rfl (fun τ x => rfl) hv
  have h2 := frame_push (c := i₀.c) (f := φ') T.m (x := (y ≫ L.r ≫ T.jQ) ≫ genι T)
    (by simp only [Category.assoc]) (fun τ x => rfl) h1
  have hx : (y ≫ L.r ≫ T.jQ) ≫ genStr T = spMap φ' := by
    have : T.jQ ≫ genStr T = pullback.snd _ _ := T.jQ_over
    rw [Category.assoc, Category.assoc, this, L.snd, reassoc_of% hys, ModelRelProbe.spMap_comp]
  let g : EigFrame T φ' ((y ≫ L.r ≫ T.jQ) ≫ genι T) :=
    ⟨_, fun τ i => (h2.1 τ i).1, fun τ i => (h2.1 τ i).2, h2.2⟩
  obtain ⟨⟨c', q'⟩, ⟨hq, hC⟩, -⟩ := UpperTheory.flag_torus_generic_point Φ k φ' _ hx g
  have tr : ∀ (x x' : Sp k ⟶ T.X) (g : EigFrame T φ' x), x' = x → (Φ.C c').Carries q' g →
      ∃ g' : EigFrame T φ' x', (Φ.C c').Carries q' g' ∧ g'.v = g.v := by
    rintro x _ g rfl h
    exact ⟨g, h, rfl⟩
  obtain ⟨g', hg', hgv⟩ := tr _ (q' ≫ (Φ.C c').π ≫ genι T) g (by rw [← Category.assoc]; exact congrArg (· ≫ genι T) hq) hC
  have huv : (fun τ i => v τ i ≫ (Y Z.i).m.φ) = (Z.fr a).bc φ := funext fun τ => funext fun i => hvu τ i
  have hM' : ConsGeo.Match L (Φ.C c') w q' := by
    refine ⟨y, v, φ', g', hy.symm, hq, fun τ i => (hv.1 τ i).1, ?_, hg', fun τ i => ?_⟩
    · rw [huv]
      refine ⟨a, φ, hφ, hu, fun τ n _ i hi => ⟨Pi.single i 1, fun j hj => Pi.single_eq_of_ne ?_ _,
        isCombAtG_single _ _ (fun j => (hu.1 τ j).1) i⟩⟩
      rintro rfl
      omega
    · rw [hgv]
      exact Category.assoc _ _ _
  have key := UpperTheory.level_unfolding_metric Φ L hfull w c c' q q' hM hM'
  obtain ⟨rfl, hqq⟩ := Sigma.mk.inj_iff.1 key
  obtain rfl := eq_of_heq hqq
  refine ⟨hq, hys, φ', g', fun σ i => ⟨v σ i ≫ L.ν.φ, v σ i ≫ ν.φ, (isTan_push L.ν y rfl (hv.1 σ i).1).1,
    (isTan_push ν y rfl (hv.1 σ i).1).1, by rw [Category.assoc, hν', Category.assoc], by rw [hgv], ?_⟩, hg'⟩
  rw [Category.assoc, hν, reassoc_of% hvu σ i]

set_option maxHeartbeats 400000 in

private theorem exists_link (Z : LocM.Mdl Y i₀) [IsDiscreteValuationRing (Z.i.c.V W)]
    {T : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model (Xo i₀.l) i₀.c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* i₀.c.F}
    {σ : i₀.c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf (Xo i₀.l) i₀.c σ N} (Φ : FlagTor T e U)
    {τ : (Y Z.i).X ⟶ (Y i₀).X} {mu : SABMap (Y Z.i).t (Y i₀).t τ} (hT : IsTrans i₀ Z.i τ mu)
    (hpq : 1 ≤ Dw.p + Dw.q) (hfull : ∀ τ k, k ≤ Dw.mult τ → k ∈ Z.ty τ) (d : ℕ)
    (hZ : ∀ C, ((nmodel Z).comp C).relDim = d) (hΦ : ∀ c, (Φ.C c).Y.dim = d)
    (hopn : ∀ a, (Z.U a).1 ≤ (nmodel Z).gen) (b : 𝓞 F →+* Z.i.c.V W)
    (hb : ∀ x : 𝓞 F, ((b x : Z.i.c.V W) : Z.i.c.F) = incl Z (e x)) (C : (nmodel Z).Comp) :
    ∃ (c : U.Comp) (μ : Match (Φ.C c).Y b ((nmodel Z).comp C)), Link Z C (Φ.C c) μ := by
  obtain ⟨L, ν, hj, hν, hν'⟩ := exists_lev Z T hpq hT
  have hopen : IsOpen Z.opn := Z.cover ▸ isOpen_iUnion fun a => (Z.U a).1.isOpen
  have hgen : ∀ C, (nmodel Z).compι C (genericPoint _) ∈ Z.opn := fun C => by
    obtain ⟨x, hxC, hxo⟩ := Z.dense.inter_open_nonempty _ C.opens.isOpen C.2.1.nonempty
    exact ((genericPoint_specializes (show ((nmodel Z).comp C).X from ⟨x, hxC⟩)).map
      ((nmodel Z).compι C).continuous).mem_open hopen hxo
  obtain ⟨c, θ, hM⟩ := generic_match Z Φ L hpq hfull d hZ hΦ hgen
    (Z.cover ▸ Set.iUnion_subset hopn) C
  obtain ⟨a, ha⟩ := Set.mem_iUnion.1 (Z.cover.ge (hgen C))
  let V : ((nmodel Z).comp C).X.Opens := (nmodel Z).compι C ⁻¹ᵁ (Z.U a).1
  have hV : genericPoint _ ∈ V := ha
  haveI : IsOpenImmersion (Z.chart a) := IsAffineOpen.isOpenImmersion_fromSpec (Z.U a).2
  let ρ : V.toScheme ⟶ Sp Γ(Z.X, (Z.U a).1) :=
    IsOpenImmersion.lift (Z.chart a) (V.ι ≫ (nmodel Z).compι C) (by
      rintro _ ⟨x, rfl⟩
      rw [show Set.range (Z.chart a) = _ from (Z.U a).2.range_fromSpec]
      exact x.2)
  have hρ : ρ ≫ Z.chart a = V.ι ≫ (nmodel Z).compι C := IsOpenImmersion.lift_fac _ _ _
  have hid : spMap (RingHom.id _) ≫ Z.chart a = Z.chart a := by
    rw [LevelCover.spMap_id', Category.id_comp]
  obtain ⟨y₁, hy₁⟩ := Pull.exists_open_lift Z hid
  let ψ : Γ(Z.X, (Z.U a).1) →+* ((nmodel Z).comp C).X.functionField :=
    (Spec.preimage (V.fromSpecStalkOfMem _ hV ≫ ρ)).hom
  have hψ : spMap ψ = V.fromSpecStalkOfMem _ hV ≫ ρ := Spec.map_preimage _
  have hψ' : spMap ψ ≫ Z.chart a = ConsGeo.gpt _ ≫ (nmodel Z).compι C := by
    rw [hψ, Category.assoc, hρ, Scheme.Opens.fromSpecStalkOfMem_ι_assoc]
  obtain ⟨hq, -, f, g, hTr, hC⟩ := link_of_match Φ L hfull hν hν' hψ' (y := spMap ψ ≫ y₁)
    (by rw [Category.assoc, hy₁, reassoc_of% hψ', Category.assoc]) hM
  haveI : LocallyOfFiniteType ((Φ.C c).π ≫ genStr T ≫ spMap e.toRingHom) := by
    rw [(Φ.C c).π_str]
    infer_instance
  haveI : LocallyOfFiniteType (Φ.C c).π :=
    locallyOfFiniteType_of_comp _ (genStr T ≫ spMap e.toRingHom)
  obtain ⟨U', hU, k, h, hUV, hk, hh, hh'⟩ := spread V _ hV (ρ ≫ y₁ ≫ L.r ≫ T.jQ) (Φ.C c).π
    (spMap θ ≫ ConsGeo.gpt _) (hq.trans (by rw [hψ]; simp only [Category.assoc]))
  have hy₁s : y₁ ≫ pullback.snd _ _ = spMap (Z.alg a) := by
    have := mono_spMap_subtype (Z.i.c.V W)
    rw [← cancel_mono (spMap (Z.i.c.V W).subtype), Category.assoc, ← ModelRelProbe.j_over, reassoc_of% hy₁,
      Pull.affineOpenChart_comp_structure_eq_spMap Z hid, RingHom.id_comp]
  have hkU : U'.fromSpecStalkOfMem _ hU ≫ k = V.fromSpecStalkOfMem _ hV := by
    rw [← cancel_mono V.ι, Category.assoc, hk, Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.Opens.fromSpecStalkOfMem_ι]
  have hstr : h ≫ (Φ.C c).Y.str ≫ spMap (algebraMap (𝓞 F) F) =
      U'.ι ≫ ((nmodel Z).comp C).str ≫ spMap b := by
    have h1 : T.jQ ≫ genStr T = pullback.snd _ _ := T.jQ_over
    have h2 : U'.ι ≫ ((nmodel Z).comp C).str = k ≫ ρ ≫ Z.chart a ≫ Z.s := by
      rw [reassoc_of% hρ, reassoc_of% hk]
      rfl
    rw [← (Φ.C c).π_str, Category.assoc, reassoc_of% hh', Category.assoc, reassoc_of% h1, reassoc_of% L.snd,
      reassoc_of% hy₁s, reassoc_of% h2, reassoc_of% Z.alg_s]
    simp only [ModelRelProbe.spMap_comp]
    congr 3
    refine RingHom.ext fun x => congrArg (Z.alg a) ?_
    exact (hb x).symm
  have hy : U'.fromSpecStalkOfMem _ hU ≫ k ≫ ρ ≫ y₁ ≫ L.r = (spMap ψ ≫ y₁) ≫ L.r := by
    rw [reassoc_of% hkU, hψ]; simp only [Category.assoc]
  have key : ∀ (q' : Sp ((nmodel Z).comp C).X.functionField ⟶ (Φ.C c).Y.X)
      (y' : Sp ((nmodel Z).comp C).X.functionField ⟶ (Xo i₀.l).XF i₀.c), q' = spMap θ ≫ ConsGeo.gpt _ →
      y' = (spMap ψ ≫ y₁) ≫ L.r → ∃ g : EigFrame T f (q' ≫ (Φ.C c).π ≫ genι T),
        (∀ σ i, Transp T (Y i₀) y' (g.v σ i) ((Z.fr a).bc ψ σ i ≫ mu.φ)) ∧ (Φ.C c).Carries q' g := by
    rintro _ _ rfl rfl
    exact ⟨g, hTr, hC⟩
  obtain ⟨g', hTr', hC'⟩ := key _ _ hh hy
  have e₁ : (k ≫ ρ ≫ y₁ ≫ L.r) ≫ (Y i₀).j = U'.ι ≫ (nmodel Z).compι C ≫ Z.π ≫ τ := by
    simp only [Category.assoc]
    rw [← hj, reassoc_of% hy₁, reassoc_of% hρ, reassoc_of% hk]
  have e₂ : (k ≫ ρ ≫ y₁ ≫ L.r) ≫ T.jQ = h ≫ (Φ.C c).π := by
    rw [hh']; simp only [Category.assoc]
  exact ⟨c, ⟨U', hU, h, hstr, θ, hh⟩, a, τ, mu, k ≫ ρ ≫ y₁ ≫ L.r, ψ, f, g', hUV, hT, e₁, e₂, hψ', hTr', hC'⟩

end

theorem UpperTheory.admissible_point_discrete_valuation :
    ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (fl : s.Flag), (∀ k, (fl.C k).Y.dim = Formalism.DegreeFormula.dimFl D.what₂.Tau N) → ∀ (p : ℕ) (hp : p.Prime) (W : ValuationSubring ℂ) (hW : (p : ℂ) ∈ W.nonunits) (z : AdmAt S κ hp hW) [IsDiscreteValuationRing (z.Z.i.c.V W)] (ε : D.what₂.LL →+* z.Z.i.c.F) (b : 𝓞 D.what₂.LL →+* z.Z.i.c.V W), (∀ x, ((ε x : z.Z.i.c.F) : ℂ) = D.what₂.embLL x) → (∀ x : 𝓞 D.what₂.LL, ((b x : z.Z.i.c.V W) : z.Z.i.c.F) = ε (x : D.what₂.LL)) → ∀ C : (nmodel z.Z).Comp, ∃ (c : s.Comp) (μ : Match (fl.C c).Y b ((nmodel z.Z).comp C)), Link z.Z C (fl.C c) μ := by
  intro D A N j S κ s fl hdim p hp W hW z _ ε b hε hb C
  have hpq : 1 ≤ S.Dw.p + S.Dw.q := (one_le_two.trans S.two_le).trans S.rank_eq.ge
  obtain ⟨τ, mu, hT⟩ := Pull.exists_trans (S.sys.clauses p W hp hW).1 z.Z.dvd z.Z.le
  exact exists_link z.Z fl hT hpq z.full _ (RelDim.relDim_comp D A N j S κ p hp W hW z) hdim
    (fun a => chart_le_gen hp hW a) b
    (fun x => Subtype.ext ((congrArg Subtype.val (hb x)).trans ((hε x).trans (κ.e_emb x).symm))) C
