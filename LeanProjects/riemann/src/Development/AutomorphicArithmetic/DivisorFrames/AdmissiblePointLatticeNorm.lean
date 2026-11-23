import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
import Development.AutomorphicArithmetic.DivisorFrames.AdmissiblePointDiscreteValuation
import Development.AutomorphicArithmetic.DivisorFrames.ExistsLevelAbelianMaps
import Development.AutomorphicArithmetic.DivisorFrames.LevelFlagCompactTangent
import Development.AutomorphicArithmetic.DivisorFrames.AdmissibleLevelMatch
import Development.AutomorphicArithmetic.DivisorFrames.LevelUnfoldingMetric
import Development.AutomorphicArithmetic.DivisorFrames.LevelFlagCompactPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsClosedImmersionBaseChange
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp
open scoped Classical

section
open GlobalTheory.ShFam.Pad.Pull GlobalTheory.LieMet MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv actR)

attribute [local instance] Over.cartesianMonoidalCategory

private theorem frame_pull {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {l : Level H} {c : Coeff l}
    {g : X' ⟶ X} (mu : SABMap t' t g) {R : Type} [CommRing R] {x' : Sp R ⟶ X'} {x : Sp R ⟶ X} (hx : x' ≫ g = x)
    {f : c.F →+* R} {u : Vecs Dw t R} (h : GlobalTheory.LocM.IsFrame t f x u) :
    ∃ v : Vecs Dw t' R, (∀ τ i, IsTanAtG t' x' (v τ i)) ∧ ∀ τ i, v τ i ≫ mu.φ = u τ i := by
  have ex : ∀ τ i, ∃ V : TanM x' t'.G, pushE mu x' hx V = tanOf (h.1 τ i).1 := fun τ i =>
    (pushE mu x' hx).surjective _
  choose V hV using ex
  exact ⟨fun τ i => (tv (V τ i)).left, fun τ i => isTan_tv _, fun τ i => congrArg (fun z => (tv z).left) (hV τ i)⟩

end

private theorem mono_j {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} (Y : LocalSystem Xo p W)
    (i : Idx H p) : Mono (Y i).j := by
  have := mono_spMap_subtype (i.c.V W)
  have := (Y i).jQ_open
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j; infer_instance

private theorem sab_w {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) :
    m.φ ≫ t.G.hom = t'.G.hom ≫ f := m.cart.1.w

private theorem sab_ext {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {S S' A : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) {a b : A ⟶ t'.G.left}
    (h₁ : a ≫ m.φ = b ≫ m.φ) (h₂ : a ≫ t'.G.hom = b ≫ t'.G.hom) : a = b := m.cart.1.hom_ext h₁ h₂

private theorem match_core {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W}
    {i₀ : Idx H p} {O : Type} [CommRing O] {β : O →+* i₀.c.F} {Z : LocM.Mdl Y i₀}
    {T : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model (Xo i₀.l) i₀.c β} (L : GlobalTheory.ConsGeo.Lev Z T)
    {τ : (Y Z.i).X ⟶ (Y i₀).X} {mu : SABMap (Y Z.i).t (Y i₀).t τ} (hr : (Y Z.i).j ≫ τ = L.r ≫ (Y i₀).j)
    {ν₂ : SABMap (Y Z.i).oF.t (Y i₀).oF.t L.r} (hν1 : ν₂.φ ≫ (Y i₀).m.φ = (Y Z.i).m.φ ≫ mu.φ)
    (hν2 : ν₂.φ ≫ (Y i₀).m0.toSABMap.φ = L.ν.φ ≫ T.m0.toSABMap.φ)
    {F : Type} [Field F] {e : F ≃+* i₀.c.F} {Φ : FlagCpt T e} {K : Type} [Field K] {w : Sp K ⟶ Z.X}
    {q : Sp K ⟶ Φ.Y.X} {y : Sp K ⟶ (Xo i₀.l).XF i₀.c} {a : Fin Z.m} {ψ : Γ(Z.X, (Z.U a).1) →+* K}
    {f : i₀.c.F →+* K} {g : EigFrame T f (q ≫ Φ.π ≫ genι T)} (hy1 : y ≫ (Y i₀).j = w ≫ Z.π ≫ τ)
    (hy2 : y ≫ T.jQ = q ≫ Φ.π) (hψ : spMap ψ ≫ Z.chart a = w)
    (htr : ∀ σ i, Transp T (Y i₀) y (g.v σ i) ((Z.fr a).bc ψ σ i ≫ mu.φ)) (hc : Φ.Carries q g) :
    GlobalTheory.ConsGeo.Match L Φ w q := by
  obtain ⟨y₂, hy₂⟩ := Pull.exists_open_lift Z hψ
  have hu := Pull.chart_frame Z hψ
  obtain ⟨v, hv, hvu⟩ := frame_pull (Y Z.i).m hy₂ hu
  have hyy : y₂ ≫ L.r = y := by
    have := mono_j Y i₀
    rw [← cancel_mono (Y i₀).j, Category.assoc, ← hr, reassoc_of% hy₂, hy1]
  have huv : (fun τ i => v τ i ≫ (Y Z.i).m.φ) = (Z.fr a).bc ψ := funext fun τ => funext fun i => hvu τ i
  refine ⟨y₂, v, f, g, hy₂.symm, ?_, hv, ?_, hc, fun σ i => ?_⟩
  · rw [← hy2, reassoc_of% hyy]
  · rw [huv]
    refine ⟨a, ψ, hψ, hu, fun τ n _ i hi => ⟨Pi.single i 1, fun j hj => Pi.single_eq_of_ne ?_ _,
      isCombAtG_single _ _ (fun j => (hu.1 τ j).1) i⟩⟩
    rintro rfl
    omega
  · obtain ⟨w₁, w₂, a1, a2, a3, a4, a5⟩ := htr σ i
    have b1 := sab_w ν₂
    have b2 := sab_w L.ν
    have b3 : v σ i ≫ _ = _ := (hv σ i).1
    have b4 := hvu σ i
    have c2 : w₂ = v σ i ≫ ν₂.φ := sab_ext (Y i₀).m (by rw [a5, Category.assoc, hν1, reassoc_of% b4])
      (by rw [a2, Category.assoc, b1, reassoc_of% b3, hyy])
    have c1 : w₁ = v σ i ≫ L.ν.φ := sab_ext T.m0.toSABMap (by rw [a3, c2, Category.assoc, hν2, Category.assoc])
      (by rw [a1, Category.assoc, b2, reassoc_of% b3, hyy])
    rw [← a4, c1, Category.assoc]

private theorem match_of_link {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W}
    {i₀ : Idx H p} {O : Type} [CommRing O] {β : O →+* i₀.c.F} {Z : LocM.Mdl Y i₀}
    [IsDiscreteValuationRing (Z.i.c.V W)] {T : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model (Xo i₀.l) i₀.c β}
    (L : GlobalTheory.ConsGeo.Lev Z T)
    (hL : ∀ (τ : (Y Z.i).X ⟶ (Y i₀).X) (mu : SABMap (Y Z.i).t (Y i₀).t τ), IsTrans i₀ Z.i τ mu →
      (Y Z.i).j ≫ τ = L.r ≫ (Y i₀).j ∧ ∃ ν₂ : SABMap (Y Z.i).oF.t (Y i₀).oF.t L.r,
        ν₂.φ ≫ (Y i₀).m.φ = (Y Z.i).m.φ ≫ mu.φ ∧ ν₂.φ ≫ (Y i₀).m0.toSABMap.φ = L.ν.φ ≫ T.m0.toSABMap.φ)
    {C : (nmodel Z).Comp} {F : Type} [Field F] [NumberField F] {e : F ≃+* i₀.c.F} {Φ : FlagCpt T e}
    {b : 𝓞 F →+* Z.i.c.V W} {μ : Match Φ.Y b ((nmodel Z).comp C)} (h : Link Z C Φ μ) :
    GlobalTheory.ConsGeo.Match L Φ (GlobalTheory.ConsGeo.gpt ((nmodel Z).comp C).X ≫ (nmodel Z).compι C)
      (spMap μ.φ ≫ genericPt Φ.Y) := by
  obtain ⟨a, τ, mu, y, ψ, f, g, -, hT, hy1, hy2, hψ, htr, hc⟩ := h
  obtain ⟨hr, ν₂, hν1, hν2⟩ := hL τ mu hT
  have e0 : μ.U.fromSpecStalkOfMem _ μ.mem ≫ μ.h = spMap μ.φ ≫ genericPt Φ.Y := μ.φ_spec
  refine e0 ▸ match_core L hr hν1 hν2 (K := ((nmodel Z).comp C).X.functionField) ?_ ?_ hψ htr hc
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hy1).trans
      ((Scheme.Opens.fromSpecStalkOfMem_ι_assoc _ _ _ _).trans (Category.assoc _ _ _).symm))
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hy2).trans (Category.assoc _ _ _).symm)

private theorem gpt_str {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B : Vert.Model O) :
    GlobalTheory.ConsGeo.gpt B.X ≫ B.str = spMap (cst B) := by
  have h1 : B.str = B.X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of O)).inv ≫ B.str.appTop) := by
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  rw [h1, Scheme.fromSpecStalk_toSpecΓ_assoc, ← Spec.map_comp]
  rfl

private theorem spC {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

private theorem spInj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective (a₁ := CommRingCat.ofHom _) (a₂ := CommRingCat.ofHom _) h)

private theorem gptInj (X : Scheme.{0}) [IsIntegral X] {k : Type} [Field k] {j j' : X.functionField →+* k}
    (h : spMap j ≫ GlobalTheory.ConsGeo.gpt X = spMap j' ≫ GlobalTheory.ConsGeo.gpt X) : j = j' := by
  haveI : Mono (GlobalTheory.ConsGeo.gpt X) := inferInstanceAs (Mono (X.fromSpecStalk (genericPoint X)))
  exact spInj ((cancel_mono _).1 h)

private theorem liesOver_iff {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W}
    {i₀ : Idx H p} {O : Type} [CommRing O] {β : O →+* i₀.c.F} {Z : LocM.Mdl Y i₀}
    {T : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model (Xo i₀.l) i₀.c β} (L : GlobalTheory.ConsGeo.Lev Z T) (hpq : 1 ≤ Dw.p + Dw.q)
    (y₂ : CxPt (Xo Z.i.l) Z.i.c) (y : CxPt (Xo i₀.l) i₀.c) : LiesOver Z.dvd y₂ y ↔ y₂.1 ≫ L.r = y.1 := by
  obtain ⟨π, hπ, hpb, hr⟩ := L.fst
  obtain ⟨π₀, -, -, huniq, -⟩ :=
    (GlobalTheory.LevelCompare.levelMaps_iff hpq).1 (GlobalTheory.moduliScheme_levelMaps_heckePoints.2 E H Dw hpq).1 _ _ Z.dvd
      (Xo i₀.l) (Xo Z.i.l)
  refine ⟨fun ⟨π', a₁, a₂, a₃⟩ => ?_, fun h => ⟨π, hπ, hpb, by rw [← hr, ← Category.assoc, h]⟩⟩
  obtain rfl : π' = π := (huniq π' a₁ a₂).trans (huniq π hπ hpb).symm
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, hr, a₃]
  · rw [Category.assoc, L.snd, ← Category.assoc, y₂.2, ← spC]
    exact y.2.symm

private theorem card_match {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W}
    {i₀ : Idx H p} {O : Type} [CommRing O] {β : O →+* i₀.c.F} {Z : LocM.Mdl Y i₀}
    {T : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model (Xo i₀.l) i₀.c β} (L : GlobalTheory.ConsGeo.Lev Z T) (hpq : 1 ≤ Dw.p + Dw.q)
    (hty : ∀ τ k, k ≤ Dw.mult τ → k ∈ Z.ty τ) {F : Type} [Field F] {e : F ≃+* i₀.c.F} (Φ : FlagCpt T e)
    (q : Sp ℂ ⟶ Φ.Y.X) (y : CxPt (Xo i₀.l) i₀.c) (hq : q ≫ Φ.π = y.1 ≫ T.jQ) :
    Nat.card {w : Sp ℂ ⟶ Z.X // GlobalTheory.ConsGeo.Match L Φ w q ∧
      w ≫ Z.s = spMap (Z.i.c.F.val.toRingHom.comp (Z.i.c.V W).subtype)} =
      levDeg Z.dvd (Xo i₀.l) i₀.c (Xo Z.i.l) Z.i.c := by
  rw [← card_liesOver hpq Z.dvd (Xo Z.i.l) Z.i.c y]
  have ex : ∀ a : {y₂ : CxPt (Xo Z.i.l) Z.i.c // LiesOver Z.dvd y₂ y},
      ∃! w : Sp ℂ ⟶ Z.X, w ≫ Z.π = a.1.1 ≫ (Y Z.i).j ∧ GlobalTheory.ConsGeo.Match L Φ w q := fun a =>
    UpperTheory.level_flag_compact_tangent L Φ hty q a.1.1 (by rw [hq, ← (liesOver_iff L hpq _ _).1 a.2, Category.assoc])
  choose w hw hu using ex
  have hj : ∀ (w : Sp ℂ ⟶ Z.X) (y₂ : Sp ℂ ⟶ (Xo Z.i.l).XF Z.i.c), w ≫ Z.π = y₂ ≫ (Y Z.i).j →
      w ≫ Z.s = (y₂ ≫ pullback.snd _ _) ≫ spMap (Z.i.c.V W).subtype := fun w y₂ h => by
    rw [← Z.π_s, reassoc_of% h, ModelRelProbe.j_over, Category.assoc]
  have := mono_j Y Z.i
  symm
  refine Nat.card_eq_of_bijective (fun a => ⟨w a, (hw a).2, by rw [hj _ _ (hw a).1, a.1.2, spC]⟩) ⟨fun a b h => ?_, ?_⟩
  · have h' : w a = w b := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext ((cancel_mono (Y Z.i).j).1 ((hw a).1.symm.trans (h' ▸ (hw b).1))))
  · rintro ⟨w₀, hm, hs⟩
    obtain ⟨y₂, -, -, -, h1, h2, -⟩ := id hm
    have := mono_spMap_subtype (Z.i.c.V W)
    have := T.jQ_open
    have k1 : y₂ ≫ pullback.snd _ _ = spMap Z.i.c.F.val.toRingHom := by
      rw [← cancel_mono (spMap (Z.i.c.V W).subtype), ← hj _ _ h1, hs, spC]
    have k2 : y₂ ≫ L.r = y.1 := by
      rw [← cancel_mono T.jQ, Category.assoc, ← h2, hq]
    exact ⟨⟨⟨y₂, k1⟩, (liesOver_iff L hpq _ _).2 k2⟩, Subtype.ext (hu _ _ ⟨h1, hm⟩).symm⟩

private theorem comp_inj {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Z : NModel O)
    {k : Type} [Field k] {C C' : Z.Comp} (a : Sp k ⟶ (Z.comp C).X) (b : Sp k ⟶ (Z.comp C').X)
    (h : a ≫ Z.compι C = b ≫ Z.compι C') : C = C' := by
  have hm (D : Z.Comp) (c : Sp k ⟶ (Z.comp D).X) : (c ≫ Z.compι D) (closedPoint k) ∈ D.opens :=
    (c (closedPoint k)).2
  exact Subtype.ext (GlobalTheory.IsNormalScheme.eq_of_mem_irreducibleComponents C.2 C'.2 (hm C a) (h ▸ hm C' b))

private theorem generic_str {F : Type} [Field F] (Y : Var F) :
    genericPt Y ≫ Y.str = spMap (algebraMap F Y.Fn) := (GlobalTheory.FlagBundle.ratOf Y).pt_s

private theorem exists_cxPt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    {T : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F} (Φ : FlagCpt T e)
    (ι : Φ.Y.Fn →+* ℂ) (hι : ι.comp (algebraMap F Φ.Y.Fn) = c.F.val.toRingHom.comp e.toRingHom) :
    ∃ y : CxPt Xo c, (spMap ι ≫ genericPt Φ.Y) ≫ Φ.π = y.1 ≫ T.jQ := by
  obtain ⟨y0, h0⟩ : ∃ y0 : Sp Φ.Y.Fn ⟶ Xo.XF c, y0 ≫ T.jQ = genericPt Φ.Y ≫ Φ.π := ⟨_, Φ.y0_x⟩
  have hj : T.jQ ≫ genStr T = pullback.snd _ _ := T.jQ_over
  have : IsIso (spMap e.toRingHom) := inferInstanceAs (IsIso (Spec.map e.toCommRingCatIso.hom))
  refine ⟨⟨spMap ι ≫ y0, ?_⟩, by rw [Category.assoc, Category.assoc, h0]⟩
  rw [← cancel_mono (spMap e.toRingHom), ← hj, ← spC, ← hι, spC, ← generic_str, ← Φ.π_str]
  simp only [Category.assoc]
  rw [reassoc_of% h0]

private theorem pt_inj {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Z : NModel O)
    {k : Type} [Field k] {P : Z.Comp → Prop} (a a' : Σ j : {C // P C}, ((Z.comp j.1).X.functionField →+* k))
    (h : spMap a.2 ≫ GlobalTheory.ConsGeo.gpt (Z.comp a.1.1).X ≫ Z.compι a.1.1 =
      spMap a'.2 ≫ GlobalTheory.ConsGeo.gpt (Z.comp a'.1.1).X ≫ Z.compι a'.1.1) : a = a' := by
  obtain ⟨⟨C, hC⟩, θ⟩ := a
  obtain ⟨⟨C', hC'⟩, θ'⟩ := a'
  have h' : (spMap θ ≫ GlobalTheory.ConsGeo.gpt (Z.comp C).X) ≫ Z.compι C = (spMap θ' ≫ GlobalTheory.ConsGeo.gpt (Z.comp C').X) ≫ Z.compι C' :=
    (Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm)
  obtain rfl : C = C' := comp_inj _ _ _ h'
  haveI : Mono (Z.compι C) := inferInstanceAs (Mono C.opens.ι)
  obtain rfl : θ = θ' := gptInj _ ((cancel_mono _).1 h')
  rfl

private theorem card_sub {A B : Type} {P : A → Prop} {Q : B → Prop} (f : A → B) (h₁ : ∀ a, P a → Q (f a))
    (h₂ : ∀ a a', f a = f a' → a = a') (h₃ : ∀ b, Q b → ∃ a, P a ∧ f a = b) :
    Nat.card {a // P a} = Nat.card {b // Q b} :=
  Nat.card_eq_of_bijective (fun a => ⟨f a.1, h₁ _ a.2⟩) ⟨fun _ _ h => Subtype.ext (h₂ _ _ (congrArg Subtype.val h)),
    fun b => let ⟨a, ha, e⟩ := h₃ b.1 b.2; ⟨⟨a, ha⟩, Subtype.ext e⟩⟩

private theorem match_uniq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W}
    {i₀ : Idx H p} {O : Type} [CommRing O] {β : O →+* i₀.c.F} {Z : LocM.Mdl Y i₀}
    {T : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model (Xo i₀.l) i₀.c β} {F : Type} [Field F] {e : F ≃+* i₀.c.F} {σ : i₀.c.F →+* ℂ}
    {N : ℕ} {U : Formalism.L2.PjFree.Unf (Xo i₀.l) i₀.c σ N} (fl : FlagTor T e U) {L : GlobalTheory.ConsGeo.Lev Z T}
    (hty : ∀ τ k, k ≤ Dw.mult τ → k ∈ Z.ty τ) {k : Type} [Field k] {w : Sp k ⟶ Z.X} {c : U.Comp}
    {q : Sp k ⟶ (fl.C c).Y.X} (h : GlobalTheory.ConsGeo.Match L (fl.C c) w q) :
    (∀ c' q', GlobalTheory.ConsGeo.Match L (fl.C c') w q' → c' = c) ∧ ∀ q', GlobalTheory.ConsGeo.Match L (fl.C c) w q' → q' = q :=
  ⟨fun c' q' h' => congrArg Sigma.fst (UpperTheory.level_unfolding_metric fl L hty w c' c q' q h' h),
    fun q' h' => eq_of_heq (Sigma.mk.inj (UpperTheory.level_unfolding_metric fl L hty w c c q' q h' h)).2⟩

set_option maxHeartbeats 1000000 in
private theorem count_core {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W}
    {i₀ : Idx H p} {O : Type} [CommRing O] {β : O →+* i₀.c.F} {Z : LocM.Mdl Y i₀}
    [IsDiscreteValuationRing (Z.i.c.V W)] {T : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model (Xo i₀.l) i₀.c β}
    {F : Type} [Field F] [NumberField F] {e : F ≃+* i₀.c.F} {σ : i₀.c.F →+* ℂ} {N : ℕ}
    {U : Formalism.L2.PjFree.Unf (Xo i₀.l) i₀.c σ N} (fl : FlagTor T e U) (hpq : 1 ≤ Dw.p + Dw.q)
    (hty : ∀ τ k, k ≤ Dw.mult τ → k ∈ Z.ty τ) (b : 𝓞 F →+* Z.i.c.V W) (c : U.Comp)
    (hgen : ∀ (L : GlobalTheory.ConsGeo.Lev Z T) (ι : (fl.C c).Y.Fn →+* ℂ) (w : Sp ℂ ⟶ Z.X),
      GlobalTheory.ConsGeo.Match L (fl.C c) w (spMap ι ≫ genericPt (fl.C c).Y) →
      ∃ (C : (nmodel Z).Comp) (θ : ((nmodel Z).comp C).X.functionField →+* ℂ),
        w = spMap θ ≫ GlobalTheory.ConsGeo.gpt ((nmodel Z).comp C).X ≫ (nmodel Z).compι C)
    (hex : ∀ C : (nmodel Z).Comp, ∃ (c : U.Comp) (μ : Match (fl.C c).Y b ((nmodel Z).comp C)), Link Z C (fl.C c) μ)
    (μ : ∀ j : {C : (nmodel Z).Comp // ∃ μ : Match (fl.C c).Y b ((nmodel Z).comp C), Link Z C (fl.C c) μ},
      Match (fl.C c).Y b ((nmodel Z).comp j.1)) (hμ : ∀ j, Link Z j.1 (fl.C c) (μ j)) (ε : F →+* Z.i.c.F)
    (hε : Z.i.c.F.val.toRingHom.comp ε = i₀.c.F.val.toRingHom.comp e.toRingHom) :
    Count μ ε Z.i.c.F.val.toRingHom (levDeg Z.dvd (Xo i₀.l) i₀.c (Xo Z.i.l) Z.i.c) := by
  intro ι hι
  obtain ⟨L, hL⟩ := UpperTheory.exists_level_abelian_maps Z T hpq
  obtain ⟨y, hy⟩ := exists_cxPt (fl.C c) ι (hι.trans hε)
  refine Eq.trans ?_ (card_match L hpq hty (fl.C c) _ y hy)
  have hm : ∀ (C : (nmodel Z).Comp) (c' : U.Comp) (m : Match (fl.C c').Y b ((nmodel Z).comp C)),
      Link Z C (fl.C c') m → ∀ θ : ((nmodel Z).comp C).X.functionField →+* ℂ,
      GlobalTheory.ConsGeo.Match L (fl.C c') (spMap θ ≫ GlobalTheory.ConsGeo.gpt ((nmodel Z).comp C).X ≫ (nmodel Z).compι C)
        (spMap (θ.comp m.φ) ≫ genericPt (fl.C c').Y) := fun C c' m h θ => by
    have := (UpperTheory.level_flag_compact_point L _ _ _ (match_of_link L hL h)).2.2.2 ℂ θ
    rwa [← Category.assoc _ _ (genericPt _), ← spC] at this
  have hs : ∀ (C : (nmodel Z).Comp) (θ : ((nmodel Z).comp C).X.functionField →+* ℂ),
      (spMap θ ≫ GlobalTheory.ConsGeo.gpt ((nmodel Z).comp C).X ≫ (nmodel Z).compι C) ≫ Z.s =
        spMap (θ.comp (cst ((nmodel Z).comp C))) := fun C θ => by
    rw [spC, ← gpt_str, Category.assoc, Category.assoc]
    rfl
  refine card_sub (fun a => spMap a.2 ≫ GlobalTheory.ConsGeo.gpt ((nmodel Z).comp a.1.1).X ≫ (nmodel Z).compι a.1.1)
    (fun a ha => ⟨?_, (hs _ _).trans (congrArg spMap ha.2)⟩) (pt_inj (nmodel Z)) ?_
  · have := hm _ _ _ (hμ a.1) a.2
    rwa [ha.1] at this
  · rintro w ⟨hw, hws⟩
    obtain ⟨C, θ, hw'⟩ := hgen L ι w hw
    obtain ⟨c', m, hl⟩ := hex C
    have hc : c' = c := (match_uniq fl hty hw).1 c' _ (hw' ▸ hm C c' m hl θ)
    obtain ⟨m, hl⟩ : ∃ m : Match (fl.C c).Y b ((nmodel Z).comp C), Link Z C (fl.C c) m := hc ▸ ⟨m, hl⟩
    have k := (match_uniq fl hty hw).2 _ (hw' ▸ hm C c _ (hμ ⟨C, m, hl⟩) θ)
    have k1 : θ.comp (μ ⟨C, m, hl⟩).φ = ι := gptInj _ k
    have k2 := spInj ((hs C θ).symm.trans (hw' ▸ hws))
    exact ⟨⟨⟨C, m, hl⟩, θ⟩, ⟨k1, k2⟩, hw'.symm⟩

theorem UpperTheory.admissible_point_lattice_norm :
    ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (fl : s.Flag), (∀ k, (fl.C k).Y.dim = Formalism.DegreeFormula.dimFl D.what₂.Tau N) → ∀ (p : ℕ) (hp : p.Prime) (W : ValuationSubring ℂ) (hW : (p : ℂ) ∈ W.nonunits) (z : AdmAt S κ hp hW) [IsDiscreteValuationRing (z.Z.i.c.V W)] (ε : D.what₂.LL →+* z.Z.i.c.F) (b : 𝓞 D.what₂.LL →+* z.Z.i.c.V W), (∀ x, ((ε x : z.Z.i.c.F) : ℂ) = D.what₂.embLL x) → (∀ x : 𝓞 D.what₂.LL, ((b x : z.Z.i.c.V W) : z.Z.i.c.F) = ε (x : D.what₂.LL)) → ∀ (c : s.Comp) (μ : ∀ j : {C : (nmodel z.Z).Comp // ∃ μ : Match (fl.C c).Y b ((nmodel z.Z).comp C), Link z.Z C (fl.C c) μ}, Match (fl.C c).Y b ((nmodel z.Z).comp j.1)), (∀ j, Link z.Z j.1 (fl.C c) (μ j)) → Count μ ε z.Z.i.c.F.val.toRingHom (cov z) := by
  intro D A N j S κ s fl hd p hp W hW z _ ε b hε hb c μ hμ
  have hpq : 1 ≤ S.Dw.p + S.Dw.q := by
    have := S.rank_eq
    have := S.two_le
    omega
  exact count_core (Z := z.Z) fl hpq z.full b c
    (fun L ι w => UpperTheory.admissible_level_match D A N j S κ s fl hd p hp W hW z L c ℂ ι w)
    (UpperTheory.admissible_point_discrete_valuation D A N j S κ s fl hd p hp W hW z ε b hε hb) μ hμ ε
    (RingHom.ext fun x => (hε x).trans (κ.e_emb x).symm)
