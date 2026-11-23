import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothOfAlgClosedUnif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCoordNeZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VarFlag

open GlobalTheory.FlagMod (FlagCover Frames)
open GlobalTheory.ShFam (EigFrame FlagCpt)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem tri_of_isFrameAt {Y : Model Xo c (RingHom.id c.F)} {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π)
    {S : Type} [CommRing S] {φ : c.F →+* S} (z : Sp S ⟶ Z) (k k' : F.J) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k)
    (hz' : ⊤ ≤ z ⁻¹ᵁ F.U k') (g g' : EigFrame Y φ (z ≫ π)) (hg : IsFrameAt F z k hz g)
    (hg' : IsFrameAt F z k' hz' g') : ∃ d, g.Tri (RingHom.id S) g' d := by
  have hh := GlobalTheory.FlagMod.le_preimage_inf hz hz'
  have h1 : spMap (dualMap (RingHom.id S)) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [dualMap]
  have h2 : spMap (RingHom.id S) = 𝟙 _ := Spec.map_id _
  refine ⟨fun τ i => F.TAt k k' z hh (some ⟨τ, i⟩), by rw [h2, Category.id_comp], rfl, fun τ i =>
    ⟨fun j => (F.B k k' τ).map (GlobalTheory.FlagMod.ev z _ hh) j i, rfl, fun j hj => F.B_map_tri k k' τ _ hj, ?_⟩⟩
  simp only [h1, Category.id_comp]
  have e : (fun j => g.v τ j) = fun j => (tv (F.vecAt k z hz rfl τ j)).left := funext (hg τ)
  rw [e, hg' τ i, GlobalTheory.LieMet.isComb_iff]
  exact F.vecAt_eq_sum k k' z hz hz' hh rfl τ i

end GlobalTheory.VarFlag

namespace GlobalTheory.VarFlag

open GlobalTheory.FlagMod (FlagCover Frames)
open GlobalTheory.ShFam (EigFrame FlagCpt)
open GlobalTheory.Toroidal (gen genι genStr)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem carries_congr {Y : Model Xo c (RingHom.id c.F)} (C : FlagCpt Y (RingEquiv.refl c.F)) {K : Type} [Field K]
    {φ : c.F →+* K} {x x' : Sp K ⟶ Y.X} (h : x = x') (g : EigFrame Y φ x) (g' : EigFrame Y φ x')
    (hv : ∀ τ i, g.v τ i = g'.v τ i) (p : Sp K ⟶ C.Y.X) : C.Carries p g ↔ C.Carries p g' := by
  subst h
  obtain ⟨v, a1, a2, a3⟩ := g
  obtain ⟨v', b1, b2, b3⟩ := g'
  have e : v = v' := funext fun τ => funext fun i => hv τ i
  subst e
  rfl

theorem carries_of_tri {Y : Model Xo c (RingHom.id c.F)} (C : FlagCpt Y (RingEquiv.refl c.F)) {K : Type} [Field K]
    {φ φ' : c.F →+* K} {x x' : Sp K ⟶ Y.X} {g : EigFrame Y φ x} {g' : EigFrame Y φ' x'}
    {d : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ} (h : g.Tri (RingHom.id K) g' d) {p : Sp K ⟶ C.Y.X}
    (hp : C.Carries p g) : C.Carries p g' := by
  obtain ⟨y, ψ, φ₁, f, t, t', h1, h2, h3⟩ := hp
  exact ⟨y, ψ, φ₁, f, t, _, h1, h2, GlobalTheory.ShFam.FlatSec.tri_trans h3 h⟩

theorem carries_over {Y : Model Xo c (RingHom.id c.F)} (C : FlagCpt Y (RingEquiv.refl c.F)) {K : Type} [Field K]
    {φ : c.F →+* K} {x : Sp K ⟶ Y.X} {g : EigFrame Y φ x} {p : Sp K ⟶ C.Y.X} (hp : C.Carries p g) :
    p ≫ C.π ≫ genι Y = x := by
  obtain ⟨y, ψ, φ₁, f, t, t', h1, h2, h3⟩ := hp
  rw [h1, Category.assoc, ← h3.1]

theorem uniq_rel : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}, ∀ (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Formalism.L2.Pj.Comp Xo c), GlobalTheory.VarFlag.FramesExist X → ∀ (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.CarriesTri C → ∀ (B : GlobalTheory.ProjVar.Var c.F) (j : B.X ⟶ GlobalTheory.Toroidal.gen Y) [IsOpenImmersion j] (f : C.Y.X ⟶ B.X), C.π = f ≫ j → (∀ (K : Type) [Field K] (χ : c.F →+* K) (x : Sp K ⟶ GlobalTheory.Toroidal.gen Y) (x' : Sp K ⟶ B.X), x' ≫ j = x → x ≫ GlobalTheory.Toroidal.genStr Y = spMap χ → ∀ g : GlobalTheory.ShFam.EigFrame Y χ (x ≫ GlobalTheory.Toroidal.genι Y), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x' ∧ C.Carries p g) → (∀ w : GlobalTheory.Toroidal.gen Y, GlobalTheory.Toroidal.genι Y w ∈ GlobalTheory.CompHS.barComp Y Z ↔ w ∈ Set.range j) → ∀ (K : Type) [Field K] (z : Sp K ⟶ GlobalTheory.CompHS.Y₀ X Z), ∃! p : Sp K ⟶ C.Y.X, GlobalTheory.VarFlag.Rel X.F C (z ≫ GlobalTheory.CompHS.inc₀ X Z) p := by
  intro E _ _ _ H Dw l Xo c Y X Z hFE C _ B j _ f hπ hlifts hbar K _ z
  set zz := z ≫ GlobalTheory.CompHS.inc₀ X Z with hzz

  let φ : c.F →+* K := (Spec.preimage (zz ≫ X.π ≫ Y.s)).hom
  have hφ : zz ≫ X.π ≫ Y.s = spMap φ := (Spec.map_preimage _).symm

  obtain ⟨k, hk⟩ := GlobalTheory.FlagMod.exists_chart_of_isLocalRing X.F.cover zz
  obtain ⟨g, hg⟩ := hFE K φ zz k hk hφ

  let xg : Sp K ⟶ gen Y := zz ≫ X.π ≫ inv (genι Y)
  have hxg : xg ≫ genι Y = zz ≫ X.π := by simp [xg]
  have hid : spMap (RingHom.id c.F) = 𝟙 _ := Spec.map_id _
  have hstr : xg ≫ genStr Y = spMap φ := by
    have e : genStr Y = genι Y ≫ Y.s := by
      calc genStr Y = genStr Y ≫ spMap (RingHom.id c.F) := by rw [hid, Category.comp_id]
        _ = genι Y ≫ Y.s := (pullback.condition (f := Y.s) (g := spMap (RingHom.id c.F))).symm
    rw [e, ← Category.assoc, hxg, Category.assoc, hφ]

  have hr : Set.range xg ⊆ Set.range j := by
    rintro _ ⟨a, rfl⟩
    refine (hbar _).1 ?_
    have e : genι Y (xg a) = X.π (GlobalTheory.CompHS.inc₀ X Z (z a)) := by
      rw [← Scheme.Hom.comp_apply, hxg]; rfl
    rw [e]
    have hm : GlobalTheory.CompHS.inc₀ X Z (z a) ∈ X.π ⁻¹ᵁ GlobalTheory.CompHS.barComp Y Z := by
      have := (Scheme.Opens.range_ι (X.π ⁻¹ᵁ GlobalTheory.CompHS.barComp Y Z)).le ⟨z a, rfl⟩
      exact this
    exact hm
  let x' := IsOpenImmersion.lift j xg hr
  have hx' : x' ≫ j = xg := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨g0, hg0⟩ : ∃ g0 : EigFrame Y φ (xg ≫ genι Y), ∀ τ i, g0.v τ i = g.v τ i := by
    rw [hxg]; exact ⟨g, fun _ _ => rfl⟩
  obtain ⟨p, ⟨hp1, hp2⟩, hpu⟩ := hlifts K φ xg x' hx' hstr g0
  refine ⟨p, ⟨φ, k, hk, g, hφ, hg, (carries_congr C hxg g0 g hg0 p).1 hp2⟩, ?_⟩
  rintro p' ⟨φ', k', hk', g', hφ', hg', hc'⟩
  have e : φ' = φ := by
    have h0 : spMap φ' = spMap φ := hφ'.symm.trans hφ
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h0)
  subst e
  obtain ⟨d, hd⟩ := tri_of_isFrameAt X.F zz k' k hk' hk g' g hg' hg
  have hc : C.Carries p' g := carries_of_tri C hd hc'
  have hc0 : C.Carries p' g0 := (carries_congr C hxg g0 g hg0 p').2 hc
  refine hpu p' ⟨?_, hc0⟩
  have h1 : p' ≫ C.π = xg := by
    rw [← cancel_mono (genι Y), Category.assoc]
    exact carries_over C hc0
  rw [← cancel_mono j, Category.assoc, ← hπ, h1, hx']

end GlobalTheory.VarFlag
