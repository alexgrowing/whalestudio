import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CartierGlue

open GlobalTheory.Cartier ReciprocityTheory.AnForm.R TopologicalSpace Opposite

variable {X Y P : Scheme.{0}}

theorem stalkMap_germ_appIso_inv (u : Y ⟶ X) [IsOpenImmersion u] {V : Y.Opens} (a : Γ(Y, V))
    (y : Y) (hy : y ∈ V) (hx : u y ∈ u ''ᵁ V) :
    (u.stalkMap y).hom ((X.presheaf.germ (u ''ᵁ V) (u y) hx).hom ((u.appIso V).inv.hom a)) =
      (Y.presheaf.germ V y hy).hom a := by
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appIso_inv_app_apply]
  exact Y.presheaf.germ_res_apply _ _ _ _

theorem stalkMap_germ_of_comp (g : P ⟶ Y) (u : Y ⟶ X) [IsOpenImmersion u] (ψ : P ⟶ X)
    (h : g ≫ u = ψ) {V : Y.Opens} (a : Γ(Y, V)) (p : P) (hp : g p ∈ V) (hx : ψ p ∈ u ''ᵁ V) :
    (ψ.stalkMap p).hom ((X.presheaf.germ (u ''ᵁ V) (ψ p) hx).hom ((u.appIso V).inv.hom a)) =
      (g.stalkMap p).hom ((Y.presheaf.germ V (g p) hp).hom a) := by
  subst h
  rw [Scheme.Hom.stalkMap_comp]
  exact congrArg (g.stalkMap p).hom (stalkMap_germ_appIso_inv u a (g p) hp hx)

theorem isRegularFn_appIso_inv (u : Y ⟶ X) [IsOpenImmersion u] {V : Y.Opens} {a : Γ(Y, V)}
    (ha : IsRegularFn a) : IsRegularFn ((u.appIso V).inv.hom a) := by
  refine isRegularFn_iff_germ.2 fun x hx => ?_
  have hx' := hx
  obtain ⟨y, hy, rfl⟩ := hx'
  have h1 := isRegularFn_iff_germ.1 ha y hy
  rw [← stalkMap_germ_appIso_inv u a y hy hx] at h1
  let e := (asIso (u.stalkMap y)).commRingCatIsoToRingEquiv
  exact comap_nonZeroDivisors_le_of_injective e.injective h1

theorem span_eq_of_ringEquiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) {a b : R}
    (h : Ideal.span {e a} = Ideal.span {e b}) : Ideal.span {a} = Ideal.span {b} := by
  have := congrArg (Ideal.map e.symm) h
  simpa [Ideal.map_span] using this

theorem stalkId_comap (J : EffCartierData Y) (φ : P ⟶ Y) (p : P) (k : J.ι) (hp : φ p ∈ J.U k) :
    FinalTheorems.stalkId (J.idealSheaf.comap φ) p =
      Ideal.span {(φ.stalkMap p).hom ((Y.presheaf.germ _ (φ p) hp).hom (J.f k))} := by
  obtain ⟨W, hpW, hW⟩ := EffCartierData.exists_affine_le (V := φ ⁻¹ᵁ J.U k) (x := p) hp
  rw [ds_stalkId_eq_map _ W p hpW, J.ideal_comap_idealSheaf φ W k hW, Ideal.map_span,
    Set.image_singleton, germ_resG]
  exact congrArg (fun t => Ideal.span {t}) (EffCartierData.germ_app φ (J.f k) p hp)

section Glue

variable {I : Type} {Y : I → Scheme.{0}} (u : ∀ i, Y i ⟶ X) (J : ∀ i, EffCartierData (Y i))
  [hu : ∀ i, IsOpenImmersion (u i)]

def gV (c : Σ i, (J i).ι) : X.Opens := u c.1 ''ᵁ (J c.1).U c.2

def gf (c : Σ i, (J i).ι) : Γ(X, gV u J c) := ((u c.1).appIso ((J c.1).U c.2)).inv.hom ((J c.1).f c.2)

include hu in

theorem span_germ_gf
    (hJ : ∀ i j, (J i).idealSheaf.comap (pullback.fst (u i) (u j)) =
      (J j).idealSheaf.comap (pullback.snd (u i) (u j)))
    (c c' : Σ i, (J i).ι) (x : X) (hx : x ∈ gV u J c) (hx' : x ∈ gV u J c') :
    Ideal.span {(X.presheaf.germ _ x hx).hom (gf u J c)} =
      Ideal.span {(X.presheaf.germ _ x hx').hom (gf u J c')} := by
  obtain ⟨i, k⟩ := c
  obtain ⟨j, l⟩ := c'
  have hx0 := hx
  obtain ⟨y, hy, rfl⟩ := hx0
  have hx1 := hx'
  obtain ⟨y', hy', e⟩ := hx1
  obtain ⟨p, rfl, rfl⟩ := Scheme.Pullback.exists_preimage_pullback (f := u i) (g := u j) y y' e.symm
  let ψ := pullback.fst (u i) (u j) ≫ u i
  have h1 := stalkMap_germ_of_comp (pullback.fst (u i) (u j)) (u i) ψ rfl ((J i).f k) p hy hx
  have h2 := stalkMap_germ_of_comp (pullback.snd (u i) (u j)) (u j) ψ pullback.condition.symm
    ((J j).f l) p hy' hx'
  have h3 := congrArg (fun I => FinalTheorems.stalkId I p) (hJ i j)
  simp only [stalkId_comap _ _ p k hy, stalkId_comap _ _ p l hy'] at h3
  rw [← h1, ← h2] at h3
  exact span_eq_of_ringEquiv (asIso (ψ.stalkMap p)).commRingCatIsoToRingEquiv h3

end Glue

section Main

variable {I : Type} {Y : I → Scheme.{0}} (u : ∀ i, Y i ⟶ X) (J : ∀ i, EffCartierData (Y i))
  [hu : ∀ i, IsOpenImmersion (u i)]

include hu in

theorem regular_gf (c : Σ i, (J i).ι) : IsRegularFn (gf u J c) :=
  isRegularFn_appIso_inv (u c.1) ((J c.1).regular c.2)

include hu in

theorem assoc_gf
    (hJ : ∀ i j, (J i).idealSheaf.comap (pullback.fst (u i) (u j)) =
      (J j).idealSheaf.comap (pullback.snd (u i) (u j))) (c c' : Σ i, (J i).ι) :
    Associated (resG X (inf_le_left : gV u J c ⊓ gV u J c' ≤ gV u J c) (gf u J c))
      (resG X (inf_le_right : gV u J c ⊓ gV u J c' ≤ gV u J c') (gf u J c')) := by
  refine ((regular_gf u J c).resG _).associated_of_germ ((regular_gf u J c').resG _)
    fun x hx => ?_
  rw [germ_resG, germ_resG]
  exact span_germ_gf u J hJ c c' x hx.1 hx.2

include hu in

def glueData (hcov : ∀ x : X, ∃ i, x ∈ Set.range (u i))
    (hJ : ∀ i j, (J i).idealSheaf.comap (pullback.fst (u i) (u j)) =
      (J j).idealSheaf.comap (pullback.snd (u i) (u j))) : EffCartierData X where
  ι := Σ i, (J i).ι
  U := gV u J
  f := gf u J
  cover := by
    refine eq_top_iff.2 fun x _ => Opens.mem_iSup.2 ?_
    obtain ⟨i, y, rfl⟩ := hcov x
    obtain ⟨k, hk⟩ := (J i).exists_mem y
    exact ⟨⟨i, k⟩, ⟨y, hk, rfl⟩⟩
  regular := regular_gf u J
  assoc := assoc_gf u J hJ

include hu in

theorem comap_glueData (hcov : ∀ x : X, ∃ i, x ∈ Set.range (u i))
    (hJ : ∀ i j, (J i).idealSheaf.comap (pullback.fst (u i) (u j)) =
      (J j).idealSheaf.comap (pullback.snd (u i) (u j))) (i : I) :
    (glueData u J hcov hJ).idealSheaf.comap (u i) = (J i).idealSheaf := by
  refine (J i).eq_idealSheaf fun y => ?_
  obtain ⟨k, hk⟩ := (J i).exists_mem y
  obtain ⟨W, hyW, hW⟩ := EffCartierData.exists_affine_le hk
  refine ⟨W, k, hW, hyW, ?_⟩
  have hW' : W.1 ≤ u i ⁻¹ᵁ (u i ''ᵁ (J i).U k) :=
    hW.trans ((u i).preimage_image_eq _).ge
  rw [(glueData u J hcov hJ).ideal_comap_idealSheaf (u i) W (⟨i, k⟩ : Σ i, (J i).ι) hW']
  congr 2
  show resG (Y i) hW' (((u i).app (u i ''ᵁ (J i).U k)).hom
    (((u i).appIso ((J i).U k)).inv.hom ((J i).f k))) = _
  have e : ((u i).app (u i ''ᵁ (J i).U k)).hom (((u i).appIso ((J i).U k)).inv.hom ((J i).f k)) =
      ((Y i).presheaf.map (eqToHom ((u i).preimage_image_eq ((J i).U k))).op).hom ((J i).f k) :=
    congrArg (fun q => q.hom ((J i).f k)) ((u i).appIso_inv_app ((J i).U k))
  rw [e]
  change ((Y i).presheaf.map _ ≫ (Y i).presheaf.map _).hom _ = _
  rw [← Functor.map_comp]
  rfl

end Main

theorem exists_glue {X : Scheme.{0}} {I : Type} {Y : I → Scheme.{0}} (u : ∀ i, Y i ⟶ X)
    (J : ∀ i, EffCartierData (Y i)) (hu : ∀ i, IsOpenImmersion (u i))
    (hcov : ∀ x : X, ∃ i, x ∈ Set.range (u i))
    (hJ : ∀ i j, (J i).idealSheaf.comap (pullback.fst (u i) (u j)) =
      (J j).idealSheaf.comap (pullback.snd (u i) (u j))) :
    ∃ D : EffCartierData X, ∀ i, D.idealSheaf.comap (u i) = (J i).idealSheaf :=
  ⟨glueData u J hcov hJ, comap_glueData u J hcov hJ⟩

end GlobalTheory.CartierGlue
