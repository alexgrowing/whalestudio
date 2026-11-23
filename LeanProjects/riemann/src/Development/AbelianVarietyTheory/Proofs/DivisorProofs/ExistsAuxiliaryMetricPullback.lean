import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializationMapCompUniversalSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjFsBasisOfUnitary

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry

set_option autoImplicit false

noncomputable section

open Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.GalCarry.Tw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  (T : Tw Z) {σ : c.F →+* ℂ}

def pullForm (h : ∀ y : CxPts (genStr Z) σ, TanM (y.1 ≫ genι Z) Z.t.G →ₗ[ℂ] TanM (y.1 ≫ genι Z) Z.t.G →ₗ⋆[ℂ] ℂ)
    (y : CxPts (genStr Z) σ) : TanM (y.1 ≫ genι Z) Z.t.G →ₗ[ℂ] TanM (y.1 ≫ genι Z) Z.t.G →ₗ⋆[ℂ] ℂ :=
  ((h (T.pt y)).comp (T.lie (T.pt_ι y).symm).toLinearMap).compl₂ (T.lie (T.pt_ι y).symm).toLinearMap

variable (h : ∀ y : CxPts (genStr Z) σ, TanM (y.1 ≫ genι Z) Z.t.G →ₗ[ℂ] TanM (y.1 ≫ genι Z) Z.t.G →ₗ⋆[ℂ] ℂ)

theorem isEig_lie {x x' : Sp ℂ ⟶ Z.X} (hx : x ≫ T.ρ.hom = x') {ρ : E →+* ℂ} {v : TanM x Z.t.G}
    (hv : IsEig ρ v) : IsEig (ρ.comp (T.s.symm : E →+* E)) (T.lie hx v) := fun a => by
  obtain ⟨b, rfl⟩ := T.σ.surjective a
  rw [← T.lie_act, hv b, map_smul]
  congr 1
  simp [T.coe_σ b]

theorem isBlockMetric_pullForm {y : CxPts (genStr Z) σ} (hh : IsBlockMetric (h (T.pt y))) :
    IsBlockMetric (T.pullForm h y) := by
  refine ⟨fun v w => hh.1 _ _, fun v hv => hh.2.1 _ ((LinearEquiv.map_ne_zero_iff _).2 hv),
    fun ρ ρ' v w hρ hv hw => hh.2.2 _ _ _ _ ?_ (T.isEig_lie _ hv) (T.isEig_lie _ hw)⟩
  intro e
  apply hρ
  ext a
  have := RingHom.congr_fun e (T.s a)
  simpa using this

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

variable [SmoothOfRelativeDimension Dw.dim (genStr Z)]

def imOpen (V : (gen Z).affineOpens) : (gen Z).affineOpens := ⟨T.g.inv ⁻¹ᵁ V.1, V.2.preimage_of_isIso _⟩

theorem preimage_imOpen (V : (gen Z).affineOpens) : T.g.hom ⁻¹ᵁ (T.imOpen V).1 = V.1 := by
  ext p
  show p ∈ T.g.hom ⁻¹ᵁ (T.g.inv ⁻¹ᵁ V.1) ↔ p ∈ V.1
  rw [Scheme.Hom.mem_preimage, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, Iso.hom_inv_id]
  rfl

theorem pt_mem_iff (V : (gen Z).affineOpens) {y : CxPts (genStr Z) σ} :
    T.pt y ∈ ptsIn _ σ (T.imOpen V).1 ↔ y ∈ ptsIn _ σ V.1 := by
  rw [← mem_ptsIn_preimage (f := T.g.hom) (fun _ => rfl), T.preimage_imOpen]

theorem preimage_ptsIn (V : (gen Z).affineOpens) :
    T.pt ⁻¹' ptsIn (genStr Z) σ (T.imOpen V).1 = ptsIn (genStr Z) σ V.1 :=
  Set.ext fun _ => T.pt_mem_iff V

def imRing (V : (gen Z).affineOpens) : Γ(gen Z, V.1) →+* Γ(gen Z, (T.imOpen V).1) :=
  (T.g.inv.appLE V.1 (T.imOpen V).1 le_rfl).hom

@[reassoc]
theorem imRing_chart (V : (gen Z).affineOpens) :
    spMap (T.imRing V) ≫ GlobalTheory.LogKS.chart V = GlobalTheory.LogKS.chart (T.imOpen V) ≫ T.g.inv :=
  IsAffineOpen.SpecMap_appLE_fromSpec _ V.2 (T.imOpen V).2 le_rfl

theorem ev_imRing (V : (gen Z).affineOpens) {y : CxPts (genStr Z) σ} (hy : y ∈ ptsIn _ σ V.1) :
    (evHom ((T.pt_mem_iff V).2 hy)).comp (T.imRing V) = evHom hy := by
  have hm : Mono (GlobalTheory.LogKS.chart V) := by
    unfold GlobalTheory.LogKS.chart; haveI := V.2.isOpenImmersion_fromSpec; exact IsOpenImmersion.mono _
  have h2 : spMap ((evHom ((T.pt_mem_iff V).2 hy)).comp (T.imRing V)) = spMap (evHom hy) := by
    rw [← cancel_mono (GlobalTheory.LogKS.chart V), ← spMap_comp', Category.assoc, T.imRing_chart, ← Category.assoc,
      spMap_evHom, spMap_evHom]
    show (y.1 ≫ T.g.hom) ≫ T.g.inv = y.1
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h2)

def pushSec (V : (gen Z).affineOpens) (v : TanM (GlobalTheory.LogKS.chart V ≫ genι Z) Z.t.G) :
    TanM (GlobalTheory.LogKS.chart (T.imOpen V) ≫ genι Z) Z.t.G :=
  tanOf (isTan_map (T.imRing V) (by simp only [Category.assoc, T.imRing_chart_assoc, Iso.inv_hom_id_assoc])
    (isTan_tv (T.lie (x' := (GlobalTheory.LogKS.chart V ≫ T.g.hom) ≫ genι Z)
      (by rw [Category.assoc, Category.assoc, T.g_ι]) v)))

theorem valAt_pushSec (V : (gen Z).affineOpens) (v : TanM (GlobalTheory.LogKS.chart V ≫ genι Z) Z.t.G)
    {y : CxPts (genStr Z) σ} (hy : y ∈ ptsIn _ σ V.1) :
    valAt (genι Z) (T.pushSec V v) ((T.pt_mem_iff V).2 hy) = T.lie (T.pt_ι y).symm (valAt (genι Z) v hy) := by
  apply tan_ext
  show spMap (dualMap (evHom ((T.pt_mem_iff V).2 hy))) ≫ spMap (dualMap (T.imRing V)) ≫ (tv v).left ≫ T.mu.cm.F =
    (spMap (dualMap (evHom hy)) ≫ (tv v).left) ≫ T.mu.cm.F
  rw [← Category.assoc, spMap_comp', ← Formalism.L2.Pj.dualMap_comp, T.ev_imRing, Category.assoc]

def auxiliary_data_pullback (x : OddPrimesWithRootsOfUnity Z) : OddPrimesWithRootsOfUnity Z :=
  { x with
    met := fun σ => T.pullForm (x.met σ)
    met_smooth := fun σ => ⟨fun _ => T.isBlockMetric_pullForm _ ((x.met_smooth σ).1 _), fun V v w => by
      obtain ⟨g, h1, h2, h3⟩ := (x.met_smooth σ).2 (T.imOpen V) (T.pushSec V v) (T.pushSec V w)
      refine ⟨g ∘ T.pt, ?_, ?_, fun y hy => ?_⟩
      · have := h1.comp_map (isOpen_ptsIn _) (m := T.pt) (f := T.g.hom) (fun _ => rfl) (manifold Z σ)
        rw [T.preimage_ptsIn] at this
        exact this
      · have := h2.comp_map (isOpen_ptsIn _) (m := T.pt) (f := T.g.hom) (fun _ => rfl) (manifold Z σ)
        rw [T.preimage_ptsIn] at this
        exact this
      · rw [Function.comp_apply, h3 _ ((T.pt_mem_iff V).2 hy), T.valAt_pushSec, T.valAt_pushSec]
        rfl⟩
    met_conj := fun σ σ' y y' v w v' w' hy hv hw =>
      x.met_conj σ σ' (T.pt y) (T.pt y') _ _ _ _
        (by show y'.1 ≫ T.g.hom = _ ≫ y.1 ≫ T.g.hom; rw [hy, Category.assoc])
        (by show (tv v').left ≫ T.mu.cm.F = _ ≫ (tv v).left ≫ T.mu.cm.F; rw [hv, Category.assoc])
        (by show (tv w').left ≫ T.mu.cm.F = _ ≫ (tv w).left ≫ T.mu.cm.F; rw [hw, Category.assoc]) }

theorem metric_at_auxiliary_pullback (x : OddPrimesWithRootsOfUnity Z) (y : CxPts (genStr Z) σ) :
    T.MetAt y (x.eigMet σ) ((T.auxiliary_data_pullback x).eigMet σ) := by
  intro f f' hf τ
  ext a b
  simp only [OddPrimesWithRootsOfUnity.eigMet_gram, OddPrimesWithRootsOfUnity.gram, gramOf, Matrix.submatrix_apply, Matrix.of_apply]
  rw [hf.vec, hf.vec]
  rfl

end GlobalTheory.ShFam.GalCarry.Tw

theorem GlobalTheory.ShFam.GalCarry.exists_auxiliary_data_metric : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) [SmoothOfRelativeDimension Dw.dim (genStr Z)] (T : Tw Z) (x : OddPrimesWithRootsOfUnity Z), ∃ x₂ : OddPrimesWithRootsOfUnity Z, ∀ σ y, T.MetAt y (x.eigMet σ) (x₂.eigMet σ) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ T x => ⟨T.auxiliary_data_pullback x, fun _ y => T.metric_at_auxiliary_pullback x y⟩
