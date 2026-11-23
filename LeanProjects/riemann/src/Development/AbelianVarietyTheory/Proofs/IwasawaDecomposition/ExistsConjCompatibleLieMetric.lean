import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryOfFrameNormConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieMetricOfT2
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjSmoothOnPreimageChartsStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open GlobalTheory.FlagMod (tanPull tanPull_left tanPull_actR)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LieMetConj

theorem spMap_conj_conj : spMap (starRingEnd ℂ) ≫ spMap (starRingEnd ℂ) = 𝟙 _ := by
  rw [← Spec.map_comp, ← Spec.map_id]
  exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => by simp))

theorem spMap_dual_conj_conj :
    spMap (dualMap (starRingEnd ℂ)) ≫ spMap (dualMap (starRingEnd ℂ)) = 𝟙 _ := by
  rw [← Spec.map_comp, ← Spec.map_id]
  exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => by ext <;> simp [dualMap]))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X}

section Fibre

variable {x x' : Sp ℂ ⟶ X} (e : spMap (starRingEnd ℂ) ≫ x = x')

def cjForm (h : TanM x' t.G →ₗ[ℂ] TanM x' t.G →ₗ⋆[ℂ] ℂ) : TanM x t.G →ₗ[ℂ] TanM x t.G →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun v w => starRingEnd ℂ (h (tanPull (starRingEnd ℂ) e v) (tanPull (starRingEnd ℂ) e w)))
    (fun _ _ _ => by simp only [map_add, LinearMap.add_apply])
    (fun _ _ _ => by simp [map_smulₛₗ])
    (fun _ _ _ => by simp only [map_add])
    (fun _ _ _ => by simp [map_smulₛₗ])

theorem cjForm_apply (h : TanM x' t.G →ₗ[ℂ] TanM x' t.G →ₗ⋆[ℂ] ℂ) (v w : TanM x t.G) :
    cjForm e h v w = starRingEnd ℂ (h (tanPull (starRingEnd ℂ) e v) (tanPull (starRingEnd ℂ) e w)) := rfl

theorem tanPull_conj_injective : Function.Injective (tanPull (G := t.G) (starRingEnd ℂ) e) := fun v w h => by
  have h1 := congrArg (fun z => spMap (dualMap (starRingEnd ℂ)) ≫ (tv z).left) h
  simp only [tanPull_left] at h1
  rw [← Category.assoc, ← Category.assoc, spMap_dual_conj_conj, Category.id_comp, Category.id_comp] at h1
  exact tan_ext h1

theorem isEig_tanPull {ρ : E →+* ℂ} {v : TanM x t.G} (hv : IsEig ρ v) :
    IsEig ((starRingEnd ℂ).comp ρ) (tanPull (starRingEnd ℂ) e v) := fun a => by
  rw [← tanPull_actR, hv a, map_smulₛₗ]
  rfl

theorem isBlockMetric_cjForm {h : TanM x' t.G →ₗ[ℂ] TanM x' t.G →ₗ⋆[ℂ] ℂ} (hh : IsBlockMetric h) :
    IsBlockMetric (cjForm e h) := by
  refine ⟨fun v w => ?_, fun v hv => ?_, fun ρ ρ' v w hρ hv hw => ?_⟩
  · rw [cjForm_apply, cjForm_apply, hh.1]
  · rw [cjForm_apply, Complex.conj_re]
    exact hh.2.1 _ fun h0 => hv (tanPull_conj_injective e (h0.trans (map_zero _).symm))
  · rw [cjForm_apply, hh.2.2 _ _ _ _ (fun h0 => hρ (RingHom.ext fun a =>
      (starRingEnd ℂ).injective (RingHom.congr_fun h0 a))) (isEig_tanPull e hv) (isEig_tanPull e hw), map_zero]

theorem isBlockMetric_add {h h' : TanM x t.G →ₗ[ℂ] TanM x t.G →ₗ⋆[ℂ] ℂ} (hh : IsBlockMetric h)
    (hh' : IsBlockMetric h') : IsBlockMetric (h + h') := by
  refine ⟨fun v w => ?_, fun v hv => ?_, fun ρ ρ' v w hρ hv hw => ?_⟩
  · simp only [LinearMap.add_apply, map_add]
    rw [hh.1, hh'.1]
  · simp only [LinearMap.add_apply, Complex.add_re]
    exact add_pos (hh.2.1 v hv) (hh'.2.1 v hv)
  · simp only [LinearMap.add_apply]
    rw [hh.2.2 _ _ _ _ hρ hv hw, hh'.2.2 _ _ _ _ hρ hv hw, add_zero]

end Fibre

section Points

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ σ' : k →+* ℂ} {d : ℕ} {f : Y ⟶ X}

theorem spMap_conj_comp (σ : k →+* ℂ) : spMap ((starRingEnd ℂ).comp σ) = spMap (starRingEnd ℂ) ≫ spMap σ := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]
  rfl

def cjPt (y : CxPts p σ) : CxPts p ((starRingEnd ℂ).comp σ) :=
  ⟨spMap (starRingEnd ℂ) ≫ y.1, by
    have : y.1 ≫ p = spMap σ := y.2
    show (spMap (starRingEnd ℂ) ≫ y.1) ≫ p = _
    rw [Category.assoc, this, spMap_conj_comp]⟩

theorem cjPt_comp (f : Y ⟶ X) (y : CxPts p σ) : spMap (starRingEnd ℂ) ≫ y.1 ≫ f = (cjPt y).1 ≫ f :=
  (Category.assoc _ _ _).symm

theorem eq_conj {y : CxPts p σ} {y' : CxPts p σ'} (h : y'.1 = spMap (starRingEnd ℂ) ≫ y.1) :
    σ' = (starRingEnd ℂ).comp σ := by
  have h1 : y.1 ≫ p = spMap σ := y.2
  have h2 : y'.1 ≫ p = spMap σ' := y'.2
  rw [h, Category.assoc, h1, ← spMap_conj_comp] at h2
  exact (congrArg CommRingCat.Hom.hom (Spec.map_injective h2)).symm

theorem isLieMetric_add {R : AnRead p σ d}
    {h h' : ∀ y : CxPts p σ, TanM (y.1 ≫ f) t.G →ₗ[ℂ] TanM (y.1 ≫ f) t.G →ₗ⋆[ℂ] ℂ}
    (hh : IsLieMetric t f R h) (hh' : IsLieMetric t f R h') : IsLieMetric t f R fun y => h y + h' y := by
  refine ⟨fun y => isBlockMetric_add (hh.1 y) (hh'.1 y), fun V v w => ?_⟩
  obtain ⟨g, h1, h2, h3⟩ := hh.2 V v w
  obtain ⟨g', h1', h2', h3'⟩ := hh'.2 V v w
  exact ⟨fun y => g y + g' y, fun i => (h1 i).add (h1' i), fun i => (h2 i).add (h2' i),
    fun y hy => congrArg₂ (· + ·) (h3 y hy) (h3' y hy)⟩

theorem valAt_cjPt {V : Y.affineOpens} (v : TanM (LogKS.chart V ≫ f) t.G) {y : CxPts p σ}
    (hy : y ∈ ptsIn p σ V.1) (hy' : cjPt y ∈ ptsIn p _ V.1) :
    valAt f v hy' = tanPull (starRingEnd ℂ) (cjPt_comp f y) (valAt f v hy) := by
  have e : evHom hy' = (starRingEnd ℂ).comp (evHom hy) := RingHom.ext fun a => by
    rw [← ev_eq, CxPts.ev_conj (y := y) rfl hy, ev_eq hy]
    rfl
  refine tan_ext ?_
  show spMap (dualMap (evHom hy')) ≫ (tv v).left =
    spMap (dualMap (starRingEnd ℂ)) ≫ spMap (dualMap (evHom hy)) ≫ (tv v).left
  rw [e, ← Category.assoc, ← Spec.map_comp]
  congr 2
  exact FlagMod.dualMap_comp _ _

theorem family_congr
    (h : ∀ (σ : k →+* ℂ) (y : CxPts p σ), TanM (y.1 ≫ f) t.G →ₗ[ℂ] TanM (y.1 ≫ f) t.G →ₗ⋆[ℂ] ℂ)
    (es : σ = σ') {y : CxPts p σ} {y' : CxPts p σ'} (ey : y.1 = y'.1) {v w : TanM (y.1 ≫ f) t.G}
    {v' w' : TanM (y'.1 ≫ f) t.G} (ev : (tv v).left = (tv v').left) (ew : (tv w).left = (tv w').left) :
    h σ y v w = h σ' y' v' w' := by
  subst es
  obtain rfl := Subtype.ext ey
  rw [tan_ext ev, tan_ext ew]

end Points

theorem isLieMetric_cj {k : Type} [Field k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {d : ℕ} [SmoothOfRelativeDimension d p]
    {σ : k →+* ℂ} {f : Y ⟶ X}
    {h : ∀ y : CxPts p ((starRingEnd ℂ).comp σ), TanM (y.1 ≫ f) t.G →ₗ[ℂ] TanM (y.1 ≫ f) t.G →ₗ⋆[ℂ] ℂ}
    (hh : IsLieMetric t f (AnRead.all p _ d) h) :
    IsLieMetric t f (AnRead.all p σ d) fun y => cjForm (cjPt_comp f y) (h (cjPt y)) := by
  refine ⟨fun y => isBlockMetric_cjForm _ (hh.1 _), fun V v w => ?_⟩
  obtain ⟨g, h1, h2, h3⟩ := hh.2 V v w
  have hs : ptsIn p σ V.1 ⊆ cjPt ⁻¹' ptsIn p _ V.1 := fun y hy => CxPts.mem_ptsIn_conj (y := y) rfl hy
  have k1 := (T.conj_smoothOn_preimage_charts k Y p d _ σ cjPt (fun _ => rfl) _ _ (isOpen_ptsIn _) h1).2.1.mono hs
  have k2 := (T.conj_smoothOn_preimage_charts k Y p d _ σ cjPt (fun _ => rfl) _ _ (isOpen_ptsIn _) h2).2.1.mono hs
  refine ⟨fun y => starRingEnd ℂ (g (cjPt y)), k1, fun i => (k2 i).neg, fun y hy => ?_⟩
  beta_reduce
  rw [cjForm_apply, h3 _ (hs hy), valAt_cjPt v hy, valAt_cjPt w hy]

theorem exists_conj_family : ∀ (k : Type) [Field k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (d : ℕ) [SmoothOfRelativeDimension d p] (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (f : Y ⟶ X), IsProjOver p → (∀ σ : k →+* ℂ, (starRingEnd ℂ).comp σ ≠ σ) → ∃ h : ∀ (σ : k →+* ℂ) (y : CxPts p σ), TanM (y.1 ≫ f) t.G →ₗ[ℂ] TanM (y.1 ≫ f) t.G →ₗ⋆[ℂ] ℂ, (∀ σ, IsLieMetric t f (AnRead.all p σ d) (h σ)) ∧ ∀ σ σ' (y : CxPts p σ) (y' : CxPts p σ') (v w : TanM (y.1 ≫ f) t.G) (v' w' : TanM (y'.1 ≫ f) t.G), y'.1 = spMap (starRingEnd ℂ) ≫ y.1 → (tv v').left = spMap (dualMap (starRingEnd ℂ)) ≫ (tv v).left → (tv w').left = spMap (dualMap (starRingEnd ℂ)) ≫ (tv w).left → h σ' y' v' w' = starRingEnd ℂ (h σ y v w) := by
  intro k _ Y p d _ E _ _ _ H X t f hp _
  choose h hh using fun σ => LieMetExist.exists_isLieMetric k Y p d σ E H X t f hp
  refine ⟨fun σ y => h σ y + cjForm (cjPt_comp f y) (h _ (cjPt y)),
    fun σ => isLieMetric_add (hh σ) (isLieMetric_cj (hh _)), fun σ σ' y y' v w v' w' ey ev ew => ?_⟩
  have es := eq_conj ey
  have key : ∀ {a : Sp (DualNumber ℂ) ⟶ t.G.left},
      spMap (dualMap (starRingEnd ℂ)) ≫ spMap (dualMap (starRingEnd ℂ)) ≫ a = a := fun {a} => by
    rw [← Category.assoc, spMap_dual_conj_conj, Category.id_comp]
  beta_reduce
  rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.add_apply, LinearMap.add_apply, cjForm_apply, cjForm_apply,
    map_add, Complex.conj_conj, add_comm]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine congrArg _ (family_congr h ?_ ?_ ?_ ?_)
    · rw [es]
      exact RingHom.ext fun a => Complex.conj_conj _
    · show spMap (starRingEnd ℂ) ≫ y'.1 = y.1
      rw [ey, ← Category.assoc, spMap_conj_conj, Category.id_comp]
    · rw [tanPull_left, ev, key]
    · rw [tanPull_left, ew, key]
  · exact family_congr h es ey ev ew

end GlobalTheory.LieMetConj
