import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializationMapCompUniversalSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncToroidalGenericBoundaryOfSncBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedNullSetCharts

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.GalCarry
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.ShFam.AutPull

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} (g : Y ≅ Y) (hg : g.hom ≫ p = p)
  {σ : k →+* ℂ} {D : ℕ}

include hg in

theorem inv_comp : g.inv ≫ p = p := by rw [Iso.inv_comp_eq, hg]

def ptMap (y : CxPts p σ) : CxPts p σ := ⟨y.1 ≫ g.hom, by rw [Category.assoc, hg, y.2]⟩

def ptH : CxPts p σ ≃ₜ CxPts p σ where
  toFun := ptMap g hg
  invFun := ptMap g.symm (inv_comp g hg)
  left_inv y := Subtype.ext (by simp [ptMap])
  right_inv y := Subtype.ext (by simp [ptMap])
  continuous_toFun := continuous_of_comp (f := g.hom) fun _ => rfl
  continuous_invFun := continuous_of_comp (f := g.inv) fun _ => rfl

@[simp] theorem ptH_apply (y : CxPts p σ) : ptH g hg y = ptMap g hg y := rfl

@[simp] theorem ptH_symm_apply (y : CxPts p σ) : (ptH g hg).symm y = ptMap g.symm (inv_comp g hg) y := rfl

def comapChart (c : AlgChart p σ D) : AlgChart p σ D where
  e := (ptH g hg).transOpenPartialHomeomorph c.e
  U := g.hom ⁻¹ᵁ c.U
  affine := c.affine.preimage_of_isIso g.hom
  x a := g.hom.app c.U (c.x a)
  etale := GlobalTheory.Mean4O.CoverExc.etale_app g.hom hg c.etale
    (RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso (g.hom.app c.U)))
  source_subset y hy := (mem_ptsIn_preimage (m := ptMap g hg) (fun _ => rfl)).2 (c.source_subset hy)
  apply_eq y hy a := (c.apply_eq _ hy a).trans (ev_of_comp (m := ptMap g hg) (fun _ => rfl) _ _ _)
  holo W f := by
    refine ((c.holo (g.inv ⁻¹ᵁ W) (g.inv.app W f)).mono fun v hv => ⟨hv.1,
      (mem_ptsIn_preimage (m := ptMap g.symm (inv_comp g hg)) (f := g.inv) (fun _ => rfl)).2 hv.2⟩).congr
      fun v _ => ?_
    exact ev_of_comp (m := ptMap g.symm (inv_comp g hg)) (f := g.inv) (fun _ => rfl) W f _

theorem comapChart_source (c : AlgChart p σ D) (y : CxPts p σ) :
    y ∈ (comapChart g hg c).e.source ↔ ptMap g hg y ∈ c.e.source := Iff.rfl

theorem levi_comapChart (c : AlgChart p σ D) (f : CxPts p σ → ℝ) (y : CxPts p σ) (ξ : Fin D → ℂ) :
    (comapChart g hg c).levi f y ξ = c.levi (f ∘ ptMap g.symm (inv_comp g hg)) (ptMap g hg y) ξ := rfl

end GlobalTheory.ShFam.AutPull

namespace GlobalTheory.ShFam.AutPull

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} (g : Y ≅ Y) (hg : g.hom ≫ p = p)
  {σ : k →+* ℂ} {D : ℕ}

@[simp] theorem ptMap_symm_ptMap (y : CxPts p σ) : ptMap g.symm (inv_comp g hg) (ptMap g hg y) = y :=
  (ptH g hg).left_inv y

@[simp] theorem ptMap_ptMap_symm (y : CxPts p σ) : ptMap g hg (ptMap g.symm (inv_comp g hg) y) = y :=
  (ptH g hg).right_inv y

def cpre (C : Closeds Y) : Closeds Y := ⟨g.hom.base ⁻¹' C, C.isClosed.preimage g.hom.base.hom.continuous⟩

theorem inv_hom_apply (a : Y) : g.hom (g.inv a) = a := by
  rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl

theorem hom_inv_apply (a : Y) : g.inv (g.hom a) = a := by
  rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]; rfl

include hg in
theorem liesIn_cpre (C : Closeds Y) (y : CxPts p σ) : LiesIn y (cpre g C) ↔ LiesIn (ptMap g hg y) C := by
  exact Iff.rfl

theorem compList_cpre {B : Set Y} {q : ℕ} {C : Fin q → Closeds Y} (h : ReciprocityTheory.AnForm.R.FinalTheorems.CompList B C)
    (hB : ∀ a, g.hom a ∈ B ↔ a ∈ B) : ReciprocityTheory.AnForm.R.FinalTheorems.CompList B (fun i => cpre g (C i)) := by
  refine ⟨fun j => ?_, ?_, fun i j hij => h.2.2 i j fun a ha => ?_⟩
  · have e : (cpre g (C j) : Set Y) = g.inv.base '' (C j : Set Y) := by
      ext a
      refine ⟨fun ha => ⟨g.hom a, ha, hom_inv_apply g a⟩, ?_⟩
      rintro ⟨b, hb, rfl⟩
      change g.hom (g.inv b) ∈ C j
      rwa [inv_hom_apply]
    rw [e]
    exact (h.1 j).image _ g.inv.base.hom.continuous.continuousOn
  · ext a
    simp only [Set.mem_iUnion]
    rw [← hB, ← h.2.1, Set.mem_iUnion]
    rfl
  · have := hij (show g.inv a ∈ cpre g (C i) from by change g.hom (g.inv a) ∈ C i; rwa [inv_hom_apply])
    change g.hom (g.inv a) ∈ C j at this
    rwa [inv_hom_apply] at this

theorem vanishingIdeal_cpre (C : Closeds Y) (W : Y.affineOpens) {t : Γ(Y, W.1)}
    (ht : (Scheme.IdealSheafData.vanishingIdeal C).ideal W = Ideal.span {t}) :
    (Scheme.IdealSheafData.vanishingIdeal (cpre g C)).ideal ⟨g.hom ⁻¹ᵁ W.1, W.2.preimage_of_isIso g.hom⟩ =
      Ideal.span {g.hom.app W.1 t} := by
  let φ : Γ(Y, W.1) ≃+* Γ(Y, g.hom ⁻¹ᵁ W.1) := (asIso (g.hom.app W.1)).commRingCatIsoToRingEquiv
  have hφ : ∀ s, φ s = g.hom.app W.1 s := fun _ => rfl
  ext u
  obtain ⟨s, rfl⟩ : ∃ s, φ s = u := φ.surjective u
  have key : φ s ∈ (Scheme.IdealSheafData.vanishingIdeal (cpre g C)).ideal ⟨g.hom ⁻¹ᵁ W.1, W.2.preimage_of_isIso g.hom⟩ ↔
      s ∈ (Scheme.IdealSheafData.vanishingIdeal C).ideal W := by
    rw [GlobalTheory.SncIso.mem_vanishingIdeal_ideal_iff, GlobalTheory.SncIso.mem_vanishingIdeal_ideal_iff, hφ, ← Scheme.preimage_basicOpen]
    constructor
    · intro H b hbU hbZ hbs
      refine H (g.inv b) ?_ ?_ ?_
      · change g.hom (g.inv b) ∈ W.1; rwa [inv_hom_apply]
      · change g.hom (g.inv b) ∈ C; rwa [inv_hom_apply]
      · change g.hom (g.inv b) ∈ Y.basicOpen s; rwa [inv_hom_apply]
    · intro H a haU haZ has
      exact H (g.hom a) haU haZ has
  rw [key, ht, Ideal.mem_span_singleton, Ideal.mem_span_singleton, ← hφ, map_dvd_iff]

theorem isDivNorm_cpre {R R' : AnRead p σ D} {C : Closeds Y} {n : CxPts p σ → ℝ} (h : IsDivNorm R C n) :
    IsDivNorm R' (cpre g C) (n ∘ ptMap g hg) := by
  refine ⟨fun y => h.1 _, fun y => ?_⟩
  obtain ⟨W, t, f, hy, ht, hf, e⟩ := h.2 (ptMap g hg y)
  have hm : ∀ z : CxPts p σ, (ptMap g hg z).1 = z.1 ≫ g.hom := fun _ => rfl
  refine ⟨⟨g.hom ⁻¹ᵁ W.1, W.2.preimage_of_isIso g.hom⟩, g.hom.app W.1 t, f ∘ ptMap g hg,
    (mem_ptsIn_preimage hm).2 hy, vanishingIdeal_cpre g C W ht, ?_, fun z hz => ?_⟩
  · exact (hf.comp_map (isOpen_ptsIn _) hm R').mono fun z hz => (mem_ptsIn_preimage hm).1 hz
  · have := e _ ((mem_ptsIn_preimage hm).1 hz)
    rw [ev_of_comp hm] at this
    exact this

include hg in

theorem isConjMap_conj {σ' : k →+* ℂ} {j : CxPts p σ' → CxPts p σ} (hj : IsConjMap j) :
    IsConjMap (fun z => ptMap g hg (j (ptMap g.symm (inv_comp g hg) z))) := fun z => by
  change (j _).1 ≫ g.hom = _
  rw [hj]
  change (spMap (starRingEnd ℂ) ≫ z.1 ≫ g.inv) ≫ g.hom = _
  simp

def pullForm (a : ChartForm p σ D) : ChartForm p σ D :=
  fun c y ξ => a (comapChart g.symm (inv_comp g hg) c) (ptMap g hg y) ξ

theorem ddcForm_comap (F : CxPts p σ → ℝ) (c : AlgChart p σ D) (y : CxPts p σ) (ξ : Fin D → ℂ) :
    ddcForm F (comapChart g.symm (inv_comp g hg) c) (ptMap g hg y) ξ = ddcForm (F ∘ ptMap g hg) c y ξ := by
  rw [ddcForm, ddcForm, levi_comapChart, ptMap_symm_ptMap]
  rfl

theorem mem_comap_source (c : AlgChart p σ D) (y : CxPts p σ) :
    ptMap g hg y ∈ (comapChart g.symm (inv_comp g hg) c).e.source ↔ y ∈ c.e.source := by
  rw [comapChart_source, ptMap_symm_ptMap]

theorem isPotential_pull {R R' : AnRead p σ D} {a : ChartForm p σ D} {S : Set (CxPts p σ)} {ψ : CxPts p σ → ℝ}
    (h : IsPotential R a S ψ) : IsPotential R' (pullForm g hg a) (ptMap g hg ⁻¹' S) (ψ ∘ ptMap g hg) :=
  ⟨h.1.preimage (ptH g hg).continuous, h.2.1.comp_map h.1 (fun _ => rfl) R', fun c y hy hyS ξ => by
    rw [pullForm, h.2.2 _ _ ((mem_comap_source g hg c y).2 hy) hyS ξ, ddcForm_comap]⟩

theorem isKaehlerForm_pull {R R' : AnRead p σ D} {a : ChartForm p σ D} (h : IsKaehlerForm R a) :
    IsKaehlerForm R' (pullForm g hg a) :=
  ⟨fun y => by
    obtain ⟨W, φ, hW, hp⟩ := h.1 (ptMap g hg y)
    exact ⟨_, _, hW, isPotential_pull g hg hp⟩,
    fun c y hy ξ hξ => h.2 _ _ ((mem_comap_source g hg c y).2 hy) ξ hξ⟩

theorem dtrans_eq_self {c c' : AlgChart p σ D} (h : ∀ z, c'.e z = c.e z) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (ξ : Fin D → ℂ) : c.dtrans c' y ξ = ξ := by
  funext b
  have e : c'.e ∘ c.e.symm =ᶠ[nhds (c.e y)] id :=
    Filter.eventually_of_mem (c.e.open_target.mem_nhds (c.e.map_source hy)) fun v hv => by
      simp only [Function.comp_apply, h, c.e.right_inv hv, id]
  rw [AlgChart.dtrans, e.fderiv_eq, fderiv_id]
  rfl

theorem isPotential_of_pull {R : AnRead p σ D} {a : ChartForm p σ D} (ha : IsKaehlerForm R a) {W : Set (CxPts p σ)}
    {φ : CxPts p σ → ℝ} (h : IsPotential R (pullForm g hg a) W φ) :
    IsPotential R a (ptMap g.symm (inv_comp g hg) ⁻¹' W) (φ ∘ ptMap g.symm (inv_comp g hg)) := by
  have h2 := isPotential_pull g.symm (inv_comp g hg) (R' := R) h
  refine ⟨h2.1, h2.2.1, fun c z hz hzW ξ => ?_⟩
  rw [← h2.2.2 c z hz hzW ξ]
  let c'' := comapChart g.symm (inv_comp g hg) (comapChart g hg c)
  have he : ∀ w, c''.e w = c.e w := fun w => by
    change c.e (ptMap g hg (ptMap g.symm (inv_comp g hg) w)) = _
    rw [ptMap_ptMap_symm]
  have hz'' : z ∈ c''.e.source := by
    change ptMap g hg (ptMap g.symm (inv_comp g hg) z) ∈ c.e.source
    rwa [ptMap_ptMap_symm]
  change a c z ξ = a c'' (ptMap g hg (ptMap g.symm (inv_comp g hg) z)) ξ
  rw [ptMap_ptMap_symm, ha.trans hz hz'' ξ, dtrans_eq_self he hz]

end GlobalTheory.ShFam.AutPull

namespace GlobalTheory.ShFam.AutPull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} [SmoothOfRelativeDimension Dw.dim (genStr Z)]

def auxiliary_data_pullback (T : Tw Z) (x : OddPrimesWithRootsOfUnity Z) : OddPrimesWithRootsOfUnity Z where
  m := x.m
  cpt i := cpre T.g (x.cpt i)
  cpt_list := compList_cpre T.g x.cpt_list T.mem_genBd
  nrm σ i := x.nrm σ i ∘ ptMap T.g T.g_str
  nrm_div σ i := isDivNorm_cpre T.g T.g_str (x.nrm_div σ i)
  nrm_conj σ σ' j hj i z := by
    have := x.nrm_conj σ σ' _ (isConjMap_conj T.g T.g_str hj) i (ptMap T.g T.g_str z)
    simpa using this
  kae σ := pullForm T.g T.g_str (x.kae σ)
  kae_kaehler σ := isKaehlerForm_pull T.g T.g_str (x.kae_kaehler σ)
  kae_conj σ σ' j hj W φ h := by
    have h1 := isPotential_of_pull T.g T.g_str (x.kae_kaehler σ) h
    have h2 := x.kae_conj σ σ' _ (isConjMap_conj T.g T.g_str hj) _ _ h1
    have h3 := isPotential_pull T.g T.g_str (R' := manifold Z σ') h2
    have e : (fun y => ptMap T.g.symm (inv_comp T.g T.g_str) (ptMap T.g T.g_str
        (j (ptMap T.g.symm (inv_comp T.g T.g_str) (ptMap T.g T.g_str y))))) = j := funext fun y => by simp
    have h4 : IsPotential (manifold Z σ') (pullForm T.g T.g_str (x.kae σ'))
        ((fun y => ptMap T.g.symm (inv_comp T.g T.g_str) (ptMap T.g T.g_str
          (j (ptMap T.g.symm (inv_comp T.g T.g_str) (ptMap T.g T.g_str y))))) ⁻¹' W)
        (φ ∘ fun y => ptMap T.g.symm (inv_comp T.g T.g_str) (ptMap T.g T.g_str
          (j (ptMap T.g.symm (inv_comp T.g T.g_str) (ptMap T.g T.g_str y))))) := h3
    rwa [e] at h4
  cst := x.cst
  cst_pos := x.cst_pos
  cst_small σ i ch y hy hL ξ := by
    have := x.cst_small σ i (comapChart T.g.symm (inv_comp T.g T.g_str) ch) (ptMap T.g T.g_str y)
      ((mem_comap_source T.g T.g_str ch y).2 hy) ((liesIn_cpre T.g T.g_str _ y).not.1 hL) ξ
    rw [ddcForm_comap] at this
    exact this
  met := x.met
  met_smooth := x.met_smooth
  met_conj := x.met_conj

theorem auxiliary_data_pullback_r (T : Tw Z) (x : OddPrimesWithRootsOfUnity Z) (σ : c.F →+* ℂ) (y : CxPts (genStr Z) σ) :
    (auxiliary_data_pullback T x).r σ y = x.r σ (T.pt y) := rfl

theorem exists_auxiliary_data_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F)
    (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) [SmoothOfRelativeDimension Dw.dim (genStr Z)] (T : Tw Z) (x : OddPrimesWithRootsOfUnity Z),
    ∃ x₁ : OddPrimesWithRootsOfUnity Z, ∀ σ y, x₁.r σ y = x.r σ (T.pt y) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ T x => ⟨auxiliary_data_pullback T x, auxiliary_data_pullback_r T x⟩

end GlobalTheory.ShFam.AutPull
