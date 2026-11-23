import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.StabSplit

section
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

open NumberField Matrix in
open scoped ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] in
theorem _root_.GlobalTheory.Mass.StabSplit.mem_perp (h : V →ₗ⋆[K] V →ₗ[K] K)
    (U : Submodule K V) (v : V) :
    v ∈ _root_.GlobalTheory.Mass.perp h U ↔ ∀ x ∈ U, h x v = 0 := by
  unfold _root_.GlobalTheory.Mass.perp
  simp [Submodule.mem_iInf, LinearMap.mem_ker]

theorem smul_eq_map (h : V →ₗ⋆[K] V →ₗ[K] K) (g : isom h) (U : Submodule K V) :
    g • U = U.map (g.1 : V →ₗ[K] V) := rfl

open NumberField Matrix in
open scoped ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] in
private lemma exists_preimage_mem_of_isom_smul_eq {h : V →ₗ⋆[K] V →ₗ[K] K} {g : _root_.Formalism.HermitianLatticesTheory.isom h}
    {U : Submodule K V} (hg : g • U = U) {x : V} (hx : x ∈ U) : ∃ u ∈ U, g.1 u = x := by
  rw [← hg, _root_.GlobalTheory.Mass.StabSplit.smul_eq_map] at hx
  obtain ⟨u, hu, hux⟩ := Submodule.mem_map.1 hx
  exact ⟨u, hu, hux⟩

open NumberField Matrix in
open scoped ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] in
private lemma isom_apply_mem_of_smul_eq {h : V →ₗ⋆[K] V →ₗ[K] K} {g : _root_.Formalism.HermitianLatticesTheory.isom h}
    {U : Submodule K V} (hg : g • U = U) {x : V} (hx : x ∈ U) : g.1 x ∈ U := by
  rw [← hg, _root_.GlobalTheory.Mass.StabSplit.smul_eq_map]
  exact Submodule.mem_map_of_mem hx

open NumberField Matrix in
open scoped ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] in

theorem _root_.GlobalTheory.Mass.StabSplit.smul_perp (h : V →ₗ⋆[K] V →ₗ[K] K) (g : _root_.Formalism.HermitianLatticesTheory.isom h)
    (U : Submodule K V) (hg : g • U = U) :
    g • _root_.GlobalTheory.Mass.perp h U = _root_.GlobalTheory.Mass.perp h U := by
  ext v
  rw [_root_.GlobalTheory.Mass.StabSplit.smul_eq_map, Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [_root_.GlobalTheory.Mass.StabSplit.mem_perp] at hw ⊢
    intro x hx
    obtain ⟨u, hu, rfl⟩ := exists_preimage_mem_of_isom_smul_eq hg hx
    have hiso : h (g.1 u) (g.1 w) = h u w := g.2 u w
    simp only [LinearEquiv.coe_coe] at hiso ⊢
    rw [hiso]
    exact hw u hu
  · intro hv
    refine ⟨g.1.symm v, ?_, by simp⟩
    rw [_root_.GlobalTheory.Mass.StabSplit.mem_perp] at hv ⊢
    intro x hx
    have hiso : h (g.1 x) (g.1 (g.1.symm v)) = h x (g.1.symm v) := g.2 x (g.1.symm v)
    rw [← hiso, LinearEquiv.apply_symm_apply]
    exact hv _ (isom_apply_mem_of_smul_eq hg hx)

noncomputable def res (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (g : isom h)
    (hg : g • U = U) : isom (hRes h U) :=
  ⟨g.1.ofSubmodules U U hg, fun x y => g.2 x y⟩

@[simp] theorem res_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (g : isom h)
    (hg : g • U = U) (x : U) : (((res h U g hg).1 x : U) : V) = g.1 x := rfl

open NumberField Matrix in
open scoped ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] in
theorem _root_.GlobalTheory.Mass.StabSplit.latIn_smul {R : Type} [CommRing R] [Algebra R K] [Module R V]
    [IsScalarTower R K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (g : _root_.Formalism.HermitianLatticesTheory.isom h)
    (hg : g • U = U) (L : Submodule R V) :
    _root_.GlobalTheory.Mass.latIn U (g • L) =
      _root_.GlobalTheory.Mass.StabSplit.res h U g hg • _root_.GlobalTheory.Mass.latIn U L := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ : ∃ y ∈ L, g.1 y = (x : V) := hx
    obtain ⟨u, hu, hux⟩ := exists_preimage_mem_of_isom_smul_eq hg x.2
    have huy : u = y := g.1.injective (hux.trans hyx.symm)
    subst huy
    exact ⟨⟨u, hu⟩, hy, Subtype.ext hux⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(y : V), hy, rfl⟩

noncomputable def resHom (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) :
    MulAction.stabilizer (isom h) U →* isom (hRes h U) × isom (hRes h (perp h U)) :=
  MonoidHom.mk' (fun γ => (res h U γ.1 γ.2, res h (perp h U) γ.1 (smul_perp h γ.1 U γ.2)))
    fun _ _ => rfl

end

open NumberField Matrix in
open scoped ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] in
private lemma apply_self_ne_zero_of_PD_of_numberField [NumberField K] {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hpd : _root_.GlobalTheory.Mass.PD h) {x : V} (hx : x ≠ 0) : h x x ≠ 0 := by
  obtain ⟨τ⟩ := (inferInstance : Nonempty (K →+* ℂ))
  have hpos := hpd τ x hx
  intro hzero
  rw [hzero, map_zero, Complex.zero_re] at hpos
  exact lt_irrefl 0 hpos

open NumberField Matrix in
open scoped ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] in
private lemma disjoint_perp_of_PD [NumberField K]
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hpd : _root_.GlobalTheory.Mass.PD h) (U : Submodule K V) :
    Disjoint U (_root_.GlobalTheory.Mass.perp h U) := by
  rw [Submodule.disjoint_def]
  intro x hxU hxW
  by_contra hx
  exact apply_self_ne_zero_of_PD_of_numberField hpd hx
    ((_root_.GlobalTheory.Mass.StabSplit.mem_perp h U x).1 hxW x hxU)

open NumberField Matrix in
open scoped ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] in
private lemma finrank_le_finrank_add_finrank_perp [FiniteDimensional K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) :
    Module.finrank K V ≤
      Module.finrank K U + Module.finrank K (_root_.GlobalTheory.Mass.perp h U) := by
  set b := Module.finBasis K U
  let F : V →ₗ[K] (Fin (Module.finrank K U) → K) := LinearMap.pi fun i => h (b i : V)
  have hker : LinearMap.ker F = _root_.GlobalTheory.Mass.perp h U := by
    ext v
    rw [LinearMap.mem_ker, _root_.GlobalTheory.Mass.StabSplit.mem_perp]
    constructor
    · intro hv x hx
      have hzero : (h.flip v).comp U.subtype = 0 := b.ext fun i => by
        simpa [F] using congrFun hv i
      simpa using LinearMap.congr_fun hzero ⟨x, hx⟩
    · intro hv
      funext i
      simpa [F] using hv (b i : V) (b i).2
  have hrn := LinearMap.finrank_range_add_finrank_ker F
  have hle : Module.finrank K (LinearMap.range F) ≤ Module.finrank K U := by
    simpa using Submodule.finrank_le (LinearMap.range F)
  rw [hker] at hrn
  omega

open NumberField Matrix in
open scoped ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] in
private lemma isCompl_perp_of_PD [NumberField K] [FiniteDimensional K V]
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hpd : _root_.GlobalTheory.Mass.PD h) (U : Submodule K V) :
    IsCompl U (_root_.GlobalTheory.Mass.perp h U) := by
  have hdisj := disjoint_perp_of_PD hpd U
  refine ⟨hdisj, codisjoint_iff.2 ?_⟩
  apply Submodule.eq_top_of_finrank_eq
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq U (_root_.GlobalTheory.Mass.perp h U)
  rw [disjoint_iff.1 hdisj, finrank_bot] at hsum
  have hle := finrank_le_finrank_add_finrank_perp h U
  have hle' := Submodule.finrank_le (U ⊔ _root_.GlobalTheory.Mass.perp h U)
  omega

open NumberField Matrix in
open scoped ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] in
private lemma apply_add_add_of_mem_perp {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    {U : Submodule K V} {u u' w w' : V} (hu' : u' ∈ U) (hu : u ∈ U)
    (hw : w ∈ _root_.GlobalTheory.Mass.perp h U)
    (hw' : w' ∈ _root_.GlobalTheory.Mass.perp h U) :
    h (u + w) (u' + w') = h u u' + h w w' := by
  have h1 : h u w' = 0 := (_root_.GlobalTheory.Mass.StabSplit.mem_perp h U w').1 hw' u hu
  have h2 : h w u' = 0 := by
    rw [← hs.eq u' w, (_root_.GlobalTheory.Mass.StabSplit.mem_perp h U w).1 hw u' hu',
      map_zero]
  simp only [map_add, LinearMap.add_apply, h1, h2]
  ring

open NumberField Matrix in
open scoped ENNReal Classical in

theorem _root_.GlobalTheory.Mass.StabSplit.main : ∀ (K V : Type) [Field K] [NumberField K]
    [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), _root_.Formalism.HermitianLatticesTheory.IsCMUnram K → h.IsSymm →
    _root_.GlobalTheory.Mass.PD h → ∀ U : Submodule K V,
    ∃ φ : MulAction.stabilizer (_root_.Formalism.HermitianLatticesTheory.isom h) U ≃*
      _root_.Formalism.HermitianLatticesTheory.isom (_root_.GlobalTheory.Mass.hRes h U) ×
        _root_.Formalism.HermitianLatticesTheory.isom (_root_.GlobalTheory.Mass.hRes h (_root_.GlobalTheory.Mass.perp h U)),
    ∀ (γ : MulAction.stabilizer (_root_.Formalism.HermitianLatticesTheory.isom h) U) (L : Submodule (𝓞 K) V),
      _root_.GlobalTheory.Mass.latIn U (γ • L) = (φ γ).1 • _root_.GlobalTheory.Mass.latIn U L ∧
      _root_.GlobalTheory.Mass.latIn (_root_.GlobalTheory.Mass.perp h U) (γ • L) =
        (φ γ).2 • _root_.GlobalTheory.Mass.latIn (_root_.GlobalTheory.Mass.perp h U) L := by
  intro K V _ _ _ _ _ _ _ _ h _ hs hpd U
  set W := _root_.GlobalTheory.Mass.perp h U with hW
  have hc : IsCompl U W := isCompl_perp_of_PD hpd U
  have hinj : Function.Injective (_root_.GlobalTheory.Mass.StabSplit.resHom h U) := by
    intro γ δ hγδ
    have eU : ∀ u ∈ U, γ.1.1 u = δ.1.1 u := fun u hu => by
      have := congrArg (fun p => ((p.1.1 ⟨u, hu⟩ : U) : V)) hγδ
      exact this
    have eW : ∀ w ∈ W, γ.1.1 w = δ.1.1 w := fun w hw => by
      have := congrArg (fun p => ((p.2.1 ⟨w, hw⟩ : W) : V)) hγδ
      exact this
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    have hv : v ∈ U ⊔ W := by rw [hc.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add, map_add, eU u hu, eW w hw]
  have hsurj : Function.Surjective (_root_.GlobalTheory.Mass.StabSplit.resHom h U) := by
    rintro ⟨a, c⟩
    let e := Submodule.prodEquivOfIsCompl U W hc
    let g : V ≃ₗ[K] V := e.symm.trans ((LinearEquiv.prodCongr a.1 c.1).trans e)
    have gU : ∀ u : U, g u = ((a.1 u : U) : V) := fun u => by
      simp [g, e, Submodule.prodEquivOfIsCompl_symm_apply_left]
    have gW : ∀ w : W, g w = ((c.1 w : W) : V) := fun w => by
      simp [g, e, Submodule.prodEquivOfIsCompl_symm_apply_right]
    have gsum : ∀ (u : U) (w : W), g ((u : V) + w) = ((a.1 u : U) : V) + (c.1 w : W) := by
      intro u w
      rw [map_add, gU, gW]
    have hiso : g ∈ _root_.Formalism.HermitianLatticesTheory.isom h := by
      intro x y
      obtain ⟨⟨u, w⟩, rfl⟩ := e.surjective x
      obtain ⟨⟨u', w'⟩, rfl⟩ := e.surjective y
      simp only [e, Submodule.coe_prodEquivOfIsCompl']
      rw [gsum, gsum, apply_add_add_of_mem_perp hs (a.1 u').2 (a.1 u).2 (c.1 w).2 (c.1 w').2,
        apply_add_add_of_mem_perp hs u'.2 u.2 w.2 w'.2]
      have ha : h (a.1 u : V) (a.1 u' : V) = h u u' := by
        exact a.2 u u'
      have hc' : h (c.1 w : V) (c.1 w' : V) = h w w' := by
        exact c.2 w w'
      rw [ha, hc']
    have hstab : (⟨g, hiso⟩ : _root_.Formalism.HermitianLatticesTheory.isom h) • U = U := by
      rw [_root_.GlobalTheory.Mass.StabSplit.smul_eq_map]
      apply le_antisymm
      · rw [Submodule.map_le_iff_le_comap]
        intro u hu
        show g u ∈ U
        rw [show u = ((⟨u, hu⟩ : U) : V) from rfl, gU]
        exact (a.1 _).2
      · intro u hu
        refine ⟨((a.1.symm ⟨u, hu⟩ : U) : V), (a.1.symm ⟨u, hu⟩).2, ?_⟩
        show g _ = u
        rw [gU, LinearEquiv.apply_symm_apply]
    exact ⟨⟨⟨g, hiso⟩, hstab⟩, Prod.ext (Subtype.ext (LinearEquiv.ext fun u => Subtype.ext (gU u)))
      (Subtype.ext (LinearEquiv.ext fun w => Subtype.ext (gW w)))⟩
  refine ⟨MulEquiv.ofBijective (_root_.GlobalTheory.Mass.StabSplit.resHom h U) ⟨hinj, hsurj⟩,
    fun γ L => ⟨?_, ?_⟩⟩
  · exact _root_.GlobalTheory.Mass.StabSplit.latIn_smul h U γ.1 γ.2 L
  · exact _root_.GlobalTheory.Mass.StabSplit.latIn_smul h W γ.1
      (_root_.GlobalTheory.Mass.StabSplit.smul_perp h γ.1 U γ.2) L

end GlobalTheory.Mass.StabSplit
