import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHtFunGenericIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField Filter Topology TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CxPts GlobalTheory.Points
open scoped ContDiff

namespace GlobalTheory.MetFam

section Fam

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
  {F G : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

def FamAt (t : ℝ → ℝ) (u : ℝ → CxPts p σ → F) (u₀ : CxPts p σ → F) (y : CxPts p σ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (f : CxPts p σ → ι → ℂ) (Φ : ℝ × (ι → ℂ) → F) (O : Set (ℝ × (ι → ℂ))),
    VInfAt f y ∧ IsOpen O ∧ (0, f y) ∈ O ∧ ContDiffOn ℝ ∞ Φ O ∧ (u₀ =ᶠ[𝓝 y] fun z => Φ (0, f z)) ∧
      ∀ᶠ x : ℝ × CxPts p σ in atTop ×ˢ 𝓝 y, u x.1 x.2 = Φ (t x.1, f x.2)

variable {t : ℝ → ℝ} {u u' : ℝ → CxPts p σ → F} {u₀ u₀' : CxPts p σ → F} {y : CxPts p σ}

theorem FamAt.congr (h : FamAt t u u₀ y) (e : ∀ᶠ x : ℝ × CxPts p σ in atTop ×ˢ 𝓝 y, u' x.1 x.2 = u x.1 x.2)
    (e₀ : u₀' =ᶠ[𝓝 y] u₀) : FamAt t u' u₀' y :=
  have ⟨ι, i, f, Φ, O, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  ⟨ι, i, f, Φ, O, h₁, h₂, h₃, h₄, e₀.trans h₅, (e.and h₆).mono fun _ hx => hx.1.trans hx.2⟩

theorem famAt_param (t : ℝ → ℝ) (y : CxPts p σ) : FamAt t (fun R _ => t R) (fun _ => (0 : ℝ)) y :=
  ⟨Empty, inferInstance, fun _ => 0, Prod.fst, univ, vInfAt_const _ _, isOpen_univ, trivial, contDiff_fst.contDiffOn,
    EventuallyEq.rfl, .of_forall fun _ => rfl⟩

theorem famAt_const (h : VInfAt u₀ y) (t : ℝ → ℝ) : FamAt t (fun _ => u₀) u₀ y := by
  obtain ⟨W, ι, _, g, Φ, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  exact ⟨ι, inferInstance, fun z a => ev p σ W (g a) z, fun x => Φ x.2, Prod.snd ⁻¹' O,
    vInfAt_pi fun a => vInfAt_ev _ h₁, h₂.preimage continuous_snd, h₃,
    h₄.comp contDiff_snd.contDiffOn fun _ hx => hx, h₅, tendsto_snd.eventually h₅⟩

theorem FamAt.comp (h : FamAt t u u₀ y) {Ψ : F → G} {T : Set F} (hT : IsOpen T) (hy : u₀ y ∈ T)
    (hΨ : ContDiffOn ℝ ∞ Ψ T) : FamAt t (fun R z => Ψ (u R z)) (fun z => Ψ (u₀ z)) y := by
  obtain ⟨ι, _, f, Φ, O, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  exact ⟨ι, inferInstance, f, Ψ ∘ Φ, O ∩ Φ ⁻¹' T, h₁, h₄.continuousOn.isOpen_inter_preimage h₂ hT,
    ⟨h₃, mem_preimage.2 (h₅.self_of_nhds ▸ hy :)⟩, hΨ.comp (h₄.mono inter_subset_left) fun _ hv => hv.2,
    h₅.fun_comp Ψ, h₆.mono fun _ hx => congrArg Ψ hx⟩

theorem FamAt.comp_contDiff (h : FamAt t u u₀ y) {Ψ : F → G} (hΨ : ContDiff ℝ ∞ Ψ) :
    FamAt t (fun R z => Ψ (u R z)) (fun z => Ψ (u₀ z)) y := h.comp isOpen_univ trivial hΨ.contDiffOn

theorem FamAt.prodMk {v : ℝ → CxPts p σ → G} {v₀ : CxPts p σ → G} (h : FamAt t u u₀ y) (h' : FamAt t v v₀ y) :
    FamAt t (fun R z => (u R z, v R z)) (fun z => (u₀ z, v₀ z)) y := by
  obtain ⟨ι, _, f, Φ, O, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  obtain ⟨ι', _, f', Φ', O', h₁', h₂', h₃', h₄', h₅', h₆'⟩ := h'
  have cl : ContDiff ℝ ∞ fun (x : ℝ × (ι ⊕ ι' → ℂ)) => (x.1, fun a => x.2 (.inl a)) :=
    contDiff_fst.prodMk (contDiff_pi.2 fun a => (contDiff_apply ℝ ℂ _).comp contDiff_snd)
  have cr : ContDiff ℝ ∞ fun (x : ℝ × (ι ⊕ ι' → ℂ)) => (x.1, fun a => x.2 (.inr a)) :=
    contDiff_fst.prodMk (contDiff_pi.2 fun a => (contDiff_apply ℝ ℂ _).comp contDiff_snd)
  refine ⟨ι ⊕ ι', inferInstance, fun z => Sum.elim (f z) (f' z),
    fun x => (Φ (x.1, fun a => x.2 (.inl a)), Φ' (x.1, fun a => x.2 (.inr a))),
    (fun x => (x.1, fun a => x.2 (.inl a))) ⁻¹' O ∩ (fun x => (x.1, fun a => x.2 (.inr a))) ⁻¹' O',
    vInfAt_pi fun a => ?_, (h₂.preimage cl.continuous).inter (h₂'.preimage cr.continuous), ⟨h₃, h₃'⟩,
    (h₄.comp cl.contDiffOn fun _ hv => hv.1).prodMk (h₄'.comp cr.contDiffOn fun _ hv => hv.2), ?_, ?_⟩
  · rcases a with a | a
    exacts [h₁.comp_contDiff (contDiff_apply ℝ ℂ a), h₁'.comp_contDiff (contDiff_apply ℝ ℂ a)]
  · filter_upwards [h₅, h₅'] with z e e' using Prod.ext e e'
  · filter_upwards [h₆, h₆'] with z e e' using Prod.ext e e'

theorem famAt_pi {ι : Type} [Fintype ι] {w : ℝ → CxPts p σ → ι → F} {w₀ : CxPts p σ → ι → F}
    (h : ∀ a, FamAt t (fun R z => w R z a) (fun z => w₀ z a) y) : FamAt t w w₀ y := by
  classical
  have key (s : Finset ι) : FamAt t (fun R z => ∑ a ∈ s, Pi.single a (w R z a) : ℝ → CxPts p σ → ι → F)
      (fun z => ∑ a ∈ s, Pi.single a (w₀ z a)) y := by
    induction s using Finset.induction_on with
    | empty => simpa using famAt_const (vInfAt_const (0 : ι → F) y) t
    | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact ((h a).prodMk ih).comp_contDiff (Ψ := fun x => Pi.single a x.1 + x.2)
        (((ContinuousLinearMap.single ℝ (fun _ : ι => F) a).contDiff.comp contDiff_fst).add contDiff_snd)
  simpa only [Finset.univ_sum_single] using key Finset.univ

theorem FamAt.pull {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) {z : CxPts q σ}
    (h : FamAt t u u₀ (PtsOver.map π hπ _ z)) :
    FamAt t (fun R w => u R (PtsOver.map π hπ _ w)) (fun w => u₀ (PtsOver.map π hπ _ w)) z := by
  obtain ⟨ι, _, f, Φ, O, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  have hc := (PtsOver.continuous_map π hπ (spMap σ)).continuousAt (x := z)
  exact ⟨ι, inferInstance, fun w => f (PtsOver.map π hπ _ w), Φ, O, h₁.pull π hπ, h₂, h₃, h₄, hc.eventually h₅,
    (tendsto_id.prodMap hc).eventually h₆⟩

theorem tendstoUniformly_of_famAt [CompactSpace (CxPts p σ)] (ht : Tendsto t atTop (𝓝 0)) (h : ∀ y, FamAt t u u₀ y) :
    TendstoUniformly u u₀ atTop := by
  rw [← tendstoLocallyUniformly_iff_tendstoUniformly_of_compactSpace, tendstoLocallyUniformly_iff_forall_tendsto]
  intro y
  obtain ⟨ι, _, f, Φ, O, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h y
  have hΦ := h₄.continuousOn.continuousAt (h₂.mem_nhds h₃)
  have hf : Tendsto (fun x : ℝ × CxPts p σ => f x.2) (atTop ×ˢ 𝓝 y) (𝓝 (f y)) := h₁.continuousAt.tendsto.comp tendsto_snd
  have a₁ := hΦ.tendsto.comp ((tendsto_const_nhds (x := (0 : ℝ))).prodMk_nhds hf)
  have a₂ := hΦ.tendsto.comp ((ht.comp tendsto_fst).prodMk_nhds hf)
  refine ((a₁.prodMk_nhds a₂).mono_right (nhds_le_uniformity _)).congr' ?_
  filter_upwards [tendsto_snd.eventually h₅, h₆] with x e e'
  exact Prod.ext e.symm e'.symm

def VFam {E : X.Modules} {r : ℕ} (t : ℝ → ℝ) (h : ℝ → VMetric p E r) (h₀ : VMetric p E r) : Prop :=
  ∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ c : Chart E r, y ∈ ptsIn p σ c.U ∧
    ∀ a b, FamAt t (fun R z => ((h R).met σ).G c z a b) (fun z => (h₀.met σ).G c z a b) y

theorem VFam.pull {E : X.Modules} {r : ℕ} {h : ℝ → VMetric p E r} {h₀ : VMetric p E r} (H : VFam t h h₀)
    {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) : VFam t (fun R => (h R).pull π hπ) (h₀.pull π hπ) := fun σ z => by
  obtain ⟨c, hc, hf⟩ := H σ (PtsOver.map π hπ _ z)
  have hn : ∀ᶠ w in 𝓝 z, PtsOver.map π hπ _ w ∈ ptsIn p σ c.U :=
    (PtsOver.continuous_map π hπ (spMap σ)).continuousAt.eventually ((isOpen_ptsIn _).mem_nhds hc)
  refine ⟨c.pull h₀.isVB π, hc, fun a b => ((hf a b).pull π hπ).congr
    ((tendsto_snd.eventually hn).mono fun x hx => ?_) (hn.mono fun w hw => ?_)⟩
  · exact congrFun (congrFun (((h x.1).met σ).pull_G π hπ c hx) a) b
  · exact congrFun (congrFun ((h₀.met σ).pull_G π hπ c hw) a) b

def LFam (t : ℝ → ℝ) (L : ℝ → HermLB p) (L₀ : HermLB p) : Prop :=
  ∃ (u : ℝ → ∀ σ : k →+* ℂ, CxPts p σ → ℝ) (hu : ∀ R σ y, CInfAt (u R σ) y)
    (hc : ∀ R σ σ', (Weight.ofFun (u R σ)).IsConj (Weight.ofFun (u R σ'))),
    (∀ R, (L₀.raise (u R) (hu R) (hc R)).Isometric (L R)) ∧ ∀ σ y, FamAt t (fun R => u R σ) (fun _ => 0) y

end Fam

open GlobalTheory.ShFam GlobalTheory.Toroidal
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.QCoh (pullbackSections)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l}
    {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz] {β : Oz →+* c.F}
    {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}

def IsDualEigOn (G : ∀ σ', EigMet Z σ') {T : Scheme.{0}} (j : T ⟶ Z.X) {q : T ⟶ Sp Oz} {g : ℕ}
    (h : VMetric q ((Scheme.Modules.pullback j).obj (omega Z.t.G)) g) : Prop :=
  ∀ (σ' : c.F →+* ℂ) (yc : CxPts (genStr Z) σ') (y : CxPts q (σ'.comp β)), y.1 ≫ j = yc.1 ≫ genι Z →
    ∀ (u : EigFrame Z σ' (yc.1 ≫ genι Z)) (U : Z.X.Opens) (W : Z.t.G.left.Opens) (hU : U ≤ unitSec Z.t.G ⁻¹ᵁ W)
      (f f' : Γ(Z.t.G.left, W)), y ∈ ptsIn q (σ'.comp β) (j ⁻¹ᵁ U) →
      (h.met (σ'.comp β)).form (pullbackSections j _ (le_refl (j ⁻¹ᵁ U)) (dUnit Z.t.G hU f))
          (pullbackSections j _ (le_refl (j ⁻¹ᵁ U)) (dUnit Z.t.G hU f')) y =
        ∑ τ : E →+* ℂ, HermFrame.form ((G σ').gram yc u τ)⁻¹ (fun i => (valR (u.v τ i) W f).snd)
          fun i => (valR (u.v τ i) W f').snd

theorem isDualEigOn_pull {G : ∀ σ', EigMet Z σ'} {g : ℕ} {h : VMetric Z.s (omega Z.t.G) g}
    (hd : VdmRec.IsDualEig G h) {T : Scheme.{0}} (j : T ⟶ Z.X) {q : T ⟶ Sp Oz} (w : j ≫ Z.s = q) :
    IsDualEigOn G j (h.pull j w) :=
  fun σ' yc y e u U W hU f f' hy =>
    ((h.met _).form_pull j w _ _ le_rfl hy).trans (hd σ' yc (PtsOver.map j w _ y) e u U W hU f f' hy)

end GlobalTheory.MetFam

end
