import Mathlib
import Development.AutomorphicArithmetic.DivisorFrames.FlagCarriesEigenframe
import Development.AutomorphicArithmetic.LocalEmbeddings.ConsAgree
import Development.AutomorphicArithmetic.LocalEmbeddings.ConsMatch
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ConsGeo

noncomputable section

namespace UpperTheory.MFib

open GlobalTheory.ShFam.Pad.Pull GlobalTheory.LieMet
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv actR)
open MonObj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

section Frames

variable {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {l l' : Level H} {c : Coeff l} {c' : Coeff l'}
  {g : X' ⟶ X} (mu : SABMap t' t g) {R : Type} [CommRing R] {x' : Sp R ⟶ X'} {x : Sp R ⟶ X} (hx : x' ≫ g = x)

include hx

private theorem exists_lift {w : Sp (DualNumber R) ⟶ t.G.left} (hw : IsTanAtG t x w) :
    ∃ v, IsTanAtG t' x' v ∧ v ≫ mu.φ = w := by
  obtain ⟨v, hv⟩ := (pushE mu x' hx).surjective (tanOf hw)
  exact ⟨(tv v).left, isTan_tv v, congrArg (fun z => (tv z).left) hv⟩

private theorem eig_pull {v : Sp (DualNumber R) ⟶ t'.G.left} (hv : IsTanAtG t' x' v) (a : 𝓞 E) (s : R)
    (h : (v ≫ mu.φ) ≫ (t.act.act a).left = spMap (epsMul s) ≫ v ≫ mu.φ) :
    v ≫ (t'.act.act a).left = spMap (epsMul s) ≫ v := by
  refine (eig_iff (tanOf hv) a s).2 ((pushE mu x' hx).injective ?_)
  rw [pushE_act, map_smul]
  exact (eig_iff _ a _).1 h

private theorem frame_pull {f' : c'.F →+* R} {f : c.F →+* R} (hf : ∀ τ a, f (embK c τ a) = f' (embK c' τ a))
    {u : Vecs Dw t' R} (hu : ∀ τ i, IsTanAtG t' x' (u τ i))
    (h : GlobalTheory.LocM.IsFrame (Dw := Dw) t f x fun τ i => u τ i ≫ mu.φ) : GlobalTheory.LocM.IsFrame t' f' x' u := by
  refine ⟨fun τ i => ⟨hu τ i, fun a => ?_⟩, fun τ w hw he => ?_⟩
  · rw [← hf]
    exact eig_pull mu hx (hu τ i) a _ ((h.1 τ i).2 a)
  · refine (existsUnique_congr fun cf => comb_push mu hx (hu τ) hw cf).1
      (h.2 τ _ (isTan_push mu x' hx hw) fun a => ?_)
    rw [Category.assoc, ← mu.act, ← Category.assoc, he, hf, Category.assoc]

end Frames

private theorem sameFlag_of_tri {X : Scheme.{0}} {t : SAB H X} {k : Type} [Field k] {x : Sp k ⟶ X} {u u' : Vecs Dw t k}
    (ty : (E →+* ℂ) → Finset ℕ) (h : ∀ τ, Pull.Tri t x (u τ) (u' τ)) : SameFlag ty t x u u' := fun τ n _ i hi => by
  obtain ⟨cf, h1, h2⟩ := h τ i
  exact ⟨cf, fun j hj => h1 j (Fin.lt_def.2 (by omega)), h2⟩

private theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective (a₁ := CommRingCat.ofHom _) (a₂ := CommRingCat.ofHom _) h)

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

private theorem mono_j (i : Idx H p) : Mono (Y i).j := by
  have := (Y i).jQ_open
  have := mono_spMap_subtype (i.c.V W)
  rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j]
  infer_instance

private theorem snd_of_chart (Z : LocM.Mdl Y i₀) {a : Fin Z.m} {R : Type} [CommRing R] {φ : Γ(Z.X, (Z.U a).1) →+* R}
    {w : Sp R ⟶ Z.X} (h : spMap φ ≫ Z.chart a = w) {y : Sp R ⟶ (Xo Z.i.l).XF Z.i.c} (hy : w ≫ Z.π = y ≫ (Y Z.i).j) :
    y ≫ pullback.snd _ _ = spMap (φ.comp (Z.alg a)) := by
  have := mono_spMap_subtype (Z.i.c.V W)
  rw [← cancel_mono (spMap (Z.i.c.V W).subtype), ← affineOpenChart_comp_structure_eq_spMap Z h, reassoc_of% hy, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j,
    Category.assoc, Category.assoc, pullback.condition, reassoc_of% (Y Z.i).jQ_over]

private theorem flagAt_tri (Z : LocM.Mdl Y i₀) (hty : ∀ τ k, k ≤ Dw.mult τ → k ∈ Z.ty τ) {k : Type} [Field k]
    {w w' : Sp k ⟶ Z.X} {y : Sp k ⟶ (Xo Z.i.l).XF Z.i.c} (hw : w ≫ Z.π = y ≫ (Y Z.i).j)
    (hw' : w' ≫ Z.π = y ≫ (Y Z.i).j) {u u' : Vecs Dw (Y Z.i).t k} (h : Z.FlagAt w u) (h' : Z.FlagAt w' u')
    (ht : ∀ τ, Pull.Tri (Y Z.i).t (y ≫ (Y Z.i).j) (u' τ) (u τ)) : w = w' := by
  have h₀ := h
  obtain ⟨a, φ, c, F, -⟩ := h
  obtain ⟨a', φ', c', F', S'⟩ := h'
  have e := snd_of_chart Z c hw
  have e' : φ.comp (Z.alg a) = φ'.comp (Z.alg a') := spMap_inj (e.symm.trans (snd_of_chart Z c' hw'))
  refine (Z.bij k _ y e u (hw ▸ F)).unique ⟨hw, h₀⟩ ⟨hw', a', φ', c', ?_, sameFlag_of_tri _ fun τ => ?_⟩
  · rw [← e', hw', ← hw]
    exact F
  · exact (tri_of_sameFlag hty S' τ).trans (frame_ind (chart_frame Z c') τ).1 (frame_ind F' τ).1 (hw' ▸ ht τ)

end UpperTheory.MFib

end

open UpperTheory.MFib GlobalTheory.ShFam.Pad.Pull GlobalTheory.LieMet in
theorem UpperTheory.level_flag_multiplicity :
    ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p} {O : Type} [CommRing O] {β : O →+* i₀.c.F} {Z : LocM.Mdl Y i₀} {T : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model (Xo i₀.l) i₀.c β} {F : Type} [Field F] {e : F ≃+* i₀.c.F} (L : Lev Z T) (C : FlagCpt T e), (∀ τ k, k ≤ Dw.mult τ → k ∈ Z.ty τ) → ∀ {k : Type} [Field k] (q : Sp k ⟶ C.Y.X) (y : Sp k ⟶ (Xo i₀.l).XF i₀.c), q ≫ C.π = y ≫ T.jQ → Nonempty ({w : Sp k ⟶ Z.X // Match L C w q} ≃ {y₂ : Sp k ⟶ (Xo Z.i.l).XF Z.i.c // y₂ ≫ L.r = y}) := by
  intro E _ _ _ H Dw Xo p W Y i₀ O _ β Z T F _ e L C hty k _ q y hq
  have := T.jQ_open
  have := mono_j (Y := Y) Z.i
  obtain ⟨⟨φ₀, g₀, hg₀⟩, hc⟩ := UpperTheory.flag_carries_eigenframe C k q
  have hr : ∀ {y₂ : Sp k ⟶ (Xo Z.i.l).XF Z.i.c}, q ≫ C.π = y₂ ≫ L.r ≫ T.jQ → y₂ ≫ L.r = y := fun h => by
    rw [← cancel_mono T.jQ, Category.assoc, ← h, hq]
  have hx : ∀ {y₂ : Sp k ⟶ (Xo Z.i.l).XF Z.i.c}, q ≫ C.π = y₂ ≫ L.r ≫ T.jQ →
      (y₂ ≫ L.r) ≫ T.jQ ≫ pullback.fst _ _ = q ≫ C.π ≫ genι T := fun h => by
    rw [reassoc_of% h, Category.assoc]
  refine ⟨Equiv.ofBijective (fun w => ⟨w.2.choose, ?_⟩) ⟨?_, ?_⟩⟩
  · obtain ⟨v, φ, g, -, h, -⟩ := w.2.choose_spec
    exact hr h
  · intro w w' h
    obtain ⟨v, φ, g, h1, h2, h3, h4, h5, h6⟩ := w.2.choose_spec
    obtain ⟨v', φ', g', h1', h2', h3', h4', h5', h6'⟩ := w'.2.choose_spec
    have h0 : w.2.choose = w'.2.choose := congrArg Subtype.val h
    rw [← h0] at h1' h2' h3'
    refine Subtype.ext (flagAt_tri Z hty h1 h1' h4 h4' fun τ j => ?_)
    obtain ⟨t, -, -, ht⟩ := ((hc φ' _ g' h5').2.2 φ _ g).1 h5
    obtain ⟨cf, -, c1, c2⟩ := ht τ j
    have hid : spMap (dualMap (RingHom.id k)) = 𝟙 _ := by
      rw [← Spec.map_id]
      congr 1
      ext r <;> simp [dualMap]
    simp only [hid, Category.id_comp, h6, h6', ← Category.assoc] at c2
    refine ⟨cf, c1, (comb_push (Y Z.i).m rfl (h3' τ) (h3 τ j) cf).2 ((comb_push L.ν rfl (h3' τ) (h3 τ j) cf).1
      ((comb_push T.m (hx h2) (fun i => isTan_push L.ν _ rfl (h3' τ i)) (isTan_push L.ν _ rfl (h3 τ j)) cf).1 ?_))⟩
    simpa only [Category.assoc] using c2
  · rintro ⟨y₂, hy₂⟩
    have h2 : q ≫ C.π = y₂ ≫ L.r ≫ T.jQ := by rw [hq, ← hy₂, Category.assoc]
    let f : Z.i.c.F →+* k := (Spec.preimage (y₂ ≫ pullback.snd _ _)).hom
    have hf : y₂ ≫ pullback.snd _ _ = spMap f := (Spec.map_preimage _).symm
    have hφ : φ₀ = f.comp (incl Z) := by
      refine spMap_inj ?_
      rw [← (hc φ₀ _ g₀ hg₀).2.1, reassoc_of% h2, T.jQ_over, L.snd, reassoc_of% hf, ModelRelProbe.spMap_comp]
    choose v₁ t₁ e₁ using fun τ i => exists_lift T.m (hx h2) (g₀.tan τ i)
    choose v t e using fun τ i => exists_lift L.ν (x' := y₂) rfl (t₁ τ i)
    have F₀ : GlobalTheory.LocM.IsFrame (Dw := Dw) T.t φ₀ (q ≫ C.π ≫ genι T) fun τ i => v₁ τ i ≫ T.m.φ := by
      simp only [e₁]
      exact ⟨fun τ i => ⟨g₀.tan τ i, g₀.eig τ i⟩, g₀.basis⟩
    have F₁ : GlobalTheory.LocM.IsFrame (Dw := Dw) T.oF.t φ₀ (y₂ ≫ L.r) fun τ i => v τ i ≫ L.ν.φ := by
      simp only [e]
      exact frame_pull T.m (hx h2) (fun _ _ => rfl) t₁ F₀
    have F₂ : GlobalTheory.LocM.IsFrame (Dw := Dw) (Y Z.i).oF.t f y₂ v :=
      frame_pull L.ν rfl (fun τ a => by rw [hφ]; rfl) t F₁
    obtain ⟨w, ⟨w1, w2⟩, -⟩ := Z.bij k f y₂ hf _ (frame_push (Y Z.i).m rfl (fun _ _ => rfl) F₂)
    have hm : Match L C w q := ⟨y₂, v, φ₀, g₀, w1, h2, t, w2, hg₀, fun τ i => by rw [reassoc_of% e, e₁]⟩
    refine ⟨⟨w, hm⟩, Subtype.ext ?_⟩
    obtain ⟨_, _, _, h1, -⟩ := hm.choose_spec
    exact (cancel_mono (Y Z.i).j).1 (h1.symm.trans w1)
