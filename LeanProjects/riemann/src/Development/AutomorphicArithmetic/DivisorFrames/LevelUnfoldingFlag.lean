import Mathlib
import Development.AutomorphicArithmetic.DivisorFrames.FlagTorusGenericPoint
import Development.AutomorphicArithmetic.DivisorFrames.FlagCarriesEigenframe
import Development.AutomorphicArithmetic.LocalEmbeddings.ConsAgree
import Development.AutomorphicArithmetic.LocalEmbeddings.ConsMatch
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ConsGeo

section
open GlobalTheory.ShFam.Pad.Pull GlobalTheory.LieMet MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv actR)

attribute [local instance] Over.cartesianMonoidalCategory

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

theorem UpperTheory.level_unfolding_flag :
    ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p} {O : Type} [CommRing O] {β : O →+* i₀.c.F} {Z : LocM.Mdl Y i₀} {T : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model (Xo i₀.l) i₀.c β} {F : Type} [Field F] {e : F ≃+* i₀.c.F} {σ : i₀.c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf (Xo i₀.l) i₀.c σ N} (Φ : FlagTor T e U) (L : Lev Z T) {k : Type} [Field k] (w : Sp k ⟶ Z.X), w (closedPoint k) ∈ Z.opn → ∃ (c : U.Comp) (q : Sp k ⟶ (Φ.C c).Y.X), Match L (Φ.C c) w q := by
  intro E _ _ _ H Dw Xo p W Y i₀ O _ β Z T F _ e σ N U Φ L k _ w hw
  rw [← Z.cover] at hw
  obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hw
  obtain ⟨φ, hφ⟩ := exists_fromSpec (Z.U a).2 w fun q _ => by
    have : q = closedPoint k := Subsingleton.elim (α := PrimeSpectrum k) _ _
    rw [this]; exact ha
  have hφ' : spMap φ ≫ Z.chart a = w := hφ
  obtain ⟨y, hy⟩ := exists_open_lift Z hφ'
  have hys : y ≫ pullback.snd _ _ = spMap (φ.comp (Z.alg a)) := by
    have := mono_spMap_subtype (Z.i.c.V W)
    have hjs : (Y Z.i).j ≫ (Y Z.i).s = pullback.snd _ _ ≫ spMap (Z.i.c.V W).subtype := by
      unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j
      rw [Category.assoc, pullback.condition, ← Category.assoc, (Y Z.i).jQ_over]
    rw [← cancel_mono (spMap (Z.i.c.V W).subtype), Category.assoc, ← hjs, reassoc_of% hy, affineOpenChart_comp_structure_eq_spMap Z hφ']
  have hu := chart_frame Z hφ'
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
  obtain ⟨⟨c, q⟩, ⟨hq, hC⟩, -⟩ := UpperTheory.flag_torus_generic_point Φ k φ' _ hx g
  have tr : ∀ (x x' : Sp k ⟶ T.X) (g : EigFrame T φ' x), x' = x → (Φ.C c).Carries q g →
      ∃ g' : EigFrame T φ' x', (Φ.C c).Carries q g' ∧ g'.v = g.v := by
    rintro x _ g rfl h
    exact ⟨g, h, rfl⟩
  obtain ⟨g', hg', hgv⟩ := tr _ (q ≫ (Φ.C c).π ≫ genι T) g (by rw [← Category.assoc]; exact congrArg (· ≫ genι T) hq) hC
  have huv : (fun τ i => v τ i ≫ (Y Z.i).m.φ) = (Z.fr a).bc φ := funext fun τ => funext fun i => hvu τ i
  refine ⟨c, q, y, v, φ', g', hy.symm, hq, fun τ i => (hv.1 τ i).1, ?_, hg', fun τ i => ?_⟩
  · rw [huv]
    refine ⟨a, φ, hφ', hu, fun τ n _ i hi => ⟨Pi.single i 1, fun j hj => Pi.single_eq_of_ne ?_ _,
      isCombAtG_single _ _ (fun j => (hu.1 τ j).1) i⟩⟩
    rintro rfl
    omega
  · rw [hgv]
    exact Category.assoc _ _ _

end
