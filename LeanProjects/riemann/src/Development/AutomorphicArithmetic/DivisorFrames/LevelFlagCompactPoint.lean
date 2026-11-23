import Mathlib
import Development.AutomorphicArithmetic.DivisorFrames.FlagCarriesEigenframe
import Development.AutomorphicArithmetic.LocalEmbeddings.ConsAgree
import Development.AutomorphicArithmetic.LocalEmbeddings.ConsMatch
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameBaseChangeRingHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentCombinationPreservedByBaseChange
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.DominatesLiftUnique
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ConsGeo

private theorem spMap_dualMap_comp_spMap_dualMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (dualMap g) ≫ spMap (dualMap f) = spMap (dualMap (g.comp f)) := by
  rw [ModelRelProbe.spMap_comp]
  congr 1
  ext s <;> simp [Formalism.L2.Pj.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

private theorem analyticChartsRealization_comp_point_eq {A B B' D : Scheme.{0}} {a : A ⟶ B} {b : B ⟶ D} {a' : A ⟶ B'} {b' : B' ⟶ D}
    (h : a ≫ b = a' ≫ b') (z : A) : b' (a' z) = b (a z) := by
  rw [← Scheme.Hom.comp_apply, ← h, Scheme.Hom.comp_apply]

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

private theorem combination_base_change {X : Scheme.{0}} {t : SAB H X} {R k k' : Type} [CommRing R] [CommRing k] [CommRing k']
    (χ : R →+* k) (ψ : k →+* k') {x : Sp k ⟶ X} {x' : Sp k' ⟶ X} (hx : spMap ψ ≫ x = x') {m : ℕ}
    {v : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} {cf : Fin m → k} {w : Sp (DualNumber k) ⟶ t.G.left}
    (h : IsCombAtG t x (fun i => spMap (dualMap χ) ≫ v i) cf w) :
    IsCombAtG t x' (fun i => spMap (dualMap (ψ.comp χ)) ≫ v i) (fun i => ψ (cf i)) (spMap (dualMap ψ) ≫ w) := by
  have := (GlobalTheory.TanBaseChange.tan_comb_baseChange E H X t k k' ψ x x' hx).2 m _ cf w h
  simpa only [← Category.assoc, spMap_dualMap_comp_spMap_dualMap] using this

private theorem flagAt_base_change {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ}
    {Y : LocalSystem Xo p W} {i₀ : Idx H p} (Z : LocM.Pre Y i₀) {k k' : Type} [Field k] [Field k'] (ψ : k →+* k')
    {w : Sp k ⟶ Z.X} {u : Vecs Dw (Y Z.i).t k} (h : Z.FlagAt w u) : Z.FlagAt (spMap ψ ≫ w) (u.bc ψ) := by
  obtain ⟨a, φ, hw, hf, hs⟩ := h
  refine ⟨a, ψ.comp φ, by rw [← hw, ← Category.assoc, ModelRelProbe.spMap_comp], ?_, fun τ n hn i hi => ?_⟩
  · rw [Category.assoc, RingHom.comp_assoc]
    exact GlobalTheory.LocM.isFrame_bc E H Dw _ _ _ _ _ _ _ ψ _ _ hf
  · obtain ⟨cf, h0, hc⟩ := hs τ n hn i hi
    exact ⟨fun j => ψ (cf j), fun j hj => by simp only [h0 j hj, map_zero],
      combination_base_change φ ψ (Category.assoc _ _ _).symm hc⟩

private theorem carries_base_change {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    {T : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt T e)
    {k k' : Type} [Field k] [Field k'] (ψ : k →+* k') {φ : c.F →+* k} {x : Sp k ⟶ T.X} {x' : Sp k' ⟶ T.X}
    (hx : spMap ψ ≫ x = x') {q : Sp k ⟶ C.Y.X} {g : EigFrame T φ x} (h : C.Carries q g) :
    ∃ g' : EigFrame T (ψ.comp φ) x', C.Carries (spMap ψ ≫ q) g' ∧ ∀ τ i, g'.v τ i = spMap (dualMap ψ) ≫ g.v τ i := by
  have hF : GlobalTheory.LocM.IsFrame T.t (ψ.comp φ) x' (Vecs.bc (Dw := Dw) ψ g.v) := hx ▸
    GlobalTheory.LocM.isFrame_bc E H Dw l c T.X T.t _ _ φ ψ x g.v ⟨fun τ i => ⟨g.tan τ i, g.eig τ i⟩, g.basis⟩
  refine ⟨⟨Vecs.bc (Dw := Dw) ψ g.v, fun τ i => (hF.1 τ i).1, fun τ i => (hF.1 τ i).2, hF.2⟩, ?_, fun _ _ => rfl⟩
  obtain ⟨y, χ, φ₁, f, t, t', hq, h0, h1, h2, h3⟩ := h
  refine ⟨y, ψ.comp χ, φ₁, f, t, fun τ i => Units.map ψ.toMonoidHom (t' τ i),
    by rw [hq, ← Category.assoc, ModelRelProbe.spMap_comp], h0,
    by rw [← hx, h1, ← Category.assoc (spMap ψ), ModelRelProbe.spMap_comp], by rw [h2, RingHom.comp_assoc],
    fun τ i => ?_⟩
  obtain ⟨cf, c1, c2, c3⟩ := h3 τ i
  exact ⟨fun j => ψ (cf j), congrArg ψ c1, fun j hj => by simp only [c2 j hj, map_zero], combination_base_change χ ψ hx c3⟩

end SlopeTestRemainingChoices

theorem UpperTheory.level_flag_compact_point :
    ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p} {O : Type} [CommRing O] {β : O →+* i₀.c.F} {Z : LocM.Mdl Y i₀} {T : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model (Xo i₀.l) i₀.c β} {F : Type} [Field F] {e : F ≃+* i₀.c.F} (L : Lev Z T) (C : FlagCpt T e) {k : Type} [Field k] (w : Sp k ⟶ Z.X) (q : Sp k ⟶ C.Y.X), Match L C w q → w (closedPoint k) ∈ Z.opn ∧ C.π (q (closedPoint k)) ∈ Set.range T.jQ ∧ (∃ f : Z.i.c.F →+* k, w ≫ Z.s = spMap f ≫ spMap (Z.i.c.V W).subtype ∧ q ≫ C.π ≫ genStr T = spMap f ≫ spMap (incl Z)) ∧ ∀ (k' : Type) [Field k'] (ψ : k →+* k'), Match L C (spMap ψ ≫ w) (spMap ψ ≫ q) := by
  intro E _ _ _ H Dw Xo p W Y i₀ O _ β Z T F _ e L C k _ w q h
  obtain ⟨y, v, φ, g, hw, hq, hv, hfl, hc, hg⟩ := h
  refine ⟨⟨y (closedPoint k), ?_⟩, ⟨(y ≫ L.r) (closedPoint k), ?_⟩, ?_, fun k' _ ψ => ?_⟩
  · exact analyticChartsRealization_comp_point_eq hw _
  · exact analyticChartsRealization_comp_point_eq (hq.trans (Category.assoc _ _ _).symm) _
  · have hf : spMap (Spec.preimage (y ≫ pullback.snd _ _)).hom = y ≫ pullback.snd _ _ := Spec.map_preimage _
    refine ⟨(Spec.preimage (y ≫ pullback.snd _ _)).hom, ?_, ?_⟩
    · rw [hf, ← Z.π_s, ← Category.assoc, hw, Category.assoc, ModelRelProbe.j_over, Category.assoc]
    · have hj : T.jQ ≫ genStr T = pullback.snd _ _ := T.jQ_over
      rw [hf, ← Category.assoc, hq, Category.assoc, Category.assoc, hj, L.snd, Category.assoc]
  · obtain ⟨g', hc', hg'⟩ := carries_base_change C ψ (x' := (spMap ψ ≫ q) ≫ C.π ≫ genι T) (Category.assoc _ _ _).symm hc
    refine ⟨spMap ψ ≫ y, v.bc ψ, ψ.comp φ, g', by rw [Category.assoc, hw, Category.assoc],
      by rw [Category.assoc, hq, Category.assoc], fun τ i => LieMet.isTan_map ψ rfl (hv τ i), ?_, hc', fun τ i => ?_⟩
    · have e₁ : (fun τ i => v.bc ψ τ i ≫ (Y Z.i).m.φ) =
          Vecs.bc (Dw := Dw) (t := (Y Z.i).t) ψ (fun τ i => v τ i ≫ (Y Z.i).m.φ) := by
        funext τ i
        exact Category.assoc _ _ _
      rw [e₁]
      exact flagAt_base_change Z.toPre ψ hfl
    · rw [hg', hg]
      exact (Category.assoc _ _ _).symm
