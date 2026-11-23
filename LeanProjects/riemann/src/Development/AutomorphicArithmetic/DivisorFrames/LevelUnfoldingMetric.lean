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

theorem UpperTheory.level_unfolding_metric :
    ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p} {O : Type} [CommRing O] {β : O →+* i₀.c.F} {Z : LocM.Mdl Y i₀} {T : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model (Xo i₀.l) i₀.c β} {F : Type} [Field F] {e : F ≃+* i₀.c.F} {σ : i₀.c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf (Xo i₀.l) i₀.c σ N} (Φ : FlagTor T e U) (L : Lev Z T), (∀ τ k, k ≤ Dw.mult τ → k ∈ Z.ty τ) → ∀ {k : Type} [Field k] (w : Sp k ⟶ Z.X) (c c' : U.Comp) (q : Sp k ⟶ (Φ.C c).Y.X) (q' : Sp k ⟶ (Φ.C c').Y.X), Match L (Φ.C c) w q → Match L (Φ.C c') w q' → (⟨c, q⟩ : Σ c : U.Comp, (Sp k ⟶ (Φ.C c).Y.X)) = ⟨c', q'⟩ := by
  intro E _ _ _ H Dw Xo p W Y i₀ O _ β Z T F _ e σ N U Φ L hty k _ w c c' q q'
  rintro ⟨y, v, φ, g, hw, hq, hv, ⟨a, χ, ha, hF, hS⟩, hc, hg⟩
    ⟨y', v', φ', g', hw', hq', hv', ⟨a', χ', ha', hF', hS'⟩, hc', hg'⟩
  have hmono : Mono (Y Z.i).j := by
    have := mono_spMap_subtype (Z.i.c.V W)
    have := (Y Z.i).jQ_open
    unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j; infer_instance
  obtain rfl : y = y' := (cancel_mono (Y Z.i).j).1 (hw.symm.trans hw')
  have hqq : q' ≫ (Φ.C c').π = q ≫ (Φ.C c).π := hq'.trans hq.symm
  obtain ⟨-, hstr, -⟩ := (UpperTheory.flag_carries_eigenframe (Φ.C c) k q).2 φ _ g hc
  obtain ⟨-, hstr', hiff⟩ := (UpperTheory.flag_carries_eigenframe (Φ.C c') k q').2 φ' _ g' hc'
  obtain rfl : φ = φ' := by
    rw [← Category.assoc, hqq, Category.assoc, hstr] at hstr'
    exact congrArg CommRingCat.Hom.hom
      (Spec.map_injective (a₁ := CommRingCat.ofHom _) (a₂ := CommRingCat.ofHom _) hstr')
  have hx : q ≫ (Φ.C c).π ≫ genι T = q' ≫ (Φ.C c').π ≫ genι T := by
    rw [← Category.assoc, ← hqq, Category.assoc]
  have hx' : (y ≫ L.r) ≫ T.j = q' ≫ (Φ.C c').π ≫ genι T := by
    rw [← Category.assoc q', hq']
    simp only [Category.assoc]
    rfl
  have tri : ∀ τ, Pull.Tri (Y Z.i).t (w ≫ Z.π) (fun i => v' τ i ≫ (Y Z.i).m.φ) (fun i => v τ i ≫ (Y Z.i).m.φ) :=
    fun τ =>
      (((Pull.tri_of_sameFlag hty hS' τ).symm (Pull.frame_ind (Pull.chart_frame Z ha') τ)
        (Pull.frame_ind hF' τ)).1.trans (Pull.frame_ind hF' τ).1 (Pull.frame_ind (Pull.chart_frame Z ha') τ).1
        (Pull.chart_tri Z hty ha' ha τ)).trans (Pull.frame_ind hF' τ).1
        (Pull.frame_ind (Pull.chart_frame Z ha) τ).1 (Pull.tri_of_sameFlag hty hS τ)
  have key : ∀ τ i, ∃ cf : Fin (Dw.mult τ) → k, cf i ≠ 0 ∧ (∀ j, i < j → cf j = 0) ∧
      IsCombAtG T.t (q ≫ (Φ.C c).π ≫ genι T) (g'.v τ) cf (g.v τ i) := by
    intro τ i
    obtain ⟨cf, h0, h1⟩ := tri τ i
    refine ⟨cf, ((tri τ).diag (Pull.frame_ind hF' τ) (Pull.frame_ind hF τ) h1).1, h0, ?_⟩
    have h2 := (Pull.comb_push (Y Z.i).m hw.symm (hv' τ) (hv τ i) cf).1 h1
    have h3 := (Pull.comb_push L.ν (x := y ≫ L.r) rfl (hv' τ) (hv τ i) cf).2 h2
    have h4 := (Pull.comb_push T.m hx' (fun j => GlobalTheory.LieMet.isTan_push L.ν y rfl (hv' τ j))
      (GlobalTheory.LieMet.isTan_push L.ν y rfl (hv τ i)) cf).2 h3
    rw [hg, show g'.v τ = _ from funext (hg' τ), hx]
    simpa only [Category.assoc] using h4
  choose cf h0 h1 h2 using key
  have e1 : spMap (dualMap (RingHom.id k)) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [dualMap]
  have e2 : spMap (RingHom.id k) = 𝟙 _ := Spec.map_id _
  have hcg : (Φ.C c').Carries q' g := (hiff φ _ g).2 ⟨fun τ i => Units.mk0 _ (h0 τ i),
    by rw [e2, Category.id_comp, hx], rfl, fun τ i => ⟨cf τ i, rfl, h1 τ i, by
      simp only [e1, Category.id_comp]
      exact h2 τ i⟩⟩
  have uniq : ∀ (x₀ : Sp k ⟶ T.X) (g₀ : EigFrame T φ x₀), x₀ = (q ≫ (Φ.C c).π) ≫ genι T →
      ∃! r : Σ i : U.Comp, (Sp k ⟶ (Φ.C i).Y.X),
        r.2 ≫ (Φ.C r.1).π = q ≫ (Φ.C c).π ∧ (Φ.C r.1).Carries r.2 g₀ := by
    rintro _ g₀ rfl
    exact UpperTheory.flag_torus_generic_point Φ k φ _ ((Category.assoc _ _ _).trans hstr) g₀
  exact (uniq _ g (Category.assoc _ _ _).symm).unique ⟨rfl, hc⟩ ⟨hqq, hcg⟩
