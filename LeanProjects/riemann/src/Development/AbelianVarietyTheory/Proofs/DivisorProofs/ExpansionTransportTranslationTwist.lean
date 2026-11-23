import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsAtExpLeB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.TwistedExpTransport

set_option maxHeartbeats 1600000 in

theorem expandsAt_twist : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₂ : DegData R I) (A A₂ : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (U₂ : UnifPre I D₂ A₂ G) (a : 𝟙_ (Over (Sp R)) ⟶ G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))) (β : D₂.toPre.P.A ⟶ D.toPre.P.A) (xe : D₂.toPre.X ≃+ D.toPre.X) (w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b) GlobalTheory.MumCmp.twε)) (wL : LB.Iso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left)) (ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![g.b.left, η[D.toPre.P.A].left] ![-1, 1])) (e : ℕ) (h : (thickObj R I e G).left ⟶ (thickObj R I e G).left), h ≫ (fstG I e G).left = (fstG I e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left → h ≫ (U.gt e).pG.left = (U₂.gt e).pG.left ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b 0 → (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι) (N : (Z ⟶ G.left) → U.LG.L.ι) (N' : (Z ⟶ G.left) → U₂.LG.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.Good U.LG.L z N → Geo.Tor.Good U₂.LG.L z N' → Geo.Tor.gv w (r ≫ (U₂.gt e).pG.left) z (fun i => J ((r ≫ (U₂.gt e).pG.left) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b i)) (J' (r ≫ (U₂.gt e).pG.left)) * Geo.Tor.gw (U₂.w e) r z (J' (r ≫ (U₂.gt e).pG.left)) (fun _ => N' (r ≫ (fstG I e G).left)) = Geo.Tor.gw (U.w e) (r ≫ h) z (J (r ≫ h ≫ (U.gt e).pG.left)) (fun _ => N (r ≫ h ≫ (fstG I e G).left)) * Geo.Tor.gw wL (r ≫ (fstG I e G).left) z (N (r ≫ (fstG I e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (N' (r ≫ (fstG I e G).left)) * Geo.Tor.val ν (r ≫ (thickObj R I e G).hom ≫ thick R I e) z J) → (∀ (χ : D₂.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.val ((U.gt e).t (xe χ)) (r ≫ h) z J = (∏ k, Geo.Tor.gv w (r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k) z (fun i => J ((r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b i)) (J' (r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k)) ^ Oinvε k) * Geo.Tor.val ((U₂.gt e).t χ) r z J' * Geo.Tor.val (g.s (xe χ)) (r ≫ (thickObj R I e G).hom ≫ thick R I e) z J) → ∀ (σ : H0 U.LG.L 1) (σ₂ : H0 U₂.LG.L 1) (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α) (f₂ : ∀ α : D₂.toPre.X, D₂.toPre.SecB 1 α), (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (N : (Z ⟶ G.left) → U.LG.L.ι) (N' : (Z ⟶ G.left) → U₂.LG.L.ι), Geo.Tor.Good U.LG.L z N → Geo.Tor.Good U₂.LG.L z N' → Geo.Tor.sval σ (r ≫ ((toUnit G ≫ a) * 𝟙 G).left) z N = (Geo.Tor.gw wL r z (N (r ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (N' r)).val * Geo.Tor.sval σ₂ r z N') → (∀ (χ : D₂.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ D₂.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b 0) z J * (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.toPre.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.toPre.P.A).left) z J).val = (∏ κ, Geo.Tor.gv w (r ≫ D₂.toPre.famφB χ κ) z (fun i => J ((r ≫ D₂.toPre.famφB χ κ) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b i)) (J' (r ≫ D₂.toPre.famφB χ κ)) ^ DegPre.famε 1 κ).val * Geo.Tor.sval (f₂ χ) r z J') → U.ExpandsAt e 1 σ f → U₂.ExpandsAt e 1 σ₂ f₂ := by
  intro R _ _ I D D₂ A A₂ G _ _ U U₂ a g β xe w wL ν e h hG hp h1 h2 σ σ₂ f f₂ hσ hf hE
  classical
  have hu : (U₂.gt e).pG.left ≫ (toUnit D₂.toPre.P.A).left = (thickObj R I e G).hom ≫ thick R I e := by
    have e1 := Over.w (toUnit D₂.toPre.P.A)
    have e2 := Over.w (U₂.gt e).pG
    have e3 : (𝟙_ (Over (Spec (CommRingCat.of R)))).hom = 𝟙 _ := rfl
    rw [e3, Category.comp_id] at e1
    rw [e1, e2]
    rfl
  obtain ⟨S, hS⟩ := expandsAt_val U e 1 σ f hE
  refine expandsAt_of_val U₂ e 1 σ₂ f₂ (S.map xe.symm.toEquiv.toEmbedding) fun y J' hJ' => ?_
  choose J hJ using fun ψ : (thickObj R I e G).left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ y)
  have hJ : Good D.toPre.P.L y J := hJ
  choose N hN using fun ψ : (thickObj R I e G).left ⟶ G.left => exists_chart U.LG.isLB (ψ y)
  have hN : Good U.LG.L y N := hN

  let ω : ((thickObj R I e G).left ⟶ D₂.toPre.P.A.left) → ((thickObj R I e G).left.presheaf.stalk y)ˣ :=
    fun ψ => gv w ψ y (fun i => J (ψ ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b i)) (J' ψ)
  have hω := fun χ => GlobalTheory.ExpTrans.prod_fam U₂ e 1 ω χ
  have hF : ∀ χ, sval (f (xe χ)) (h ≫ pGl U e) y J *
      (val (g.s (xe χ)) ((thickObj R I e G).hom ≫ thick R I e) y J * val ν ((thickObj R I e G).hom ≫ thick R I e) y J).val =
      (∏ κ, ω (pGl U₂ e ≫ D₂.toPre.famφB χ κ) ^ DegPre.famε 1 κ).val * sval (f₂ χ) (pGl U₂ e) y J' := by
    intro χ
    have := hf χ _ (pGl U₂ e) y J J' hJ hJ'
    rw [hu] at this
    rw [hp]
    exact this
  have hT : ∀ χ, val ((U.gt e).t (xe χ)) h y J =
      (∏ k, ω (Oφl U₂ e χ k) ^ Oinvε k) * val (tG U₂ e χ) (𝟙 (thickObj R I e G).left) y J' *
        val (g.s (xe χ)) ((thickObj R I e G).hom ≫ thick R I e) y J := by
    intro χ
    have := h2 χ _ (𝟙 _) y J J' hJ hJ'
    simp only [Category.id_comp] at this
    exact this
  refine ⟨fun χ hχ => ?_, fun jL' hL' => ?_⟩
  · have hi : xe χ ∉ S := fun hc => hχ (Finset.mem_map.2 ⟨xe χ, hc, xe.symm_apply_apply χ⟩)
    have z0 := (hS _ h y J hJ).1 _ hi
    have := hF χ
    rw [z0, zero_mul] at this
    exact (Units.mul_right_eq_zero _).1 this.symm
  · obtain ⟨N', hN', eN'⟩ := exists_good U₂.LG.L U₂.LG.isLB y (K := PUnit) (fun _ => fGl I G e) (fun _ => jL')
      (fun _ _ _ => rfl) (fun _ => hL')
    have eN : N' (fGl I G e) = jL' := eN' PUnit.unit
    have hL₁ : fGl I G e (h y) ∈ U.LG.L.U (N (fGl I G e ≫ ((toUnit G ≫ a) * 𝟙 G).left)) := by
      have m := hN (h ≫ fGl I G e)
      have e' : N (h ≫ fGl I G e) = N (fGl I G e ≫ ((toUnit G ≫ a) * 𝟙 G).left) := congrArg N hG
      rw [e'] at m
      exact m
    have W' : ω (pGl U₂ e) * wv U₂ e (𝟙 _) y (J' (pGl U₂ e)) jL' =
        wv U e h y (J (h ≫ pGl U e)) (N (fGl I G e ≫ ((toUnit G ≫ a) * 𝟙 G).left)) *
          gw wL (fGl I G e) y (N (fGl I G e ≫ ((toUnit G ≫ a) * 𝟙 G).left)) jL' *
          val ν ((thickObj R I e G).hom ≫ thick R I e) y J := by
      have := h1 _ (𝟙 _) y J J' N N' hJ hJ' hN hN'
      simp only [Category.id_comp] at this
      rw [hG, eN] at this
      exact this
    have Sg : sv U 1 σ (h ≫ fGl I G e) y (N (fGl I G e ≫ ((toUnit G ≫ a) * 𝟙 G).left)) =
        (gw wL (fGl I G e) y (N (fGl I G e ≫ ((toUnit G ≫ a) * 𝟙 G).left)) jL').val * sv U₂ 1 σ₂ (fGl I G e) y jL' := by
      have := hσ _ (fGl I G e) y N N' hN hN'
      rw [sval_of σ _ y N (fun _ => N (fGl I G e ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (fun _ => by rw [Category.comp_id]),
        sval_of σ₂ _ y N' (fun _ => jL') (fun _ => by rw [Category.comp_id]; exact eN), eN] at this
      rw [hG]
      exact this
    have E := (hS _ h y J hJ).2 _ hL₁
    refine (ω (pGl U₂ e)).mul_right_inj.1 ?_
    have key : ∀ χ, (val ν ((thickObj R I e G).hom ≫ thick R I e) y J).val *
        (sval (f (xe χ)) (h ≫ pGl U e) y J * (val ((U.gt e).t (xe χ)) h y J).val) =
        (ω (pGl U₂ e)).val * (sval (f₂ χ) (pGl U₂ e) y J' * (val (tG U₂ e χ) (𝟙 (thickObj R I e G).left) y J').val) := by
      intro χ
      have hF' := hF χ
      have hω' := congrArg Units.val (hω χ)
      simp only [Units.val_mul, pow_one] at hF' hω'
      rw [hT χ]
      simp only [Units.val_mul]
      linear_combination ((∏ k, ω (Oφl U₂ e χ k) ^ Oinvε k).val * (val (tG U₂ e χ) (𝟙 (thickObj R I e G).left) y J').val) * hF' +
        (sval (f₂ χ) (pGl U₂ e) y J' * (val (tG U₂ e χ) (𝟙 (thickObj R I e G).left) y J').val) * hω'
    have L1 : (ω (pGl U₂ e)).val * ((wv U₂ e (𝟙 _) y (J' (pGl U₂ e)) jL' ^ 1).val * sv U₂ 1 σ₂ (fGl I G e) y jL') =
        (val ν ((thickObj R I e G).hom ≫ thick R I e) y J).val *
          ∑ α ∈ S, sval (f α) (h ≫ pGl U e) y J * (val ((U.gt e).t α) h y J).val := by
      rw [← E, pow_one, pow_one, Sg, ← _root_.mul_assoc, ← Units.val_mul, W']
      simp only [Units.val_mul]
      ring
    rw [L1, Finset.sum_map, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    obtain ⟨χ, rfl⟩ := xe.surjective x
    have e₀ : xe.symm.toEquiv.toEmbedding (xe χ) = χ := xe.symm_apply_apply χ
    rw [e₀]
    exact key χ

end GlobalTheory.TwistedExpTransport
