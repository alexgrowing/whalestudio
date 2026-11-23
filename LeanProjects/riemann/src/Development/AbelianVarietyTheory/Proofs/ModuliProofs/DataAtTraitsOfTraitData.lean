import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.LocalFramePowerSections
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ValuationExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TraitDataIntrinsic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)

theorem sp_sq {A B B' C : Type} [CommRing A] [CommRing B] [CommRing B'] [CommRing C] {f : A →+* B} {g : B →+* C}
    {f' : A →+* B'} {g' : B' →+* C} (e : ∀ a, g (f a) = g' (f' a)) : spMap g ≫ spMap f = spMap g' ≫ spMap f' := by
  rw [← spMap_comp, ← spMap_comp]; exact congrArg spMap (RingHom.ext e)

theorem j_s : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap β := by
  rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]

theorem exists_generic {S T : Scheme.{0}} {i : T ⟶ S} {χ : S ⟶ Y.X} {t : SAB H S} (m : SABMap t Y.t χ) {v : T ⟶ Xo.XF c}
    (hv : v ≫ Y.j = i ≫ χ) : ∃ (t' : SAB H T) (m₁ : SABMap t' t i) (n : SABMap t' Y.oF.t v)
      (m₂ : SABMap t' Xo.univ.t (v ≫ pullback.fst _ _)), m₁.φ ≫ m.φ = n.φ ≫ Y.m.φ ∧ m₂.φ = n.φ ≫ Y.m0.toSABMap.φ := by
  obtain ⟨t', ⟨p⟩⟩ := (GlobalTheory.ModelPoints.model_points_charts E H D l Xo c O β Y).2.1 _ (i ≫ χ)
  obtain ⟨m₁, h₁⟩ := GlobalTheory.ObjMaps.exists_sab_cancel m p
  have key : ∀ u : T ⟶ Y.X, v ≫ Y.j = u → ∀ p : SABMap t' Y.t u, ∃ n : SABMap t' Y.oF.t v, p.φ = n.φ ≫ Y.m.φ := by
    rintro _ rfl p
    exact GlobalTheory.ObjMaps.exists_sab_cancel Y.m p
  obtain ⟨n, hn⟩ := key _ hv p
  obtain ⟨m₂, h₂⟩ := GlobalTheory.ObjMaps.exists_sab_comp Y.m0.toSABMap n
  exact ⟨t', m₁, n, m₂, h₁.symm.trans hn, h₂⟩

theorem isProper_of_range {X S X' S' : Scheme.{0}} {p : X ⟶ S} {p' : X' ⟶ S'} {χ : S' ⟶ S} {F : X' ⟶ X}
    (h : IsPullback F p' p χ) (U : S.Opens) [IsProper (p ∣_ U)] (hU : Set.range χ ⊆ U) : IsProper p' := by
  have h₁ := (isPullback_morphismRestrict p U).flip
  have e : IsOpenImmersion.lift U.ι χ (by rwa [Scheme.Opens.range_ι]) ≫ U.ι = χ := IsOpenImmersion.lift_fac _ _ _
  rw [← e] at h
  have w := h.w
  rw [← Category.assoc] at w
  exact MorphismProperty.of_isPullback (P := @IsProper)
    (IsPullback.of_right (by rw [h₁.lift_fst]; exact h) (h₁.lift_snd _ _ w) h₁) ‹_›

theorem arcDataAt_of_hasArcData {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'} (a : ArcIn D l β O' b) {W : Type}
    [CommRing W] [IsDomain W] [IsLocalRing W] (f : O' →+* W) (u : W) {χ : Sp W ⟶ Y.X} {v : Sp (FractionRing W) ⟶ Xo.XF c}
    (hv : v ≫ Y.j = Out.jK W ≫ χ) (h : Y.HasArcData a (IsLocalRing.maximalIdeal W) f u χ) :
    GlobalTheory.IndefiniteRowSideFullHecke.LocalFramePowerSections.ArcDataAt Xo a f u (v ≫ pullback.fst _ _) := by
  obtain ⟨t, m, P, φ, he, w, e, h1, h2, h3, h4, h5, h6⟩ := h
  obtain ⟨t', m₁, n, m₂, e₁, e₂⟩ := exists_generic Y m hv
  refine ⟨t, t', m₁, m₂, P, φ, he, w, e, h1, h2, h3, h4, h5, fun F _ _ _ _ uF hf hu => ?_⟩
  obtain ⟨k₁, k₂⟩ := h6 F uF hf hu
  refine ⟨k₁, fun k p₀ σ hσ q₀ q x x' hq hy hz hx₁ hx₂ => ?_⟩
  have : IsPreimmersion (Out.jK W) :=
    IsPreimmersion.of_isLocalization (R := W) (S := FractionRing W) (nonZeroDivisors W)
  have hb : x' ≫ t'.G.hom = Out.jFK (R := W) F := by
    rw [← cancel_mono (Out.jK W), Category.assoc, ← m₁.cart.1.w, ← Category.assoc]
    refine (congrArg (· ≫ t.G.hom) hx₁).trans ?_
    have w₁ : P.U.gen.inv.left ≫ pullback.snd t.G.hom (Out.jK W) = P.A.A.hom := Over.w P.U.gen.inv
    have w₂ : x.left ≫ P.A.A.hom = Out.jFK (R := W) F := Over.w x
    simp only [Category.assoc]
    rw [pullback.condition, ← w₂, ← w₁]
    simp only [Category.assoc]
  have key : ∀ σ' : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G, σ'.left ≫ Y.m0.toSABMap.φ = pullback.fst _ _ ≫ σ.left →
      x.left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (Out.jK W) ≫ m.φ =
        (Out.jFK (R := W) F ≫ v) ≫ σ'.left ≫ Y.m.φ := fun σ' hσ' => by
    have w₃ : σ'.left ≫ Y.oF.t.G.hom = 𝟙 _ := Over.w σ'
    have hn : x' ≫ n.φ = (Out.jFK (R := W) F ≫ v) ≫ σ'.left := by
      apply Y.m0.cart.1.hom_ext
      · refine (Category.assoc _ _ _).trans ((congrArg (x' ≫ ·) e₂.symm).trans (hx₂.trans ?_))
        refine Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hσ')).symm
        simp only [Category.assoc]
      · refine (Category.assoc _ _ _).trans ((congrArg (x' ≫ ·) n.cart.1.w).trans ?_)
        refine Eq.trans ?_ ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) w₃).trans (Category.comp_id _))).symm
        rw [← Category.assoc, hb]
    refine Eq.trans ?_ ((congrArg (· ≫ Y.m.φ) hn).trans (Category.assoc _ _ _))
    rw [Category.assoc, ← e₁, ← Category.assoc x', hx₁]
    simp only [Category.assoc]
  have hyF : (Out.jFK (R := W) F ≫ v) ≫ Y.j = Out.jFK (R := W) F ≫ Out.jK W ≫ χ := by
    rw [Category.assoc, hv]
  rcases hσ with ⟨hk, z, hp, rfl⟩ | ⟨hk, z, hz', hp, rfl⟩
  · exact k₂ _ hyF k p₀ _ (.inl ⟨hk, z, hp, rfl⟩) q₀ q x hq hy hz (key _ (Y.m0.etaA z))
  · exact k₂ _ hyF k p₀ _ (.inr ⟨hk, z, hz', hp, rfl⟩) q₀ q x hq hy hz (key _ (Y.m0.eta z))

theorem exists_ext {R₁ : Type} [CommRing R₁] [IsDomain R₁] {r : O →+* R₁} {y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c}
    (h : y₁ ≫ pullback.snd _ _ ≫ spMap β = Out.jK R₁ ≫ spMap r) {W : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] (ρ : R₁ →+* W) (κ : FractionRing R₁ →+* FractionRing W)
    (hκ : ∀ x, κ (algebraMap R₁ _ x) = algebraMap W _ (ρ x)) :
    ∃ χ : Sp W ⟶ Y.X, spMap κ ≫ y₁ ≫ Y.j = Out.jK W ≫ χ := by
  let fK : c.F →+* FractionRing W := (Spec.preimage (spMap κ ≫ y₁ ≫ pullback.snd _ _)).hom
  have hf : spMap fK = spMap κ ≫ y₁ ≫ pullback.snd _ _ := Spec.map_preimage _
  have ho : (algebraMap W (FractionRing W)).comp (ρ.comp r) = fK.comp β := by
    have e : spMap ((algebraMap W (FractionRing W)).comp (ρ.comp r)) = spMap (fK.comp β) := by
      rw [spMap_comp _ fK, hf, Category.assoc, Category.assoc, h, ← Category.assoc,
        sp_sq (f := algebraMap R₁ (FractionRing R₁)) (g := κ) (f' := ρ) hκ]
      simp only [spMap_comp, Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  obtain ⟨⟨χ, ⟨-, h₂⟩, -⟩, -⟩ := GlobalTheory.ValuativeExtension.valuation_extension E H D l Xo c _ _ Y W (FractionRing W) _ fK
    (spMap κ ≫ y₁) ho (by rw [hf, Category.assoc])
  exact ⟨χ, by rw [h₂, Category.assoc]⟩

theorem dataAtTraits_of_traitData : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O' : Type) [CommRing O'] [IsDomain O'] (b : O →+* O') (a : ArcIn D l β O' b) (R₁ : Type) [CommRing R₁] [IsDomain R₁] (g : PowerSeries O' →+* R₁) (y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c), (∃ U : Y.X.Opens, (U : Set Y.X) = abLocus Y.t.G ∧ IsProper (Y.t.G.hom ∣_ U)) → Function.Injective (g.comp (PowerSeries.C (R := O'))) → g PowerSeries.X ≠ 0 → GlobalTheory.LN.TraitData Y a g y₁ → GlobalTheory.IndefiniteRowSideFullHecke.LocalFramePowerSections.DataAtTraits Xo a g y₁ := by
  intro E _ _ _ H D l Xo c O _ β Y O' _ _ b a R₁ _ _ g y₁ ⟨U, hU, hp⟩ hi hX h
  have h0 := h.1
  rw [j_s] at h0
  have : CharZero (FractionRing R₁) :=
    (RingHom.charZero_iff (Spec.preimage (y₁ ≫ pullback.snd _ _)).hom.injective).1 inferInstance
  refine ⟨RingHom.charZero (algebraMap R₁ (FractionRing R₁)), hi, hX, h0, fun W _ _ _ ρ κ hW => ?_⟩
  have hκ : ∀ x, κ (algebraMap R₁ _ x) = algebraMap W _ (ρ x) := RingHom.congr_fun hW.2
  have := hW.1.1
  obtain ⟨χ, hχ⟩ := exists_ext Y (r := (g.comp (PowerSeries.C (R := O'))).comp b)
    (h0.trans (by simp only [spMap_comp, Category.assoc])) ρ κ hκ
  obtain ⟨k₁, k₂⟩ := h.2 W hW.1 ρ κ hκ χ hχ
  refine ⟨fun hu => ?_, fun hu => ?_⟩
  · obtain ⟨W', _, _, _, io, hW', ioi, iof, hd⟩ := k₂ hu
    have hinj : Function.Injective ((algebraMap W' (FractionRing W')).comp io) := (IsFractionRing.injective W' _).comp ioi
    let jo : FractionRing W →+* FractionRing W' := IsFractionRing.lift hinj
    have hjo : ∀ x, jo (algebraMap W _ x) = algebraMap W' _ (io x) := IsFractionRing.lift_algebraMap hinj
    refine ⟨W', inferInstance, inferInstance, inferInstance, io, jo.comp κ, ioi, iof,
      ⟨hW', RingHom.ext fun x => (congrArg jo (hκ x)).trans (hjo _)⟩, ?_⟩
    rw [← Category.assoc]
    refine arcDataAt_of_hasArcData Y a _ _ ?_ hd
    rw [spMap_comp, Category.assoc, Category.assoc, hχ, ← Category.assoc, ← Category.assoc,
      sp_sq (f := algebraMap W (FractionRing W)) (g := jo) (f' := io) (g' := algebraMap W' (FractionRing W')) hjo]
  · obtain ⟨t, ⟨m⟩⟩ := (GlobalTheory.ModelPoints.model_points_charts E H D l Xo c O β Y).2.1 _ χ
    obtain ⟨t', m₁, -, m₂, -⟩ := exists_generic Y m ((Category.assoc _ _ _).trans hχ)
    rw [← Category.assoc]
    exact ⟨t, t', m₁, m₂, isProper_of_range m.cart.1 U (hU ▸ k₁ hu)⟩

end GlobalTheory.TraitDataIntrinsic
