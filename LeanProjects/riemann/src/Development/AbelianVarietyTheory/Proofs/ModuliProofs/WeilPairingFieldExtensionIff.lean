import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsMonHomIffOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleTrivialIsoDescendFieldStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.WeilFieldExt

open GlobalTheory.CommPairing ReciprocityTheory.ChartRestriction.G.Out

theorem corr_of_val_epi {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')} (q : Y' ⟶ Y) [Epi q]
    (hq : ∀ U : Y.Opens, Function.Injective (q.app U).hom)
    (h : ∀ y J, Good L y J → val t q y J = val t' q y J) : LB.Gen.Corr L φ ε φ' ε' t t' := by
  intro j j' c₁ c₂ c₃
  have inj : Function.Injective (pullU q (LB.wchart L φ j ⊓ LB.wchart L φ' j')) := fun a b e =>
    Units.ext (hq _ (congrArg Units.val e))
  apply inj
  refine unit_ext fun y hy => ?_
  have hy' : q y ∈ LB.wchart L φ j ⊓ LB.wchart L φ' j' := hy
  obtain ⟨J, hJ, e⟩ := exists_good L hL y (fun k => q ≫ Sum.elim φ φ' k) (Sum.elim j j') (by
    intro a b e
    have e := (cancel_epi q).1 e
    rcases a with a | a <;> rcases b with b | b
    exacts [c₁ a b e, c₃ a b e, (c₃ b a e.symm).symm, c₂ a b e]) (by
    rintro (a | a)
    exacts [Set.mem_iInter.1 hy'.1 a, Set.mem_iInter.1 hy'.2 a])
  have := h y J hJ
  rw [val_of t _ y J j (fun k => e (.inl k)), val_of t' _ y J j' (fun k => e (.inr k))] at this
  exact (gm_id_pull q y _ hy' _).trans ((gm_res _ y _ hy' _).trans (this.trans
    ((gm_res _ y _ hy' _).symm.trans (gm_id_pull q y _ hy' _).symm)))

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}

omit [GrpObj A] in
theorem isPullback_whisker {T T' : Over S} (h : T' ⟶ T) :
    IsPullback (h ▷ A).left (fst T' A).left (fst T A).left h.left := by
  refine (IsPullback.of_right (h₁₁ := (h ▷ A).left) (v₁₁ := pullback.fst T'.hom A.hom)
    (h₁₂ := pullback.snd T.hom A.hom) (v₁₂ := pullback.fst T.hom A.hom) (h₂₁ := h.left) (h₂₂ := T.hom)
    (v₁₃ := A.hom) ?_ ?_ (IsPullback.of_hasPullback T.hom A.hom).flip)
  · have e : (h ▷ A).left ≫ pullback.snd T.hom A.hom = pullback.snd T'.hom A.hom :=
      congrArg (fun q => q.left) (whiskerRight_snd h A)
    rw [e, Over.w h]
    exact (IsPullback.of_hasPullback T'.hom A.hom).flip
  · exact congrArg (fun q => q.left) (whiskerRight_fst h A)

theorem commIsOf_descend (hA : IsAbelianScheme A) (hL : L.IsLB) {T T' : Over S} (h : T' ⟶ T)
    [Epi (h ▷ A).left] (hq : ∀ U, Function.Injective ((h ▷ A).left.app U).hom)
    {θx θy : ThetaGrp A L k T} {a b : ThetaGrp A L k T'} (ha : a.pt = h ≫ θx.pt) (hb : b.pt = h ≫ θy.pt)
    {c : Γ(T.left, ⊤)ˣ} (H : CommIsOf A L k a b (Units.map h.left.appTop.hom.toMonoidHom c)) :
    CommIsOf A L k θx θy c := by
  obtain ⟨θx', hx, vx⟩ := exists_pull hL h θx
  obtain ⟨θy', hy, vy⟩ := exists_pull hL h θy
  have H' := (commIsOf_iff hL _ _ _).1
    (commIsOf_change globalFns_holds hA hL (hx.trans ha.symm) (hy.trans hb.symm) H)
  refine corr_of_val_epi hL (h ▷ A).left hq fun z J hJ => ?_
  have key : ∀ θ θ' : ThetaGrp A L k T,
      val (LB.mulGen L _ _ _ _ θ.φ (LB.pullGen L _ _ θ'.φ (translT A θ.pt).left)) (h ▷ A).left z J =
        tval θ (h ▷ A).left z J * tval θ' ((h ▷ A).left ≫ (translT A θ.pt).left) z J := fun θ θ' =>
    (val_mul hJ _ _ _).trans (congrArg (tval θ (h ▷ A).left z J * ·) (val_pull hJ _ _ _))
  have e := H' _ (𝟙 _) z J hJ
  have t : ∀ x : T ⟶ A, (𝟙 _ ≫ (translT A (h ≫ x)).left) ≫ (h ▷ A).left =
      (h ▷ A).left ≫ (translT A x).left := fun x => by
    rw [Category.id_comp, ← Over.comp_left, ← Over.comp_left, whisker_translT]
  have g : gm (𝟙 _ ≫ (fst T' A).left) z ⊤ (Units.map h.left.appTop.hom.toMonoidHom c) =
      gm ((h ▷ A).left ≫ (fst T A).left) z ⊤ c := by
    refine (gm_pull (𝟙 _ ≫ (fst T' A).left) h.left z ⊤ trivial c).trans ?_
    rw [Category.id_comp, ← Over.comp_left, ← Over.comp_left, whiskerRight_fst]
  rw [vx _ _ z J hJ, vx _ _ z J hJ, vy _ _ z J hJ, vy _ _ z J hJ, hx, hy, t, t, g, Category.id_comp] at e
  exact (key θx θy).trans (e.trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (key θy θx) (H1.val_constGen L c _ z J))).symm)

theorem weilIs_iff (hA : IsAbelianScheme A) (hL : L.IsLB) {T : Over S} [Unique T.left] (x y : T ⟶ A)
    (c : Γ(T.left, ⊤)ˣ) : WeilIs A L k x y c ↔
      ∃ θx θy : ThetaGrp A L k T, θx.pt = x ∧ θy.pt = y ∧ CommIsOf A L k θx θy c := by
  constructor
  · intro H
    obtain ⟨V, hp, ⟨θx, θy, hx, hy⟩, hc⟩ := H default
    obtain rfl : V = ⊤ := eq_top_iff.2 fun p _ => by rwa [Unique.eq_default p]
    let s : T ⟶ overRes (⊤ : T.left.Opens) := Over.homMk T.left.topIso.inv (by
      show T.left.topIso.inv ≫ T.left.topIso.hom ≫ T.hom = T.hom
      rw [Iso.inv_hom_id_assoc])
    have w : s.left ≫ (⊤ : T.left.Opens).ι = 𝟙 _ := T.left.topIso.inv_hom_id
    have w' : s ≫ overResι ⊤ = 𝟙 T := Over.OverMorphism.ext w
    obtain ⟨a, b, ha, hb, H'⟩ := exists_commIsOf_pull hL s (hc θx θy hx hy)
    rw [hx, ← Category.assoc, w', Category.id_comp] at ha
    rw [hy, ← Category.assoc, w', Category.id_comp] at hb
    have e : Units.map s.left.appTop.hom.toMonoidHom (unitRes ⊤ c) = c := by
      apply Units.ext
      have := congrArg (fun q => q.appTop.hom c.val) w
      simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at this
      exact this
    rw [e] at H'
    exact ⟨a, b, ha, hb, H'⟩
  · rintro ⟨θx, θy, rfl, rfl, H⟩ p
    obtain ⟨a, b, ha, hb, H'⟩ := exists_commIsOf_pull hL (overResι (⊤ : T.left.Opens)) H
    exact ⟨⊤, trivial, ⟨a, b, ha, hb⟩, fun a' b' ha' hb' =>
      commIsOf_change globalFns_holds hA hL (ha'.trans ha.symm) (hb'.trans hb.symm) H'⟩

theorem exists_lift_descend (hL : L.IsLB) {T T' : Over S} (h : T' ⟶ T)
    (hd : ∀ M : LB (T ⊗ A).left, M.IsLB → (∃ t : (M.pull (h ▷ A).left).Gen, t.IsGen) → ∃ t : M.Gen, t.IsGen)
    (x : T ⟶ A) (a : ThetaGrp A L k T') (ha : a.pt = h ≫ x) : ∃ θ : ThetaGrp A L k T, θ.pt = x := by
  obtain ⟨t, ht⟩ := hd (thetaLB A L k x) (DVR.linComb_isLB L hL _ _)
    (gen_chartPull (chartPullOut L ![(snd T A).left, (translPt A x).left] ![k, -k] (h ▷ A).left
      ![(snd T' A).left, (translPt A a.pt).left] (fun i => by
        fin_cases i
        · exact (congrArg (fun q => q.left) (whiskerRight_snd h A)).symm
        · show (translPt A a.pt).left = (h ▷ A).left ≫ (translPt A x).left
          rw [← Over.comp_left, whisker_translPt, ha])) a.φ a.isGen)
  exact ⟨⟨x, t, ht⟩, rfl⟩

theorem unitOn_map {K Ω : Type} [CommRing K] [CommRing Ω] (i : K →+* Ω) (c : Kˣ) :
    unitOn (Units.map i.toMonoidHom c) = Units.map (spMap i).appTop.hom.toMonoidHom (unitOn c) := by
  apply Units.ext
  exact congrArg (fun q => q.hom c.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom i))

end GlobalTheory.WeilFieldExt

namespace GlobalTheory

open WeilFieldExt CommPairing in

theorem weilIs_fieldExt_iff : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (K Ω : Type) [Field K] [Field Ω] (i : K →+* Ω) (x : Sp K ⟶ S) (L : LB G.left) (k : ℤ) (y y' : Over.mk x ⟶ G) (c : Kˣ), IsAbelianScheme G → L.IsLB → (Out.WeilIs G L k ((Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ y) ((Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ y') (unitOn (Units.map i.toMonoidHom c)) ↔ Out.WeilIs G L k y y' (unitOn c)) := by
  intro S G _ K Ω _ _ i x L k y y' c hG hL
  rw [unitOn_map]
  let h : Over.mk (spMap i ≫ x) ⟶ Over.mk x := Over.homMk (spMap i) rfl
  refine ⟨fun H => ?_, fun H => weilIs_pull globalFns_holds hG hL h H⟩
  letI : Unique (Over.mk x).left := inferInstanceAs (Unique (PrimeSpectrum K))
  letI : Unique (Over.mk (spMap i ≫ x)).left := inferInstanceAs (Unique (PrimeSpectrum Ω))
  obtain ⟨a, b, ha, hb, Hc⟩ := (weilIs_iff hG hL _ _ _).1 H
  have pb : IsPullback (h ▷ G).left (fst _ G).left (fst _ G).left (spMap i) := isPullback_whisker h
  obtain ⟨e, -, -, -, inj⟩ := (FieldBaseChange.epi_and_isMonHom_iff K Ω i).1 _ _ _ _ _ pb
  have hd := (GlobalTheory.T.lineBundle_trivial_iso_descend_field K Ω i _ _ _ _ _
    (by have := hG.smooth; exact inferInstanceAs (Smooth (pullback.fst x G.hom)))
    (by have := hG.proper; exact inferInstanceAs (IsProper (pullback.fst x G.hom)))
    (by have := hG.geomConnected; exact inferInstanceAs (GeometricallyConnected (pullback.fst x G.hom))) pb).1
  obtain ⟨θ, rfl⟩ := exists_lift_descend hL h hd y a ha
  obtain ⟨θ', rfl⟩ := exists_lift_descend hL h hd y' b hb
  exact (weilIs_iff hG hL _ _ _).2 ⟨θ, θ', rfl, rfl, commIsOf_descend hG hL h inj ha hb Hc⟩

end GlobalTheory
