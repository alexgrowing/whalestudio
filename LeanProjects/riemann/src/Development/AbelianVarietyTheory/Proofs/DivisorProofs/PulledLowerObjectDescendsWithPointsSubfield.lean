import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEtalePointOfExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackPointDescendsAlgClosedSubfieldStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMulEquivPointsOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.PtsDescent

theorem pow_left_of_isGrpPullback {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') (x : T ⟶ G') (z : Over.mk (T.hom ≫ f) ⟶ G)
    (hz : z.left = x.left ≫ φ) (n : ℕ) : (z ^ n).left = (x ^ n).left ≫ φ := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.LamF.exists_mulEquiv_points_of_isGrpPullback S S' f G G' φ h T
  have e : Φ x = z := Over.OverMorphism.ext ((hΦ x).trans hz.symm)
  rw [← hΦ, map_pow, e]

theorem degPre_c_nsmul {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (y : D.X) (n : ℕ) :
    D.c (n • y) = D.c y ^ n := by
  have h0 : D.c 0 = 1 := by
    have := D.c_add 0 0
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  induction n with
  | zero => simpa using h0
  | succ n ih => rw [succ_nsmul, D.c_add, ih, pow_succ]; rfl

end GlobalTheory.UCanon.PtsDescent

namespace GlobalTheory.UCanon.PtsDescent

theorem pulledObj_descends_with_points : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X), DivFrom L Q oQ iw s ε e → ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (ev : V →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (o' : LowObj D' c ((ev.comp iw).comp L.b)) (m₁ : ObjMap o' L.o (spMap (ev.comp iw))), ∀ (B₀ : Over (Sp k₀)) [GrpObj B₀] [IsCommMonObj B₀] (M₀ : LB B₀.left) (c₀ : Q.X → (Sp k₀ ⟶ B₀.left)) (B' : Over (Sp K)) [GrpObj B'] (π₁ : B'.left ⟶ Q.P.A.left) (π₀ : B'.left ⟶ B₀.left) (w : LB.Iso (Q.P.L.pull π₁) (M₀.pull π₀)) (c' : Q.X → (Sp K ⟶ B'.left)) (θ : o'.t.G.left ⟶ B'.left), IsAbelianScheme B₀ → M₀.IsLB → IsGrpPullback B' Q.P.A (spMap ev) π₁ → IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ → w.IsGen → (∀ a, c' a ≫ B'.hom = 𝟙 _ ∧ c' a ≫ π₁ = spMap ev ≫ (Q.c a).left ∧ c' a ≫ π₀ = spMap k₀.subtype ≫ c₀ a) → IsGrpPullback o'.t.G B' (𝟙 _) θ → LBIso o'.t.PP.L (Q.P.L.pull (θ ≫ π₁)) → (∀ (x : Sp K ⟶ o'.t.G.left) (a : Q.X), x ≫ o'.t.G.hom = 𝟙 _ → x ≫ m₁.toSABMap.φ ≫ L.φB = spMap (ev.comp iw) ≫ (L.D.c (l.M' • e a)).left → x ≫ θ ≫ π₁ = spMap ev ≫ (Q.c a).left) → IsGrpPullback o'.t.G B₀ (spMap k₀.subtype) (θ ≫ π₀) ∧ LBIso o'.t.PP.L (M₀.pull (θ ≫ π₀)) ∧ ∀ y : L.D.X, ∃ x : Sp K ⟶ o'.t.G.left, x ≫ o'.t.G.hom = 𝟙 _ ∧ x ≫ m₁.toSABMap.φ ≫ L.φB = spMap (ev.comp iw) ≫ (L.D.c y).left ∧ ∃ x₀ : Sp k₀ ⟶ B₀.left, x ≫ θ ≫ π₀ = spMap k₀.subtype ≫ x₀ := by
  intro E _ _ _ H D' l c L V _ _ Q _ oQ iw I _ s ε e hdiv K _ _ _ ev k₀ hk₀ o' m₁ B₀ _ _ M₀ c₀ B' _ π₁ π₀ w c' θ hB₀ hM₀ hpb1 hpb0 hw hc' hθ hL hpts
  have h1 : IsGrpPullback o'.t.G B₀ (spMap k₀.subtype) (θ ≫ π₀) :=
    (hθ.comp hpb0).congr (Category.id_comp _) rfl
  refine ⟨h1, ?_, ?_⟩
  · exact LBIso.trans o'.t.PP.isLB (pull_isLB Q.P.isLB _) (pull_isLB hM₀ _) hL
      (GlobalTheory.GenSpread.lbIso_pull_comp θ rfl rfl ⟨w, hw⟩)

  · intro y
    have hpb : IsGrpPullback o'.t.G L.D.P.A (spMap (ev.comp iw)) (m₁.toSABMap.φ ≫ L.φB) :=
      (m₁.cart.comp L.ab.1).congr (Category.comp_id _) rfl
    let x : Sp K ⟶ o'.t.G.left := hpb.1.lift (spMap (ev.comp iw) ≫ (L.D.c y).left) (𝟙 _)
      (by rw [Category.assoc, Over.w (L.D.c y)]; simp)
    have hx1 : x ≫ m₁.toSABMap.φ ≫ L.φB = spMap (ev.comp iw) ≫ (L.D.c y).left := hpb.1.lift_fst _ _ _
    have hx2 : x ≫ o'.t.G.hom = 𝟙 _ := hpb.1.lift_snd _ _ _
    refine ⟨x, hx2, hx1, ?_⟩
    let xp : 𝟙_ (Over (Sp K)) ⟶ o'.t.G := Over.homMk x (by simpa using hx2)
    let z : Over.mk ((𝟙_ (Over (Sp K))).hom ≫ spMap (ev.comp iw)) ⟶ L.D.P.A := toUnit _ ≫ L.D.c y
    have htu : (toUnit (Over.mk ((𝟙_ (Over (Sp K))).hom ≫ spMap (ev.comp iw)))).left =
        (𝟙_ (Over (Sp K))).hom ≫ spMap (ev.comp iw) := by
      simpa using Over.w (toUnit (Over.mk ((𝟙_ (Over (Sp K))).hom ≫ spMap (ev.comp iw))))
    have hz : z.left = xp.left ≫ m₁.toSABMap.φ ≫ L.φB := by
      show (toUnit (Over.mk ((𝟙_ (Over (Sp K))).hom ≫ spMap (ev.comp iw))) ≫ L.D.c y).left = x ≫ m₁.toSABMap.φ ≫ L.φB
      rw [Over.comp_left, htu, hx1]; simp
    have hpow := pow_left_of_isGrpPullback hpb _ xp z hz l.M'
    have hxa : (xp ^ l.M').left ≫ m₁.toSABMap.φ ≫ L.φB =
        spMap (ev.comp iw) ≫ (L.D.c (l.M' • e (e.symm y))).left := by
      rw [LinearEquiv.apply_symm_apply, degPre_c_nsmul, ← hpow]
      show ((toUnit (Over.mk ((𝟙_ (Over (Sp K))).hom ≫ spMap (ev.comp iw))) ≫ L.D.c y) ^ l.M').left = _
      rw [← MonObj.comp_pow, Over.comp_left, htu]; simp
    have hxs : (xp ^ l.M').left ≫ o'.t.G.hom = 𝟙 _ := by simpa using Over.w (xp ^ l.M')
    have h₁ := hpts _ (e.symm y) hxs hxa
    have hsec : (xp ^ l.M').left ≫ θ = c' (e.symm y) := by
      apply hpb1.1.hom_ext
      · rw [Category.assoc, h₁, (hc' _).2.1]
      · rw [Category.assoc, hθ.1.w, ← Category.assoc, hxs, (hc' _).1]; simp
    have hM' : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
    obtain ⟨y₀, hy₀⟩ := GlobalTheory.T.grpPullback_point_descends_algClosed_subfield K k₀ hk₀ B₀ o'.t.G (θ ≫ π₀) hB₀ h1 l.M' hM' xp (c₀ (e.symm y))
      (by rw [← Category.assoc, hsec, (hc' _).2.2])
    exact ⟨y₀, hy₀⟩

end GlobalTheory.UCanon.PtsDescent
