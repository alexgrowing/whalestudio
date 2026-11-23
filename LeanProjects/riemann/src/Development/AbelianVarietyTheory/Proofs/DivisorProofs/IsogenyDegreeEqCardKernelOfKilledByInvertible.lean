import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FormallyUnramifiedMulInvertibleInteger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFlatFinrankStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.DegSep

variable {S : Scheme.{0}}

theorem one_left' (T : Over S) (G : Over S) [GrpObj G] : (1 : T ⟶ G).left = T.hom ≫ η[G].left := by
  have h := Over.w (toUnit T)
  change (toUnit T ≫ η[G]).left = _
  rw [Over.comp_left]
  congr 1

theorem comp_pow_id (T G : Over S) [GrpObj G] (x : T ⟶ G) (n : ℕ) : x ≫ (𝟙 G) ^ n = x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih, Category.comp_id]

end GlobalTheory.AV.DegSep

example (K : Type) [Field K] (X : Scheme) (f : X ⟶ Sp K) [IsFinite f] : LocallyOfFinitePresentation f := inferInstance

namespace GlobalTheory.AV.DegSep

theorem isUnit_natCast_Γ (K : Type) [Field K] (n : ℕ) (hn : (n : K) ≠ 0) : IsUnit (n : Γ(Sp K, ⊤)) := by
  have h : IsUnit (n : K) := hn.isUnit
  have := h.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  simpa using this

theorem deg_eq_card_ker (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B) (n : ℕ) (hn : (n : K) ≠ 0)
    (hiso : IsIsogeny f) (hker : ∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ≫ f.hom = 1 → x ^ n = 1) :
    deg f = Nat.card (ptMap f).ker := by
  have hfl : Flat f.hom.left := (GlobalTheory.T.dim_eq_flat_finrank_eq_deg_of_isIsogeny K A B f hiso).2.1
  have hfin : IsFinite f.hom.left := hiso.1
  have hprop : IsProper B.X.hom := B.ab.proper
  let e : Sp K ⟶ B.X.left := η[B.X].left
  have he1 : e ≫ B.X.hom = 𝟙 _ := Over.w η[B.X]
  have hecl : IsClosedImmersion e := by
    have : IsClosedImmersion (e ≫ B.X.hom) := by rw [he1]; infer_instance
    exact IsClosedImmersion.of_comp e B.X.hom
  let p := pullback.snd f.hom.left e
  let i := pullback.fst f.hom.left e
  have hpi : i ≫ A.X.hom = p := by
    calc i ≫ A.X.hom = i ≫ f.hom.left ≫ B.X.hom := by rw [Over.w f.hom]
      _ = p ≫ e ≫ B.X.hom := by rw [← Category.assoc, pullback.condition, Category.assoc]
      _ = p := by rw [he1, Category.comp_id]
  have hifu : FormallyUnramified i := inferInstance

  let T : Over (Sp K) := Over.mk (i ≫ A.X.hom)
  let x : T ⟶ A.X := Over.homMk i
  have hx1 : x ≫ f.hom = 1 := by
    ext1
    rw [Over.comp_left, one_left']
    change i ≫ f.hom.left = (i ≫ A.X.hom) ≫ e
    rw [hpi, pullback.condition]
  have hxn := hker T x hx1
  have hleft : i ≫ (Out.mulA A.X n).left = p ≫ η[A.X].left := by
    have h : (x ^ n).left = (1 : T ⟶ A.X).left := by rw [hxn]
    rw [← comp_pow_id, one_left'] at h
    change i ≫ (Out.mulA A.X n).left = _ at h
    rw [h]
    change (i ≫ A.X.hom) ≫ _ = _
    rw [hpi]
  let j : pullback f.hom.left e ⟶ pullback (Out.mulA A.X n).left η[A.X].left :=
    pullback.lift i p hleft
  have hmu : FormallyUnramified (Out.mulA A.X n).left :=
    GlobalTheory.formallyUnramified_mulA (Sp K) A.X n (isUnit_natCast_Γ K n hn)
  have hsnd : FormallyUnramified (pullback.snd (Out.mulA A.X n).left η[A.X].left) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) hmu
  have hjfu : FormallyUnramified j := by
    have : FormallyUnramified (j ≫ pullback.fst _ _) := by
      rw [pullback.lift_fst]; exact hifu
    exact FormallyUnramified.of_comp j (pullback.fst _ _)
  have hpfu : FormallyUnramified p := by
    have : j ≫ pullback.snd _ _ = p := pullback.lift_snd _ _ _
    rw [← this]
    exact MorphismProperty.comp_mem (@FormallyUnramified) _ _ hjfu hsnd
  have hpet : Etale p := Etale.of_formallyUnramified_of_flat p

  let t : Sp (AlgebraicClosure K) ⟶ Sp K := (ptOver K (AlgebraicClosure K)).hom
  obtain ⟨-, hcard⟩ := GlobalTheory.FinEt.card_points_eq_finrank p t (IsLocalRing.closedPoint _)
  rw [Scheme.Hom.finrank_pullback_snd] at hcard
  have horig : e (t (IsLocalRing.closedPoint _)) = B.origin := by
    rw [origin, one_left']
    change e _ = (𝟙 (Sp K) ≫ e) _
    rw [Category.id_comp]
    congr 1
    exact Subsingleton.elim _ _
  rw [horig] at hcard
  rw [deg, if_pos hiso, ← hcard]
  symm
  refine Nat.card_congr ?_
  exact
    { toFun := fun y => ⟨pullback.lift y.1.left t (by
          have h := y.2
          rw [MonoidHom.mem_ker, ptMap_apply] at h
          have h2 : (y.1 ≫ f.hom).left = (1 : ptOver K (AlgebraicClosure K) ⟶ B.X).left := by rw [h]
          rw [Over.comp_left, one_left'] at h2
          exact h2), pullback.lift_snd _ _ _⟩
      invFun := fun y => ⟨Over.homMk (y.1 ≫ i) (by
          change (y.1 ≫ i) ≫ A.X.hom = t
          rw [Category.assoc, hpi, y.2]), by
          rw [MonoidHom.mem_ker, ptMap_apply]
          ext1
          rw [Over.comp_left, one_left']
          change (y.1 ≫ i) ≫ f.hom.left = t ≫ e
          rw [Category.assoc, pullback.condition, ← Category.assoc, y.2]⟩
      left_inv := fun y => by
        apply Subtype.ext
        ext1
        exact pullback.lift_fst _ _ _
      right_inv := fun y => by
        apply Subtype.ext
        apply pullback.hom_ext
        · exact pullback.lift_fst _ _ _
        · rw [pullback.lift_snd]; exact y.2.symm }

end GlobalTheory.AV.DegSep

namespace GlobalTheory.AV.DegSep

theorem deg_eq_card_ker_of_killed : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B) (n : ℕ), (n : K) ≠ 0 →
    IsIsogeny f → (∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ≫ f.hom = 1 → x ^ n = 1) →
    deg f = Nat.card (ptMap f).ker :=
  fun K _ A B f n hn hiso hker => deg_eq_card_ker K A B f n hn hiso hker

end GlobalTheory.AV.DegSep
