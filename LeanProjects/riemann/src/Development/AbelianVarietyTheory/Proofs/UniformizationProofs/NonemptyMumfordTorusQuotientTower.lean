import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEvenPull

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.TowerEx

section Levels
variable {V : Type} [CommRing V] [IsLocalRing V] (e : ℕ)

instance nontrivial_level : Nontrivial (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1)) :=
  Ideal.Quotient.nontrivial_iff.2 fun h => (IsLocalRing.maximalIdeal.isMaximal V).ne_top
    (top_le_iff.1 (h.ge.trans (Ideal.pow_le_self (Nat.succ_ne_zero e))))

instance isLocalRing_level : IsLocalRing (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1)) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

theorem isNilpotent_max : IsNilpotent (IsLocalRing.maximalIdeal (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1))) := by
  refine ⟨e + 1, ?_⟩
  rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk (IsLocalRing.maximalIdeal V ^ (e + 1)))
    Ideal.Quotient.mk_surjective, ← Ideal.map_pow, Ideal.map_quotient_self, Ideal.zero_eq_bot]

end Levels

theorem thickMap_w {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) :
    thickMap R I e G ≫ (thickObj R I (e + 1) G).hom = (thickObj R I e G).hom ≫ thickTrans R I e :=
  pullback.lift_snd _ _ _

theorem isGrpPullback_thickMap {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] : IsGrpPullback (thickObj R I e G) (thickObj R I (e + 1) G) (thickTrans R I e) (thickMap R I e G) :=
  (isGrpPullback_pullback G (thick R I (e + 1))).cancel
    ((isGrpPullback_pullback G (thick R I e)).congr (thickTrans_comp R I e).symm
      ((pullback.lift_fst _ _ _).trans (Category.comp_id _)).symm) (pullback.lift_snd _ _ _)

theorem exists_isCPMap_thickMap {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {P : CP G} {P₀ : CP (thickObj R I e G)}
    {P₁ : CP (thickObj R I (e + 1) G)} (h₀ : IsLevelCP I e P₀ P) (h₁ : IsLevelCP I (e + 1) P₁ P) :
    ∃ w, IsCPMap P₀ P₁ (thickTrans R I e) (thickMap R I e G) (thickMap_w I e G) w := by
  obtain ⟨_, h₀⟩ := h₀
  obtain ⟨_, h₁⟩ := h₁
  exact exists_cancel h₁ h₀ (isGrpPullback_thickMap I e G) (thickTrans_comp R I e)
    ((pullback.lift_fst _ _ _).trans (Category.comp_id _))

theorem exists_levelMap {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {G : Over (Spec (CommRingCat.of V))}
    [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) {P : CP G} {X : Type} [AddCommGroup X] [Module.Free ℤ X] {e : ℕ}
    (l : Lev (IsLocalRing.maximalIdeal V) P X e) (l' : Lev (IsLocalRing.maximalIdeal V) P X (e + 1))
    (h : TorusCompat (thickTrans V _ e) (thickMap V _ e G) l.Q.i l'.Q.i) :
    ∃ β : l.Q.B.left ⟶ l'.Q.B.left, IsCPPullback l.D.M l'.D.M (thickTrans V _ e) β ∧
      l.Q.q.left ≫ β = thickMap V _ e G ≫ l'.Q.q.left := by
  have := hG.smooth
  have := hG.geomConnected
  have : Smooth (thickObj V (IsLocalRing.maximalIdeal V) e G).hom := by
    show Smooth (pullback.snd _ _); infer_instance
  have : GeometricallyConnected (thickObj V (IsLocalRing.maximalIdeal V) e G).hom := by
    show GeometricallyConnected (pullback.snd _ _); infer_instance
  have : ConnectedSpace (Spec (CommRingCat.of (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1)))) :=
    SplitTorus.connectedSpace_of_isLocalRing _
  have := (GroupConn.connectedSpace_group _ (thickObj V (IsLocalRing.maximalIdeal V) e G)).1
  obtain ⟨_, hP⟩ := exists_isCPMap_thickMap l.lev l'.lev
  exact exists_transition (isGrpPullback_thickMap _ e G) hP h l'.D l.D

theorem nonempty_tower : (AllSet fun s => Nonempty (Tower s)) := by
  intro V _ _ _ A G _ _ s
  have := s.semi.smooth
  have := s.semi.geomConnected
  have hs : ∀ e, Smooth (thickObj V (IsLocalRing.maximalIdeal V) e G).hom := fun e => by
    show Smooth (pullback.snd _ _); infer_instance
  have hc : ∀ e, GeometricallyConnected (thickObj V (IsLocalRing.maximalIdeal V) e G).hom := fun e => by
    show GeometricallyConnected (pullback.snd _ _); infer_instance
  let L : ℕ → Type 1 := fun e => {l : Lev (IsLocalRing.maximalIdeal V) s.P s.X e // ∃ σ : CubTriv l.Pe.c l.Q.i, σ.Even}
  have step : ∀ (e : ℕ) (l : L e), ∃ l' : L (e + 1),
      TorusCompat (thickTrans V _ e) (thickMap V _ e G) l.1.Q.i l'.1.Q.i := fun e l => by
    obtain ⟨P₁, h₁⟩ := exists_isLevelCP (IsLocalRing.maximalIdeal V) (e + 1) s.P
    obtain ⟨_, hP⟩ := exists_isCPMap_thickMap l.1.lev h₁
    obtain ⟨Q, hQ, hσ⟩ := exists_lift (isNilpotent_max (e + 1)) _ (Ideal.Quotient.factor_surjective _) _ _
      (isGrpPullback_thickMap _ e G) hP l.1.Q l.2
    obtain ⟨D⟩ := nonempty_desc _ (isNilpotent_max (e + 1)) _ P₁ Q hσ
    exact ⟨⟨⟨Q, P₁, h₁, D⟩, hσ⟩, hQ⟩
  choose nxt hnxt using step
  obtain ⟨D₀⟩ := nonempty_desc _ (isNilpotent_max 0) _ s.P₀ s.Q₀ s.even₀
  let l : ∀ e, L e := fun e => Nat.rec (motive := L) ⟨⟨s.Q₀, s.P₀, s.lev₀, D₀⟩, s.even₀⟩ nxt e
  have tor : ∀ e, TorusCompat (thickTrans V _ e) (thickMap V _ e G) (l e).1.Q.i (l (e + 1)).1.Q.i :=
    fun e => hnxt e (l e)
  choose β hβ hq using fun e => exists_levelMap s.semi (l e).1 (l (e + 1)).1 (tor e)
  exact ⟨⟨fun e => (l e).1, tor, β, hβ, hq⟩⟩

end GlobalTheory.UU.TowerEx
end
