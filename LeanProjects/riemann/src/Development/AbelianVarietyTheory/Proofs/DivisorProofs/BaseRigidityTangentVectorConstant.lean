import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfNsmulEqOfEqClosedPointDualNumbersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsObjectMapsOfDualNumberIdentificationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberPointsPulledBackObjectFromBaseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RigBase

theorem grp_through {S S₁ S₂ : Scheme.{0}} {B' : Over S₂} {Q : Over S₁} {D O : Over S} [GrpObj B'] [GrpObj Q]
    [GrpObj D] [GrpObj O] {g : S₂ ⟶ S} {π : B'.left ⟶ Q.left} {β : Q.left ⟶ D.left} {φB : O.left ⟶ D.left}
    {ρ₁ : S₂ ⟶ S₁} {j : S₁ ⟶ S} (hπ : IsGrpPullback B' Q ρ₁ π) (hβ : IsGrpPullback Q D j β)
    (hφ : IsGrpPullback O D (𝟙 S) φB) (hg : ρ₁ ≫ j = g) :
    ∃ π' : B'.left ⟶ O.left, π' ≫ φB = π ≫ β ∧ π' ≫ O.hom = B'.hom ≫ g ∧ IsGrpPullback B' O g π' := by
  have hc := (hπ.comp hβ).congr hg rfl
  have w : (π ≫ β) ≫ D.hom = (B'.hom ≫ g) ≫ 𝟙 S := by rw [Category.comp_id]; exact hc.1.w
  exact ⟨hφ.1.lift (π ≫ β) (B'.hom ≫ g) w, hφ.1.lift_fst _ _ _, hφ.1.lift_snd _ _ _,
    hφ.cancel (hc.congr (Category.comp_id g).symm (hφ.1.lift_fst _ _ _).symm) (hφ.1.lift_snd _ _ _)⟩

theorem lb_through {X Y Z T : Scheme.{0}} {L₀ : LB X} {L : LB Y} {M : LB Z} (hL₀ : L₀.IsLB) (hL : L.IsLB)
    (hM : M.IsLB) {φB : X ⟶ Y} {β : Z ⟶ Y} {π₁ π₂ : T ⟶ Z} {π₁' π₂' : T ⟶ X} (h₀ : LBIso L₀ (L.pull φB))
    (hβ : LBIso M (L.pull β)) (h : LBIso (M.pull π₁) (M.pull π₂)) (e₁ : π₁' ≫ φB = π₁ ≫ β)
    (e₂ : π₂' ≫ φB = π₂ ≫ β) : LBIso (L₀.pull π₁') (L₀.pull π₂') := by
  have key : ∀ {A : Scheme.{0}} {L' : LB A} {F : A ⟶ Y}, LBIso L' (L.pull F) → ∀ j : T ⟶ A,
      LBIso (L'.pull j) (L.pull (j ≫ F)) := fun H j =>
    LBIso.chartPull (chartPullPull _ _) (chartPullSame L _ _ _ j fun _ => rfl) H
  have a₁ := key h₀ π₁'
  have a₂ := key h₀ π₂'
  have b₁ := key hβ π₁
  have b₂ := key hβ π₂
  rw [e₁] at a₁
  rw [e₂] at a₂
  exact LBIso.trans (pull_isLB hL₀ _) (pull_isLB hL _) (pull_isLB hL₀ _) (LBIso.trans (pull_isLB hL₀ _) (pull_isLB hM _) (pull_isLB hL _)
    (LBIso.trans (pull_isLB hL₀ _) (pull_isLB hM _) (pull_isLB hM _) (LBIso.trans (pull_isLB hL₀ _) (pull_isLB hL _) (pull_isLB hM _) a₁ b₁.symm) h) b₂) a₂.symm

theorem const_on_base : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), ∀ (k : Type) [Field k] (ρ : R →+* DualNumber k) (a : Fin C.m → k), GlobalTheory.RigChart.IsConstAlong C.P.D.toPre C.s (fun i => (l.M' : ℤ) • C.δ i) ρ a → ρ.comp (Cn.ψ.comp MvPolynomial.C) = GlobalTheory.RigChart.constHom (ρ.comp (Cn.ψ.comp MvPolynomial.C)) := by
  intro E _ _ _ H Dw l Xo c φ R _ _ _ _ C Cn k _ ρ a hC
  obtain ⟨B', _, π₁, π₂, w, c', h₁, h₂, h0, hw, hc', -⟩ := hC
  obtain ⟨g, hD, -, hxe, -⟩ := Cn.data
  haveI := hD.e_hom
  have hβ : IsGrpPullback C.P.D.toPre.P.A Cn.L.D.P.A (specOf (Cn.ψ.comp MvPolynomial.C))
      (hD.e.hom.left ≫ pullback.fst Cn.L.D.P.A.hom (specOf (Cn.ψ.comp MvPolynomial.C))) :=
    ((isGrpPullback_of_iso hD.e).comp (isGrpPullback_pullback _ _)).congr (Category.id_comp _) rfl
  have hsp : ∀ ρ' : R →+* DualNumber k, spMap ρ' ≫ specOf (Cn.ψ.comp MvPolynomial.C) = spMap (ρ'.comp (Cn.ψ.comp MvPolynomial.C)) := fun ρ' => by
    rw [← Spec.map_comp]; rfl
  obtain ⟨π₁', e₁, w₁, g₁⟩ := grp_through h₁ hβ Cn.L.ab.1 (hsp ρ)
  obtain ⟨π₂', e₂, w₂, g₂⟩ := grp_through h₂ hβ Cn.L.ab.1
    (hsp _ : _ = spMap (GlobalTheory.RigChart.constHom (ρ.comp (Cn.ψ.comp MvPolynomial.C))))
  have hfst : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (ρ.comp (Cn.ψ.comp MvPolynomial.C)) =
      spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (GlobalTheory.RigChart.constHom (ρ.comp (Cn.ψ.comp MvPolynomial.C))) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  have agree : ∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k),
      x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁' = x ≫ π₂' := by
    intro Z x y hx
    apply Cn.L.ab.1.1.hom_ext
    · rw [Category.assoc, Category.assoc, e₁, e₂, ← Category.assoc, ← Category.assoc, h0 Z x y hx]
    · rw [Category.assoc, Category.assoc, w₁, w₂, ← Category.assoc, ← Category.assoc, hx, Category.assoc,
        Category.assoc, hfst]
  obtain ⟨w₀, hw₀⟩ := Cn.L.ab.2.2
  have hLB : LBIso (Cn.L.o.t.PP.L.pull π₁') (Cn.L.o.t.PP.L.pull π₂') :=
    lb_through Cn.L.o.t.PP.isLB Cn.L.D.P.isLB C.P.D.toPre.P.isLB ⟨w₀, hw₀⟩ ⟨hD.w, hD.w_gen⟩ ⟨w, hw⟩ e₁ e₂
  obtain ⟨o', m₁, m₂, io, hio, hm₁, hm₂⟩ :=
    GlobalTheory.T.exists_objectMaps_of_dualNumber_identifications c Cn.L.W Cn.L.b Cn.L.o k (ρ.comp (Cn.ψ.comp MvPolynomial.C)) B' π₁' π₂' g₁ g₂ agree hLB
  have hn : ((l.M' : ℕ) : k) ≠ 0 := by
    intro h0'
    have hM : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
    have hk : ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ((ρ.comp (Cn.ψ.comp MvPolynomial.C)).comp Cn.L.b))
        (l.M' : c.F) = 0 := by rw [map_natCast]; exact h0'
    rw [map_eq_zero_iff _ (RingHom.injective _)] at hk
    exact hM (by exact_mod_cast hk)
  have agree' : ∀ (Z : Scheme.{0}) (x : Z ⟶ o'.t.G.left) (y : Z ⟶ Sp k),
      x ≫ o'.t.G.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom →
        x ≫ m₁.toSABMap.φ = x ≫ m₂.toSABMap.φ := by
    intro Z x y hx
    rw [hm₁, hm₂, ← Category.assoc, ← Category.assoc]
    exact agree Z _ y (by rw [Category.assoc, hio, hx])
  have hinv : io.inv ≫ o'.t.G.hom = B'.hom := by rw [← hio, Iso.inv_hom_id_assoc]
  have hc : ∀ y, (C.P.D.toPre.c (Cn.e.symm y)).left ≫ hD.e.hom.left ≫ pullback.fst Cn.L.D.P.A.hom (specOf (Cn.ψ.comp MvPolynomial.C)) =
      specOf (Cn.ψ.comp MvPolynomial.C) ≫ (Cn.L.D.c (l.M' • y)).left := fun y => by
    have := hD.c_pr (Cn.e.symm y)
    rw [hxe, LinearEquiv.apply_symm_apply] at this
    exact this
  obtain ⟨x, hx₁, hx₂, hx₀⟩ := GlobalTheory.T.dualNumber_points_pulledBack_object_from_base Cn.L k (ρ.comp (Cn.ψ.comp MvPolynomial.C)) o' m₁ m₂ l.M' hn agree'
    (fun y => c' (Cn.e.symm y) ≫ io.inv)
    (fun y => by rw [Category.assoc, hinv, (hc' _).1])
    (fun y => by
      rw [hm₁]; simp only [Category.assoc, Iso.inv_hom_id_assoc]; rw [e₁, ← Category.assoc, (hc' _).2.1, Category.assoc, hc,
        ← Category.assoc, hsp])
    (fun y => by
      rw [hm₂]; simp only [Category.assoc, Iso.inv_hom_id_assoc]; rw [e₂, ← Category.assoc, (hc' _).2.2, Category.assoc, hc,
        ← Category.assoc, hsp]; rfl)
  exact Cn.L.fineEps k (ρ.comp (Cn.ψ.comp MvPolynomial.C)) o' m₁ m₂ x hx₁ hx₂ hx₀

end GlobalTheory.RigBase
