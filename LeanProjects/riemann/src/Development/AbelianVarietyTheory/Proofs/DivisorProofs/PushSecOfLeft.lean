import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToSiegAmple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelPull

theorem push_sec_of_left {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (hpb : IsGrpPullback A' A f φ) {x : 𝟙_ (Over S) ⟶ A} {x' : 𝟙_ (Over S') ⟶ A'}
    (hx : x'.left ≫ φ = f ≫ x.left) (T : Over S') :
    pushHom hpb T (toUnit T ≫ x') = toUnit (Over.mk (T.hom ≫ f)) ≫ x := by
  apply Over.OverMorphism.ext
  show ((toUnit T).left ≫ x'.left) ≫ φ = (toUnit (Over.mk (T.hom ≫ f))).left ≫ x.left
  rw [Category.assoc, hx, Over.toUnit_left, Over.toUnit_left, ← Category.assoc]
  rfl

theorem isSympLev_pull {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] [IsCommMonObj A]
    [IsCommMonObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left} {φ₂ : (G2 A').left ⟶ (G2 A).left}
    (hpb : IsGrpPullback A' A f φ) (sq : IsSquare φ φ₂) {P : LB (G2 A).left} {P' : LB (G2 A').left}
    (hP : P.IsLB) (hP' : P'.IsLB) (H : LBIso P' (P.pull φ₂)) {h M : ℕ} {B : Type} [CommRing B] {ζ : B}
    {s : S ⟶ Sp B} {lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)}
    {lev' : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S') ⟶ A')} (hl : ∀ a, (lev' a).left ≫ φ = f ≫ (lev a).left)
    (hS : IsSympLev P h M ζ s lev) : IsSympLev P' h M ζ (f ≫ s) lev' := by
  have hp' : ∀ a, pushHom hpb _ (lev' a) = toUnit _ ≫ lev a := fun a => by
    have e := push_sec_of_left hpb (hl a) (𝟙_ (Over S'))
    rwa [toUnit_unit, Category.id_comp] at e
  refine ⟨fun a b => push_injective hpb _ ?_, fun a => push_injective hpb _ ?_, ?_⟩
  · rw [map_mul, hp', hp', hp', hS.1, MonObj.comp_mul]
  · rw [map_pow, map_one, hp', ← MonObj.comp_pow, hS.2.1, MonObj.comp_one]
  intro k _ _ x β z hx hz
  obtain ⟨g₁, g₂, g₃⟩ := hS.2.2 k (x ≫ f) β z (by rw [Category.assoc, hx]) hz
  refine ⟨fun a => Iff.trans ?_ (g₁ a), fun g hg => ?_, fun a b => ?_⟩
  · rw [← (push_injective hpb (Over.mk x)).eq_iff, push_sec_of_left hpb (hl a), map_one]
    rfl
  · obtain ⟨a, ha⟩ := g₂ (pushHom hpb (Over.mk x) g) (by
      have := congrArg (pushHom hpb (Over.mk x)) hg
      rw [map_pow, map_one] at this
      exact this)
    exact ⟨a, push_injective hpb _ ((push_sec_of_left hpb (hl a) _).trans ha)⟩
  · exact (weilIs_grpPullback_of_comm S S' A A' f φ _ _ (pull_isLB hP _) (pull_isLB hP' _) hpb
      (diag_iso sq H) (Over.mk x) M _ _ _ _ _
      (congrArg (fun q => q.left) (push_sec_of_left hpb (hl a) (Over.mk x)).symm)
      (congrArg (fun q => q.left) (push_sec_of_left hpb (hl b) (Over.mk x)).symm)).2 (g₃ a b)

theorem kerBy_pull {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left} (h : IsGrpPullback A' A f φ) (sq : IsSquare φ φ₂)
    {P : LB (A ⊗ A).left} {P' : LB (A' ⊗ A').left} (hP : P.IsLB) (hP' : P'.IsLB) (H : LBIso P' (P.pull φ₂)) (d : ℕ)
    (hn : ∀ (T : Over S) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ d = 1)
    (T : Over S') (x : T ⟶ A') (hx : ∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) :
    x ^ d = 1 := by
  obtain ⟨u, hu⟩ := H
  obtain ⟨t, ht⟩ := hx
  refine push_injective h T ?_
  rw [map_pow, map_one]
  refine hn _ (pushHom h T x) ?_
  let T₀ : Over S := Over.mk (T.hom ≫ f)
  have w₁ : (fst A T₀).left ≫ A.hom = ((snd A T₀).left ≫ T.hom) ≫ f :=
    pullback.condition.trans (Category.assoc _ _ _).symm
  let a : (A ⊗ T₀).left ⟶ A'.left := h.1.lift _ _ w₁
  have a₁ : a ≫ φ = (fst A T₀).left := h.1.lift_fst _ _ _
  have a₂ : a ≫ A'.hom = (snd A T₀).left ≫ T.hom := h.1.lift_snd _ _ _
  let χ : (A ⊗ T₀).left ⟶ (A' ⊗ T).left := pullback.lift a (snd A T₀).left a₂
  have c₁ : χ ≫ (fst A' T).left = a := pullback.lift_fst _ _ _
  have c₂ : χ ≫ (snd A' T).left = (snd A T₀).left := pullback.lift_snd _ _ _
  obtain ⟨t₂, ht₂, -⟩ := exists_up ((isGen_iff u).1 hu) hP hP' t ht
  refine gen_chartPull (chartPullSame P _ _ _ χ fun _ => ?_) t₂ ht₂
  refine ((Category.id_comp _).symm.trans (lift_sq sq (T := A ⊗ T₀) χ _ _ (𝟙 _) _ _ ?_ ?_).symm)
  · rw [Over.comp_left, Category.assoc, ← Category.assoc χ, c₂, Category.id_comp]
    rfl
  · rw [← Category.assoc, c₁, a₁, Category.id_comp]

theorem siegKerBy_pull {S S' : Scheme.{0}} {h M : ℕ} {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {ζ' : B'}
    {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {c : SiegPre h M ζ s} {c' : SiegPre h M ζ' s'} {f : S' ⟶ S}
    (m : SiegPB c' c f) {d : ℕ} (hc : SiegKerBy c d) : SiegKerBy c' d := by
  obtain ⟨φ, φ₂, pb, sq, iso, -⟩ := m
  exact ⟨(GlobalTheory.pol_pull S S' c.A c'.A f φ _ _ (pull_isLB c.isLB _) (pull_isLB c'.isLB _) c.ab pb
    (diag_iso sq iso)).2.1 hc.1, kerBy_pull pb sq c.isLB c'.isLB iso d hc.2⟩

end GlobalTheory.UPel.HT
