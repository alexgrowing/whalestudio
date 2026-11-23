import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelObjectOddLevelRigid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemePrimeToCharTorsionRational
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPolAVHypSRetract
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon GlobalTheory.PolDeg GlobalTheory.TInj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PresRigid

open GlobalTheory.CechPic GlobalTheory.SiegLev GlobalTheory.SiegRigid GlobalTheory.ZM

theorem eq_of_field_of_ample {S : Scheme.{0}} {A : Over S} [GrpObj A] (c : CechPic.Pic A.left)
    {K : Type} [Field K] [IsAlgClosed K] {A' : Over (Sp K)} [GrpObj A'] (hA' : IsAbelianScheme A') {z : Sp K ⟶ S}
    {φ φ' : A'.left ⟶ A.left} (h : IsGrpPullback A' A z φ) (h' : IsGrpPullback A' A z φ')
    {M : LB A'.left} (hM : M.IsLB) (hamp : Out.RelAmple A' M) (hMc : cls M hM = pull φ' c)
    (hc : pull φ c = pull φ' c) {N : ℕ} (hN : 3 ≤ N) (hNK : (N : K) ≠ 0)
    (hfix : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Sp K) (x : Over.mk t ⟶ A'), x ^ N = 1 →
      x.left ≫ φ = x.left ≫ φ') : φ = φ' := by
  obtain ⟨σ, hσ, e⟩ := exists_aut h h'
  have := hA'.comm
  have key := serreAmple K A' hA' M hM hamp N hN hNK σ hσ
    (by rw [hMc, ← pull_comp, e, hc]) fun Ω _ _ t x hx => by
      apply Over.OverMorphism.ext
      apply h'.1.hom_ext
      · rw [Over.comp_left, Category.assoc, e]
        exact hfix Ω t x hx
      · rw [Over.w, Over.w]
  rw [← e, key, Over.id_left, Category.id_comp]

theorem cls_diag_lam_pull {S S' : Scheme.{0}} {G : Over S} {H : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj H]
    [IsCommMonObj H] {f : S' ⟶ S} {φ : H.left ⟶ G.left} (hp : IsGrpPullback H G f φ) {L : LB G.left} (hL : L.IsLB)
    (h₁ : ((abelian₂ G L).pull (lift (𝟙 G) (𝟙 G)).left).IsLB)
    (h₂ : ((abelian₂ H (L.pull φ)).pull (lift (𝟙 H) (𝟙 H)).left).IsLB) : cls _ h₂ = pull φ (cls _ h₁) := by
  have hL' := pull_isLB hL φ
  have hΛ : (abelian₂ G L).IsLB := LB.isLB_linComb hL _ _
  have hΛ' : (abelian₂ H (L.pull φ)).IsLB := LB.isLB_linComb hL' _ _
  have c₁ : cls _ hΛ = lam (cls L hL) (fst G G) (snd G G) := cls_cube_two hL _ _ hΛ
  have c₂ : cls _ hΛ' = lam (cls _ hL') (fst H H) (snd H H) := cls_cube_two hL' _ _ hΛ'
  have c₃ : lam (cls L hL) (pushHom hp H (𝟙 H)) (pushHom hp H (𝟙 H)) = lam (pull φ (cls L hL)) (𝟙 H) (𝟙 H) := by
    simp only [lam, ← map_mul, ← map_one (pushHom hp H)]
    simp only [← pull_comp]
    rfl
  have c₄ : pull (pushHom hp H (𝟙 H)).left (lam (cls L hL) (𝟙 G) (𝟙 G)) =
      lam (cls L hL) (pushHom hp H (𝟙 H)) (pushHom hp H (𝟙 H)) := by
    rw [pull_lam, Category.comp_id]
  have c₅ : (pushHom hp H (𝟙 H)).left = φ := Category.id_comp φ
  rw [cls_pull hΛ, cls_pull hΛ', c₁, c₂, pull_lam, pull_lam, lift_fst, lift_snd, lift_fst, lift_snd, cls_pull hL,
    ← c₃, ← c₄]
  exact congrArg (fun q => pull q _) c₅

theorem diag_square {S S' : Scheme.{0}} {A : Over S'} {B : Over S} {φ : A.left ⟶ B.left}
    {φ₂ : (A ⊗ A).left ⟶ (B ⊗ B).left} (hs : IsSquare φ φ₂) :
    (lift (𝟙 A) (𝟙 A)).left ≫ φ₂ = φ ≫ (lift (𝟙 B) (𝟙 B)).left := by
  have a₁ := congrArg (fun q => q.left) (lift_fst (𝟙 B) (𝟙 B))
  have a₂ := congrArg (fun q => q.left) (lift_snd (𝟙 B) (𝟙 B))
  have b₁ := congrArg (fun q => q.left) (lift_fst (𝟙 A) (𝟙 A))
  have b₂ := congrArg (fun q => q.left) (lift_snd (𝟙 A) (𝟙 A))
  simp only [Over.comp_left, Over.id_left] at a₁ a₂ b₁ b₂
  apply pullback.hom_ext
  · show (_ ≫ _) ≫ (fst B B).left = (_ ≫ _) ≫ (fst B B).left
    rw [Category.assoc, hs.1, ← Category.assoc, b₁, Category.assoc, a₁]; simp
  · show (_ ≫ _) ≫ (snd B B).left = (_ ≫ _) ≫ (snd B B).left
    rw [Category.assoc, hs.2, ← Category.assoc, b₂, Category.assoc, a₂]; simp

theorem eq_of_lam_of_torsion : ∀ (V : Type) [CommRing V] [IsDomain V] [CharZero V] (D : DegPre V) {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B] (P : LB (G2 B).left), P.IsLB → ∀ (t : Sp V ⟶ S) (a₁ a₂ : D.P.A.left ⟶ B.left) (aa₁ aa₂ : (G2 D.P.A).left ⟶ (G2 B).left), IsGrpPullback D.P.A B t a₁ → IsGrpPullback D.P.A B t a₂ → IsSquare a₁ aa₁ → IsSquare a₂ aa₂ → LBIso (abelian₂ D.P.A D.P.L) (P.pull aa₁) → LBIso (abelian₂ D.P.A D.P.L) (P.pull aa₂) → ∀ n : ℕ, 3 ≤ n → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F], (∀ x : TF (R := V) F ⟶ D.P.A, x ^ n = 1 → x.left ≫ a₁ = x.left ≫ a₂) → a₁ = a₂ := by
  intro V _ _ _ D S B _ _ P hP t a₁ a₂ aa₁ aa₂ g₁ g₂ s₁ s₂ w₁ w₂ n hn F _ _ _ hfix
  have hab := D.P.isAb
  have hL := D.P.isLB
  have hΛ : (abelian₂ D.P.A D.P.L).IsLB := LB.isLB_linComb hL _ _
  have hN := pull_isLB hΛ (lift (𝟙 D.P.A) (𝟙 D.P.A)).left
  have hcls : ∀ (a : D.P.A.left ⟶ B.left) (aa : (G2 D.P.A).left ⟶ (G2 B).left), IsSquare a aa →
      LBIso (abelian₂ D.P.A D.P.L) (P.pull aa) →
      cls _ hN = pull a (pull (lift (𝟙 B) (𝟙 B)).left (cls P hP)) := by
    intro a aa s w
    rw [cls_pull hΛ, (cls_eq_iff hΛ (pull_isLB hP aa)).2 w, cls_pull hP, ← pull_comp, ← pull_comp, diag_square s]
  let ψ : D.P.A.left ⟶ D.P.A.left := g₂.1.lift a₁ D.P.A.hom g₁.1.w
  have e₁ : ψ ≫ a₂ = a₁ := g₂.1.lift_fst _ _ _
  have e₂ : ψ ≫ D.P.A.hom = D.P.A.hom := g₂.1.lift_snd _ _ _
  have hψ : IsGrpPullback D.P.A D.P.A (𝟙 _) ψ :=
    IsGrpPullback.cancel g₂ (by rw [Category.id_comp, e₁]; exact g₁) (by rw [e₂, Category.comp_id])
  have hψc : pull ψ (cls _ hN) = cls _ hN := by
    refine Eq.trans ?_ (hcls a₁ aa₁ s₁ w₁).symm
    rw [hcls a₂ aa₂ s₂ w₂, ← pull_comp, e₁]
  let j : Sp F ⟶ Sp V := DegPre.jFR (R := V) F
  have hp := isGrpPullback_pullback D.P.A j
  have := hab.smooth
  have := hab.proper
  have := hab.geomConnected
  have habF : IsAbelianScheme ((Over.pullback j).obj D.P.A) :=
    { comm := Functor.isCommMonObj_obj
      smooth := by change Smooth (pullback.snd D.P.A.hom j); infer_instance
      proper := by change IsProper (pullback.snd D.P.A.hom j); infer_instance
      geomConnected := by change GeometricallyConnected (pullback.snd D.P.A.hom j); infer_instance }
  have : CharZero (FractionRing V) := IsFractionRing.charZero_of_isFractionRing V
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap (FractionRing V) F).injective
  have hnF : (n : F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have e' : pullback.fst D.P.A.hom j ≫ ψ = pullback.fst D.P.A.hom j := by
    have := habF.comm
    have hL' := pull_isLB hL (pullback.fst D.P.A.hom j)
    obtain ⟨w, hw⟩ := (cls_eq_iff hL' hL').1 rfl
    have ha' : Out.RelAmple ((Over.pullback j).obj D.P.A) (D.P.L.pull (pullback.fst D.P.A.hom j)) :=
      relAmple_pull hp.1 hL hL' ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ => trivial) D.P.ample
    have hamp := GlobalTheory.EighthPowerFactor.relAmple_diag_lam habF hL'
      (exists_gen_theta_of_isAbelianScheme F _ habF _ hL') ha'
    have hM := pull_isLB (LB.isLB_linComb hL' _ _ : (abelian₂ ((Over.pullback j).obj D.P.A) _).IsLB)
      (lift (𝟙 ((Over.pullback j).obj D.P.A)) (𝟙 ((Over.pullback j).obj D.P.A))).left
    refine eq_of_field_of_ample (cls _ hN) habF ((hp.comp hψ).congr (Category.comp_id _) rfl) hp hM hamp
      (cls_diag_lam_pull hp hL hN hM) (by rw [pull_comp, hψc]) hn hnF fun Ω _ _ x y hy => ?_
    obtain ⟨e, rfl⟩ : ∃ e : F →+* Ω, x = spMap e := ⟨(Spec.preimage x).hom, (Spec.map_preimage x).symm⟩
    obtain ⟨y₀, hy₀⟩ := GlobalTheory.TorsRat.torsion_point_rational F Ω e _ habF n (IsUnit.mk0 _ hnF) y hy
    have : Epi (spMap e) := Flat.epi_of_flat_of_surjective (spMap e)
    have hw₀ : y₀ ≫ ((Over.pullback j).obj D.P.A).hom = 𝟙 _ := by
      rw [← cancel_epi (spMap e), ← Category.assoc, ← hy₀, Over.w y, Category.comp_id]
      rfl
    let y₁ : Over.mk (𝟙 (Sp F)) ⟶ (Over.pullback j).obj D.P.A := Over.homMk y₀ hw₀
    let u : Over.mk (spMap e) ⟶ Over.mk (𝟙 (Sp F)) := Over.homMk (spMap e) (Category.comp_id _)
    have hyu : y = u ≫ y₁ := Over.OverMorphism.ext hy₀
    have hy₁ : y₁ ^ n = 1 := by
      apply Over.OverMorphism.ext
      have h1 : u ≫ y₁ ^ n = u ≫ 1 := by rw [MonObj.comp_pow, ← hyu, hy, MonObj.comp_one]
      exact (cancel_epi (spMap e)).1 (congrArg (fun q => q.left) h1)
    have hy₂ : pushHom hp (Over.mk (𝟙 (Sp F))) y₁ ^ n = 1 := by rw [← map_pow, hy₁, map_one]
    let v : TF (R := V) F ⟶ Over.mk ((Over.mk (𝟙 (Sp F))).hom ≫ j) := Over.homMk (𝟙 _) (by simp [j])
    have hx := hfix (v ≫ pushHom hp (Over.mk (𝟙 (Sp F))) y₁) (by rw [← MonObj.comp_pow, hy₂, MonObj.comp_one])
    have hxl : (v ≫ pushHom hp (Over.mk (𝟙 (Sp F))) y₁).left = y₀ ≫ pullback.fst D.P.A.hom j := Category.id_comp _
    rw [hxl] at hx
    rw [hy₀, Category.assoc, Category.assoc]
    congr 1
    apply g₂.1.hom_ext
    · rw [Category.assoc, Category.assoc, e₁, ← Category.assoc, hx]
    · rw [Category.assoc, Category.assoc, e₂, Category.assoc]
  have hd := ReciprocityTheory.ChartRestriction.G.DVR.GC.isDominant_jFR (V := V) F
  have : IsDominant (pullback.fst D.P.A.hom j) := by
    refine ⟨?_⟩
    rw [DenseRange, Scheme.Pullback.range_fst]
    exact hd.denseRange.preimage D.P.A.hom.isOpenMap
  have : IsReduced D.P.A.left := GlobalTheory.isReduced_of_smooth_of_isReduced D.P.A.hom
  have key : ψ = 𝟙 _ :=
    ext_of_isDominant_of_isSeparated D.P.A.hom (e₂.trans (Category.id_comp _).symm) (pullback.fst D.P.A.hom j)
      (e'.trans (Category.comp_id _).symm)
  rw [← e₁, key, Category.id_comp]

end GlobalTheory.PresRigid

end
