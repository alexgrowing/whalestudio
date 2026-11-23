import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamTrivOfMemKL
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.DualAbelianSchemes.Rigdesc

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.QuotDesc

def idq {S : Scheme.{0}} {A B : Over S} (q : A ⟶ B) : A ⊗ A ⟶ A ⊗ B := lift (fst A A) (snd A A ≫ q)

theorem evc_lam {S : Scheme.{0}} {A Y : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) (hΛ : (abelian₂ A L).IsLB)
    (a b : Y ⟶ A) : evc hΛ a b = lam (cls L hL) a b := by
  rw [evc, show cls _ hΛ = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hΛ, pull_lam, lift_fst,
    lift_snd]

theorem lam_mul_right_sub {S : Scheme.{0}} {A Y : Over S} [GrpObj A] [IsCommMonObj A] (c : Pic A.left)
    (a k y : Y ⟶ A) : lam c a (k * y) - lam c a y = lam c (a * y) k - lam c y k := by
  simp only [lam]
  rw [show a * y * k = a * (k * y) by rw [_root_.mul_assoc, _root_.mul_comm y k],
    show y * k = k * y from _root_.mul_comm y k]
  abel

theorem exists_descent_lam : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A],
    IsAbelianScheme A → ∀ (L : LB A.left) (hL : L.IsLB) (H : Over (Sp R)) [GrpObj H] (i : H ⟶ A), IsMonHom i →
    Mono i → IsFinite H.hom → Flat H.hom →
    (∀ (T : Over (Sp R)) (x : T ⟶ A), GlobalTheory.MemKL A L x ↔ ∃ z : T ⟶ H, z ≫ i = x) →
    ∀ (B : Over (Sp R)) [GrpObj B] (q : A ⟶ B), IsAbelianScheme B → IsMonHom q → IsFinite q.left → Flat q.left →
    Surjective q.left → IsPullback ((fst H A ≫ i) * snd H A) (snd H A) q q →
    ∃ (P : LB (A ⊗ B).left) (hP : P.IsLB), ∀ (Y : Over (Sp R)) (a x : Y ⟶ A),
      evc hP a (x ≫ q) = GlobalTheory.CechPic.pull (a * x).left (cls L hL) - GlobalTheory.CechPic.pull a.left (cls L hL) -
        GlobalTheory.CechPic.pull x.left (cls L hL) + GlobalTheory.CechPic.pull (1 : Y ⟶ A).left (cls L hL) := by
  intro R _ _ A _ hA L hL H _ i _ _ _ _ hK B _ q hB _ hqf hqfl hqs hpb
  have := hA.comm
  have hΛ : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have hku : lam (cls L hL) (fst A H) (snd A H ≫ i) = 0 := by
    rw [← evc_lam hL hΛ, ← triv_ev_iff hΛ]
    exact lam_triv_of_memKL _ A hA L hL H i ((hK H i).2 ⟨𝟙 H, Category.id_comp i⟩)
  have := hB.smooth
  have := hqf
  have : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
  have hlfp : LocallyOfFinitePresentation q.left := inferInstance
  obtain ⟨-, h2⟩ := CompanionTheory.PfDual.rigDescent_holds (Sp R) A A B hA q hqfl hlfp hqs
  have hrig : Triv (ev (abelian₂ A L) (1 : A ⟶ A) (𝟙 A)) := by
    rw [triv_ev_iff hΛ, evc_lam hL hΛ, lam_one_left]
  have hinv : ∀ (T : Over (Sp R)) (x x' : T ⟶ A), x ≫ q = x' ≫ q →
      LBIso (ev (abelian₂ A L) (fst A T) (snd A T ≫ x)) (ev (abelian₂ A L) (fst A T) (snd A T ≫ x')) := by
    intro T x x' hxx
    refine (cls_eq_iff (pull_isLB hΛ _) (pull_isLB hΛ _)).1 ?_
    rw [cls_ev hΛ, cls_ev hΛ, evc_lam hL hΛ, evc_lam hL hΛ]
    obtain ⟨z, hz1, hz2⟩ : ∃ z : T ⟶ H ⊗ A, z ≫ ((fst H A ≫ i) * snd H A) = x ∧ z ≫ snd H A = x' :=
      ⟨_, hpb.lift_fst x x' hxx, hpb.lift_snd x x' hxx⟩
    subst hz1 hz2
    have ex : snd A T ≫ z ≫ ((fst H A ≫ i) * snd H A) =
        (snd A T ≫ z ≫ fst H A ≫ i) * (snd A T ≫ z ≫ snd H A) := by
      rw [MonObj.comp_mul, MonObj.comp_mul]
    rw [ex, ← sub_eq_zero, lam_mul_right_sub]
    have k : ∀ u : A ⊗ T ⟶ A, lam (cls L hL) u (snd A T ≫ z ≫ fst H A ≫ i) = 0 := fun u => by
      have e := congrArg (GlobalTheory.CechPic.pull (lift u (snd A T ≫ z ≫ fst H A)).left) hku
      rwa [map_zero, pull_lam, lift_fst, lift_snd_assoc, Category.assoc, Category.assoc] at e
    rw [k, k, sub_zero]
  obtain ⟨N, hN, -, hiso⟩ := h2 (abelian₂ A L) hΛ hrig hinv
  refine ⟨N, hN, fun Y a x => ?_⟩
  have hPc : GlobalTheory.CechPic.pull (idq q).left (cls N hN) = cls (abelian₂ A L) hΛ :=
    ((cls_eq_iff hΛ (pull_isLB hN _)).2 hiso).symm
  have e : lift a (x ≫ q) = lift a x ≫ idq q := by
    simp [idq]
  rw [evc, e, Over.comp_left, pull_comp, hPc, show cls _ hΛ = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hΛ, pull_lam, lift_fst,
    lift_snd]
  rfl

end GlobalTheory.QuotDesc
