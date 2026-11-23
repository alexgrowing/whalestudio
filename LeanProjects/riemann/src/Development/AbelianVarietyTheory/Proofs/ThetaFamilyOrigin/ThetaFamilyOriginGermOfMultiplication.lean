import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsVVGenOfIsThetaFamily
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsIndepSections

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaGerm

theorem associated_gs_down {X Y Z : Scheme.{0}} (L : LB X) (σ : Y ⟶ X) (ρ : X ⟶ Y) (e : ρ ≫ σ = 𝟙 X) (n : ℤ)
    (b : (LB.LinComb L (K := Fin 1) (fun _ => σ) (fun _ => n)).Sec) (r : Z ⟶ X) (z : Z) (j : PUnit → L.ι)
    (hj : r z ∈ LB.wchart L (fun _ : PUnit => 𝟙 X) j) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    Associated (gs r z (LB.wchart L (fun _ : PUnit => 𝟙 X) j) ((PowSec.down L σ ρ e n b).f j))
      (sval b (r ≫ ρ) z J) := by
  have hle := (PowSec.chart_eq L σ ρ e j).le
  have h₁ : gs r z (LB.wchart L (fun _ : PUnit => 𝟙 X) j) ((PowSec.down L σ ρ e n b).f j) =
      gs (r ≫ ρ) z (LB.wchart L (fun _ : Fin 1 => σ) (fun _ => j PUnit.unit)) (b.f (fun _ => j PUnit.unit)) :=
    (gs_res r z hle hj _).trans (gs_pull r ρ z _ (hle hj) _)
  rw [h₁, sec_trans b (r ≫ ρ) z (j := fun _ => j PUnit.unit) (hle hj) (hJ.mem (fun _ : Fin 1 => σ) (r ≫ ρ))]
  exact associated_unit_mul_left _ _ (Units.isUnit _)

theorem germ_origin : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N m : ℕ) (J : Type) (x : J → ((Out.baseOver (Sp K)) ⟶ P.A)) (th : LB.Sec (Out.LPow P.A P.L 1 (Out.baseOver (Sp K)))) (t : J → LB.Sec (Out.LPow P.A P.L N (Out.baseOver (Sp K)))) (ρ : P.A.left ⟶ ((Out.baseOver (Sp K)) ⊗ P.A).left) (e : ρ ≫ (snd (Out.baseOver (Sp K)) P.A).left = 𝟙 P.A.left) (a : J), Out.IsGenSec P.A P.L 1 th → IsThetaFamily P N m x th t → x a = 1 → (∃ l, (PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e ((1 : ℕ) : ℤ) (th)).f l ≠ 0) ∧ (∀ (y : P.A.left) k l, y ∈ (lbPow P.L N).U k → (Out.mulA P.A m).left y ∈ (lbPow P.L 1).U l → Associated (gs (𝟙 P.A.left) y ((lbPow P.L N).U k) ((PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e ((N : ℕ) : ℤ) (t a)).f k)) (gs (Out.mulA P.A m).left y ((lbPow P.L 1).U l) ((PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e ((1 : ℕ) : ℤ) (th)).f l))) := by
  intro hLaw K _ _ P N m J x th t ρ e a hth H hx
  let π : P.A ⟶ Out.baseOver (Sp K) := Over.homMk P.A.hom (Category.comp_id _)
  let ρ' : P.A ⟶ Out.baseOver (Sp K) ⊗ P.A := lift π (𝟙 _)
  have ρ₂ : ρ'.left ≫ (snd (Out.baseOver (Sp K)) P.A).left = 𝟙 _ :=
    congrArg (fun q => q.left) (lift_snd _ _ : ρ' ≫ _ = _)
  have ρ₁ : ρ'.left ≫ (fst (Out.baseOver (Sp K)) P.A).left = P.A.hom :=
    congrArg (fun q => q.left) (lift_fst _ _ : ρ' ≫ _ = _)
  have ρ₃ : (snd (Out.baseOver (Sp K)) P.A).left ≫ ρ'.left = 𝟙 _ := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ρ₁).trans (pullback.condition.symm.trans
        ((Category.comp_id _).trans (Category.id_comp _).symm)))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ρ₂).trans
        ((Category.comp_id _).trans (Category.id_comp _).symm))
  obtain rfl : ρ = ρ'.left := by
    rw [← Category.comp_id ρ, ← ρ₃, ← Category.assoc, e, Category.id_comp]
  haveI : IsIso ρ'.left := ⟨_, ρ₂, ρ₃⟩
  refine ⟨?_, fun y k l hk hl => ?_⟩
  · by_contra hne
    push_neg at hne
    have hz : Out.SecM.ofSec P.A th = 0 := by
      refine Subtype.ext (funext fun j => ?_)
      obtain ⟨k, rfl⟩ : ∃ k, j = fun _ => k := ⟨j 0, funext fun q => by rw [Subsingleton.elim q 0]⟩
      exact PowSec.appLE_injective ρ'.left _ _
        (PowSec.chart_eq P.L (snd (Out.baseOver (Sp K)) P.A).left ρ'.left ρ₂ (fun _ => k))
        ((hne fun _ => k).trans (map_zero _).symm)
    have : Subsingleton (Out.SecM P.A P.L (1 : ℕ) (Out.baseOver (Spec (CommRingCat.of K)))) :=
      subsingleton_of_forall_eq 0 fun y => by
        obtain ⟨r, hr⟩ := hth (Out.SecM.toSec P.A y)
        have e : y = r • Out.SecM.ofSec P.A th := Subtype.ext (funext hr)
        exact e.trans ((congrArg (r • ·) hz).trans (smul_zero r))
    have hnt : Nontrivial Γ((Out.baseOver (Spec (CommRingCat.of K))).left, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.domain_nontrivial
    have := hLaw.globalSectionsRank K P 1 le_rfl
    rw [Module.finrank_zero_of_subsingleton, one_pow] at this
    exact zero_ne_one this
  · obtain ⟨s, α, U, -, hs, hU, ht⟩ := H
    choose I hI using fun χ : P.A.left ⟶ P.A.left => exists_chart P.isLB (χ y)
    have hI' : Good P.L y I := hI
    have b₁ := ThetaCoord.sv_act ((hU a).pt_eq.trans hx) (ht a) π hI' (𝟙 _)
    have b₂ := ThetaCoord.sv_mulPull hs π hI' (𝟙 _)
    rw [MonObj.comp_one, _root_.one_mul, b₂] at b₁
    have e₁ : (Out.mulA P.A m).left ≫ ρ'.left = (lift π (𝟙 P.A ^ m)).left := by
      rw [← Over.comp_left, comp_lift, Category.comp_id]
      congr 2
      exact Over.OverMorphism.ext (Over.w (Out.mulA P.A m))
    have a₁ := associated_gs_down P.L _ _ e (N : ℤ) (t a) (𝟙 _) y k hk hI'
    have a₂ := associated_gs_down P.L _ _ e ((1 : ℕ) : ℤ) th (Out.mulA P.A m).left y l hl hI'
    rw [Category.id_comp] at a₁
    rw [e₁] at a₂
    refine a₁.trans (Associated.trans ?_ a₂.symm)
    exact (Associated.of_eq b₁).trans ((associated_unit_mul_left _ _ (Units.isUnit _)).trans
      (associated_unit_mul_left _ _ (Units.isUnit _)))

end GlobalTheory.ThetaGerm
