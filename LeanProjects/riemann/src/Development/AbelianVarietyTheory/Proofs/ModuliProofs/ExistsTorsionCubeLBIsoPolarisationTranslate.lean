import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTheoremAndSectionsFiniteGrowthAbelianVariety
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LamIsoOfPairings
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.TorsionTranslation

open Out CommutatorPairing PrimCocycle CechPic

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

theorem transl_mulA (k : ℕ) (y : 𝟙_ (Over S) ⟶ A) (hy : y ^ k = 1) :
    ((toUnit A ≫ y) * 𝟙 A).left ≫ (mulA A k).left = (mulA A k).left := by
  rw [← Over.comp_left, mulA, MonObj.comp_pow, Category.comp_id, mul_pow, ← MonObj.comp_pow, hy,
    MonObj.comp_one, _root_.one_mul]

theorem exists_character (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {X : Scheme.{0}} {M : LB X} (hM : M.IsLB)
    {I : Type} [Fintype I] (φ : I → (A.left ⟶ X)) (ε : I → ℤ) (k : ℕ)
    (u : LB.Gen (LB.LinComb M (fun i => (mulA A k).left ≫ φ i) ε)) (hu : u.IsGen) :
    ∃ χ : {y : 𝟙_ (Over S) ⟶ A // y ^ k = 1} → Γ((𝟙_ (Over S)).left, ⊤)ˣ,
      (∀ x y, χ ⟨x.1 * y.1, by rw [mul_pow, x.2, y.2, _root_.one_mul]⟩ = χ x * χ y) ∧
      ∀ y (z : A.left) J, Good M z J →
        val u ((toUnit A ≫ y.1) * 𝟙 A).left z J = val u (𝟙 _) z J * gm (toUnit A).left z ⊤ (χ y) := by
  have he : (1 : 𝟙_ (Over S) ⟶ A).left ≫ (toUnit A).left = 𝟙 _ := by
    rw [← Over.comp_left, comp_toUnit, toUnit_unit]; rfl
  have hp : Function.Surjective (toUnit A).left.appTop.hom := by
    have e : (toUnit A).left = A.hom := (Category.comp_id _).symm.trans (Over.w (toUnit A))
    rw [e]
    exact (hG _ _ hA).2
  have H : ∀ y : {y : 𝟙_ (Over S) ⟶ A // y ^ k = 1}, ∃ c : Γ((𝟙_ (Over S)).left, ⊤)ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ A.left) (z : Z) (J), Good M z J →
        val u (r ≫ ((toUnit A ≫ y.1) * 𝟙 A).left) z J = val u r z J * gm (r ≫ (toUnit A).left) z ⊤ c := by
    intro y
    obtain ⟨c, hc⟩ := exists_ratio hM (fun U _ h => Finset.prod_congr rfl fun i _ => by
        rw [← Category.assoc, transl_mulA k y.1 y.2]) (toUnit A).left _ he hp
      (DVR.pullGen_isGen _ _ _ u hu ((toUnit A ≫ y.1) * 𝟙 A).left) hu
    exact ⟨c, fun Z r z J hJ => (val_pull hJ _ _ _).symm.trans (hc Z r z J hJ)⟩
  choose χ hχ using H
  refine ⟨χ, fun x y => unit_ext fun z _ => ?_, fun y z J hJ => ?_⟩
  · choose J hJ using fun ψ : (𝟙_ (Over S)).left ⟶ X => exists_chart hM (ψ z)
    have a := hχ ⟨x.1 * y.1, by rw [mul_pow, x.2, y.2, _root_.one_mul]⟩ _ (1 : 𝟙_ (Over S) ⟶ A).left z J hJ
    have b := hχ x _ (1 : 𝟙_ (Over S) ⟶ A).left z J hJ
    have c := hχ y _ ((1 : 𝟙_ (Over S) ⟶ A).left ≫ ((toUnit A ≫ x.1) * 𝟙 A).left) z J hJ
    have e₁ : ((toUnit A ≫ x.1) * 𝟙 A).left ≫ ((toUnit A ≫ y.1) * 𝟙 A).left =
        ((toUnit A ≫ (x.1 * y.1)) * 𝟙 A).left := by
      rw [← Over.comp_left, MonObj.comp_mul, MonObj.comp_mul, comp_toUnit_assoc, Category.comp_id,
        ← _root_.mul_assoc, mul_comm (toUnit A ≫ y.1)]
    have e₂ : ((toUnit A ≫ x.1) * 𝟙 A).left ≫ (toUnit A).left = (toUnit A).left := by
      rw [← Over.comp_left, comp_toUnit]
    rw [b, Category.assoc, Category.assoc, e₁, e₂, a, he, _root_.mul_assoc, ← map_mul] at c
    exact mul_left_cancel c
  · have := hχ y _ (𝟙 _) z J hJ
    rwa [Category.id_comp, Category.id_comp] at this

theorem exists_gen_mulA {M : LB A.left} (hM : M.IsLB) (hΘ : ∃ t : LB.Gen (Theta A M), t.IsGen) (k : ℕ)
    (x : 𝟙_ (Over S) ⟶ A) (hx : x ^ k = 1) :
    ∃ u : LB.Gen (LB.LinComb M (fun I : ULift.{0} (Finset (Fin 2)) =>
      (mulA A k).left ≫ (psum A ![toUnit A ≫ x, 𝟙 A] I.down).left) lamε), u.IsGen := by
  refine (cls_eq_zero_iff (LB.isLB_linComb hM _ _)).1 ?_
  have h₁ : (cubeLB A ![toUnit A ≫ x, 𝟙 A] M).IsLB := LB.isLB_linComb hM _ _
  have e := congrArg (CechPic.pull (mulA A k).left) ((cls_linComb hM _ _ h₁).symm.trans (cls_cube_two hM _ _ h₁))
  rw [pull_lam, comp_toUnit_assoc, Category.comp_id, map_sum] at e
  have e' : lam (cls M hM) (toUnit A ≫ x) (mulA A k) = 0 := by
    rw [mulA, lam_pow_right hM hΘ, ← lam_pow_left hM hΘ, ← MonObj.comp_pow, hx, MonObj.comp_one, lam_one_left]
  rw [cls_linComb hM]
  refine Eq.trans (Finset.sum_congr rfl fun I _ => ?_) (e.trans e')
  rw [map_zsmul, pull_comp]

end GlobalTheory.TorsionTranslation

namespace GlobalTheory

open TorsionTranslation PairingDetermines IsoDescent PrimCocycle

theorem exists_torsion_lbIso_cubeLB : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (k : ℕ) (x : 𝟙_ (Over (Sp K)) ⟶ P.A), M.IsLB → (k : K) ≠ 0 → x ^ k = 1 → ∃ y : 𝟙_ (Over (Sp K)) ⟶ P.A, y ^ k = 1 ∧ LBIso (cubeLB P.A ![toUnit P.A ≫ x, 𝟙 P.A] M) (cubeLB P.A ![toUnit P.A ≫ y, 𝟙 P.A] P.L) := by
  intro hL hL' K _ _ P M k x hM hk hx
  haveI : IsCommMonObj P.A := P.isAb.comm
  obtain ⟨u, hu⟩ := exists_gen_mulA hM (AbLaw.CubeAssembly.cube_gen _ P M hM) k x hx
  obtain ⟨χ, hχ, vχ⟩ := exists_character hL.globalFns P.isAb hM _ _ k u hu
  obtain ⟨y, ⟨hy, hw⟩, -⟩ := hL'.charPair K P k hk (fun δ => (χ δ)⁻¹) (fun a b =>
    (congrArg (·⁻¹) (hχ a b)).trans (mul_inv _ _))
  refine ⟨y, hy, ?_⟩
  obtain ⟨u₀, hu₀, v₀⟩ := exists_gen_lam hL.globalFns hL.cube P (𝟙 P.A) 1 k y hy
  obtain ⟨u', hu', v'⟩ := exists_gen P.isLB (φ' := fun I : ULift.{0} (Finset (Fin 2)) =>
      (Out.mulA P.A k).left ≫ (psum P.A ![toUnit P.A ≫ y, 𝟙 P.A] I.down).left) (ε' := lamε)
    (fun U _ h => Finset.prod_congr rfl fun I _ => by
      have e : (lift (toUnit P.A ≫ y) (𝟙 P.A)).left ≫ lamφ P.A I =
          (psum P.A ![toUnit P.A ≫ y, 𝟙 P.A] I.down).left :=
        congrArg (fun q => q.left) ((psum_hom (preHom (lift (toUnit P.A ≫ y) (𝟙 P.A))) (x2 P.A) I.down).trans
          (congrArg (fun q => psum P.A q I.down) (funext fun i => by fin_cases i <;> simp [preHom, x2])))
      rw [Over.id_left, Category.comp_id, e, Nat.cast_one, _root_.mul_one]) u₀ hu₀
  refine lbIso_of_invariant hM P.isLB _ _ _ _ (Out.mulA P.A k).left
    (I := {y : 𝟙_ (Over (Sp K)) ⟶ P.A // y ^ k = 1}) (fun y => ((toUnit P.A ≫ y.1) * 𝟙 P.A).left)
    (fun δ => transl_mulA k δ.1 δ.2)
    (fun U f hf => torsion_invariant_descends (fun S _ P n hn => by
      obtain ⟨a, b, c, e, -⟩ := hL.mulN S P n hn
      exact ⟨a, b, c, e⟩) K P k hk U f fun y hy => hf ⟨y, hy⟩) u hu u' hu'
    (fun δ z J J' hJ hJ' => ?_)
  have w := CommPairing.weilIs_symm P.isLB (hw δ)
  rw [inv_inv] at w
  have h₁ := vχ δ z J hJ
  have h₂ := v₀ δ.1 (χ δ) δ.2 (by rw [Category.comp_id, Category.comp_id]; exact w) z J' hJ'
  rw [pow_one, ← v' _ _ z J' hJ', ← v' _ _ z J' hJ'] at h₂
  refine (congrArg₂ (fun a b => a * b⁻¹) h₂ h₁).trans ?_
  exact mul_div_mul_right_eq_div _ _ _ |> fun h => by simpa only [div_eq_mul_inv] using h

end GlobalTheory
