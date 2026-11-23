import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PrimitiveCocycle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KTrivExternalTensorPowerLineBundle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UU.KTwist

open GlobalTheory.KerPow

section General

variable {X Y B : Scheme.{0}} {N N' : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem gen_div_of_gen {M M' : LB Y} (h : ∃ t : LB.Gen M, t.IsGen) (h' : ∃ t : LB.Gen M', t.IsGen) :
    ∃ t : LB.Gen (LB.div M M'), t.IsGen := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨t', ht'⟩ := h'
  refine ⟨⟨fun p => res (inf_le_left : M.U p.1 ⊓ M'.U p.2 ≤ _) (t.s p.1) *
    (res (inf_le_right : M.U p.1 ⊓ M'.U p.2 ≤ _) (t'.s p.2))⁻¹⟩, fun p q => unit_ext fun y hy => ?_⟩
  have v : ∀ p : M.ι × M'.ι, y ∈ M.U p.1 ⊓ M'.U p.2 → gm (𝟙 Y) y (M.U p.1 ⊓ M'.U p.2)
      (res (inf_le_left : M.U p.1 ⊓ M'.U p.2 ≤ _) (t.s p.1) *
        (res (inf_le_right : M.U p.1 ⊓ M'.U p.2 ≤ _) (t'.s p.2))⁻¹) =
      gm (𝟙 Y) y _ (t.s p.1) * (gm (𝟙 Y) y _ (t'.s p.2))⁻¹ := fun p hp =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ y _ hp _)
      ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res _ y _ hp _))))
  have tr : ∀ {A : LB Y} {a : LB.Gen A}, a.IsGen → ∀ i j, y ∈ A.U i ⊓ A.U j →
      gm (𝟙 Y) y _ (a.s i) = gm (𝟙 Y) y _ (A.g i j) * gm (𝟙 Y) y _ (a.s j) := fun ha i j hm =>
    (gm_res _ y _ hm _).symm.trans ((congrArg (gm (𝟙 Y) y _) (ha i j)).trans
      ((map_mul _ _ _).trans (congrArg _ (gm_res _ y _ hm _))))
  refine ((gm_res _ y _ hy _).trans (v p hy.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_div M' M (𝟙 Y) y p q hy) ((gm_res _ y _ hy _).trans (v q hy.2)))).symm)
  rw [tr ht p.1 q.1 ⟨hy.1.1, hy.2.1⟩, tr ht' p.2 q.2 ⟨hy.1.2, hy.2.2⟩, mul_inv, _root_.mul_mul_mul_comm]

theorem hasGen_div_iff (hN : N.IsLB) (hN' : N'.IsLB) (h' : HasGen N' φ ε) :
    HasGen (LB.div N N') φ ε ↔ HasGen N φ ε := by
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨u', hu'⟩ := h'
    obtain ⟨u, hu, -⟩ := DescendedPrincipal.exists_gen_mul_div hN hN' u' hu' q hq
    exact ⟨u, hu⟩
  · intro h
    obtain ⟨w, hw⟩ := gen_div_of_gen h h'
    exact gen_chartPull (DescendedPrincipal.chartPullDiv N N' φ ε) w hw

theorem locGen_div_iff (hN : N.IsLB) (hN' : N'.IsLB) {π : Y ⟶ B} (h' : LocGen N' π φ ε) :
    LocGen (LB.div N N') π φ ε ↔ LocGen N π φ ε := by
  have shrink : ∀ {A : LB X} {V W : B.Opens}, W ≤ V → HasGen A (fun k => (π ⁻¹ᵁ V).ι ≫ φ k) ε →
      HasGen A (fun k => (π ⁻¹ᵁ W).ι ≫ φ k) ε := fun {A V W} hle t =>
    t.pull (Y.homOfLE (show π ⁻¹ᵁ W ≤ π ⁻¹ᵁ V from fun _ h => hle h))
      (fun k => by rw [← Category.assoc, Scheme.homOfLE_ι])
  constructor <;> intro H p <;> obtain ⟨V, hV, t⟩ := H p <;> obtain ⟨V', hV', t'⟩ := h' p
  · exact ⟨V ⊓ V', ⟨hV, hV'⟩, (hasGen_div_iff hN hN' (shrink inf_le_right t')).1 (shrink inf_le_left t)⟩
  · exact ⟨V ⊓ V', ⟨hV, hV'⟩, (hasGen_div_iff hN hN' (shrink inf_le_right t')).2 (shrink inf_le_left t)⟩

end General

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] {T : Over S}

theorem inK_div_iff {L O : LB B.left} (hL : L.IsLB) (hO : O.IsLB) {x : T ⟶ B} (hx : InK B O x) :
    InK B (LB.div L O) x ↔ InK B L x :=
  (inK_iff_locGen x).trans ((locGen_div_iff hL hO ((inK_iff_locGen x).1 hx)).trans (inK_iff_locGen x).symm)

theorem inK_of_lam [IsCommMonObj B] {O : LB B.left} (hO : O.IsLB) (hu : ∃ u : LB.Gen (abelian₂ B O), u.IsGen)
    (x : T ⟶ B) : InK B O x := by
  have H₀ : HasGen O (PrimCocycle.lamφ B) PrimCocycle.lamε := hu
  have H₁ : LocGen O (fst T B).left
      (fun I => (lift (fst T B ≫ x) (snd T B)).left ≫ PrimCocycle.lamφ B I) PrimCocycle.lamε := fun _ =>
    ⟨⊤, trivial, H₀.pull (((fst T B).left ⁻¹ᵁ ⊤).ι ≫ (lift (fst T B ≫ x) (snd T B)).left)
      fun _ => Category.assoc _ _ _⟩
  have H₂ := BoxKernel.locGen_base hO (fst T B).left (K := Fin 2) ![x.left, (1 : T ⟶ B).left] ![-1, 1]
  refine (inK_iff_locGen x).2 (H₁.comb hO H₂ fun U _ h => ?_)
  rw [PrimCocycle.prod_lam (fst T B ≫ x) (snd T B) h, Fin.prod_univ_two, Fin.prod_univ_two]
  have e₁ : (fst T B).left ≫ (1 : T ⟶ B).left = (1 : T ⊗ B ⟶ B).left :=
    congrArg (fun q : T ⊗ B ⟶ B => q.left) (MonObj.comp_one (fst T B))
  show h (translPt B x).left * (h ((fst T B).left ≫ x.left))⁻¹ * (h (snd T B).left)⁻¹ * h (1 : T ⊗ B ⟶ B).left *
      (h ((fst T B).left ≫ x.left) ^ (-1 : ℤ) * h ((fst T B).left ≫ (1 : T ⟶ B).left) ^ (1 : ℤ))⁻¹ =
    h (translPt B x).left ^ (1 : ℤ) * h (snd T B).left ^ (-1 : ℤ)
  rw [e₁]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

end GlobalTheory.UU.KTwist

namespace GlobalTheory.UU

end GlobalTheory.UU

end
