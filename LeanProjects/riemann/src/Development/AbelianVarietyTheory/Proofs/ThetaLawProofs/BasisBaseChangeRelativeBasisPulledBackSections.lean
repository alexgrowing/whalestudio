import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IndepOnEmpty
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PwIsoIsGen
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.BasisPowerSectionsLocalBaseChange

noncomputable section

namespace GlobalTheory.RelBasisFibre

section General

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw (pw isLB_pw)
open GlobalTheory.RelBasis GlobalTheory.KeyBasis

variable {X Y : Scheme.{0}} {L : LB X} {M : LB Y} {C : Type} [CommRing C] {n N : ℕ}
  {φ : Y ⟶ X} {w : LB.Iso M (L.pull φ)}

theorem comb_eq (p : Y ⟶ Sp C) {b : Fin N → LB.Sec (pw L (n : ℤ))} {b' : Fin N → ∀ i, Γ(Y, M.U i)}
    (hb : ∀ k, KeyVia.Via w n (b' k) (b k).f) (a : Fin N → C) (y : Y) {j : L.ι} {i : M.ι}
    (hj : φ y ∈ L.U j) (hi : y ∈ M.U i) :
    comb b p φ ⊤ (fun k => (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (a k)) y j =
      (gw w (𝟙 Y) y j i ^ n).val * gs (𝟙 Y) y (M.U i) (∑ k, AbLaw.cst p (M.U i) (a k) * b' k i) := by
  rw [gs_comb p (M.U i) (𝟙 Y) y hi, Finset.mul_sum, comb]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e := via_val (hb k) (𝟙 Y) y (j := j) (i := i) hj hi
  rw [Category.id_comp] at e
  rw [mul_left_comm, ← e, Category.id_comp]
  rfl

theorem exists_down (hL : L.IsLB) (hM : M.IsLB) (hw : w.IsGen) (V : Y.Opens) (hV : ∀ y, y ∈ V)
    (σ : ∀ j : L.ι, Γ(Y, V ⊓ φ ⁻¹ᵁ L.U j))
    (hσ : ∀ (y : Y) (j j' : L.ι), φ y ∈ L.U j → φ y ∈ L.U j' →
      gs (𝟙 Y) y _ (σ j) = (gm φ y (L.U j ⊓ L.U j') (L.g j j') ^ (n : ℤ)).val * gs (𝟙 Y) y _ (σ j')) :
    ∃ s : LB.Sec (pw M (n : ℤ)), ∀ (y : Y) (j : L.ι) (i : M.ι), φ y ∈ L.U j → y ∈ M.U i →
      gs (𝟙 Y) y _ (σ j) = (gw w (𝟙 Y) y j i ^ n).val * gs (𝟙 Y) y (M.U i) (s.f i) := by
  have le : ∀ j : (L.pull φ).ι, (L.pull φ).U j ≤ V ⊓ φ ⁻¹ᵁ L.U (j PUnit.unit) :=
    fun j y hy => ⟨hV y, KeyVia.chart_le j hy⟩
  let t : LB.Sec (pw (L.pull φ) (n : ℤ)) := ⟨fun j => resG Y (le j) (σ (j PUnit.unit)), fun j j' => fn_ext fun y hy => by
    refine ((gs_res (𝟙 Y) y _ hy _).trans (gs_res (𝟙 Y) y (le j) hy.1 _)).trans
      ((hσ y _ _ (le j hy.1).2 (le j' hy.2).2).trans (Eq.trans ?_ (gs_mul (𝟙 Y) y _ hy _ _).symm))
    refine congrArg₂ (· * ·) ?_ ((gs_res (𝟙 Y) y _ hy _).trans (gs_res (𝟙 Y) y (le j') hy.2 _)).symm
    refine Eq.trans ?_ ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (map_zpow _ _ _))).symm
    refine congrArg (fun u : (Y.presheaf.stalk y)ˣ => (u ^ (n : ℤ)).val) ?_
    have e := gm_pull_g L φ (𝟙 Y) y j j' hy.1 hy.2
    rw [Category.id_comp] at e
    exact e.symm⟩
  have hu := KeyVia.pwIso_isGen hw (n : ℤ)
  have hA := isLB_pw hM (n : ℤ)
  have hB := isLB_pw (DVR.linComb_isLB L hL (fun _ : PUnit => φ) (fun _ => 1)) (n : ℤ)
  refine ⟨DVR.secOfIso t hu hA hB, fun y j i hj hi => ?_⟩
  have hj' : y ∈ (L.pull φ).U (fun _ => j) := mem_pull.2 hj
  have hm : (𝟙 Y : Y ⟶ Y) y ∈ M.U i ⊓ (L.pull φ).U (fun _ => j) := ⟨hi, hj'⟩
  have e : gs (𝟙 Y) y (M.U i) ((DVR.secOfIso t hu hA hB).f i) =
      ((gw w (𝟙 Y) y j i ^ n)⁻¹).val * gs (𝟙 Y) y _ (σ j) := by
    refine (gs_res (𝟙 Y) y inf_le_left hm _).symm.trans ((congrArg (gs (𝟙 Y) y _)
      (DVR.secOfIso_spec t hu hA hB i (fun _ => j))).trans ((gs_mul (𝟙 Y) y _ hm _ _).trans
        (congrArg₂ (· * ·) ?_ ((gs_res (𝟙 Y) y _ hm _).trans (gs_res (𝟙 Y) y (le _) hj' _)))))
    refine (gs_unit (𝟙 Y) y _ hm _).trans (congrArg Units.val ((map_inv _ _).trans ?_))
    exact congrArg (·⁻¹) ((gm_res (𝟙 Y) y _ hm _).trans ((map_zpow _ _ _).trans (zpow_natCast _ _)))
  rw [e, Units.mul_inv_cancel_left]

end General

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

theorem main : ∀ (R R' : Type) [CommRing R] [CommRing R'] (x : KeyIn R) (x' : KeyIn R') (f : R →+* R') φ w (l N : ℕ) (b : Fin N → RR x l) (b' : Fin N → RR x' l), KeyVia x' x f φ w → (∀ k, SecVia x' x φ w (b' k) (b k)) → IsBasis x' b' → GlobalTheory.RelBasis.IndepOn b x'.P.A.hom φ ⊤ ∧ GlobalTheory.RelBasis.SpanOn b x'.P.A.hom φ ⊤ := by
  rintro R R' _ _ x x' f φ w l N b b' ⟨he, hg, F, -, hw, -⟩ hb hB
  have bij := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R')).inv
  have hb' : ∀ k, KeyVia.Via w l (b' k).f (b k).f := hb
  constructor
  · intro c hc
    choose a ha using fun k => bij.2 (c k)
    obtain rfl : (fun k => (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom (a k)) = c := funext ha
    let z : RR x' l := ⟨fun _ => 0, fun _ _ => (map_zero _).trans ((congrArg _ (map_zero _)).trans (mul_zero _)).symm⟩
    have h₁ : Coords x' b' a z.f := fun i => fn_ext fun y hy => by
      obtain ⟨j, hj⟩ := exists_chart x.P.isLB (φ y)
      have e := (comb_eq x'.P.A.hom hb' a y hj hy).symm.trans (hc y j trivial hj)
      rw [Units.mul_right_eq_zero] at e
      refine Eq.trans ?_ e.symm
      exact (GlobalTheory.RelBasis.gs_eq_gsHom _ y _ hy _).trans (map_zero _)
    have h₂ : Coords x' b' 0 z.f := fun i =>
      (Finset.sum_eq_zero fun k _ => by rw [Pi.zero_apply, map_zero, zero_mul]).symm
    obtain rfl : a = 0 := (hB z).unique h₁ h₂
    exact funext fun k => map_zero _
  · intro σ hσ
    obtain ⟨s, hs⟩ := exists_down x.P.isLB x'.P.isLB hw (x'.P.A.hom ⁻¹ᵁ ⊤) (fun _ => trivial) σ
      (fun y j j' hj hj' => hσ y j j' trivial hj hj')
    obtain ⟨a, ha, -⟩ := hB s
    refine ⟨fun k => (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom (a k), fun y j _ hj => ?_⟩
    obtain ⟨i, hi⟩ := exists_chart x'.P.isLB y
    exact (hs y j i hj hi).trans ((congrArg _ (GlobalTheory.KeyBasis.gs_congr _ y (ha i))).trans
      (comb_eq x'.P.A.hom hb' a y hj hi).symm)

end GlobalTheory.RelBasisFibre

end
