import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsNormPull
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

noncomputable section

namespace GlobalTheory.TestFibre.CombValue

open GlobalTheory.UT.CoefBasic

variable {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ} {x : TFK (R := R) F ⟶ A.A} {e : FrameAt A x}

theorem valIs_comb {J : Type} [Fintype J] {s : J → SecA A F k} {b c : J → F} {t : SecA A F k} (h : IsComb A s b t)
    (hs : ∀ i, ValIs A (s i) x e (c i)) : ValIs A t x e (∑ i, b i * c i) := fun z I hI => by
  have e₀ : SecM.ofSec A.A t = ∑ l, cF R (b l) • SecM.ofSec A.A (s l) := by
    refine Subtype.ext (funext fun j => (h j).trans ?_)
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  let φ : SecM A.A A.L k (TFK (R := R) F) →+ (TFK (R := R) F).left.presheaf.stalk z :=
    AddMonoidHom.mk' (fun v => ThetaAct.sv v (ptSecT A.A x).left z I) fun a b => ThetaAct.sv_add a b _ z hI
  let ψ : F →+* (TFK (R := R) F).left.presheaf.stalk z := cstH (R := R) z
  have e₁ : ∀ a : F, @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z a) = ψ a := fun a => cst_eq z a
  refine (congrArg φ e₀).trans ((map_sum φ _ _).trans ?_)
  rw [e₁, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => (ThetaAct.sv_smul _ _ _ z hI).trans ?_
  rw [ThetaPtMove.ptSecT_fst, map_mul, _root_.mul_assoc, ← e₁, ← e₁]
  exact congrArg (@id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z (b i)) * ·) (hs i z I hI)

theorem valIs_smul {t t' : SecA A F k} {a c : F} (h : ∀ j, t'.f j = liftFun A.A _ (cF R a) * t.f j)
    (ht : ValIs A t x e c) : ValIs A t' x e (a * c) := by
  have := valIs_comb (J := Unit) (s := fun _ => t) (b := fun _ => a) (c := fun _ => c) (t := t')
    (fun j => (h j).trans (by rw [Fintype.sum_unique])) fun _ => ht
  rwa [Fintype.sum_unique] at this

theorem valIs_unique {t : SecA A F k} {c c' : F} (h : ValIs A t x e c) (h' : ValIs A t x e c') : c = c' := by
  obtain ⟨z⟩ := exists_pt (R := R) (F := F)
  obtain ⟨J, hJ⟩ := exists_good' (Z := (TFK (R := R) F).left) A.isLB z
  have := (Units.mul_left_inj _).1 ((h z J hJ).symm.trans (h' z J hJ))
  simp only [id, cst_eq] at this
  exact cstH_inj z this

theorem exists_valIs (hL : Laws) (he : e.IsGen) (t : SecA A F k) : ∃ c, ValIs A t x e c := by
  obtain ⟨w, hw, -⟩ := hL.evVal _ A k x e he t
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 w
  refine ⟨c, fun z J hJ => ?_⟩
  have := ThetaPtMove.sv_of_isValueAt hw (𝟙 _) z hJ
  rw [Category.id_comp] at this
  exact this

theorem valIs_linear : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (x : TFK (R := R) F ⟶ A.A) (e : FrameAt A x), (∀ (J : Type) [Fintype J] (s : J → SecA A F k) (b c : J → F) (t : SecA A F k), IsComb A s b t → (∀ i, ValIs A (s i) x e (c i)) → ValIs A t x e (∑ i, b i * c i)) ∧ (∀ (t t' : SecA A F k) (a c : F), (∀ j, t'.f j = liftFun A.A _ (cF R a) * t.f j) → ValIs A t x e c → ValIs A t' x e (a * c)) ∧ (∀ (t : SecA A F k) c c', ValIs A t x e c → ValIs A t x e c' → c = c') ∧ (e.IsGen → ∀ t : SecA A F k, ∃ c, ValIs A t x e c) :=
  fun hL _ _ _ _ _ _ _ _ _ _ =>
    ⟨fun _ _ _ _ _ _ h hs => valIs_comb h hs, fun _ _ _ _ h ht => valIs_smul h ht,
      fun _ _ _ h h' => valIs_unique h h', fun he t => exists_valIs hL he t⟩

end GlobalTheory.TestFibre.CombValue
end
