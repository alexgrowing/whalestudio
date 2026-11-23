import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousCoordsInStandardChartRatioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDivPowFactorialIsUnitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.CrdSym

open GlobalTheory.Points GlobalTheory.ProjSpace

variable {k Ω : Type} [CommRing k] [Field Ω] [Algebra k Ω]

theorem div_mem_O {o : Type} [CommRing o] {M : RatModel k Ω} {n : ℕ} {h : M.Z ⟶ PSpace o n}
    {c : Fin (n + 1) → Ω} (hc : PCrd (M.pt ≫ h) c) {a : Fin (n + 1)} {z : M.Z}
    (hz : z ∈ h ⁻¹ᵁ ProjSpace.chart o n a) : c a ≠ 0 ∧ ∀ b, c b / c a ∈ M.O z := by
  have hW : ⊤ ≤ M.pt ⁻¹ᵁ (h ⁻¹ᵁ ProjSpace.chart o n a) := M.top_le_preimage_pt ⟨z, hz⟩
  obtain ⟨h0, hv⟩ := GlobalTheory.T.homogeneousCoords_in_standardChart_ratio o Ω n (M.pt ≫ h) c a hc (le_preimage_comp M.pt h le_rfl hW)
  refine ⟨h0, fun b => ?_⟩
  have e : valF M.pt (h ⁻¹ᵁ ProjSpace.chart o n a) (ProjSpace.pullRatio h _ a le_rfl b) = c b / c a :=
    (Points.valR_appLE M.pt h le_rfl hW _).trans (hv b)
  exact e ▸ M.valF_mem_O hz _

theorem valR_pullO1_g {L : Type} [Field L] {X : Scheme.{0}} {o : Type} [CommRing o] {r : ℕ} (y0 : Sp L ⟶ X)
    (π : X ⟶ PSpace o r) {t : Fin (r + 1) → L} (ht : PCrd (y0 ≫ π) t) (i j : PUnit → Fin (r + 1))
    (h : ⊤ ≤ y0 ⁻¹ᵁ (((ProjSpace.O1 o r).pull π).U i ⊓ ((ProjSpace.O1 o r).pull π).U j)) :
    valR y0 _ (((ProjSpace.O1 o r).pull π).g i j).val = t (j PUnit.unit) / t (i PUnit.unit) := by
  have h1 : ⊤ ≤ (y0 ≫ π) ⁻¹ᵁ (ProjSpace.chart o r (i PUnit.unit) ⊓ ProjSpace.chart o r (j PUnit.unit)) :=
    le_preimage_comp y0 π (inf_le_inf (LB.wchart_le (ProjSpace.O1 o r) (fun _ => π) i PUnit.unit)
      (LB.wchart_le (ProjSpace.O1 o r) (fun _ => π) j PUnit.unit)) h
  refine (TuplePoint.valR_linComb_g y0 (ProjSpace.O1 o r) π 1 i j h).trans ((zpow_one _).trans ?_)
  refine (valR_res (y0 ≫ π) inf_le_left h1 (ProjSpace.ratio o r (i PUnit.unit) (j PUnit.unit))).trans ?_
  exact (GlobalTheory.T.homogeneousCoords_in_standardChart_ratio o L r (y0 ≫ π) t _ ht (le_preimage_mono _ inf_le_left h1)).2 _

open Classical in

def unitOf (M : RatModel k Ω) (U : M.Z.Opens) (x : Ω) (hx : ∀ z ∈ U, x ≠ 0 ∧ x ∈ M.O z ∧ x⁻¹ ∈ M.O z) :
    Γ(M.Z, U)ˣ :=
  if hU : (U : Set M.Z).Nonempty then
    Units.map (M.sectionsEquiv U hU).symm.toMonoidHom
      ⟨⟨x, RatModel.mem_ringOn.2 fun z hz => (hx z hz).2.1⟩, ⟨x⁻¹, RatModel.mem_ringOn.2 fun z hz => (hx z hz).2.2⟩,
        Subtype.ext (mul_inv_cancel₀ (hx _ hU.some_mem).1), Subtype.ext (inv_mul_cancel₀ (hx _ hU.some_mem).1)⟩
  else 1

theorem valR_unitOf {M : RatModel k Ω} {U : M.Z.Opens} {x : Ω} {hx : ∀ z ∈ U, x ≠ 0 ∧ x ∈ M.O z ∧ x⁻¹ ∈ M.O z}
    (h : ⊤ ≤ M.pt ⁻¹ᵁ U) : valR M.pt U (unitOf M U x hx).val = x := by
  have hU : (U : Set M.Z).Nonempty := ⟨_, h (x := IsLocalRing.closedPoint Ω) trivial⟩
  rw [unitOf, dif_pos hU]
  have := M.coe_sectionsEquiv U hU ((M.sectionsEquiv U hU).symm ⟨x, RatModel.mem_ringOn.2 fun z hz => (hx z hz).2.1⟩)
  rw [RingEquiv.apply_symm_apply] at this
  exact this.symm

end GlobalTheory.UMin.CrdSym
end

namespace GlobalTheory.UMin.CrdSym
open GlobalTheory.Points GlobalTheory.ProjSpace

theorem lbIso_symTup : ∀ (k Ω o : Type) [CommRing k] [Field Ω] [Algebra k Ω] [CommRing o] (M : RatModel k Ω) (n : ℕ) (h : M.Z ⟶ PSpace k n) (g : M.Z ⟶ PSpace o n) (c : Fin (n + 1) → Ω), PCrd (M.pt ≫ h) c → PCrd (M.pt ≫ g) (symTup c) → LBIso ((ProjSpace.O1 o n).pull g) (lbPow ((ProjSpace.O1 k n).pull h) (n + 1).factorial) := by
  intro k Ω o _ _ _ _ M n h g c hc he
  set D := (n + 1).factorial
  set L := (ProjSpace.O1 o n).pull g
  set L' := lbPow ((ProjSpace.O1 k n).pull h) D
  have h2 : ∀ a : L'.ι, L'.U a ≤ ((ProjSpace.O1 k n).pull h).U (a PUnit.unit) := fun a =>
    LB.wchart_le ((ProjSpace.O1 k n).pull h) (fun _ => 𝟙 M.Z) a PUnit.unit
  have hL' : ∀ a : L'.ι, L'.U a ≤ h ⁻¹ᵁ ProjSpace.chart k n (a PUnit.unit PUnit.unit) := fun a =>
    (h2 a).trans (LB.wchart_le (ProjSpace.O1 k n) (fun _ => h) _ PUnit.unit)
  have hL : ∀ j : L.ι, L.U j ≤ g ⁻¹ᵁ ProjSpace.chart o n (j PUnit.unit) := fun j =>
    LB.wchart_le (ProjSpace.O1 o n) (fun _ => g) j PUnit.unit
  let x : L'.ι × L.ι → Ω := fun p => symTup c (p.2 PUnit.unit) / c (p.1 PUnit.unit PUnit.unit) ^ D
  have hx : ∀ p : L'.ι × L.ι, ∀ z ∈ (LB.div L' L).U p, x p ≠ 0 ∧ x p ∈ M.O z ∧ (x p)⁻¹ ∈ M.O z := by
    rintro ⟨a, j⟩ z ⟨hza, hzj⟩
    obtain ⟨h1, h3⟩ := div_mem_O hc (hL' a hza)
    obtain ⟨h4, h5⟩ := div_mem_O he (hL j hzj)
    exact GlobalTheory.T.thetaSymmetricFunctions_div_pow_factorial_isUnit k Ω (M.O z) (n + 1) c _ _ h1 h3 h4 h5
  have nzh : ∀ a : L'.ι, ⊤ ≤ M.pt ⁻¹ᵁ L'.U a → c (a PUnit.unit PUnit.unit) ≠ 0 := fun a ha =>
    (GlobalTheory.T.homogeneousCoords_in_standardChart_ratio k Ω n (M.pt ≫ h) c _ hc (le_preimage_comp M.pt h (hL' a) ha)).1
  have nzg : ∀ j : L.ι, ⊤ ≤ M.pt ⁻¹ᵁ L.U j → symTup c (j PUnit.unit) ≠ 0 := fun j hj =>
    (GlobalTheory.T.homogeneousCoords_in_standardChart_ratio o Ω n (M.pt ≫ g) (symTup c) _ he (le_preimage_comp M.pt g (hL j) hj)).1
  let w : LB.Iso L L' := ⟨fun p => unitOf M ((LB.div L' L).U p) (x p) (hx p)⟩
  refine ⟨w, ?_⟩
  rintro ⟨a, j⟩ ⟨a', j'⟩
  refine Units.ext (TuplePoint.ext_of_dense M.pt fun hW => ?_)
  have ha := le_preimage_mono M.pt inf_le_left hW
  have hb := le_preimage_mono M.pt inf_le_right hW
  have hk : ⊤ ≤ M.pt ⁻¹ᵁ (L'.U a ⊓ L'.U a') :=
    le_preimage_mono M.pt (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)) hW
  have hj : ⊤ ≤ M.pt ⁻¹ᵁ (L.U j ⊓ L.U j') :=
    le_preimage_mono M.pt (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)) hW
  have e1 := TuplePoint.valR_linComb_g M.pt ((ProjSpace.O1 k n).pull h) (𝟙 M.Z) D a a' hk
  rw [Category.comp_id, valR_pullO1_g M.pt h hc _ _ (le_preimage_mono M.pt (inf_le_inf (h2 a) (h2 a')) hk),
    zpow_natCast] at e1
  have e2 := valR_pullO1_g M.pt g he j j' hj
  have n1 := nzh a (le_preimage_mono M.pt inf_le_left ha)
  have n2 := nzh a' (le_preimage_mono M.pt inf_le_left hb)
  have n3 := nzg j (le_preimage_mono M.pt inf_le_right ha)
  have n4 := nzg j' (le_preimage_mono M.pt inf_le_right hb)
  refine (TuplePoint.valR_res_unit M.pt _ hW _).trans ((valR_unitOf (hx := hx (a, j)) ha).trans (Eq.symm ?_))
  refine (TuplePoint.valR_mul_unit M.pt hW _ _).trans ?_
  have eg : valR M.pt _ ((LB.div L' L).g (a, j) (a', j')).val =
      (c (a' PUnit.unit PUnit.unit) / c (a PUnit.unit PUnit.unit)) ^ D *
        (symTup c (j' PUnit.unit) / symTup c (j PUnit.unit))⁻¹ := by
    refine (TuplePoint.valR_mul_unit M.pt hW _ _).trans ?_
    exact congrArg₂ (· * ·) ((TuplePoint.valR_res_unit M.pt _ hW _).trans e1)
      ((TuplePoint.valR_inv_unit M.pt hW _).trans (congrArg (·⁻¹) ((TuplePoint.valR_res_unit M.pt _ hW _).trans e2)))
  rw [eg, TuplePoint.valR_res_unit M.pt _ hW, valR_unitOf (hx := hx (a', j')) hb]
  simp only [x]
  rw [div_pow]
  field_simp

end GlobalTheory.UMin.CrdSym
