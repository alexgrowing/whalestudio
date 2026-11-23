import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

noncomputable section
namespace GlobalTheory.Ex.Arch.FibEx
open GlobalTheory.CubeValues GlobalTheory.SymmetricSemicharacter GlobalTheory.EigenNorm GlobalTheory.FrameValue

theorem val_iso {X : Scheme.{0}} (x : Sp ℂ ⟶ X) {L M : LB X} (hM : M.IsLB) {w : LB.Iso L M} (hw : w.IsGen)
    (m : M.ι) (i j : L.ι) (hm : ⊤ ≤ x ⁻¹ᵁ M.U m) (hi : ⊤ ≤ x ⁻¹ᵁ L.U i) (hj : ⊤ ≤ x ⁻¹ᵁ L.U j) :
    valAt' x _ (w.s (m, i)).val * valAt' x (L.U i ⊓ L.U j) (L.g i j).val = valAt' x _ (w.s (m, j)).val := by
  have h : ⊤ ≤ x ⁻¹ᵁ (M.U m ⊓ L.U i ⊓ (M.U m ⊓ L.U j)) :=
    (le_preimage_inf x _ _).2 ⟨(le_preimage_inf x _ _).2 ⟨hm, hi⟩, (le_preimage_inf x _ _).2 ⟨hm, hj⟩⟩
  have l₁ : M.U m ⊓ L.U i ⊓ (M.U m ⊓ L.U j) ≤ M.U m ⊓ M.U m :=
    le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
  have l₂ : M.U m ⊓ L.U i ⊓ (M.U m ⊓ L.U j) ≤ L.U i ⊓ L.U j :=
    le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  suffices H : ∀ (a : Γ(X, M.U m ⊓ L.U i)ˣ) (b : Γ(X, M.U m ⊓ L.U j)ˣ), res inf_le_left a =
      res l₁ (M.g m m) * (res l₂ (L.g i j))⁻¹ * res inf_le_right b →
      valAt' x _ a.val * valAt' x (L.U i ⊓ L.U j) (L.g i j).val = valAt' x _ b.val from
    H (w.s (m, i)) (w.s (m, j)) (hw (m, i) (m, j))
  intro a b e
  have e' : res inf_le_left a * res l₂ (L.g i j) = res l₁ (M.g m m) * res inf_le_right b := by
    rw [e, mul_right_comm, inv_mul_cancel_right]
  have o : valAt' x (M.U m ⊓ M.U m) (M.g m m).val = 1 := by
    obtain ⟨ev, hev⟩ := (valueRules X x).2.1 _ hm
    rw [← val_res x valueRules (le_inf le_rfl le_rfl) hm, hM.g_self, hev, Units.val_one, map_one]
  have v := congrArg (fun q : Γ(X, _)ˣ => valAt' x _ q.val) e'
  obtain ⟨ev, hev⟩ := (valueRules X x).2.1 _ h
  simp only [hev, Units.val_mul, map_mul] at v
  simp only [← hev] at v
  rw [val_res x valueRules _ h, val_res x valueRules _ h, val_res x valueRules _ h, val_res x valueRules _ h, o,
    _root_.one_mul] at v
  exact v

theorem fibEx : Laws → ThetaUnifAV → FibExSt := by
  intro hL hT R _ _ _ P J hJ
  obtain ⟨P', φ, hφ, -, hmul, t, ht⟩ := hL.polBaseChange _ _ (TF (R := R) ℂ).hom P
  have gp : IsGrpPullback P'.A P.A (TF (R := R) ℂ).hom φ := ⟨hφ, fun T x y x₀ y₀ hx hy => by
    have ex : x₀ = toBase hφ.w x := Over.OverMorphism.ext hx
    have ey : y₀ = toBase hφ.w y := Over.OverMorphism.ext hy
    rw [ex, ey, ← hmul]; rfl⟩
  obtain ⟨w, hw⟩ := LBIso.symm ⟨t, ht⟩
  obtain ⟨rig, hrig⟩ := P'.rigid
  obtain ⟨u, Hm, χ, Ef, hAH, -, h₁, h₂, h₃, -, hE, hB, -⟩ := hT P' rig hrig
  let ex : (Fin P'.g → ℂ) → (TF (R := R) ℂ ⟶ P.A) := fun z => Over.homMk ((u.ex z).left ≫ φ) (by
    show ((u.ex z).left ≫ φ) ≫ P.A.hom = _
    rw [Category.assoc, hφ.w, ← Category.assoc, Over.w]
    exact Category.id_comp _)
  have hm : ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (P.L.pull φ).U (fun _ => J (ex z).left) := fun z =>
    (le_preimage_wchart _ P.L _ _).2 fun _ => hJ _
  have hc := fun z => le_chartAt P'.isLB (u.ex z).left
  refine ⟨P'.g, u.Λ, Hm, χ, Ef, ex, fun z => Units.mk0
    (valAt' (u.ex z).left _ (w.s (fun _ => J (ex z).left, chartAt P'.isLB (u.ex z).left)).val *
      u.fr (chartAt P'.isLB (u.ex z).left) z)
    (mul_ne_zero (val_unit_ne_zero _ valueRules ((le_preimage_inf _ _ _).2 ⟨hm z, hc z⟩) _) (u.fr_ne _ _ (hc z))),
    ⟨hJ, P', φ, w, u, rfl, gp, hw, hAH, h₁, h₂, h₃, fun _ => rfl, fun z i hi => ?_⟩, hE, hB⟩
  rw [Units.val_mk0, u.fr_compat _ i z ((le_preimage_inf _ _ _).2 ⟨hc z, hi⟩), ← _root_.mul_assoc]
  exact congrArg (· * u.fr i z) (val_iso _ (pull_isLB P.isLB φ) hw _ _ _ (hm z) (hc z) hi)

end GlobalTheory.Ex.Arch.FibEx
end
