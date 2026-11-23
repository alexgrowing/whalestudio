import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AgreeOfCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfDataRigid
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

noncomputable section

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem gen_eq_of_eq_along_section {Y S : Scheme.{0}} {N : LB Y} (hN : ∀ y : Y, ∃ i, y ∈ N.U i)
    (p : Y ⟶ S) (e : S ⟶ Y) (he : e ≫ p = 𝟙 _) (hp : Function.Surjective p.appTop.hom)
    {t₁ t₂ : LB.Gen N} (h₁ : t₁.IsGen) (h₂ : t₂.IsGen)
    (h : ∀ (s : S) (i : N.ι), e s ∈ N.U i → gm e s (N.U i) (t₁.s i) = gm e s (N.U i) (t₂.s i)) : t₁ = t₂ := by
  have tr : ∀ {t : LB.Gen N}, t.IsGen → ∀ (i j : N.ι) (x : Y), x ∈ N.U i ⊓ N.U j →
      gm (𝟙 Y) x (N.U i) (t.s i) = gm (𝟙 Y) x (N.U i ⊓ N.U j) (N.g i j) * gm (𝟙 Y) x (N.U j) (t.s j) := by
    intro t ht i j x hx
    have := congrArg (gm (𝟙 Y) x (N.U i ⊓ N.U j)) (ht i j)
    rwa [map_mul, gm_res _ x _ hx, gm_res _ x _ hx] at this
  obtain ⟨u, hu⟩ := glue_unit ⊤ N.U (fun _ => le_top) (fun y _ => Opens.mem_iSup.2 (hN y))
    (fun i => t₁.s i * (t₂.s i)⁻¹) (fun i j x hx => by
      rw [map_mul, map_mul, map_inv, map_inv, tr h₁ i j x hx, tr h₂ i j x hx, mul_inv, _root_.mul_mul_mul_comm,
        mul_inv_cancel, _root_.one_mul])
  obtain ⟨a, ha⟩ := hp u.val
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : N.ι), r z ∈ N.U i →
      (gm r z (N.U i) (t₁.s i) * (gm r z (N.U i) (t₂.s i))⁻¹).val = gs (r ≫ p) z ⊤ a := by
    intro Z r z i hi
    rw [← map_inv, ← map_mul, ← hu i, gm_res r z _ hi]
    exact (gs_unit r z ⊤ trivial _).symm.trans
      ((congrArg (gs r z ⊤) ha.symm).trans (gs_pull r p z ⊤ trivial a))
  have a1 : a = 1 := fn_ext fun y _ => by
    obtain ⟨i, hi⟩ := hN (e y)
    have := key _ e y i hi
    rw [h y i hi, mul_inv_cancel, he] at this
    rw [← this, gs_eq _ y ⊤ trivial, map_one, map_one, Units.val_one]
  cases t₁ with
  | mk s₁ =>
  cases t₂ with
  | mk s₂ =>
  congr 1
  funext i
  refine unit_ext fun x hx => ?_
  have := key _ (𝟙 Y) x i hx
  rw [a1, gs_eq _ x ⊤ trivial, map_one, map_one] at this
  exact mul_inv_eq_one.1 (Units.ext this)

theorem iso_eq_of_maps_along_section {Y S : Scheme.{0}} {L M : LB Y} (hL : ∀ y : Y, ∃ i, y ∈ L.U i)
    (hM : ∀ y : Y, ∃ i, y ∈ M.U i) (p : Y ⟶ S) (e : S ⟶ Y) (he : e ≫ p = 𝟙 _)
    (hp : Function.Surjective p.appTop.hom) {w₁ w₂ : LB.Iso L M} (h₁ : w₁.IsGen) (h₂ : w₂.IsGen)
    {a : LB.Gen (L.pull e)} {b : LB.Gen (M.pull e)}
    (m₁ : LB.Gen.Maps (LB.linCombIso w₁ (K := PUnit) (fun _ => e) (fun _ => 1)) a b)
    (m₂ : LB.Gen.Maps (LB.linCombIso w₂ (K := PUnit) (fun _ => e) (fun _ => 1)) a b) : w₁ = w₂ := by
  refine gen_eq_of_eq_along_section (fun y => ?_) p e he hp h₁ h₂ ?_
  · obtain ⟨i, hi⟩ := hL y
    obtain ⟨j, hj⟩ := hM y
    exact ⟨(j, i), hj, hi⟩
  · rintro s ⟨j, i⟩ ⟨hj, hi⟩
    have k₁ := gm_maps_pt m₁ (𝟙 S) s j i hj hi
    have k₂ := gm_maps_pt m₂ (𝟙 S) s j i hj hi
    rw [Category.id_comp] at k₁ k₂
    exact mul_right_cancel (k₁.symm.trans k₂)

theorem rigidified_iso_unique (hG : Out.GlobalFnsSt) {S : Scheme.{0}} (P : Out.PolAV S) {B₀ : Scheme.{0}}
    {M₀ : LB B₀} (hM₀ : M₀.IsLB) (φ : P.A.left ⟶ B₀) (w₁ w₂ : LB.Iso P.L (M₀.pull φ))
    (h₁ : w₁.IsGen) (h₂ : w₂.IsGen) (rig : LB.Gen (P.L.pull (eSec P.A)))
    (r₀ : LB.Gen ((M₀.pull φ).pull (eSec P.A)))
    (m₁ : LB.Gen.Maps (LB.linCombIso w₁ (K := PUnit) (fun _ => eSec P.A) (fun _ => 1)) rig r₀)
    (m₂ : LB.Gen.Maps (LB.linCombIso w₂ (K := PUnit) (fun _ => eSec P.A) (fun _ => 1)) rig r₀) :
    w₁ = w₂ :=
  iso_eq_of_maps_along_section (S := S) (exists_chart P.isLB)
    (fun y => (exists_chart hM₀ (φ y)).elim fun j hj => ⟨fun _ => j, mem_pull.2 hj⟩)
    P.A.hom (eSec P.A) (Over.w η[P.A]) (hG _ _ P.isAb).2 h₁ h₂ m₁ m₂

end GlobalTheory
