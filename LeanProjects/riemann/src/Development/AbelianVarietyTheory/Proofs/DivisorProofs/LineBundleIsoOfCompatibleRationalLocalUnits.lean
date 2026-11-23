import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.GlueRat

variable {S : Scheme.{0}} [IsIntegral S]

theorem genericPoint_mem' {U : S.Opens} {x : S} (hx : x ∈ U) : genericPoint S ∈ U :=
  ((genericPoint_spec S).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, hx⟩

theorem unit_eq_of_germ {V : S.Opens} {a b : Γ(S, V)ˣ}
    (h : ∀ hg : genericPoint S ∈ V, S.presheaf.germ V (genericPoint S) hg (a : Γ(S, V)) =
      S.presheaf.germ V (genericPoint S) hg (b : Γ(S, V))) : a = b := by
  by_cases hg : genericPoint S ∈ V
  · exact Units.ext (germ_injective_of_isIntegral S (genericPoint S) hg (h hg))
  · exact unit_ext fun x hx => (hg (genericPoint_mem' hx)).elim

theorem germ_res_unit {U V : S.Opens} (hle : V ≤ U) (hg : genericPoint S ∈ V) (a : Γ(S, U)ˣ) :
    S.presheaf.germ V (genericPoint S) hg ((res hle a : Γ(S, V)ˣ) : Γ(S, V)) =
      S.presheaf.germ U (genericPoint S) (hle hg) (a : Γ(S, U)) :=
  S.presheaf.germ_res_apply (homOfLE hle) _ hg _

theorem exists_unit_of_local {W : S.Opens} (f : S.presheaf.stalk (genericPoint S))
    (H : ∀ x ∈ W, ∃ (V : S.Opens) (_ : V ≤ W) (_ : x ∈ V) (u : Γ(S, V)ˣ),
      ∀ h : genericPoint S ∈ V, S.presheaf.germ V (genericPoint S) h (u : Γ(S, V)) = f) :
    ∃ s : Γ(S, W)ˣ, ∀ h : genericPoint S ∈ W, S.presheaf.germ W (genericPoint S) h (s : Γ(S, W)) = f := by
  choose V hVW hxV u hu using fun x : W => H x.1 x.2
  obtain ⟨s, hs⟩ := glue_unit W V hVW (fun x hx => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxV _⟩) u
    (fun i j z hz => by
      rw [← gm_res (𝟙 S) z (inf_le_left : V i ⊓ V j ≤ V i) hz,
        ← gm_res (𝟙 S) z (inf_le_right : V i ⊓ V j ≤ V j) hz]
      congr 1
      refine unit_eq_of_germ fun hg => ?_
      rw [germ_res_unit, germ_res_unit, hu i (hg.1), hu j hg.2])
  refine ⟨s, fun h => ?_⟩
  rw [← germ_res_unit (hVW ⟨_, h⟩) (hxV ⟨_, h⟩), hs]
  exact hu _ _

end GlobalTheory.GlueRat

open GlobalTheory.GlueRat in

theorem GlobalTheory.GlueRat.lbIso_of_rat : ∀ (S : Scheme.{0}) [IsIntegral S] (A B : LB S) (f : B.ι × A.ι → S.presheaf.stalk (genericPoint S)),
    (∀ p, ∀ x ∈ B.U p.1 ⊓ A.U p.2, ∃ (V : S.Opens) (_ : V ≤ B.U p.1 ⊓ A.U p.2) (_ : x ∈ V) (u : Γ(S, V)ˣ),
      ∀ h : genericPoint S ∈ V, S.presheaf.germ V (genericPoint S) h (u : Γ(S, V)) = f p) →
    (∀ p q (h1 : genericPoint S ∈ B.U p.1 ⊓ B.U q.1) (h2 : genericPoint S ∈ A.U p.2 ⊓ A.U q.2),
      f p * S.presheaf.germ _ (genericPoint S) h2 (A.g p.2 q.2 : Γ(S, A.U p.2 ⊓ A.U q.2)) =
        S.presheaf.germ _ (genericPoint S) h1 (B.g p.1 q.1 : Γ(S, B.U p.1 ⊓ B.U q.1)) * f q) →
    LBIso A B := by
  intro S _ A B f H1 H2
  choose s hs using fun p => exists_unit_of_local (f p) (H1 p)
  refine ⟨⟨s⟩, fun p q => unit_eq_of_germ fun hg => ?_⟩
  have hp : genericPoint S ∈ B.U p.1 ⊓ A.U p.2 := hg.1
  have hq : genericPoint S ∈ B.U q.1 ⊓ A.U q.2 := hg.2
  have h1 : genericPoint S ∈ B.U p.1 ⊓ B.U q.1 := ⟨hg.1.1, hg.2.1⟩
  have h2 : genericPoint S ∈ A.U p.2 ⊓ A.U q.2 := ⟨hg.1.2, hg.2.2⟩
  refine ((germ_res_unit _ hg _).trans (hs p hp)).trans ?_
  set O := (LB.div B A).U p ⊓ (LB.div B A).U q
  have lB : O ≤ B.U p.1 ⊓ B.U q.1 := le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
  have lA : O ≤ A.U p.2 ⊓ A.U q.2 := le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  have lq : O ≤ B.U q.1 ⊓ A.U q.2 := inf_le_right
  change f p = S.presheaf.germ O (genericPoint S) hg
    (((res lB (B.g p.1 q.1) * (res lA (A.g p.2 q.2))⁻¹ * res lq (s q) : Γ(S, O)ˣ)) : Γ(S, O))
  have e : S.presheaf.germ O (genericPoint S) hg (((res lA (A.g p.2 q.2))⁻¹ : Γ(S, O)ˣ) : Γ(S, O)) *
      S.presheaf.germ _ (genericPoint S) h2 (A.g p.2 q.2 : Γ(S, A.U p.2 ⊓ A.U q.2)) = 1 := by
    rw [← germ_res_unit lA hg, ← map_mul, Units.inv_mul, map_one]
  have H := H2 p q h1 h2
  simp only [Units.val_mul, map_mul, germ_res_unit, hs q hq]
  calc f p = f p * (S.presheaf.germ O (genericPoint S) hg (((res lA (A.g p.2 q.2))⁻¹ : Γ(S, O)ˣ) : Γ(S, O)) *
      S.presheaf.germ _ (genericPoint S) h2 (A.g p.2 q.2 : Γ(S, A.U p.2 ⊓ A.U q.2))) := by rw [e, _root_.mul_one]
    _ = _ := by rw [mul_comm (S.presheaf.germ O _ hg _), ← _root_.mul_assoc, H]; ring
