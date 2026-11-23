import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpansAt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionLinCombFiberProductSeparated
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BoxFibre

variable {X : Scheme.{0}} {G : Over X} (L : LB G.left) {S : Type} [CommRing S] (x0 : Sp S ⟶ X) (k : ℕ)

def BoxAt {n : ℕ} (s : SecPw x0 L n k) {I : Type} [Fintype I] (c : I → S) (σ : I → Fin n → H0 L k) : Prop :=
  ∀ (T : Scheme.{0}) (r : T ⟶ (Pw G x0 n).left) (z : T) (J : (T ⟶ G.left) → L.ι), Good L z J →
    sval s r z J = ∑ i, gs (r ≫ (fst (Over.mk x0) (powObj G n)).left) z ⊤ (toΓ S (c i)) *
      ∏ b, sval (σ i b) (r ≫ pr G x0 b) z J

end GlobalTheory.BoxFibre

namespace GlobalTheory.BoxFibre
variable {X : Scheme.{0}} {G : Over X} (L : LB G.left) {S : Type} [CommRing S] (x0 : Sp S ⟶ X) (k : ℕ)

theorem base (s : SecPw x0 L 0 k) : ∃ (c : Fin 1 → S) (σ : Fin 1 → Fin 0 → H0 L k), BoxAt L x0 k s c σ := by
  have hf : IsIso (fst (Over.mk x0) (powObj G 0)) := by
    show IsIso (fst (Over.mk x0) (𝟙_ (Over X)))
    rw [← CartesianMonoidalCategory.rightUnitor_hom]; infer_instance
  have hf' : IsIso (fst (Over.mk x0) (powObj G 0)).left :=
    inferInstanceAs (IsIso ((Over.forget X).map (fst (Over.mk x0) (powObj G 0))))
  set f := (fst (Over.mk x0) (powObj G 0)).left with hfdef
  let j0 : Fin 0 → L.ι := Fin.elim0
  have hle : f ⁻¹ᵁ ⊤ ≤ LB.wchart L (pr G x0 (n := 0)) j0 := fun y _ => Set.mem_iInter.2 fun b => b.elim0
  obtain ⟨t, ht⟩ := (ConcreteCategory.bijective_of_isIso (f.app ⊤)).2
    (((Pw G x0 0).left.presheaf.map (homOfLE hle).op).hom (s.f j0))
  obtain ⟨c, hc⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S)).inv).2 t
  refine ⟨fun _ => c, fun _ => Fin.elim0, fun T r z J hJ => ?_⟩
  refine (sval_of s r z J j0 (fun b => b.elim0)).trans ((gs_res r z hle trivial (s.f j0)).symm.trans ?_)
  rw [← ht, gs_pull r f z ⊤ trivial]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, _root_.mul_one, Finset.univ_unique, Finset.sum_singleton]
  rw [← hc]
  rfl

end GlobalTheory.BoxFibre

namespace GlobalTheory.BoxFibre
variable {X : Scheme.{0}} (G : Over X) {S : Type} [CommRing S] (x0 : Sp S ⟶ X)

abbrev Y1 : Over (Sp S) := Over.mk (fst (Over.mk x0) G).left

abbrev Y2 (n : ℕ) : Over (Sp S) := Over.mk (fst (Over.mk x0) (powObj G n)).left

end GlobalTheory.BoxFibre

namespace GlobalTheory.BoxFibre
variable {X : Scheme.{0}} {G : Over X} (L : LB G.left) {S : Type} [Field S] (x0 : Sp S ⟶ X) (k : ℕ)

end GlobalTheory.BoxFibre

namespace GlobalTheory.BoxFibre

end GlobalTheory.BoxFibre
