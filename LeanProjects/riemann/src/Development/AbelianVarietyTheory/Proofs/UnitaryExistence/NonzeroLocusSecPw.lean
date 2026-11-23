import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsUnitIffMem

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.ProjAffineLoci

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (gs gs_res gs_mul fn_ext)
open TopologicalSpace

variable {X : Scheme.{0}} {R : Type} [CommRing R]

def zeroSec (H : LB X) : LB.Sec H := ⟨fun _ => 0, fun _ _ => by rw [map_zero, map_zero, mul_zero]⟩

def secPw {L : LB X} (σ : LB.Sec L) (d : ℕ) : LB.Sec (pw L d) where
  f := fun k => σ.f k ^ d
  compat := fun i j => by
    have h := congrArg (· ^ d) (σ.compat i j)
    simp only [mul_pow, ← map_pow] at h
    refine h.trans (congrArg (· * _) ?_)
    change _ = ((L.g i j ^ (d : ℤ) : Γ(X, L.U i ⊓ L.U j)ˣ) : Γ(X, L.U i ⊓ L.U j))
    rw [zpow_natCast, Units.val_pow_eq_pow_val]

theorem chart (f : X ⟶ Spec (CommRingCat.of R)) {H : LB X} (hH : H.IsLB) {I : Type} (t : I → LB.Sec H) (i : I)
    {W : X.Opens} (e : nonzeroLocus (t i) = W) {n : ℕ} (b : Fin n → Γ(X, W))
    (hb : Function.Surjective (MvPolynomial.eval₂Hom (cst f W) b)) (c : Fin n → I)
    (hc : ∀ l k, rs X (inf_le_right : W ⊓ H.U k ≤ H.U k) ((t (c l)).f k) =
      rs X (inf_le_left : W ⊓ H.U k ≤ W) (b l) * rs X (inf_le_right : W ⊓ H.U k ≤ H.U k) ((t i).f k)) :
    ∃ r : I → Γ(X, nonzeroLocus (t i)),
      (∀ j k, rs X (inf_le_right : nonzeroLocus (t i) ⊓ H.U k ≤ H.U k) ((t j).f k) =
        rs X (inf_le_left : nonzeroLocus (t i) ⊓ H.U k ≤ nonzeroLocus (t i)) (r j) *
          rs X (inf_le_right : nonzeroLocus (t i) ⊓ H.U k ≤ H.U k) ((t i).f k)) ∧
      Function.Surjective (MvPolynomial.eval₂Hom (cst f (nonzeroLocus (t i))) r) := by
  subst e
  choose ρ hρ using fun j => GlobalTheory.VeryAmplePow.exists_ratio (t i) (t j)
  refine ⟨ρ, fun j k => fn_ext fun y hy => ?_, fun y => ?_⟩
  · exact (gs_res _ y _ hy _).trans ((hρ j _ (𝟙 X) y k hy.1 hy.2).trans ((gs_mul _ y _ hy _ _).trans
      (congrArg₂ (· * ·) (gs_res _ y _ hy _) (gs_res _ y _ hy _))).symm)
  · have hρb : ∀ l, ρ (c l) = b l := fun l => fn_ext fun z hz => by
      obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (show z ∈ ⨆ k, H.U k by rw [hH.cover]; trivial)
      have hm : (𝟙 X : X ⟶ X) z ∈ nonzeroLocus (t i) ⊓ H.U k := ⟨hz, hk⟩
      have h₁ := (gs_res _ z _ hm _).symm.trans ((congrArg (gs (𝟙 X) z _) (hc l k)).trans
        ((gs_mul _ z _ hm _ _).trans (congrArg₂ (· * ·) (gs_res _ z _ hm _) (gs_res _ z _ hm _))))
      have u := (GlobalTheory.VeryAmplePow.isUnit_iff_mem (t i) (𝟙 X) z hk).2 hz
      exact u.mul_left_inj.1 ((hρ (c l) _ (𝟙 X) z k hz hk).symm.trans h₁)
    obtain ⟨p, rfl⟩ := hb y
    refine ⟨MvPolynomial.rename c p, ?_⟩
    rw [MvPolynomial.eval₂Hom_rename]
    congr 2
    exact funext hρb

end GlobalTheory.ProjAffineLoci
