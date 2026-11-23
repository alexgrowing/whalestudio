import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyDegreeEqCardKernelOfKilledByInvertibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIntCastSmulIsogenyDegreeStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem comp_pow_id_torscard {S : Scheme.{0}} {G T : Over S} [GrpObj G] (x : T ⟶ G) (n : ℕ) :
    x ≫ (𝟙 G) ^ n = x ^ n := by
  induction n with
  | zero => simp [MonObj.comp_one]
  | succ k ih => rw [pow_succ, MonObj.comp_mul, ih, Category.comp_id, pow_succ]

theorem card_torsion_pt (K : Type) [Field K] (A : AbVar K) (n : ℕ) (hn : (n : K) ≠ 0) :
    Nat.card {x : A.Pt // x ^ n = 1} = n ^ (2 * A.dim) := by
  have hn0 : (n : ℤ) ≠ 0 := by
    intro h; apply hn; simp at h; simp [h]
  obtain ⟨hiso, hdeg⟩ := GlobalTheory.T.abelianVariety_intCast_smul_isogeny_degree K A (n : ℤ) hn0
  have hf : ((n : ℤ) • 𝟙 A).hom = (𝟙 A.X) ^ n := by
    rw [natCast_zsmul, nsmul_hom, id_hom]
  have hker : ∀ {T : Over (Sp K)} (x : T ⟶ A.X), x ≫ ((n : ℤ) • 𝟙 A).hom = x ^ n := by
    intro T x; rw [hf, comp_pow_id_torscard]
  have hd := GlobalTheory.T.isogenyDegree_eq_card_kernel_of_killed_by_invertible K A A ((n : ℤ) • 𝟙 A) n hn hiso (fun T x hx => by rw [← hker]; exact hx)
  rw [hdeg, Int.natAbs_natCast] at hd
  rw [hd]
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun x => by rw [MonoidHom.mem_ker, ptMap_apply, hker])

end GlobalTheory.AV.AbVar
