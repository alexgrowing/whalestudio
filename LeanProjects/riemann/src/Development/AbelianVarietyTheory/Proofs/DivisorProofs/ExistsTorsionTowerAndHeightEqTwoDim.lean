import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.FrobFieldExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullbackBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfBijectiveAffinePts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIntCastSmulIsogenyDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFlatFinrank
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
open CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi (mulN)

namespace GlobalTheory.AVTower

theorem finrank_torsion {k : Type} [Field k] (A : AbVar k) {N : ℕ} (hN : N ≠ 0)
    {S : Type} [CommRing S] [Algebra k S] [Module.Finite k S] (y : SpAlg k S ⟶ A.X)
    (h : IsPullback y.left (spMap (algebraMap k S)) (mulN A.X N).left η[A.X].left) :
    Module.finrank k S = N ^ (2 * A.dim) := by
  obtain ⟨hi, hd⟩ := GlobalTheory.MulIsogeny.mul_isogeny k A (N : ℤ) (by exact_mod_cast hN)
  obtain ⟨-, hfl, -, hrk⟩ := GlobalTheory.AV.AbVar.isogeny_flat_finrank k A A _ hi
  have hf : IsFinite ((N : ℤ) • 𝟙 A).hom.left := hi.1
  have e : ((N : ℤ) • 𝟙 A).hom = mulN A.X N := by
    rw [zsmul_hom, id_hom, GrpTangent.mulN_eq_pow, zpow_natCast]
  rw [e] at hf hfl hrk
  have h2 := Scheme.Hom.finrank_of_isPullback _ _ _ _ h (⊥ : PrimeSpectrum k)
  rw [hrk, hd, Int.natAbs_natCast] at h2
  rw [← h2, spMap, Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
  rfl

theorem exists_tower (p : ℕ) [hp : Fact p.Prime] (k : Type) [Field k] (A : AbVar k) :
    ∃ G : PDivGroup p k, G.height = 2 * A.dim ∧ Nonempty (G.TorsionTower A.X) := by
  have := A.ab.comm
  have hN : ∀ n : ℕ, 1 ≤ p ^ n := fun n => Nat.one_le_pow _ _ hp.out.pos
  choose R _ _ y h1 h2 H using fun n : ℕ => AbelianPDiv.exists_isPullback (A := A.X) A.ab (hN n)
  have h := fun n => AbelianPDiv.isUnivTorsion_of_isPullback (y n) (H n)
  have hr : ∀ n (q : PrimeSpectrum k), Module.rankAtStalk (R n) q = (p ^ n) ^ (2 * A.dim) := fun n q => by
    rw [Module.rankAtStalk_eq_finrank_of_free]
    exact finrank_torsion A (pow_ne_zero _ hp.out.ne_zero) (y n) (H n)
  choose r r1 r2 r3 using fun n : ℕ =>
    (h n).exists_res (h (n + 1)) (by rw [pow_succ, pow_mul, (h n).1, one_pow])
  let G : PDivGroup p k :=
    { height := 2 * A.dim
      A := R
      hopf := fun n => (h n).hopfAlgebra
      cocomm := fun n => (h n).isCocomm
      finite := h1
      projective := h2
      rank_eq := fun n q => (hr n q).trans (pow_mul _ _ _).symm
      res := r
      res_surjective := r1
      ker_res := r2 }
  exact ⟨G, rfl, ⟨{
    y := y
    mul := fun n B _ _ => (h n).mul_y
    inj := fun n B _ _ _ _ => (h n).inj
    surj := fun n B _ _ z hz => ((h n).2 B z hz).exists
    res := r3 }⟩⟩

theorem height_eq {p : ℕ} [hp : Fact p.Prime] {k : Type} [Field k] (A : AbVar k) (G : PDivGroup p k)
    (t : G.TorsionTower A.X) : G.height = 2 * A.dim := by
  have P := (TorsionTower.isPullback_y p k G A.X t 1).map (Over.forget _)
  have e : (toUnit (SpAlg k (G.A 1))).left = spMap (algebraMap k (G.A 1)) := by
    simpa using Over.w (toUnit (SpAlg k (G.A 1)))
  simp only [Over.forget_map] at P
  rw [e] at P
  have hf := finrank_torsion A (pow_ne_zero 1 hp.out.ne_zero) (t.y 1) P
  have hr := G.rank_eq 1 ⊥
  rw [Module.rankAtStalk_eq_finrank_of_free] at hr
  change Module.finrank k (G.A 1) = _ at hr
  rw [hf, pow_one, Nat.one_mul] at hr
  exact (Nat.pow_right_injective hp.out.two_le hr).symm

theorem exists_tower_and_height_eq : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (A : AbVar k),
    (∃ G : PDivGroup p k, Nonempty (G.TorsionTower A.X)) ∧
      ∀ (G : PDivGroup p k) (t : G.TorsionTower A.X), G.height = 2 * A.dim := by
  intro p _ k _ A
  obtain ⟨G, -, hG⟩ := exists_tower p k A
  exact ⟨⟨G, hG⟩, fun G t => height_eq A G t⟩

end GlobalTheory.AVTower
