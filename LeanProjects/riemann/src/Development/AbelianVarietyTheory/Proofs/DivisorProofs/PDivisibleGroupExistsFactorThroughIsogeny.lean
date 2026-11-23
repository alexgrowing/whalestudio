import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivHomDivisibleByPowOfKillsPowTorsionStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu WithConv

namespace GlobalTheory.Dieu

theorem hom_eq_zero_of_pow_smul_eq_zero {p : ℕ} [Fact p.Prime] {k : Type} [CommRing k]
    {G H : PDivGroup p k} (m : ℕ) {f : G ⟶ H} (e : (p : ℤ_[p]) ^ m • f = 0) : f = 0 := by
  induction m generalizing f with
  | zero => simpa using e
  | succ m ih =>
    refine ih ?_
    refine eq_zero_of_prime_smul_eq_zero ?_
    rw [← mul_smul, ← pow_succ']
    exact e

theorem exists_comp_eq_of_kerIdeal_le : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (G Q H : PDivGroup p k) (m : ℕ) (q : G ⟶ Q) (q' : Q ⟶ G) (f : G ⟶ H),
    q ≫ q' = (p : ℤ_[p]) ^ m • 𝟙 G → q' ≫ q = (p : ℤ_[p]) ^ m • 𝟙 Q →
    kerIdeal (f.app m) ≤ kerIdeal (q.app m) → ∃ g : Q ⟶ H, q ≫ g = f := by
  intro p _ k _ _ G Q H m q q' f h1 h2 hk

  have hq : kerIdeal (q.app m) ≤ RingHom.ker (q'.app m : G.A m →ₐ[k] Q.A m) := by
    refine (kerIdeal_le_ker_iff (q.app m) _).2 fun c => ?_
    have e := congrArg (fun x => Hom.conv x m) h2
    simp only [pow_smul_conv] at e
    have e2 := DFunLike.congr_fun (congrArg ofConv (congrArg toPts e)) c
    rw [map_one] at e2
    refine e2.trans ?_
    rfl
  have hf := (kerIdeal_le_ker_iff (f.app m) _).1 (hk.trans hq)
  have hc : Hom.conv (q' ≫ f) m = 1 := by
    refine toPts_injective (ofConv_injective (AlgHom.ext fun c => ?_))
    rw [map_one]
    refine (hf c).trans ?_
    rfl
  obtain ⟨g, hg⟩ := GlobalTheory.T.pDivHom_divisible_by_pow_of_kills_pow_torsion p k Q H m (q' ≫ f) hc
  refine ⟨g, sub_eq_zero.1 (hom_eq_zero_of_pow_smul_eq_zero m ?_)⟩
  rw [smul_sub, ← Linear.comp_smul, ← hg, ← Category.assoc, h1, Linear.smul_comp,
    Category.id_comp, sub_self]

end GlobalTheory.Dieu
