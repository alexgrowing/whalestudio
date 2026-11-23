import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffectiveDivisorPosDegreeAmpleClassStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPullbackAmpleVanishingOriginStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberMultilinearSymmStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem inter_pull_ample_pos : ∀ (K : Type) [Field K] (A B : AbVar K) (n : ℕ), A.dim = n + 1 → ∀ (c : Pic A.X.left) (d : Pic B.X.left), IsAmpleCls c → IsAmpleCls d → ∀ f : A ⟶ B, f ≠ 0 → 0 < inter A (Fin.cons (CechPic.pull f.hom.left d) (fun _ : Fin n => c) : Fin (n + 1) → Pic A.X.left) := by
  intro K _ A B n hdim c d hc hd f hf
  obtain ⟨m, M, hM, s, hm, hcls, hne, horig⟩ := GlobalTheory.T.exists_section_pullbackAmple_vanishing_origin K A B f d hd hf
  have htop : Out.nonzeroLocus s ≠ ⊤ := by
    intro h
    apply horig
    rw [h]
    trivial
  have hpos := GlobalTheory.T.effectiveDivisor_pos_degree_ampleClass K A n hdim c hc M hM s hne htop
  obtain ⟨⟨Φ, hΦ⟩, -⟩ := GlobalTheory.T.intersection_number_multilinear_symm K A (Fin (n + 1)) (by simp [hdim])
  set x := CechPic.pull f.hom.left d
  have hcons : (Fin.cons (cls M hM) (fun _ : Fin n => c) : Fin (n + 1) → Pic A.X.left)
      = Function.update (Fin.cons x (fun _ : Fin n => c)) 0 ((m : ℤ) • x) := by
    rw [hcls]
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [natCast_zsmul]
    · simp [Function.update, Fin.succ_ne_zero]
  rw [← hΦ, hcons, Φ.map_update_smul, Fin.update_cons_zero, smul_eq_mul] at hpos
  rw [← hΦ]
  exact pos_of_mul_pos_right hpos (by exact_mod_cast hm.le)

end GlobalTheory.AV.AbVar
