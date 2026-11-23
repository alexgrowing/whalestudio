import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.Ggeo.WpKInv

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)

def toPi (i : N.Loc) :
    TensorProduct (N.O i) (Fin R.r → N.O i) (FractionRing (N.O i)) ≃ₗ[N.O i] (Fin R.r → Kf N i) :=
  (TensorProduct.comm (N.O i) _ _).trans
    (TensorProduct.piScalarRight (N.O i) (N.O i) (FractionRing (N.O i)) (Fin R.r))

theorem toPi_tmul (i : N.Loc) (v : Fin R.r → N.O i) (k : FractionRing (N.O i)) :
    toPi N i (v ⊗ₜ k) = fun j => algebraMap (N.O i) (Kf N i) (v j) * k := by
  funext j
  simp [toPi, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul, Algebra.smul_def]

theorem Wp_apply (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) (g : G H.E N.Om)
    (v : Fin R.r → N.O i) :
    Glob.Wp N i ρ g v = ((((N.chi i 1 g)⁻¹ : (N.O i)ˣ) : N.O i) •
      ((ρ g : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i))).mulVec v := by
  rw [Matrix.smul_mulVec]
  rfl

theorem toPi_WpK (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) (g : G H.E N.Om)
    (t : TensorProduct (N.O i) (Fin R.r → N.O i) (FractionRing (N.O i))) :
    toPi N i (Glob.WpK N i ρ g t) = (GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts.matW N i ρ g).mulVec (toPi N i t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, Matrix.mulVec_add]
  | tmul v k =>
    have h1 : Glob.WpK N i ρ g (v ⊗ₜ k) = (Glob.Wp N i ρ g v) ⊗ₜ k := by
      simp [Glob.WpK, coefRep, Representation.tprod_apply]
    rw [h1, toPi_tmul, toPi_tmul, Wp_apply]
    have h2 : (fun j => algebraMap (N.O i) (Kf N i) (v j) * k) =
        k • (algebraMap (N.O i) (Kf N i) ∘ v) := by
      funext j; simp [mul_comm]
    rw [h2, Matrix.mulVec_smul]
    funext j
    rw [Pi.smul_apply, smul_eq_mul, mul_comm, GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts.matW, ← RingHom.map_mulVec]

theorem H0_weight_part_eq_bot :
    ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (i : N.Loc)
      (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) (Dg : Subgroup (G H.E N.Om)),
      GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts.NoInv Dg (GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts.matW N i ρ) →
        H0 ((Formalism.MainNotions.N.Glob.WpK N i ρ).comp Dg.subtype) = ⊥ := by
  intro R H what₂ N i ρ Dg h
  rw [eq_bot_iff]
  intro t ht
  rw [Submodule.mem_bot]
  have ht' : ∀ g ∈ Dg, Glob.WpK N i ρ g t = t := fun g hg =>
    (Representation.mem_invariants _ t).1 ht ⟨g, hg⟩
  have h0 : toPi N i t = 0 := h _ fun g hg => by rw [← toPi_WpK, ht' g hg]
  exact (toPi N i).map_eq_zero_iff.1 h0

end GlobalTheory.Ggeo.WpKInv
