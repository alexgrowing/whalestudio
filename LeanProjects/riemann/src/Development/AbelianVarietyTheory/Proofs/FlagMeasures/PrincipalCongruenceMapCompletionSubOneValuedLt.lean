import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasLabelOfIsCuspOf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecompositionStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem GLp.inc_map_sub_one_valued_lt_one : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (g n : ℕ) [Fact g.Prime] (θ : v.adicCompletion F ≃+* ℚ_[g]), (∀ z, ‖θ z‖ < 1 → Valued.v z < 1) → ∀ k ∈ (GlobalTheory.GLp.red g n).ker, ∀ a b : Fin n, Valued.v ((Matrix.GeneralLinearGroup.map θ.symm.toRingHom (GlobalTheory.GLp.inc g n k) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b - (((((1 : GL (Fin n) (ZMod g)) : Matrix (Fin n) (Fin n) (ZMod g)) a b).val : ℕ) : v.adicCompletion F)) < 1 := by
  intro F _ _ v g n _ θ hθ k hk a b
  have hk' : PadicInt.toZMod ((k : Matrix (Fin n) (Fin n) ℤ_[g]) a b) =
      ((1 : GL (Fin n) (ZMod g)) : Matrix (Fin n) (Fin n) (ZMod g)) a b := by
    have := congrArg (fun x : GL (Fin n) (ZMod g) => (x : Matrix (Fin n) (Fin n) (ZMod g)) a b)
      (MonoidHom.mem_ker.mp hk)
    simpa [GlobalTheory.GLp.red] using this
  set c : ℕ := (((1 : GL (Fin n) (ZMod g)) : Matrix (Fin n) (Fin n) (ZMod g)) a b).val with hc
  have hmem : (k : Matrix (Fin n) (Fin n) ℤ_[g]) a b - (c : ℤ_[g]) ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
    rw [RingHom.mem_ker, map_sub, hk', map_natCast, hc, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZMod] at hmem
  have hnorm : ‖(k : Matrix (Fin n) (Fin n) ℤ_[g]) a b - (c : ℤ_[g])‖ < 1 := PadicInt.mem_nonunits.mp hmem
  apply hθ
  have he : θ ((Matrix.GeneralLinearGroup.map θ.symm.toRingHom (GlobalTheory.GLp.inc g n k) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b - (c : v.adicCompletion F)) =
      (((k : Matrix (Fin n) (Fin n) ℤ_[g]) a b - (c : ℤ_[g]) : ℤ_[g]) : ℚ_[g]) := by
    simp [GlobalTheory.GLp.inc, Matrix.GeneralLinearGroup.map]
  rw [he, PadicInt.padic_norm_e_of_padicInt]
  exact hnorm

end GlobalTheory
