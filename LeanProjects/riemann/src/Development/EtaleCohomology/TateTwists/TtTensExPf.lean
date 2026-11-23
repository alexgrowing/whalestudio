import Development.EtaleCohomology.TateTwists.EtaleTensorTwistedResolutionOfExistenceBoundAndS

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.EtaleFoundations

structure TensPre {R : Type} [CommRing R] (I J : Cx R) where
  P : CochainComplex (Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) ℤ
  e : ∀ (U : Scheme.{0}) (w : ℤ), Tens I J U w ≃ₗ[ULift.{1} R] (P.X w).obj (op U)
  nat : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w),
    e V w (Tens.res g w x) = ((P.X w).map g.op).hom (e U w x)
  leibniz : ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
    ((P.d w (w + 1)).app (op U)).hom (e U w (DirectSum.of _ ⟨(s, t), h⟩ (a ⊗ₜ b))) =
      e U (w + 1) (DirectSum.of _ ⟨(s + 1, t), by omega⟩ (Sec.map (I.d s (s + 1)) a ⊗ₜ b)) +
      s.negOnePow • e U (w + 1) (DirectSum.of _ ⟨(s, t + 1), by omega⟩ (a ⊗ₜ Sec.map (J.d t (t + 1)) b))

def tt_tens_pre : Prop :=
  ∀ (R : Type) [CommRing R] (I J : Cx R), Nonempty (TensPre I J)

def tt_tens_sheafify : Prop :=
  ∀ (R : Type) [CommRing R] (I J : Cx R), TensPre I J → ∃ (K : Cx R) (μ : Pair I J K), μ.IsTensor

theorem tt_tens_ex_of (hpre : tt_tens_pre) (hsh : tt_tens_sheafify) : tt_tens_ex := by
  intro R _ I J
  obtain ⟨T⟩ := hpre R I J
  exact hsh R I J T

end LateralTheory.EtaleFoundations
