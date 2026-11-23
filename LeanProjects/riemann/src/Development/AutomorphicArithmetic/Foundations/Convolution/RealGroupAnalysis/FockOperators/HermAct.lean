import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.EqAmOfBarEq

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.Fo.HermitianActionFixed

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E)

private noncomputable def st (X : Matrix (Fin 2) (Fin 2) (A E)) : Matrix (Fin 2) (Fin 2) (A E) := (X.map D.bar)ᵀ

private theorem st_mul (X Y : Matrix (Fin 2) (Fin 2) (A E)) : st D (X * Y) = st D Y * st D X := by
  simp only [st, Matrix.map_mul, Matrix.transpose_mul]

private theorem st_st (X : Matrix (Fin 2) (Fin 2) (A E)) : st D (st D X) = X := by
  ext i j
  simp [st]

private theorem st_herm (v : V4 F) : st D (D.herm v) = D.herm v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [st, Dat.herm, Dat.bar_mkE]

private theorem mkE_of_fixed {z : A E} (h : D.bar z = z) : D.mkE (D.co z 0) 0 = z := by
  rw [D.mkE_base]
  exact (D.eq_am_of_bar_eq h).symm

private theorem herm_unherm {X : Matrix (Fin 2) (Fin 2) (A E)} (h : st D X = X) :
    D.herm (D.unherm X) = X := by
  have e : ∀ i j, D.bar (X j i) = X i j := fun i j => congrFun (congrFun h i) j
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [Dat.herm, Dat.unherm] using mkE_of_fixed D (e 0 0)
  · simpa [Dat.herm, Dat.unherm] using D.mkE_co (X 0 1)
  · have := D.bar_mkE (D.co (X 0 1) 0) (D.co (X 0 1) 1)
    rw [D.mkE_co, e] at this
    simpa [Dat.herm, Dat.unherm] using this.symm
  · simpa [Dat.herm, Dat.unherm] using mkE_of_fixed D (e 1 1)

private noncomputable def eps (K : Type) [Field K] [NumberField K] : A K := (0, 1)

private theorem eps_mul_snd (a : A F) : (eps F * a).2 = a.2 := one_mul _

private theorem am_eps : am E (eps F) = eps E := by
  refine Prod.ext ?_ ?_
  · exact map_zero (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E))
  · exact map_one (AdeleBaseChange.finiteAdeleMap F E)

end UpperTheory.ConvolutionTheory.R2.Fo.HermitianActionFixed

open UpperTheory.ConvolutionTheory.R2.Fo.HermitianActionFixed in
theorem UpperTheory.ConvolutionTheory.R2.Fo.hermAct :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E), (∀ h v, D.herm (D.act h v) = h.val * D.herm v * (h.val.map D.bar)ᵀ) ∧ (∀ u t, D.bar (D.mkE u t) = D.mkE u (-t)) ∧
    (∀ z, D.mkE (D.co z 0) (D.co z 1) = z) ∧ ∀ u t : A F, (D.mkE u t).2 = 0 → u.2 = 0 ∧ t.2 = 0 := by
  intro F E _ _ _ _ _ _ _ D
  refine ⟨fun h v => ?_, D.bar_mkE, D.mkE_co, fun u t h0 => ?_⟩
  · change D.herm (D.unherm (h.val * D.herm v * st D h.val)) = h.val * D.herm v * st D h.val
    apply herm_unherm
    rw [st_mul, st_mul, st_st, st_herm, mul_assoc]
  · have h1 : D.mkE (eps F * u) (eps F * t) = D.mkE 0 0 := by
      rw [← D.am_mul_mkE, am_eps, D.mkE_zero]
      refine Prod.ext (zero_mul _) ?_
      rw [eps_mul_snd, h0]
      rfl
    obtain ⟨hu, ht⟩ := D.mkE_inj h1
    exact ⟨(eps_mul_snd u).symm.trans (congrArg Prod.snd hu), (eps_mul_snd t).symm.trans (congrArg Prod.snd ht)⟩
