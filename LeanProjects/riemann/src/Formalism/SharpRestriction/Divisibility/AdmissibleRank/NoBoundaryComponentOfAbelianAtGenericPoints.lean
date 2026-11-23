import Mathlib
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.SharpRestriction.Divisibility.IntegralModelsLocalData
import Formalism.SharpRestriction.Divisibility.BoundaryLocalData
import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
import Formalism.SharpRestriction.Divisibility.AdmissibleRank.LogDiscriminantLeSquareSizeFamily

namespace Formalism.MainNotions.DIV

open Formalism.BasicNotions Formalism.MainNotions

section WeightAlgebra

variable {D : D7}

theorem quadratic_statement_of_parts (large₂ : SizeData₂ D) {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} (X : WeightAlgebra.Prov D B P)
    (K : WeightAlgebra.KAdm) (H : WeightAlgebra.KHyp) (Ch Ah Cq Aq C2 A2 CR Bx CT A : ℝ)
    (hb : WeightFamilies.Stmt large₂ B K.CG K.AG K.CL K.AL K.CRm H.CK Ch Ah Cq Aq)
    (h8 : WeightAlgebra.Stmt large₂ X K H Ch Ah Cq Aq C2 A2 CR Bx CT A)
    (a1 : WeightAlgebra.adm1 B) (a2 : WeightAlgebra.adm2 large₂ X H.CA H.C1 H.A1 K.CG K.AG) (a3 : WeightAlgebra.adm3 large₂ X H.CA K.Cf K.Af)
    (a4 : WeightAlgebra.ArchimedeanSignatureMatching large₂ X H.CA H.C1 H.A1 K.CW K.AW) (b3 : WeightFamilies.adm3 B) (bB : WeightFamilies.TransferenceTheoremCond) (bC : WeightFamilies.ChowlaSelbergPeriod large₂) :
    WeightAlgebra.Conclusion1 large₂ X H C2 A2 CR CT ∧ WeightAlgebra.Conclusion2 large₂ X H C2 A2 CR Bx CT A := by
  obtain ⟨p1, p2, p3⟩ := hb ⟨a1, a2.2, b3, bB, bC⟩
  exact h8 ⟨a1, a2, a3, a4, p1, p2, p3⟩

end WeightAlgebra

section P08F

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (PL : Formalism.MainNotions.DIV.Align.PrinLevF Fm) (BF : WeightFamilies.ProvF Fm)
  (PF : ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), ModuliIntegralCharts.Prov (Fm.D x i))
  (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), WeightAlgebra.Prov (Fm.D x i) (BF x hx i) (PF x hx i))

end P08F

section BoundaryLocalData

variable (D : D7) (X : ModuliIntegralCharts.Prov D)

end BoundaryLocalData

section IntegralModelsLocalData

variable (D : D7) (XD : DivX D) (X : IntegralModelsLocalData.Prov D XD)

end IntegralModelsLocalData

section WeightThresholdDefs

variable (D : D7) (V : DivX D) (P : Formalism.MainNotions.DIV.Align.PrinLev V) (X : IntegralModelsLocalData.Prov D V)

end WeightThresholdDefs

section WeightThresholdDefs

variable (D : D7) (V : DivX D) (P : Formalism.MainNotions.DIV.Align.PrinLev V) (X : IntegralModelsLocalData.Prov D V)

end WeightThresholdDefs

section WeightThresholdDefs

variable (D : D7) (V : DivX D) (P : Formalism.MainNotions.DIV.Align.PrinLev V) (X : IntegralModelsLocalData.Prov D V)

end WeightThresholdDefs

section Fam66x

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (PL : Formalism.MainNotions.DIV.Align.PrinLevF Fm) (XF : IntegralModelsLocalData.ProvF Fm)

end Fam66x

section Base

variable {D : D7}

noncomputable def zText (L : SizeData₂ D) : ℝ := (D.R.f : ℝ) * (D.R.r : ℝ) + L.sc.L + logdE D

end Base

end Formalism.MainNotions.DIV
