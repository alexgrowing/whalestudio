import Formalism.LocalToGlobal.Columns.TiedValFi
import Formalism.LocalToGlobal.Columns.TiedValRat
import Formalism.LocalToGlobal.Columns.TiedValLat
import Formalism.LocalToGlobal.Columns.TiedValDil
import Formalism.LocalToGlobal.Columns.TiedValNorm
import Formalism.LocalToGlobal.Columns.TiedValBw
import Formalism.LocalToGlobal.Columns.TiedValBwP

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {d : ColDat} (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (u : d.what₂.Word) (i : ℕ)
  (hi : i ≤ d.R.m)

def valuationAgreementConcrete : CF.ValTied (D := d.colRec a) u (atTTied a hH u).eV i hi (classAgreement a hS hH hP u i hi) :=
  valuationAgreement a hS hH hP u i hi (tieEV d.sp.cm d.hX d.hPr u)
    (Val.fi (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr d.σ₀ d.star_cx u i (colDia (X := d.X) (Pr := d.Pr) d.R u i) (hP u i)
      (valCrd a hS hH u i hi))
    (Val.rat (Pr := d.Pr) d.W d.lev d.hX d.σ₀ d.star_cx u i (valCrd a hS hH u i hi))
    (Val.lat (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.σ₀ d.star_cx u i d.what₂.places d.plEq d.plEq.surjective hH.val_eq
      (valCrd a hS hH u i hi))
    (Val.dil (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr d.σ₀ u i (colDia (X := d.X) (Pr := d.Pr) d.R u i) (hP u i)
      (tieEV d.sp.cm d.hX d.hPr u) (tieEV_over d.sp.cm d.hX d.hPr u) (valCrd a hS hH u i hi))
    (Val.dilT (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr d.σ₀ d.star_cx u i (colDia (X := d.X) (Pr := d.Pr) d.R u i) (hP u i)
      (tieEV d.sp.cm d.hX d.hPr u) (tieEV_over d.sp.cm d.hX d.hPr u) (valCrd a hS hH u i hi))

theorem stepValTied_eY : (valuationAgreementConcrete a hS hH hP u i hi).eY = valEY (Pr := d.Pr) d.W d.lev d.σ₀ u i (valCrd a hS hH u i hi) := rfl

theorem stepNormTie : CF.NormTie (valuationAgreementConcrete a hS hH hP u i hi) :=
  normTie a hS hH hP u i hi _ (valuationAgreementConcrete a hS hH hP u i hi) rfl

theorem stepBwTie : CF.BwTie (atTTied a hH u) (valuationAgreementConcrete a hS hH hP u i hi) :=
  bwTie_of a hS hH hP u i hi (valuationAgreementConcrete a hS hH hP u i hi) rfl
    (Val.bw (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr d.σ₀ d.star_cx u i d.what₂.places d.plEq hH.val_eq (valCrd a hS hH u i hi)
      (atTTied a hH u).Pv (fun _ => Ideal.mk_ker))

end Formalism.L2.Col
