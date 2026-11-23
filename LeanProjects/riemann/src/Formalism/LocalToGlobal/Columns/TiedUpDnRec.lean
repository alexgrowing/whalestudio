import Formalism.LocalToGlobal.Columns.TiedUpDn
import Formalism.LocalToGlobal.Columns.TiedValAll

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {d : ColDat} (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (u : d.what₂.Word) (i : ℕ)
  (hi : i ≤ d.R.m)

set_option maxHeartbeats 1000000 in

theorem upNatTied (W : CF.ValTied (D := d.colRec a) u (atTTied a hH u).eV i hi (classAgreement a hS hH hP u i hi))
    (hW : ∀ s, (W.eY s).1 = s.1) : CF.UpNatTie (levelAgreement a hS hH u i hi) (classAgreement a hS hH hP u i hi) W :=
  fun v c z hz => tud_up (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr d.σ₀ d.star_cx u i (colDia (X := d.X) (Pr := d.Pr) d.R u i) (hP u i)
    (stepCrd a hS hH u i hi) W.eY hW v c z hz

set_option maxHeartbeats 1000000 in

theorem dnNatTied (W : CF.ValTied (D := d.colRec a) u (atTTied a hH u).eV i hi (classAgreement a hS hH hP u i hi))
    (hW : ∀ s, (W.eY s).1 = s.1) : CF.DnNatTie (levelAgreement a hS hH u i hi) (classAgreement a hS hH hP u i hi) W :=
  fun v c g hg => tud_dn (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr d.σ₀ d.star_cx u i (colDia (X := d.X) (Pr := d.Pr) d.R u i) (hP u i)
    (stepCrd a hS hH u i hi) W.eY hW v c g hg

theorem stepUpNatTied : CF.UpNatTie (levelAgreement a hS hH u i hi) (classAgreement a hS hH hP u i hi) (valuationAgreementConcrete a hS hH hP u i hi) :=
  upNatTied a hS hH hP u i hi _ fun _ => rfl

theorem stepDnNatTied : CF.DnNatTie (levelAgreement a hS hH u i hi) (classAgreement a hS hH hP u i hi) (valuationAgreementConcrete a hS hH hP u i hi) :=
  dnNatTied a hS hH hP u i hi _ fun _ => rfl

end Formalism.L2.Col
