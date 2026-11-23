import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.ExistsIsLiftOfEtP
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.H1LiftNaturality
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.FirstChernRestrictionCocycle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace CrystallineSemistableComparison.HT

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem half1 (ht : TFil l) {e : E.EtFam l K} (he : EtP e) : Half1 ht (fun {_} r {_} v x => IsLift ht e r v x) where
  comp h := h.1
  ex := exists_isLift_of_etP ht he
  uniq := shS_eq_of_isLift ht
  add := h1_lift_add ht he
  smul := h1_lift_smul ht he
  sh := h1_lift_shift ht he
  gal := h1_lift_galois ht he
  nat := h1_lift_naturality ht he
  cup := isLift_cupS_of_cupT ht he
  one := isLift_oneS_of_lev_eq_one ht he
  first_chern_class_exists := he.first_chern_class_exists
  c1 := h1_lift_of_firstChern ht he

end CrystallineSemistableComparison.HT
