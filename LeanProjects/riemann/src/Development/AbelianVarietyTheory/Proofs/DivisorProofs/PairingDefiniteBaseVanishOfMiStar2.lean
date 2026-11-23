import Formalism.LocalToGlobal.IndefiniteReal.IsometricPeriodsOfUnitHypotheses
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Div

theorem pairing_definite_base_vanish_of_miStar2 : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (s : ℕ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → PrimRows3 R F → ∀ (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH), (R.toCx3 F).MIstar2 (F.eV (R.toCx3 F).zs) sEE → CxData.BtVanish (fc := F.fc) (R.toCx3 F) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hsep hC hP sEE hM
  have hR := complex_data_conditions_base_level_of_primitive_links hOk hsep hC hP
  obtain ⟨d, hU, hI, -⟩ := hM
  exact CxData.base_tuple_vanishing_of_hypotheses _ F.cr F.cv hR.jIsoR (hR.levs true).1 (hR.levs true).2.1 (hR.levs true).2.2
    (definite_coordinates_in_good_part _ true) (EvTie.evTie_of_ok hOk F _) hU hI

end GlobalTheory.Div
