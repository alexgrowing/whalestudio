import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnrOffOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDetInt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqMulOfResSNeOne

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StabDet

theorem toEAf_detAt_mem {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {g : GA D V} (hg : finE V g ∈ St β)
    (e : AE D) (he : e * e = e) :
    toEAf D ((GlobalTheory.VecInv.detAt e he V g : (AE D)ˣ) : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨a, ha, -⟩ := GlobalTheory.VecInv.exists_det_int hg
  have hE : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    GlobalTheory.IdemRes.toEAf_mem_of_finPart
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, he]))
  have hd := GlobalTheory.VecInv.isDetAt_detAt e he V g
  unfold IsDetAt at hd
  rw [hd, map_add, map_mul, map_sub, map_one, ← ha]
  exact add_mem (mul_mem hE a.2) (sub_mem (one_mem _) hE)

theorem toEAf_detAt {D : D7} (V : HSp D) (g : GA D V) (e : AE D) (he : e * e = e) :
    toEAf D ((GlobalTheory.VecInv.detAt e he V g : (AE D)ˣ) : AE D) =
      toEAf D e * toEAf D (Formalism.L2.Theta.mt V g).det + (1 - toEAf D e) := by
  have hd := GlobalTheory.VecInv.isDetAt_detAt e he V g
  unfold IsDetAt at hd
  rw [hd, map_add, map_mul, map_sub, map_one]

theorem map_eq_of_idem {R K : Type} [Ring R] [Ring K] (S : Subring R) (f : S →+* K) (x ε a : S) (h1 : f ε = 1)
    (hx : (x : R) = (ε : R) * (a : R) + (1 - (ε : R))) : f a = f x := by
  have hx' : x = ε * a + (1 - ε) := Subtype.ext (by push_cast; exact hx)
  rw [hx', map_add, map_mul, map_sub, map_one, h1]
  simp

theorem toEAf_detAt_inv_mem {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {g : GA D V} (hg : finE V g ∈ St β)
    (e : AE D) (he : e * e = e) :
    toEAf D (((GlobalTheory.VecInv.detAt e he V g)⁻¹ : (AE D)ˣ) : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  rw [← map_inv (GlobalTheory.VecInv.detAt e he V) g]
  exact toEAf_detAt_mem (by rw [map_inv]; exact inv_mem hg) e he

theorem res_detAt {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {g : GA D V} (hg : finE V g ∈ St β)
    (e : AE D) (he : e * e = e) (PP : Pl D.host.E) (hP : Formalism.L2.NTheta.IsIdemAt e PP) :
    ((Matrix.GeneralLinearGroup.det (redFn β PP (finE V g)) : (kP PP)ˣ) : kP PP) =
      resS D.host.F PP ⟨toEAf D ((GlobalTheory.VecInv.detAt e he V g : (AE D)ˣ) : AE D), toEAf_detAt_mem hg e he⟩ := by
  obtain ⟨a, ha, hred⟩ := GlobalTheory.VecInv.exists_det_int hg
  obtain ⟨hE, h1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D e PP hP
  rw [hred PP]
  refine map_eq_of_idem _ (resS D.host.F PP) _ ⟨toEAf D e, hE⟩ a h1 ?_
  show toEAf D _ = toEAf D e * (a : Lev.EAf D) + (1 - toEAf D e)
  rw [toEAf_detAt V g e he, ha]

theorem exists_detAt_int : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (g : GA D V), finE V g ∈ St β → ∀ e : AE D, e * e = e → ∃ x : (AE D)ˣ, IsDetAt e V g x ∧ finPart D (x : AE D) ∈ intAE D ∧ finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D ∧ ∃ hx : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, ∀ PP : Pl D.host.E, Formalism.L2.NTheta.IsIdemAt e PP → ((Matrix.GeneralLinearGroup.det (redFn β PP (finE V g)) : (kP PP)ˣ) : kP PP) = resS D.host.F PP ⟨toEAf D (x : AE D), hx⟩ := by
  intro D V β g hg e he
  exact ⟨GlobalTheory.VecInv.detAt e he V g, GlobalTheory.VecInv.isDetAt_detAt e he V g,
    GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (toEAf_detAt_mem hg e he),
    GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (toEAf_detAt_inv_mem hg e he),
    toEAf_detAt_mem hg e he, fun PP hP => res_detAt hg e he PP hP⟩

end GlobalTheory.StabDet

end
