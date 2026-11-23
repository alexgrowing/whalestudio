import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.IsUnitOfComp

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Rg.Rsw.L.LGenK

variable {D : D7} {n : ℕ}

theorem mat_proj (v : Pl D) (g : G D n) :
    ((matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n) (GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g) : GL (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) :
      Matrix (Fin (n + n)) (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) = (mat g).map (cv D v) := rfl

theorem mulVec_int (v : Pl D) {m : ℕ} (A : Matrix (Fin m) (Fin m) (Fv D.host.F v ⊗[D.host.F] D.host.E))
    (x : Fin m → Fv D.host.F v ⊗[D.host.F] D.host.E) (hA : ∀ i j, A i j ∈ intLoc D.host.F D.host.E v)
    (hx : ∀ j, x j ∈ intLoc D.host.F D.host.E v) (i : Fin m) : (A *ᵥ x) i ∈ intLoc D.host.F D.host.E v := by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun j _ => mul_mem (hA i j) (hx j)

theorem single_int (v : Pl D) {m : ℕ} (j : Fin m) (i : Fin m) :
    (Pi.single j (1 : Fv D.host.F v ⊗[D.host.F] D.host.E) : Fin m → _) i ∈ intLoc D.host.F D.host.E v := by
  rw [Pi.single_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem KOff_props {D : D7} {n : ℕ} {S : Finset (Pl D)} {k : G D n} (hk : k ∈ KOff D n S) :
    (mat k).map (infPart D) = 1 ∧ (∀ v ∈ S, (mat k).map (cv D v) = 1) ∧
    ∀ v ∉ S, ∀ i j, cv D v (mat k i j) ∈ intLoc D.host.F D.host.E v := by
  obtain ⟨⟨hfin, haway⟩, hoff⟩ := Subgroup.mem_inf.1 hk
  refine ⟨congrArg Units.val (MonoidHom.mem_ker.1 hfin), fun v hv => ?_, fun v hv i j => ?_⟩
  · have h1 := MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 haway v) hv)
    rw [← mat_proj, h1, map_one, Units.val_one]
  · have h1 := Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hoff v) hv)
    have h2 := Subgroup.mem_comap.1 h1
    have hs : (Pi.single j 1 : Fin (n + n) → Fv D.host.F v ⊗[D.host.F] D.host.E) ∈
        latLoc D.host.F (stdLattice D.host.E (n + n)) v :=
      mem_latLoc_stdLattice.2 (single_int v j)
    have h3 := mem_latLoc_stdLattice.1 ((h2 _).1 hs) i
    rw [mat_proj] at h3
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h3

theorem mem_KOff {D : D7} {n : ℕ} {S : Finset (Pl D)} (g : G D n) (hinf : (mat g).map (infPart D) = 1)
    (hS : ∀ v ∈ S, (mat g).map (cv D v) = 1)
    (hint : ∀ v ∉ S, ∀ i j, cv D v (mat g i j) ∈ intLoc D.host.F D.host.E v ∧
      cv D v (mat g⁻¹ i j) ∈ intLoc D.host.F D.host.E v) :
    g ∈ KOff D n S := by
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨MonoidHom.mem_ker.2 (Units.ext hinf), ?_⟩, ?_⟩
  · refine Subgroup.mem_iInf.2 fun v => Subgroup.mem_iInf.2 fun hv => MonoidHom.mem_ker.2 ?_
    refine matHom_injective _ _ _ (Units.ext ?_)
    rw [mat_proj, hS v hv, map_one, Units.val_one]
  · refine Subgroup.mem_iInf.2 fun v => Subgroup.mem_iInf.2 fun hv => ?_
    refine Subgroup.mem_comap.2 (Subgroup.mem_comap.2 ?_)
    have hM : ∀ i j, ((matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n)
        (GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g) : GL (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) : Matrix (Fin (n + n)) (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) i j ∈ intLoc D.host.F D.host.E v := by
      intro i j; rw [mat_proj]; exact (hint v hv i j).1
    have hM' : ∀ i j, ((matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n)
        (GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g⁻¹) : GL (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) : Matrix (Fin (n + n)) (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) i j ∈ intLoc D.host.F D.host.E v := by
      intro i j; rw [mat_proj]; exact (hint v hv i j).2
    have hinv : ((matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n)
        (GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g⁻¹) : GL (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) : Matrix (Fin (n + n)) (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) *
        ((matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n)
        (GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g) : GL (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) : Matrix (Fin (n + n)) (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) = 1 := by
      rw [← Units.val_mul, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, Units.val_one]
    intro x
    rw [mem_latLoc_stdLattice, mem_latLoc_stdLattice]
    constructor
    · intro hx i
      exact mulVec_int v _ x hM hx i
    · intro hx i
      have e : x = ((matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n)
          (GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g⁻¹) : GL (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) : Matrix (Fin (n + n)) (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) *ᵥ
          (((matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n)
          (GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g) : GL (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) : Matrix (Fin (n + n)) (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) *ᵥ x) := by
        rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
      rw [e]
      exact mulVec_int v _ _ hM' hx i

end PositivityTheory.Rg.Rsw.L.LGenK
