import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.HeckeSmooth

theorem exists_open_unit_subgroup_ker : ∀ {E : Type} [Field E] [NumberField E] (χ : HChar E)
    (w : HeightOneSpectrum (𝓞 E)),
    ∃ U : Subgroup (w.adicCompletion E)ˣ, IsOpen (U : Set (w.adicCompletion E)ˣ) ∧
      (∀ x ∈ U, IsUnitAt w x) ∧ ∀ x ∈ U, χ.1 (localIdele E w x) = 1 := by
  intro E _ _ χ w
  have hker : IsOpen ((χ.loc w).ker : Set (w.adicCompletion E)ˣ) := GlobalTheory.HeckeComp.smooth_loc χ w
  let V : Subgroup (w.adicCompletion E)ˣ :=
    { carrier := {x | Valued.v (x : w.adicCompletion E) = 1}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, Units.val_mul, map_mul] at ha hb ⊢
        rw [ha, hb, one_mul]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq, Units.val_inv_eq_inv_val, map_inv₀] at ha ⊢
        rw [ha, inv_one] }
  have hV : IsOpen (V : Set (w.adicCompletion E)ˣ) := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hx1 : Valued.v (x : w.adicCompletion E) = 1 := hx
    have hx0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by rw [hx1]; exact one_ne_zero
    have h2 : (fun y : (w.adicCompletion E)ˣ => (y : w.adicCompletion E)) ⁻¹'
        {y | Valued.v y = Valued.v (x : w.adicCompletion E)} ∈ nhds x :=
      Units.continuous_val.continuousAt (Valued.locally_const hx0)
    refine Filter.mem_of_superset h2 ?_
    intro y hy
    have hy' : Valued.v (y : w.adicCompletion E) = Valued.v (x : w.adicCompletion E) := hy
    show Valued.v (y : w.adicCompletion E) = 1
    rw [hy', hx1]
  refine ⟨(χ.loc w).ker ⊓ V, ?_, ?_, ?_⟩
  · rw [Subgroup.coe_inf]
    exact hker.inter hV
  · intro x hx
    exact (Subgroup.mem_inf.mp hx).2
  · intro x hx
    exact MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp hx).1

end GlobalTheory.CompanionTheory.HeckeSmooth
