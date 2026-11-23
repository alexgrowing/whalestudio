import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ArthurClozel
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL

theorem exists_open_trace_ne_zero (Ω : Type) [Field Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
    (l : ℕ) [Fact l.Prime] (a : ℕ) (ha : 1 ≤ a) (r : G K Ω →* GL (Fin a) (Qbar l)) (hr : Continuous r) :
    ∃ N : Subgroup (G K Ω), IsOpen (N : Set (G K Ω)) ∧ ∀ n ∈ N, (r n).val.trace ≠ 0 := by
  have hc : Continuous fun g : G K Ω => (r g).val.trace :=
    (Units.continuous_val.comp hr).matrix_trace
  set U : Set (G K Ω) := {g | (r g).val.trace ≠ 0} with hU
  have hUo : IsOpen U := isOpen_ne_fun hc continuous_const
  have h1 : (1 : G K Ω) ∈ U := by
    simp only [hU, Set.mem_setOf_eq, map_one, Units.val_one, Matrix.trace_one, Fintype.card_fin]
    exact_mod_cast (by omega : a ≠ 0)
  obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff K Ω U).mp (hUo.mem_nhds h1)
  exact ⟨E.fixingSubgroup, E.fixingSubgroup_isOpen, fun n hn => hEU hn⟩

end GlobalTheory.AboveL
