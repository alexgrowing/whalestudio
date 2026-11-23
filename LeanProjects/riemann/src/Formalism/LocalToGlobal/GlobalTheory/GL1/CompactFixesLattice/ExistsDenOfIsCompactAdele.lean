import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.CompactFixesLattice
import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.AdeleIntA

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem isOpen_intAd : IsOpen ((intAd F : Subring (AF F)) : Set (AF F)) :=
  RestrictedProduct.isOpen_forall_mem (fun _ => Valued.isOpen_valuationSubring _)

theorem algebraMap_mem_intAd (m : 𝓞 F) : algebraMap F (AF F) (m : F) ∈ intAd F :=
  fun v => Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.int_R v m

theorem smul_mem_intAd (m : 𝓞 F) {a : AF F} (ha : a ∈ intAd F) : (m : F) • a ∈ intAd F := by
  rw [Algebra.smul_def]
  exact mul_mem (algebraMap_mem_intAd m) ha

theorem exists_den_adele (a : AF F) : ∃ d : 𝓞 F, d ≠ 0 ∧ (d : F) • a ∈ intAd F := by
  obtain ⟨r, hr, h⟩ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.exists_den (R := 𝓞 F) (K := F) a
  refine ⟨r, hr, ?_⟩
  rw [Algebra.smul_def]
  exact h

theorem exists_den_of_isCompact_adele (C : Set (AF F)) (hC : IsCompact C) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ a ∈ C, (d : F) • a ∈ intAd F := by
  classical
  have hopen : ∀ d : {d : 𝓞 F // d ≠ 0},
      IsOpen {a : AF F | ((d : 𝓞 F) : F) • a ∈ intAd F} := by
    intro d
    have hc : Continuous fun a : AF F => algebraMap F (AF F) ((d : 𝓞 F) : F) * a :=
      continuous_const.mul continuous_id
    have := isOpen_intAd.preimage hc
    convert this using 1
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, SetLike.mem_coe, Algebra.smul_def]
  have hcov : C ⊆ ⋃ d : {d : 𝓞 F // d ≠ 0}, {a : AF F | ((d : 𝓞 F) : F) • a ∈ intAd F} := by
    intro a _
    obtain ⟨d, hd, h⟩ := exists_den_adele a
    exact Set.mem_iUnion.mpr ⟨⟨d, hd⟩, h⟩
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover _ hopen hcov
  refine ⟨∏ d ∈ t, (d : 𝓞 F), Finset.prod_ne_zero_iff.mpr fun d _ => d.2, fun a ha => ?_⟩
  obtain ⟨d, hdt, hd⟩ := Set.mem_iUnion₂.mp (ht ha)
  have hd' : ((d : 𝓞 F) : F) • a ∈ intAd F := hd
  rw [← Finset.mul_prod_erase t _ hdt, mul_comm]
  have e : (((∏ x ∈ t.erase d, (x : 𝓞 F)) * (d : 𝓞 F) : 𝓞 F) : F) =
      ((∏ x ∈ t.erase d, (x : 𝓞 F) : 𝓞 F) : F) * ((d : 𝓞 F) : F) := rfl
  rw [e, mul_smul]
  exact smul_mem_intAd _ hd'

theorem exists_sub_mem_intAd (a : AF F) : ∃ u : F, a - algebraMap F (AF F) u ∈ intAd F :=
  Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.exists_approx_adele (R := 𝓞 F) (K := F) a

theorem mem_range_of_mem_intAd (u : F) (h : algebraMap F (AF F) u ∈ intAd F) :
    u ∈ (algebraMap (𝓞 F) F).range :=
  Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.mem_of_isInt (R := 𝓞 F) u h

end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory

end
