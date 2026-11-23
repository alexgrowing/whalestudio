import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupIInfEigenspaceEqTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev
  Formalism.IndefR
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GoodFiniteDim

variable {D : D7}

theorem isOpen_comap_Kg (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (T : Finset (Pl D.host.E)) :
    IsOpen (((Kg D.sp.cm V.gram β T).comap (finE V) : Subgroup (GA D V)) : Set (GA D V)) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ V β T] with κ hh
  obtain ⟨h1, h2, h3⟩ := hh
  exact ⟨⟨h1, h2⟩, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_princAt.2 ⟨h2, h3 PP hP⟩⟩

theorem levFn_eq_one {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} {T : Finset (Pl D.host.E)}
    (hg : L.Pg ⊆ T) (hq : L.Q ⊆ T) {x : GL (Fin V.rank) (Lev.EAf D)} (hx : x ∈ Kg D.sp.cm V.gram β T) :
    levFn β L x = 1 := by
  have h3 : ∀ PP ∈ T, redFn β PP x = 1 := by
    have h1 : x ∈ ⨅ PP ∈ T, princAt β PP := hx.2
    exact fun PP hP => (mem_princAt.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h1 PP) hP)).2
  have h4 : rTup β L x = 1 := by
    funext PP
    show upperLeftBlock L.hr (redFn β PP.1 x) = 1
    rw [h3 PP.1 (hg PP.2)]; exact blockDiagonalExtendByOnePrimeField_one _ _
  unfold levFn
  rw [h4, blockDiagonalExtendByOnePrimeField_one, one_mul, Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
  · intro PP hP
    rw [h3 PP (hq hP), dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]
  · intro PP hP
    refine Finset.prod_eq_one fun c _ => ?_
    rw [h3 PP (hg hP), dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]

theorem exists_open_subgroup (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧
      ∀ k ∈ U, k ∈ GfC V → k ∈ (levG V β L : Set (GA D V)) ∧ levChi V β L k = 1 := by
  classical
  refine ⟨_, isOpen_comap_Kg V β (L.Pg ∪ L.Q), fun k hk hf => ⟨⟨hf, ?_⟩, ?_⟩⟩
  · exact Kg_le_lev (D := L) (T := L.Pg ∪ L.Q) Finset.subset_union_left Finset.subset_union_right hk
  · unfold levChi
    rw [levFn_eq_one Finset.subset_union_left Finset.subset_union_right hk, Units.val_one]

theorem goodFinite_of_hcFinite' (D : D7)
    (h : ∀ θ (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ (M : GlobalTheory.IndefiniteRowSideFullHecke.GoodReductionModelReading.ModelW D j) J χ, HCFinite θ M J χ) :
    GlobalTheory.HeckeOrthSum.GoodFinite D := by
  intro θ hθ pb Pg _ pl _ red ψ _ om _ Sb _ j h1 h2 hj M β _
  have := h θ j h1 h2 M _ _ hθ (exists_open_subgroup (D.sp.W j) β (GlobalTheory.IndefiniteRowSideFullHecke.GoodReductionModelReading.levelDatumAtBasePrime (D.sp.W j) Pg ψ))
  exact Submodule.finiteDimensional_of_le (goodPart_le θ M _ _ _)

theorem goodFinite_of_hcFinite : ∀ D : Formalism.BasicNotions.D7,
    (∀ θ (V : Formalism.BasicNotions.TH.HSp D) S (M : Formalism.IndefR.Mult.DSModel V S) J χ, Formalism.IndefR.Mult.HCFinite θ M J χ) →
      GlobalTheory.HeckeOrthSum.GoodFinite D := by
  intro D h θ hθ pb Pg _ pl _ red ψ _ om _ Sb _ j _ _ hj M β _
  have := h θ _ _ M _ _ hθ (exists_open_subgroup (D.sp.W j) β (GlobalTheory.IndefiniteRowSideFullHecke.GoodReductionModelReading.levelDatumAtBasePrime (D.sp.W j) Pg ψ))
  exact Submodule.finiteDimensional_of_le (goodPart_le θ M _ _ _)

end GlobalTheory.GoodFiniteDim
