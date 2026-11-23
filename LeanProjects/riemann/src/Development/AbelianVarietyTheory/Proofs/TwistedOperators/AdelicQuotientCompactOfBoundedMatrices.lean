import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent

noncomputable section

open Matrix Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms GlobalTheory.RegSS
open scoped TensorProduct

namespace GlobalTheory.RegSS.CptQuot

theorem continuous_adj {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A) (hσ : Continuous σ) (J : Matrix n n A) :
    Continuous (adj σ J) := by
  unfold adj
  have hc : Continuous (fun l : Matrix n n A => cT σ l) := by
    unfold Formalism.UG.cT
    exact (continuous_id.matrix_map hσ).matrix_transpose
  exact (continuous_const.matrix_mul hc).matrix_mul continuous_const

theorem exists_isCompact {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [T2Space A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A) (hσ : Continuous σ)
    {J : Matrix n n A} (hJ : IsUnit J.det) (γ : GL n A) {D : Set (Matrix n n A)}
    (hD : IsCompact D) :
    ∃ K : Set (UJ σ J ⊓ Subgroup.centralizer {γ} : Subgroup (GL n A)), IsCompact K ∧
      ∀ g : (UJ σ J ⊓ Subgroup.centralizer {γ} : Subgroup (GL n A)),
        ((g : GL n A) : Matrix n n A) ∈ D → g ∈ K := by
  have hca := continuous_adj σ hσ J
  let C : Set (Matrix n n A) := D ∩ {M | M * adj σ J M = 1 ∧ adj σ J M * M = 1 ∧
    M * (γ : Matrix n n A) = (γ : Matrix n n A) * M}
  have hCc : IsCompact C := by
    refine hD.inter_right ?_
    exact (isClosed_eq (continuous_id.matrix_mul hca) continuous_const).inter
      ((isClosed_eq (hca.matrix_mul continuous_id) continuous_const).inter
        (isClosed_eq (continuous_id.matrix_mul continuous_const)
          (continuous_const.matrix_mul continuous_id)))
  let u : C → GL n A := fun M => ⟨M.1, adj σ J M.1, M.2.2.1, M.2.2.2.1⟩
  have hu : ∀ M : C, u M ∈ (UJ σ J ⊓ Subgroup.centralizer {γ} : Subgroup (GL n A)) := by
    intro M
    refine Subgroup.mem_inf.2 ⟨(mem_UJ_iff_adj_mul σ hJ (u M)).2 M.2.2.2.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact M.2.2.2.2.symm
  let f : C → (UJ σ J ⊓ Subgroup.centralizer {γ} : Subgroup (GL n A)) := fun M => ⟨u M, hu M⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    rw [Units.continuous_iff]
    exact ⟨continuous_subtype_val, hca.comp continuous_subtype_val⟩
  have : CompactSpace C := isCompact_iff_compactSpace.mp hCc
  refine ⟨Set.range f, isCompact_range hf, ?_⟩
  intro g hg
  have hg' := Subgroup.mem_inf.1 g.2
  have h1 := (mem_UJ_iff_mul_adj σ hJ (g : GL n A)).1 hg'.1
  have h2 := (mem_UJ_iff_adj_mul σ hJ (g : GL n A)).1 hg'.1
  have h3 : ((g : GL n A) : Matrix n n A) * γ = γ * (g : GL n A) := by
    have hc := congrArg Units.val (Subgroup.mem_centralizer_iff.1 hg'.2 γ (Set.mem_singleton γ))
    rw [Units.val_mul, Units.val_mul] at hc
    exact hc.symm
  refine ⟨⟨_, hg, h1, h2, h3⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  rfl

theorem compactOfMatBounded (hL : TensorLattice) : CompactOfMatBounded := by
  intro F E _ _ _ _ n _ _ σ J γ hreg hM
  have := quad_finite hreg.quad
  obtain ⟨hTR, -, hT2, -⟩ := hL F E
  obtain ⟨D, hD, hDg⟩ := hM
  let : TopologicalSpace (E ⊗[F] AdeleRing (𝓞 F) F) :=
    Formalism.BasicNotions.tensTopL (F := F) (E := E) (AdeleRing (𝓞 F) F)
  have : IsTopologicalRing (E ⊗[F] AdeleRing (𝓞 F) F) := hTR
  have : T2Space (E ⊗[F] AdeleRing (𝓞 F) F) := hT2
  have hD' : IsCompact D := hD
  have hσ' : Continuous (sigR σ (AdeleRing (𝓞 F) F)) := continuous_sigR σ (AdeleRing (𝓞 F) F)
  have hJ' : IsUnit (J.map (inclE (F := F) (AdeleRing (𝓞 F) F))).det :=
    isUnit_det_map (inclE (F := F) (AdeleRing (𝓞 F) F)) hreg.nondeg
  have key : ∃ K : Set (centPts σ J γ (AdeleRing (𝓞 F) F)), IsCompact K ∧
      ∀ g : centPts σ J γ (AdeleRing (𝓞 F) F),
        ((g : GL n (E ⊗[F] AdeleRing (𝓞 F) F)) : Matrix n n (E ⊗[F] AdeleRing (𝓞 F) F)) ∈ D →
          g ∈ K :=
    exists_isCompact (sigR σ (AdeleRing (𝓞 F) F)) hσ' hJ'
      (bc (inclE (F := F) (AdeleRing (𝓞 F) F)) γ) hD'
  obtain ⟨K, hK, hKD⟩ := key
  have hδc : ∀ δ ∈ centRat σ J γ,
      bc (inclE (F := F) (AdeleRing (𝓞 F) F)) δ ∈ centPts σ J γ (AdeleRing (𝓞 F) F) := by
    intro δ hδ
    have hδ' := Subgroup.mem_inf.1 (show δ ∈ UJ (σ : E →+* E) J ⊓ Subgroup.centralizer {γ} from hδ)
    have hadj := (mem_UJ_iff_adj_mul (σ : E →+* E) hreg.nondeg δ).1 hδ'.1
    have hcomm := Subgroup.mem_centralizer_iff.1 hδ'.2 γ (Set.mem_singleton γ)
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · show _ ∈ UJ (sigR σ (AdeleRing (𝓞 F) F)) (J.map (inclE (F := F) (AdeleRing (𝓞 F) F)))
      rw [mem_UJ_iff_adj_mul _ hJ']
      show adj (sigR σ (AdeleRing (𝓞 F) F)) (J.map (inclE (F := F) (AdeleRing (𝓞 F) F)))
          ((δ : Matrix n n E).map (inclE (F := F) (AdeleRing (𝓞 F) F))) *
          (δ : Matrix n n E).map (inclE (F := F) (AdeleRing (𝓞 F) F)) = 1
      rw [adj_map (σ : E →+* E) (sigR σ (AdeleRing (𝓞 F) F)) (inclE (F := F) (AdeleRing (𝓞 F) F))
        (fun x => inclE_conj σ (AdeleRing (𝓞 F) F) x) hreg.nondeg, ← Matrix.map_mul, hadj,
        Matrix.map_one _ (map_zero _) (map_one _)]
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.1 hh, ← map_mul, ← map_mul, hcomm]
  refine ⟨?_⟩
  have himg : (QuotientGroup.mk '' K : Set (centPts σ J γ (AdeleRing (𝓞 F) F) ⧸
      ((centRat σ J γ).map (bc (inclE (F := F) (AdeleRing (𝓞 F) F)))).subgroupOf
        (centPts σ J γ (AdeleRing (𝓞 F) F)))) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨δ, hδ, hgδ⟩ := hDg g g.2
    refine ⟨g * ⟨_, hδc δ hδ⟩, hKD _ hgδ, ?_⟩
    exact QuotientGroup.mk_mul_of_mem _ (Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨δ, hδ, rfl⟩))
  rw [← himg]
  exact hK.image QuotientGroup.continuous_mk

end GlobalTheory.RegSS.CptQuot
