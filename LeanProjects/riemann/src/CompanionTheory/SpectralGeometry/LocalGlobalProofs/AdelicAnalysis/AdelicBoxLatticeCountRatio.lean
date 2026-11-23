import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeBallCountRatioBoundStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Pack

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def intSub {d M : ℕ} (b : Module.Basis (Fin d) F E) {Λ : Type} [AddCommGroup Λ]
    (e : Λ →+ (Fin 1 → Fin M → AF F ⊗[F] E)) (N : ℕ) : AddSubgroup Λ where
  carrier := {l | ∀ v, (fun a i => (N : Fv F v ⊗[F] E) * projV v (projFin (e l)) a i) ∈ latV b v}
  zero_mem' := by
    intro v a i k
    simp [projV, projFin]
  add_mem' := by
    intro x y hx hy v a i k
    have h := add_mem (hx v a i k) (hy v a i k)
    simpa [projV, projFin, mul_add, map_add] using h
  neg_mem' := by
    intro x hx v a i k
    have h := neg_mem (hx v a i k)
    simpa [projV, projFin, mul_neg, map_neg] using h

def coord (hF : IsTotallyReal F) {d M : ℕ} (b : Module.Basis (Fin d) F E) :
    (Fin 1 → Fin M → AF F ⊗[F] E) →+ PiLp 1 (fun _ : Fin 1 × Fin M × Fin d × InfinitePlace F => ℝ) :=
  AddMonoidHom.mk' (fun X => WithLp.toLp 1 fun p =>
    InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal p.2.2.2)
      ((Algebra.TensorProduct.basis (Ainf F) b).repr (projInf X p.1 p.2.1) p.2.2.1 p.2.2.2)) (by
    intro X Y
    ext p
    simp only [projInf, map_add, Pi.add_apply, Finsupp.coe_add, PiLp.add_apply]
    exact map_add _ _ _)

theorem norm_coord (hF : IsTotallyReal F) {d M : ℕ} (b : Module.Basis (Fin d) F E)
    (X : Fin 1 → Fin M → AF F ⊗[F] E) : ‖coord hF b X‖ = sizeTup b (projInf X) := by
  rw [PiLp.norm_eq_of_L1]
  simp only [sizeTup, sizeInf, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun v _ => ?_
  exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (IsTotallyReal.isReal v)).norm_map_of_map_zero
    (map_zero _) _

theorem finrank_coord (hF : IsTotallyReal F) (d M : ℕ) :
    Module.finrank ℝ (PiLp 1 (fun _ : Fin 1 × Fin M × Fin d × InfinitePlace F => ℝ)) =
      d * Module.finrank ℚ F * M := by
  have h : Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank F
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces F
    simp only [IsTotallyReal.nrComplexPlaces_eq_zero] at h1 h2
    omega
  rw [(WithLp.linearEquiv 1 ℝ _).finrank_eq, Module.finrank_fintype_fun_eq_card]
  simp only [Fintype.card_prod, Fintype.card_fin, h]
  ring

theorem box_packing : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ), ∀ (Λ : Type) [AddCommGroup Λ] (e : Λ →+ (Fin 1 → Fin M → AF F ⊗[F] E)) (N : ℕ) (r R : ℝ), 0 < r → r ≤ R → ∑' l : Λ, (Set.indicator (box b N R) (fun _ => (1 : ℝ≥0∞))) (e l) ≤ ENNReal.ofReal ((5 * R / r) ^ (2 * Module.finrank ℚ F * M)) * ∑' l : Λ, (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) (e l) := by
  intro F E _ _ _ _ _ σ hσ d b M Λ _ e N r R hr hrR
  obtain ⟨hF, -, h2, -⟩ := hσ
  have hd : d = 2 := by
    rw [← h2, Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hd
  have key := GlobalTheory.T.lattice_ball_count_ratio_bound (PiLp 1 (fun _ : Fin 1 × Fin M × Fin 2 × InfinitePlace F => ℝ)) (intSub b e N)
    ((coord hF b).comp (e.comp (intSub b e N).subtype)) r R hr hrR
  rw [finrank_coord hF 2 M] at key
  have conv : ∀ t : ℝ, ∑' l : Λ, (Set.indicator (box b N t) (fun _ => (1 : ℝ≥0∞))) (e l) =
      ∑' l : intSub b e N, Set.indicator {l : intSub b e N |
        ‖((coord hF b).comp (e.comp (intSub b e N).subtype)) l‖ ≤ t} (fun _ => (1 : ℝ≥0∞)) l := by
    intro t
    have h := tsum_subtype ((intSub b e N : AddSubgroup Λ) : Set Λ)
      (fun l => Set.indicator {l : Λ | sizeTup b (projInf (e l)) ≤ t} (fun _ => (1 : ℝ≥0∞)) l)
    refine Eq.trans ?_ (Eq.trans h.symm ?_)
    · refine tsum_congr fun l => ?_
      have hb : e l ∈ box b N t ↔ l ∈ ((intSub b e N : AddSubgroup Λ) : Set Λ) ∧
          l ∈ {l : Λ | sizeTup b (projInf (e l)) ≤ t} := Iff.rfl
      by_cases hm : e l ∈ box b N t
      · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (hb.1 hm).1, Set.indicator_of_mem (hb.1 hm).2]
      · rw [Set.indicator_of_notMem hm]
        by_cases h1 : l ∈ ((intSub b e N : AddSubgroup Λ) : Set Λ)
        · rw [Set.indicator_of_mem h1, Set.indicator_of_notMem fun h => hm (hb.2 ⟨h1, h⟩)]
        · rw [Set.indicator_of_notMem h1]
    · refine tsum_congr fun l => ?_
      simp [Set.indicator, norm_coord]
  rw [conv R, conv r]
  exact key

end GlobalTheory.CompanionTheory.SW.Pack
