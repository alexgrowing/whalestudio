import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisZero
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ConjTransposeBoostMulSignatureMulBoost
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.QhtUnip

noncomputable section
namespace GlobalTheory.QhtUnip.HeightBound

section L2
open scoped Matrix.Norms.L2Operator

theorem opNorm_le_of_entries {m : Type} [Fintype m] [DecidableEq m] (y : Matrix m m ℂ) {c : ℝ}
    (h : ∀ i j, ‖y i j‖ ≤ c) : (opNorm y : ℝ) ≤ Real.sqrt (∑ _i : m, ∑ _j : m, c ^ 2) := by
  have e : (opNorm y : ℝ) = ‖y‖ := by rw [Matrix.l2_opNorm_def]; rfl
  rw [e]
  refine (GlobalTheory.MatrixBall.l2_opNorm_le_hilbertSchmidt y).trans (Real.sqrt_le_sqrt ?_)
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
    pow_le_pow_left₀ (norm_nonneg _) (h i j) 2

end L2

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]

theorem bddA_mono {S S' : Finset (Pl F)} {c c' : ℝ≥0} (hS : S ⊆ S') (hc : c ≤ c') (h1 : 1 ≤ c') {z : AE F E}
    (hz : z ∈ bddA E S c) : z ∈ bddA E S' c' := by
  refine ⟨fun v => ?_, fun w τ => (hz.2 w τ).trans hc⟩
  have h := hz.1 v
  by_cases hv : v ∈ S
  · rw [if_pos hv] at h; rw [if_pos (hS hv)]; exact h.trans hc
  · rw [if_neg hv] at h
    by_cases hv' : v ∈ S'
    · rw [if_pos hv']; exact h.trans h1
    · rw [if_neg hv']; exact h

theorem exists_common {κ ι : Type} [Fintype κ] (f : κ → ι → AE F E) (hf : ∀ k, f k ∈ Bdd F E ι) :
    ∃ (S : Finset (Pl F)) (c : ℝ≥0), 1 ≤ c ∧ ∀ k t, f k t ∈ bddA E S c := by
  classical
  have hf' : ∀ k, ∃ (S : Finset (Pl F)) (c : ℝ≥0), ∀ t, f k t ∈ bddA E S c := hf
  choose S c h using hf'
  exact ⟨Finset.univ.biUnion S, max 1 (Finset.univ.sup c), le_max_left _ _, fun k t =>
    bddA_mono (Finset.subset_biUnion_of_mem S (Finset.mem_univ k))
      ((Finset.le_sup (f := c) (Finset.mem_univ k)).trans (le_max_right _ _)) (le_max_left _ _) (h k t)⟩

theorem absFin_le_bd {S : Finset (Pl F)} {c : ℝ≥0} (hc : 1 ≤ c) {z : AE F E} (hz : z ∈ bddA E S c)
    (v : Pl F) : absFin F v (compFin F E v z) ≤ c := by
  have h := hz.1 v
  by_cases hv : v ∈ S
  · rwa [if_pos hv] at h
  · rw [if_neg hv] at h; exact h.trans hc

theorem absFin_le_one_bd {S : Finset (Pl F)} {c : ℝ≥0} {z : AE F E} (hz : z ∈ bddA E S c) {v : Pl F}
    (hv : v ∉ S) : absFin F v (compFin F E v z) ≤ 1 := by
  have h := hz.1 v
  rwa [if_neg hv] at h

variable {n : ℕ}

theorem htFin_le_bd {S : Finset (Pl F)} {c : ℝ≥0} (hc : 1 ≤ c) (g : GL (Fin n) (AE F E))
    (hg : ∀ i j, (g : Matrix (Fin n) (Fin n) (AE F E)) i j ∈ bddA E S c)
    (hg' : ∀ i j, ((g⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) i j ∈ bddA E S c) (v : Pl F) :
    htFin F v (Formalism.UG.bc (compFin F E v) g) ≤ c := by
  refine max_le hc (max_le ((normFin_le_iff F v).2 fun i j => absFin_le_bd hc (hg i j) v)
    ((normFin_le_iff F v).2 fun i j => ?_))
  rw [← map_inv]
  exact absFin_le_bd hc (hg' i j) v

theorem htFin_eq_one_bd {S : Finset (Pl F)} {c : ℝ≥0} (g : GL (Fin n) (AE F E))
    (hg : ∀ i j, (g : Matrix (Fin n) (Fin n) (AE F E)) i j ∈ bddA E S c)
    (hg' : ∀ i j, ((g⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) i j ∈ bddA E S c) {v : Pl F}
    (hv : v ∉ S) : htFin F v (Formalism.UG.bc (compFin F E v) g) = 1 := by
  refine htOf_eq_one.2 ⟨(normFin_le_iff F v).2 fun i j => absFin_le_one_bd (hg i j) hv,
    (normFin_le_iff F v).2 fun i j => ?_⟩
  rw [← map_inv]
  exact absFin_le_one_bd (hg' i j) hv

theorem htInf_le_bd {S : Finset (Pl F)} {c : ℝ≥0} (g : GL (Fin n) (AE F E))
    (hg : ∀ i j, (g : Matrix (Fin n) (Fin n) (AE F E)) i j ∈ bddA E S c)
    (hg' : ∀ i j, ((g⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) i j ∈ bddA E S c)
    (w : InfinitePlace F) :
    htInf F w (Formalism.UG.bc (compInf F E w) g) ≤
      max 1 (Real.toNNReal (Real.sqrt (∑ _i : Fin n, ∑ _j : Fin n, (c : ℝ) ^ 2))) := by
  have key : ∀ y : GL (Fin n) (AE F E), (∀ i j, (y : Matrix (Fin n) (Fin n) (AE F E)) i j ∈ bddA E S c) →
      normInf F w ((Formalism.UG.bc (compInf F E w) y : GL (Fin n) (w.Completion ⊗[F] E)) :
        Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E)) ≤
        Real.toNNReal (Real.sqrt (∑ _i : Fin n, ∑ _j : Fin n, (c : ℝ) ^ 2)) := by
    intro y hy
    refine (normInf_le_iff F w).2 fun τ => ?_
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
    refine opNorm_le_of_entries _ fun i j => ?_
    have := (hy i j).2 w τ
    exact_mod_cast this
  refine max_le_max le_rfl (max_le (key g hg) ?_)
  rw [← map_inv]
  exact key g⁻¹ hg'

theorem heightGL_bdd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (ι : Type) (g : ι → GL (Fin n) (AE F E)),
    (∀ i j, (fun t => (g t : Matrix (Fin n) (Fin n) (AE F E)) i j) ∈ Bdd F E ι) →
    (∀ i j, (fun t => (((g t)⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) i j) ∈ Bdd F E ι) →
    ∃ K : ℝ≥0, ∀ t, heightGL F (g t) ≤ K := by
  intro F E _ _ _ _ _ n ι g hg hg'
  obtain ⟨S, c, hc, h⟩ := exists_common (F := F) (E := E) (κ := (Fin n × Fin n) ⊕ (Fin n × Fin n))
    (fun k => Sum.elim (fun p t => (g t : Matrix (Fin n) (Fin n) (AE F E)) p.1 p.2)
      (fun p t => (((g t)⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) p.1 p.2) k)
    (by rintro (⟨i, j⟩ | ⟨i, j⟩); exacts [hg i j, hg' i j])
  refine ⟨(∏ _w : InfinitePlace F, max 1 (Real.toNNReal (Real.sqrt (∑ _i : Fin n, ∑ _j : Fin n, (c : ℝ) ^ 2)))) *
    ∏ _v ∈ S, c, fun t => ?_⟩
  have e1 : ∀ i j, (g t : Matrix (Fin n) (Fin n) (AE F E)) i j ∈ bddA E S c := fun i j => h (Sum.inl (i, j)) t
  have e2 : ∀ i j, (((g t)⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) i j ∈ bddA E S c :=
    fun i j => h (Sum.inr (i, j)) t
  unfold heightGL
  refine mul_le_mul' (Finset.prod_le_prod' fun w _ => htInf_le_bd (g t) e1 e2 w) ?_
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) ?_]
  · exact Finset.prod_le_prod' fun v _ => htFin_le_bd hc (g t) e1 e2 v
  · intro v hv
    by_contra hvS
    exact hv (htFin_eq_one_bd (g t) e1 e2 (fun h' => hvS (Finset.mem_coe.2 h')))

end GlobalTheory.QhtUnip.HeightBound
