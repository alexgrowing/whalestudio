import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemStabLocStdLatticeIffHtFinEqOne
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryLatticeDenominatorHeightBoundProof
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField

noncomputable section

namespace GlobalTheory.AdelicU

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

namespace HeightProper

omit [NumberField F] [NumberField E] in

theorem repr_map {R R' ι : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (b : Module.Basis ι F E)
    (φ : R →ₐ[F] R') (z : R ⊗[F] E) (i : ι) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map φ (AlgHom.id F E) z) i =
      φ ((Algebra.TensorProduct.basis R b).repr z i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add y z hy hz => simp only [map_add, Finsupp.add_apply, hy, hz]
  | tmul a e => simp [Algebra.TensorProduct.basis_repr_tmul]

theorem nnnorm_repr_le_absFin {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)
    (hb : ∀ i, IsIntegral ℤ (b i)) (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E) (i : ι) :
    ‖(Algebra.TensorProduct.basis (Fv F v) b.traceDual).repr y i‖₊ ≤ absFin F v y := by
  rw [← absBar_algebraMap, algebraMap_basis_repr]
  refine (valBar F v).map_sum_le fun τ _ => ?_
  change absBar F v _ ≤ _
  rw [absBar_mul]
  refine (mul_le_of_le_one_right' ?_).trans (le_absFin F v τ y)
  have := (le_absFin F v τ _).trans (absFin_tmul_le F v 1 (⟨b i, hb i⟩ : 𝓞 E))
  rw [finEmb_tmul, map_one, one_mul, nnnorm_one] at this
  exact this

theorem exists_norm_repr_le {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)
    (w : InfinitePlace F) (c : ℝ) (i : ι) : ∃ B : ℝ, ∀ y : w.Completion ⊗[F] E,
      (∀ τ : EmbOver E w, ‖infEmb τ y‖ ≤ c) →
      ‖(Algebra.TensorProduct.basis w.Completion b.traceDual).repr y i‖ ≤ B := by
  letI : Algebra F ℂ := w.embedding.toAlgebra
  let t : (E →ₐ[F] ℂ) → EmbOver E w := fun τ => ⟨τ, RingHom.ext τ.commutes⟩
  have key : ∀ y : w.Completion ⊗[F] E, InfinitePlace.Completion.extensionEmbedding w
      ((Algebra.TensorProduct.basis w.Completion b.traceDual).repr y i) =
      ∑ τ : E →ₐ[F] ℂ, infEmb (t τ) y * τ (b i) := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz => simp only [map_add, Finsupp.add_apply, hy, hz, add_mul, Finset.sum_add_distrib]
    | tmul a e =>
      have h : ∀ x : F, InfinitePlace.Completion.extensionEmbedding w (algebraMap F w.Completion x) =
          algebraMap F ℂ x := fun x =>
        InfinitePlace.Completion.extensionEmbedding_coe w ((WithAbs.equiv w.1).symm x)
      rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul,
        h, Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply,
        trace_eq_sum_embeddings, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [infEmb_tmul, map_mul, mul_assoc]; rfl
  refine ⟨∑ τ : E →ₐ[F] ℂ, c * ‖τ (b i)‖, fun y hy => ?_⟩
  rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _), key]
  refine norm_sum_le_of_le _ fun τ _ => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hy _) (norm_nonneg _)

theorem norm_entry_le_opNorm {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (i j : n) :
    ‖A i j‖ ≤ opNorm A := by
  have h := (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A).le_opNorm (EuclideanSpace.single j 1)
  have h2 := PiLp.norm_apply_le (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A (EuclideanSpace.single j 1)) i
  have h3 : (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A (EuclideanSpace.single j 1)) i = A i j := by
    change ∑ k, A i k * (EuclideanSpace.single j (1 : ℂ)) k = _
    simp [Pi.single_apply]
  rw [h3] at h2
  simpa [opNorm] using h2.trans h

theorem exists_compact_adeles (B : InfinitePlace F → ℝ) (c : ℝ≥0) : ∃ C : Set (AF F), IsCompact C ∧
    ∀ a : AF F, (∀ w, ‖evInf F w a‖ ≤ B w) → ∀ d : ℕ, 0 < d → (d : ℝ≥0) ≤ c →
      (∀ v, ‖(d : Fv F v) * evFin F v a‖ ≤ 1) → a ∈ C := by
  have h1 : IsCompact (X := Ainf F) (Set.pi Set.univ fun w : InfinitePlace F => {x : w.Completion | ‖x‖ ≤ B w}) :=
    isCompact_univ_pi fun w => by
      have := (InfinitePlace.Completion.isometry_extensionEmbedding w).isClosedEmbedding.isCompact_preimage
        (isCompact_closedBall 0 (B w))
      convert this using 1
      ext x
      rw [Set.mem_preimage, mem_closedBall_zero_iff,
        (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _), Set.mem_setOf_eq]
  have h2 : IsCompact (⋃ d ∈ Finset.range (⌊c⌋₊ + 1), (fun x : Af F => algebraMap F (Af F) (d : F)⁻¹ * x) ''
      {a : Af F | ∀ v, a v ∈ v.adicCompletionIntegers F}) :=
    (Finset.range _).isCompact_biUnion fun d _ =>
      (GlobalTheory.AdeleCocompact.isCompact_integral F).image (continuous_const.mul continuous_id)
  refine ⟨_, h1.prod h2, fun a ha d hd hdc hv => ⟨fun w _ => ha w, ?_⟩⟩
  refine Set.mem_biUnion (x := d) (Finset.mem_coe.2 (Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor hdc))))
    ⟨(d : Af F) * a.2, fun v => ?_, ?_⟩
  · have := hv v
    rw [← map_natCast (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v)] at this
    exact Valued.toNormedField.norm_le_one_iff.1 this
  · have hd0 : (d : F) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
    beta_reduce
    rw [← mul_assoc, ← map_natCast (algebraMap F (Af F)), ← map_mul, inv_mul_cancel₀ hd0, map_one, one_mul]

theorem exists_compact_entries (n : Type) [Fintype n] [DecidableEq n] (c : ℝ≥0) :
    ∃ C : Set (AF F ⊗[F] E), IsCompact C ∧
      ∀ g : GL n (AF F ⊗[F] E), heightGL F g ≤ c → ∀ i j, g.1 i j ∈ C := by
  classical
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨s, b, hb⟩ := FiniteDimensional.exists_is_basis_integral (𝓞 F) F E
  have hb' : ∀ i, IsIntegral ℤ (b i) := fun i => isIntegral_trans _ (hb i)
  choose B hB using fun (k : s) (w : InfinitePlace F) => exists_norm_repr_le b w c k
  choose C hC hC' using fun k : s => exists_compact_adeles (B k) c
  let e := (Algebra.TensorProduct.basis (AF F) b.traceDual).equivFun
  have he : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  refine ⟨e.symm '' Set.pi Set.univ C, (isCompact_univ_pi hC).image he, fun g hg i j =>
    ⟨e (g.1 i j), fun k _ => ?_, e.symm_apply_apply _⟩⟩
  obtain ⟨d, hd, hdc, hv⟩ := GlobalTheory.SmoothForms.denom_global (fun v => htFin F v (bc (compFin F E v) g))
    (fun v => one_le_htOf _ _) (finite_mulSupport_htFin F g)
  refine hC' k _ (fun w => ?_) d hd ?_ fun v => hv v _ ?_
  · refine (congrArg norm (repr_map b.traceDual (evInf F w) (g.1 i j) k)).symm.trans_le (hB k w _ fun τ => ?_)
    have h := (((normInf_le_iff F w).1 (le_htOf _ _) τ).trans (GlobalTheory.Grow.htInf_le_heightGL F g w)).trans hg
    exact (norm_entry_le_opNorm _ i j).trans (NNReal.coe_le_coe.2 h)
  · exact (hdc.trans (le_mul_of_one_le_left' (Finset.one_le_prod' fun _ _ => one_le_htOf _ _))).trans hg
  · refine (congrArg nnnorm (repr_map b.traceDual (evFin F v) (g.1 i j) k)).symm.trans_le
      ((nnnorm_repr_le_absFin b hb' v _ k).trans ?_)
    exact (absFin_le_normFin F v (bc (compFin F E v) g).1 i j).trans (le_htOf _ _)

end HeightProper

section GeneralLinearIntegers

variable (F) {n : Type} [Fintype n] [DecidableEq n]

theorem isCompact_heightGL_le (c : ℝ≥0) : IsCompact {g : GL n (AF F ⊗[F] E) | heightGL F g ≤ c} := by
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  have : T2Space (AF F ⊗[F] E) := e.isEmbedding.t2Space
  obtain ⟨C, hC, hC'⟩ := HeightProper.exists_compact_entries (F := F) (E := E) n c
  let S : Set (Matrix n n (AF F ⊗[F] E)) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => C
  have hS : IsCompact S := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hC
  have hK := (Units.isClosedEmbedding_embedProduct (α := Matrix n n (AF F ⊗[F] E))).isCompact_preimage
    (hS.prod (hS.image MulOpposite.continuous_op))
  refine hK.of_isClosed_subset (isClosed_le (GlobalTheory.Grow.continuous_heightGL F) continuous_const) fun g hg => ?_
  exact ⟨fun i _ j _ => hC' g hg i j, (g⁻¹).1, fun i _ j _ => hC' g⁻¹ (by rwa [heightGL_inv]) i j, rfl⟩

end GeneralLinearIntegers

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem isClosedEmbedding_matHom_GAd : Topology.IsClosedEmbedding (matHom (AF F) σ J) := by
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  have : T2Space (AF F ⊗[F] E) := e.isEmbedding.t2Space
  have hcl : IsClosed (HR (AF F) σ J : Set (GL (Fin n) (AF F ⊗[F] E))) := by
    have hv : Continuous fun g : GL (Fin n) (AF F ⊗[F] E) => (g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) :=
      Units.continuous_val
    exact isClosed_eq (((hv.matrix_map (GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF F) σ)).matrix_transpose.matrix_mul
      continuous_const).matrix_mul hv) continuous_const
  exact hcl.isClosedEmbedding_subtypeVal

theorem continuous_height_GAd : Continuous (height σ J) :=
  (GlobalTheory.Grow.continuous_heightGL F).comp (isEmbedding_matHom _ σ J).continuous

theorem isCompact_height_le (c : ℝ≥0) : IsCompact {g : GAd σ J | height σ J g ≤ c} :=
  (isClosedEmbedding_matHom_GAd σ J).isCompact_preimage (isCompact_heightGL_le F c)

theorem height_bddAbove_of_isCompact {K : Set (GAd σ J)} (hK : IsCompact K) :
    ∃ c : ℝ≥0, ∀ g ∈ K, height σ J g ≤ c := by
  obtain ⟨c, hc⟩ := hK.bddAbove_image (continuous_height_GAd σ J).continuousOn
  exact ⟨c, fun g hg => hc ⟨g, hg, rfl⟩⟩

end GlobalTheory.AdelicU

end
