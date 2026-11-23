import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleLocalGlobalProperties
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContDiffOnChartGlobalWhittakerCoefficient
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TotallyRealContinuousEmbeddingInfiniteAdeles
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BoxF

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem repr_map {R S : Type} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
    (g : R →ₐ[F] S) {d : ℕ} (b : Module.Basis (Fin d) F E) (y : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis S b).repr (Algebra.TensorProduct.map g (AlgHom.id F E) y) k =
      g ((Algebra.TensorProduct.basis R b).repr y k) := by
  induction y with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | tmul r e =>
    simp [Algebra.TensorProduct.basis_repr_tmul]

theorem repr_tmul_mul {R : Type} [CommRing R] [Algebra F R] {d : ℕ} (b : Module.Basis (Fin d) F E)
    (t : R) (y : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis R b).repr ((t ⊗ₜ[F] (1 : E)) * y) k =
      t * (Algebra.TensorProduct.basis R b).repr y k := by
  have h : (t ⊗ₜ[F] (1 : E)) * y = t • y := by
    rw [Algebra.smul_def]; rfl
  rw [h, map_smul]; simp

theorem repr_nat_mul {R : Type} [CommRing R] [Algebra F R] {d : ℕ} (b : Module.Basis (Fin d) F E)
    (N : ℕ) (y : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis R b).repr ((N : R ⊗[F] E) * y) k =
      (N : R) * (Algebra.TensorProduct.basis R b).repr y k := by
  have h : (N : R ⊗[F] E) = (N : R) ⊗ₜ[F] (1 : E) := by
    rw [← map_natCast (algebraMap R (R ⊗[F] E)) N]; rfl
  rw [h, repr_tmul_mul]

end Alg

section Top

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

theorem topRing : IsTopologicalRing (R ⊗[F] E) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  exact IsModuleTopology.isTopologicalRing R _

theorem cont_repr {d : ℕ} (b : Module.Basis (Fin d) F E) (k : Fin d) :
    Continuous fun y : R ⊗[F] E => (Algebra.TensorProduct.basis R b).repr y k := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := topRing R
  exact IsModuleTopology.continuous_of_linearMap
    ((Finsupp.lapply k).comp (Algebra.TensorProduct.basis R b).repr.toLinearMap)

def coordH {d : ℕ} (b : Module.Basis (Fin d) F E) : R ⊗[F] E ≃ₜ (Fin d → R) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := topRing R
  exact
  { (Algebra.TensorProduct.basis R b).equivFun.toEquiv with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis R b).equivFun.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis R b).equivFun.symm.toLinearMap }

end Top

section Inf

variable {F : Type} [Field F] [NumberField F]

theorem ball_cpt (w : InfinitePlace F) (r : ℝ) : IsCompact (Metric.closedBall (0 : w.Completion) r) := by
  have hi := InfinitePlace.Completion.isometry_extensionEmbedding w
  have hc := hi.isClosedEmbedding
  rw [← hi.preimage_closedBall]
  exact hc.isCompact_preimage (isCompact_closedBall _ _)

theorem ainf_ball_cpt (r : ℝ) : IsCompact {y : Ainf F | ∀ w, ‖y w‖ ≤ r} := by
  let S : Set (Ainf F) := Set.pi Set.univ fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) r
  have hS : IsCompact S := isCompact_univ_pi fun w => ball_cpt w r
  have e : {y : Ainf F | ∀ w, ‖y w‖ ≤ r} = S := by
    refine Set.ext fun y => ⟨fun h w _ => mem_closedBall_zero_iff.2 (h w), fun h w => ?_⟩
    exact mem_closedBall_zero_iff.1 (h w trivial)
  rw [e]
  exact hS

theorem cont_norm_w (w : InfinitePlace F) : Continuous fun y : Ainf F => ‖y w‖ :=
  continuous_norm.comp (continuous_apply (A := fun w : InfinitePlace F => w.Completion) w)

theorem cont_fstA : Continuous (fstA F) :=
  (continuous_fst : Continuous (Prod.fst : Ainf F × Af F → Ainf F))

theorem cont_sndA : Continuous (sndA F) :=
  (continuous_snd : Continuous (Prod.snd : Ainf F × Af F → Af F))

end Inf

section Den

variable {F : Type} [Field F] [NumberField F]

def intS (N : ℕ) : Set (Af F) :=
  {y | ∀ v, (N : Fv F v) * evalV F v y ∈ v.adicCompletionIntegers F}

theorem intS_open (N : ℕ) : IsOpen (intS (F := F) N) := by
  have h : IsOpen {f : Af F | ∀ v, evalV F v f ∈ (v.adicCompletionIntegers F : Set (Fv F v))} :=
    RestrictedProduct.isOpen_forall_mem (fun _ => Valued.isOpen_valuationSubring _)
  have hc : Continuous (fun y : Af F => (N : Af F) * y) := continuous_const.mul continuous_id
  have e : intS (F := F) N = (fun y : Af F => (N : Af F) * y) ⁻¹'
      {f : Af F | ∀ v, evalV F v f ∈ (v.adicCompletionIntegers F : Set (Fv F v))} := by
    ext y
    simp only [intS, Set.mem_setOf_eq, Set.mem_preimage, map_mul, map_natCast]
    rfl
  rw [e]
  exact h.preimage hc

theorem exists_nat_v (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) :
    ∃ N : ℕ, 0 < N ∧ (N : Fv F v) * a ∈ v.adicCompletionIntegers F := by
  obtain ⟨β, hβ, h⟩ := HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v a
  have hb0 : β ≠ 0 := nonZeroDivisors.ne_zero hβ
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {β}))
  refine ⟨Ideal.absNorm (Ideal.span {β}), Nat.pos_of_ne_zero ?_, ?_⟩
  · intro h0
    rw [Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot] at h0
    exact hb0 h0
  · have e : ((Ideal.absNorm (Ideal.span {β}) : ℕ) : Fv F v) =
        algebraMap (𝓞 F) (Fv F v) c * algebraMap (𝓞 F) (Fv F v) β := by
      rw [← map_mul, hc, map_natCast]
    rw [e, mul_assoc, mul_comm (algebraMap (𝓞 F) (Fv F v) β) a]
    exact mul_mem (Formalism.UG.P.levelaf_int_mem_v v c) h

theorem exists_nat_Af (y : Af F) : ∃ N : ℕ, 0 < N ∧ y ∈ intS (F := F) N := by
  classical
  have hfin : {v | ¬ evalV F v y ∈ (v.adicCompletionIntegers F : Set (Fv F v))}.Finite :=
    Filter.eventually_cofinite.1 y.2
  choose f hf0 hf using fun v => exists_nat_v (F := F) v (evalV F v y)
  refine ⟨∏ v ∈ hfin.toFinset, f v, Finset.prod_pos fun v _ => hf0 v, fun v => ?_⟩
  by_cases hv : v ∈ hfin.toFinset
  · rw [← Finset.mul_prod_erase _ _ hv, Nat.cast_mul, mul_comm ((f v : Fv F v)), mul_assoc]
    exact mul_mem (natCast_mem _ _) (hf v)
  · have h1 : evalV F v y ∈ v.adicCompletionIntegers F := by
      by_contra h
      exact hv (hfin.mem_toFinset.2 h)
    exact mul_mem (natCast_mem _ _) h1

theorem intS_mono {N N' : ℕ} (h : N ∣ N') : intS (F := F) N ⊆ intS N' := by
  obtain ⟨c, rfl⟩ := h
  intro y hy v
  push_cast
  rw [mul_comm (N : Fv F v), mul_assoc]
  exact mul_mem (natCast_mem _ _) (hy v)

end Den

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) {n M : ℕ}

theorem mem_lat_iff (N : ℕ) (v : HeightOneSpectrum (𝓞 F)) (Y : Fin n → Fin M → Fv F v ⊗[F] E) :
    (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v ↔
      ∀ a i k, (N : Fv F v) * (Algebra.TensorProduct.basis (Fv F v) b).repr (Y a i) k ∈
        v.adicCompletionIntegers F := by
  simp only [latV, Set.mem_setOf_eq, repr_nat_mul]

theorem comp_v (v : HeightOneSpectrum (𝓞 F)) (X : Fin n → Fin M → AF F ⊗[F] E) (a : Fin n) (i : Fin M)
    (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) b).repr (projV v (projFin X) a i) k =
      evalV F v (sndA F ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k)) := by
  simp only [projV, projFin, repr_map]

theorem size_eq (X : Fin n → Fin M → AF F ⊗[F] E) :
    sizeTup b (projInf X) = ∑ a, ∑ i, ∑ k, ∑ w : InfinitePlace F,
      ‖(fstA F ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k)) w‖ := by
  simp only [sizeTup, sizeInf, projInf, repr_map]

theorem cont_size : Continuous fun X : Fin n → Fin M → AF F ⊗[F] E => sizeTup b (projInf X) := by
  simp only [size_eq]
  refine continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun i _ =>
    continuous_finset_sum _ fun k _ => continuous_finset_sum _ fun w _ => ?_
  exact (cont_norm_w w).comp (cont_fstA.comp ((cont_repr (AF F) b k).comp
    ((continuous_apply i).comp (continuous_apply a))))

def intT (N : ℕ) : Set (Fin n → Fin M → AF F ⊗[F] E) :=
  {X | ∀ a i k, sndA F ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k) ∈ intS (F := F) N}

theorem intT_open (N : ℕ) : IsOpen (intT (n := n) (M := M) b N) := by
  have e : intT (n := n) (M := M) b N = ⋂ a, ⋂ i, ⋂ k,
      (fun X : Fin n → Fin M → AF F ⊗[F] E =>
        sndA F ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k)) ⁻¹' intS (F := F) N := by
    ext X
    simp [intT]
  rw [e]
  refine isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun i =>
    isOpen_iInter_of_finite fun k => (intS_open N).preimage ?_
  exact cont_sndA.comp ((cont_repr (AF F) b k).comp ((continuous_apply i).comp (continuous_apply a)))

theorem mem_intT_iff (N : ℕ) (X : Fin n → Fin M → AF F ⊗[F] E) :
    X ∈ intT b N ↔ ∀ v, (fun a i => (N : Fv F v ⊗[F] E) * projV v (projFin X) a i) ∈ latV b v := by
  simp only [mem_lat_iff, comp_v, intT, intS, Set.mem_setOf_eq]
  exact ⟨fun h v a i k => h a i k v, fun h a i k v => h v a i k⟩

theorem mem_box_iff (N : ℕ) (r : ℝ) (X : Fin n → Fin M → AF F ⊗[F] E) :
    X ∈ box b N r ↔ X ∈ intT b N ∧ sizeTup b (projInf X) ≤ r := by
  rw [mem_intT_iff]; rfl

theorem exists_intT (X : Fin n → Fin M → AF F ⊗[F] E) : ∃ N : ℕ, 0 < N ∧ X ∈ intT b N := by
  choose f hf0 hf using fun p : Fin n × Fin M × Fin d =>
    exists_nat_Af (F := F) (sndA F ((Algebra.TensorProduct.basis (AF F) b).repr (X p.1 p.2.1) p.2.2))
  refine ⟨∏ p, f p, Finset.prod_pos fun p _ => hf0 p, fun a i k => ?_⟩
  exact intS_mono (Finset.dvd_prod_of_mem f (Finset.mem_univ (a, i, k))) (hf (a, i, k))

theorem intT_mono {N N' : ℕ} (h : N ∣ N') : intT (n := n) (M := M) b N ⊆ intT b N' :=
  fun _ hX a i k => intS_mono h (hX a i k)

theorem exhaust (C : Set (Fin n → Fin M → AF F ⊗[F] E)) (hC : IsCompact C) :
    ∃ (N : ℕ) (r : ℝ), 0 < N ∧ 0 < r ∧ C ⊆ box b N r := by
  obtain ⟨⟨N, hN⟩, hNC⟩ := hC.elim_directed_cover
    (fun N : {N : ℕ // 0 < N} => intT (n := n) (M := M) b N.1)
    (fun N => intT_open b N.1)
    (fun X _ => by
      obtain ⟨N, hN, hX⟩ := exists_intT b X
      exact Set.mem_iUnion.2 ⟨⟨N, hN⟩, hX⟩)
    (fun N N' => ⟨⟨N.1 * N'.1, Nat.mul_pos N.2 N'.2⟩, intT_mono b (Nat.dvd_mul_right _ _),
      intT_mono b (Nat.dvd_mul_left _ _)⟩)
  obtain ⟨B, hB⟩ := (hC.image (cont_size (n := n) (M := M) b)).bddAbove
  refine ⟨N, max B 1, hN, lt_of_lt_of_le one_pos (le_max_right _ _), fun X hX => ?_⟩
  exact (mem_box_iff b N _ X).2 ⟨hNC hX, (hB ⟨X, hX, rfl⟩).trans (le_max_left _ _)⟩

theorem cinf_cpt (r : ℝ) :
    IsCompact {Y : Fin n → Fin M → Ainf F ⊗[F] E | sizeTup b Y ≤ r} := by
  let H : (Fin n → Fin M → Ainf F ⊗[F] E) ≃ₜ (Fin n → Fin M → Fin d → Ainf F) :=
    Homeomorph.piCongrRight fun _ => Homeomorph.piCongrRight fun _ => coordH (Ainf F) b
  let S : Set (Fin n → Fin M → Fin d → Ainf F) :=
    {c | ∑ a, ∑ i, ∑ k, ∑ w : InfinitePlace F, ‖c a i k w‖ ≤ r}
  have hcl : IsClosed S := by
    refine isClosed_le ?_ continuous_const
    refine continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun i _ =>
      continuous_finset_sum _ fun k _ => continuous_finset_sum _ fun w _ => ?_
    exact (cont_norm_w w).comp ((continuous_apply k).comp ((continuous_apply i).comp (continuous_apply a)))
  have hB : IsCompact (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin M =>
      Set.pi Set.univ fun _ : Fin d => {y : Ainf F | ∀ w, ‖y w‖ ≤ r}) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => ainf_ball_cpt r
  have hS : IsCompact S := by
    refine hB.of_isClosed_subset hcl ?_
    intro c hc a _ i _ k _ w
    refine le_trans ?_ hc
    have t1 : ‖c a i k w‖ ≤ ∑ w : InfinitePlace F, ‖c a i k w‖ :=
      Finset.single_le_sum (f := fun w : InfinitePlace F => ‖c a i k w‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_univ w)
    have t2 : ∑ w : InfinitePlace F, ‖c a i k w‖ ≤ ∑ k, ∑ w : InfinitePlace F, ‖c a i k w‖ :=
      Finset.single_le_sum (f := fun k => ∑ w : InfinitePlace F, ‖c a i k w‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ k)
    have t3 : ∑ k, ∑ w : InfinitePlace F, ‖c a i k w‖ ≤ ∑ i, ∑ k, ∑ w : InfinitePlace F, ‖c a i k w‖ :=
      Finset.single_le_sum (f := fun i => ∑ k, ∑ w : InfinitePlace F, ‖c a i k w‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
        (Finset.mem_univ i)
    have t4 : ∑ i, ∑ k, ∑ w : InfinitePlace F, ‖c a i k w‖ ≤
        ∑ a, ∑ i, ∑ k, ∑ w : InfinitePlace F, ‖c a i k w‖ :=
      Finset.single_le_sum (f := fun a => ∑ i, ∑ k, ∑ w : InfinitePlace F, ‖c a i k w‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
          Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ a)
    exact t1.trans (t2.trans (t3.trans t4))
  have e : {Y : Fin n → Fin M → Ainf F ⊗[F] E | sizeTup b Y ≤ r} = H ⁻¹' S := rfl
  rw [e]
  exact H.isCompact_preimage.2 hS

theorem cv_cpt (N : ℕ) (hN : 0 < N) (v : HeightOneSpectrum (𝓞 F))
    (hL : IsCompact (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E))) :
    IsCompact {Y : Fin n → Fin M → Fv F v ⊗[F] E |
      (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v} := by
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := topRing (Fv F v)
  have hN0 : (N : Fv F v) ≠ 0 := by
    have h0 : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    rw [← map_natCast (algebraMap F (Fv F v)) N]
    exact (map_ne_zero (algebraMap F (Fv F v))).2 h0
  have hu : ((N : Fv F v)⁻¹ ⊗ₜ[F] (1 : E)) * (N : Fv F v ⊗[F] E) = 1 := by
    have h : (N : Fv F v ⊗[F] E) = (N : Fv F v) ⊗ₜ[F] (1 : E) := by
      rw [← map_natCast (algebraMap (Fv F v) (Fv F v ⊗[F] E)) N]; rfl
    rw [h, Algebra.TensorProduct.tmul_mul_tmul, inv_mul_cancel₀ hN0, mul_one]; rfl
  let u : Fv F v ⊗[F] E := (N : Fv F v)⁻¹ ⊗ₜ[F] (1 : E)
  let e : (Fin n → Fin M → Fv F v ⊗[F] E) ≃ₜ (Fin n → Fin M → Fv F v ⊗[F] E) :=
    { toFun := fun Y a i => (N : Fv F v ⊗[F] E) * Y a i
      invFun := fun Y a i => u * Y a i
      left_inv := fun Y => by
        funext a i
        show u * ((N : Fv F v ⊗[F] E) * Y a i) = Y a i
        rw [← mul_assoc, hu, one_mul]
      right_inv := fun Y => by
        funext a i
        show (N : Fv F v ⊗[F] E) * (u * Y a i) = Y a i
        rw [← mul_assoc, mul_comm _ u, hu, one_mul]
      continuous_toFun := continuous_pi fun a => continuous_pi fun i =>
        continuous_const.mul ((continuous_apply i).comp (continuous_apply a))
      continuous_invFun := continuous_pi fun a => continuous_pi fun i =>
        continuous_const.mul ((continuous_apply i).comp (continuous_apply a)) }
  exact e.isCompact_preimage.2 hL

theorem cv_cof (N : ℕ) (hN : 0 < N) :
    ∀ᶠ v in Filter.cofinite, ∀ Y : Fin n → Fin M → Fv F v ⊗[F] E,
      (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v → Y ∈ latV b v := by
  have h := (algebraMap F (Af F) ((N : F)⁻¹)).2
  filter_upwards [h] with v hv Y hY a i k
  have h1 := (mem_lat_iff b N v Y).1 hY a i k
  have hN0 : (N : Fv F v) ≠ 0 := by
    have h0 : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    rw [← map_natCast (algebraMap F (Fv F v)) N]
    exact (map_ne_zero (algebraMap F (Fv F v))).2 h0
  have h2 : (N : Fv F v)⁻¹ ∈ v.adicCompletionIntegers F := by
    have e : evalV F v (algebraMap F (Af F) ((N : F)⁻¹)) = (N : Fv F v)⁻¹ := by
      rw [AlgHom.commutes, map_inv₀, map_natCast]
    rw [← e]
    exact hv
  have h3 := mul_mem h2 h1
  rwa [← mul_assoc, inv_mul_cancel₀ hN0, one_mul] at h3

end Main

section Scale

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) {n M : ℕ}

theorem projFin_scale (t : Ainf F) (X : Fin n → Fin M → AF F ⊗[F] E) :
    projFin ((pairA F t 1 ⊗ₜ[F] (1 : E)) • X) = projFin X := by
  funext a i
  simp only [projFin, Pi.smul_apply, smul_eq_mul, map_mul, Algebra.TensorProduct.map_tmul]
  have : sndA F (pairA F t 1) = 1 := rfl
  rw [this]
  simp [← Algebra.TensorProduct.one_def]

theorem size_scale (t : Ainf F) (c : ℝ) (ht : ∀ w : InfinitePlace F, ‖t w‖ = c)
    (X : Fin n → Fin M → AF F ⊗[F] E) :
    sizeTup b (projInf ((pairA F t 1 ⊗ₜ[F] (1 : E)) • X)) = c * sizeTup b (projInf X) := by
  have e : ∀ a i, projInf ((pairA F t 1 ⊗ₜ[F] (1 : E)) • X) a i =
      (t ⊗ₜ[F] (1 : E)) * projInf X a i := by
    intro a i
    simp only [projInf, Pi.smul_apply, smul_eq_mul, map_mul, Algebra.TensorProduct.map_tmul]
    rfl
  simp only [sizeTup, sizeInf, e, repr_tmul_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun w _ => ?_
  have : (t * (Algebra.TensorProduct.basis (Ainf F) b).repr (projInf X a i) k) w =
      t w * (Algebra.TensorProduct.basis (Ainf F) b).repr (projInf X a i) k w := rfl
  rw [this, norm_mul, ht]

end Scale

theorem box_facts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ), (∀ (N : ℕ) (r : ℝ), 0 < N → IsCompact (box b N r : Set (Fin n → Fin M → AF F ⊗[F] E))) ∧ (∀ C : Set (Fin n → Fin M → AF F ⊗[F] E), IsCompact C → ∃ (N : ℕ) (r : ℝ), 0 < N ∧ 0 < r ∧ C ⊆ box b N r) ∧ ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ → ∀ (N : ℕ) (r x : ℝ) (X : Fin n → Fin M → AF F ⊗[F] E), ((τ (Multiplicative.ofAdd (x)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • X ∈ box b N (Real.exp x * r) ↔ X ∈ box b N r := by
  intro F E _ _ _ _ _ σ hcm d b n M
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  refine ⟨fun N r hN => ?_, fun C hC => exhaust b C hC, fun τ hτ N r x X => ?_⟩
  · have hc := (GlobalTheory.CompanionTheory.SW.Glue.glue_main F E σ hcm d b n M).2.2.2 {Y | sizeTup b Y ≤ r}
      (fun v => {Y | (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v})
      (cinf_cpt b r) (fun v => cv_cpt b N hN v (GlobalTheory.CompanionTheory.SW.LatCpt.latV_compact_open F E σ hcm d b n M v).1)
      (cv_cof b N hN)
    have e : (box b N r : Set (Fin n → Fin M → AF F ⊗[F] E)) =
        {X | projInf X ∈ {Y | sizeTup b Y ≤ r} ∧ ∀ v, projV v (projFin X) ∈
          {Y | (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v}} := by
      ext X
      exact And.comm
    rw [e]
    exact hc
  · obtain ⟨-, θ, hθ, hτx⟩ := hτ
    have hth := (GlobalTheory.CompanionTheory.AdelicRealLine.exists_continuous_real_embedding F hcm.1).2 θ hθ (Real.exp x)
    have hw : ∀ w : InfinitePlace F, ‖θ (Real.exp x) w‖ = Real.exp x := fun w => by
      rw [hth w, abs_of_pos (Real.exp_pos x)]
    rw [hτx x]
    have hp := projFin_scale (E := E) (θ (Real.exp x)) X
    have hs := size_scale b (θ (Real.exp x)) (Real.exp x) hw X
    simp only [box, Set.mem_setOf_eq, hp, hs]
    refine and_congr_right fun _ => ?_
    exact ⟨fun h => le_of_mul_le_mul_left h (Real.exp_pos x),
      fun h => mul_le_mul_of_nonneg_left h (Real.exp_pos x).le⟩

end GlobalTheory.CompanionTheory.SW.BoxF
