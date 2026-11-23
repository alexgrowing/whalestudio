import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.SizeScale

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}

theorem continuous_size (b : Module.Basis (Fin d) F E) :
    Continuous (sizeInf b : Ainf F ⊗[F] E → ℝ) := by
  have : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  unfold sizeInf
  refine continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun v _ => ?_
  have hk : Continuous fun y : Ainf F ⊗[F] E =>
      (Algebra.TensorProduct.basis (Ainf F) b).coord k y :=
    IsModuleTopology.continuous_of_linearMap _
  simp only [← Module.Basis.coord_apply]
  exact continuous_norm.comp ((continuous_apply v).comp hk)

theorem size_nonneg (b : Module.Basis (Fin d) F E) (y : Ainf F ⊗[F] E) : 0 ≤ sizeInf b y :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem tup_nonneg {M n : ℕ} (b : Module.Basis (Fin d) F E) (X : Fin n → Fin M → Ainf F ⊗[F] E) :
    0 ≤ sizeTup b X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => size_nonneg b _

theorem size_add_le (b : Module.Basis (Fin d) F E) (x y : Ainf F ⊗[F] E) :
    sizeInf b (x + y) ≤ sizeInf b x + sizeInf b y := by
  unfold sizeInf
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun v _ => ?_
  rw [map_add]
  exact norm_add_le _ _

theorem size_zero (b : Module.Basis (Fin d) F E) : sizeInf b (0 : Ainf F ⊗[F] E) = 0 := by
  unfold sizeInf
  refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun v _ => ?_
  have h0 : ((0 : Fin d →₀ Ainf F) k) v = 0 := rfl
  rw [map_zero, h0, norm_zero]

theorem size_sum_le {ι : Type} (b : Module.Basis (Fin d) F E) (s : Finset ι)
    (f : ι → Ainf F ⊗[F] E) : sizeInf b (∑ c ∈ s, f c) ≤ ∑ c ∈ s, sizeInf b (f c) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [size_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (size_add_le b _ _).trans (by gcongr)

theorem coord_le_size (b : Module.Basis (Fin d) F E) (y : Ainf F ⊗[F] E) (j : Fin d)
    (v : InfinitePlace F) :
    ‖(Algebra.TensorProduct.basis (Ainf F) b).repr y j v‖ ≤ sizeInf b y := by
  unfold sizeInf
  calc ‖(Algebra.TensorProduct.basis (Ainf F) b).repr y j v‖
      ≤ ∑ w, ‖(Algebra.TensorProduct.basis (Ainf F) b).repr y j w‖ :=
        Finset.single_le_sum
          (f := fun w => ‖(Algebra.TensorProduct.basis (Ainf F) b).repr y j w‖)
          (fun _ _ => norm_nonneg _) (Finset.mem_univ v)
    _ ≤ _ := Finset.single_le_sum
        (f := fun k => ∑ w, ‖(Algebra.TensorProduct.basis (Ainf F) b).repr y k w‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ j)

theorem repr_mul (b : Module.Basis (Fin d) F E) (x y : Ainf F ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis (Ainf F) b).repr (x * y) k =
      ∑ i, ∑ j, (Algebra.TensorProduct.basis (Ainf F) b).repr x i *
        (Algebra.TensorProduct.basis (Ainf F) b).repr y j *
          algebraMap F (Ainf F) (b.repr (b i * b j) k) := by
  set B := Algebra.TensorProduct.basis (Ainf F) b with hB
  have hBB : ∀ i j, B.repr (B i * B j) k = algebraMap F (Ainf F) (b.repr (b i * b j) k) := by
    intro i j
    simp [hB, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.basis_repr_tmul]
  conv_lhs => rw [← B.sum_repr x, ← B.sum_repr y, Finset.sum_mul_sum]
  simp only [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, smul_mul_smul_comm, map_smul,
    Finsupp.smul_apply, hBB, smul_eq_mul]

theorem exists_size_mul_le (b : Module.Basis (Fin d) F E) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x y : Ainf F ⊗[F] E, sizeInf b (x * y) ≤ K * sizeInf b x * sizeInf b y := by
  obtain ⟨S₀, hS₀⟩ := (Set.finite_range (fun p : Fin d × Fin d × Fin d × InfinitePlace F =>
    ‖(algebraMap F (Ainf F) (b.repr (b p.1 * b p.2.1) p.2.2.1)) p.2.2.2‖)).bddAbove
  set S := |S₀| with hS
  have hS0 : 0 ≤ S := abs_nonneg _
  have hs : ∀ i j k v, ‖(algebraMap F (Ainf F) (b.repr (b i * b j) k)) v‖ ≤ S := fun i j k v =>
    (hS₀ ⟨(i, j, k, v), rfl⟩).trans (le_abs_self _)
  refine ⟨(d : ℝ) * d * S, by positivity, fun x y => ?_⟩
  set B := Algebra.TensorProduct.basis (Ainf F) b with hB
  have hpt : ∀ k (v : InfinitePlace F), ‖B.repr (x * y) k v‖ ≤
      (d : ℝ) * S * sizeInf b y * ∑ i, ‖B.repr x i v‖ := by
    intro k v
    have hev : B.repr (x * y) k v =
        ∑ i, ∑ j, B.repr x i v * B.repr y j v * (algebraMap F (Ainf F) (b.repr (b i * b j) k)) v := by
      rw [repr_mul b x y k]
      have := map_sum (Pi.evalRingHom (fun w : InfinitePlace F => w.Completion) v)
        (fun i => ∑ j, B.repr x i * B.repr y j * algebraMap F (Ainf F) (b.repr (b i * b j) k))
        Finset.univ
      refine this.trans (Finset.sum_congr rfl fun i _ => ?_)
      exact map_sum (Pi.evalRingHom (fun w : InfinitePlace F => w.Completion) v) _ _
    rw [hev]
    calc ‖∑ i, ∑ j, B.repr x i v * B.repr y j v * (algebraMap F (Ainf F) (b.repr (b i * b j) k)) v‖
        ≤ ∑ i, ∑ j : Fin d, ‖B.repr x i v‖ * sizeInf b y * S := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [norm_mul, norm_mul]
          exact mul_le_mul (mul_le_mul_of_nonneg_left (coord_le_size b y j v) (norm_nonneg _))
            (hs i j k v) (norm_nonneg _) (mul_nonneg (norm_nonneg _) (size_nonneg b y))
      _ = (d : ℝ) * S * sizeInf b y * ∑ i, ‖B.repr x i v‖ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
  calc sizeInf b (x * y) = ∑ k, ∑ v : InfinitePlace F, ‖B.repr (x * y) k v‖ := rfl
    _ ≤ ∑ k : Fin d, ∑ v : InfinitePlace F, (d : ℝ) * S * sizeInf b y * ∑ i, ‖B.repr x i v‖ :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun v _ => hpt k v
    _ = (d : ℝ) * ((d : ℝ) * S * sizeInf b y * ∑ v : InfinitePlace F, ∑ i, ‖B.repr x i v‖) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Finset.mul_sum]
    _ = (d : ℝ) * d * S * sizeInf b x * sizeInf b y := by
        have : sizeInf b x = ∑ v : InfinitePlace F, ∑ i, ‖B.repr x i v‖ := Finset.sum_comm
        rw [this]; ring

end

theorem size_rmul_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (n M : ℕ) (C : Set (Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E))), IsCompact C → ∃ c : ℝ, 0 < c ∧ ∀ g ∈ C, ∀ X : Fin n → Fin M → Ainf F ⊗[F] E, sizeTup b (rmul (Ainf F) X g) ≤ c * sizeTup b X := by
  intro F E _ _ _ _ _ σ _ d b n M C hC
  obtain ⟨K, hK0, hK⟩ := exists_size_mul_le b
  have hcont : Continuous fun g : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) =>
      ∑ c, ∑ a, sizeInf b (g c a) :=
    continuous_finsetSum _ fun c _ => continuous_finsetSum _ fun a _ =>
      (continuous_size b).comp (continuous_id.matrix_elem c a)
  obtain ⟨D, hD⟩ := (hC.image hcont).bddAbove
  refine ⟨K * |D| + 1, by positivity, fun g hg X => ?_⟩
  have hg' : ∀ c, ∑ a, sizeInf b (g c a) ≤ |D| := fun c =>
    (Finset.single_le_sum (f := fun c => ∑ a, sizeInf b (g c a))
      (fun _ _ => Finset.sum_nonneg fun _ _ => size_nonneg b _) (Finset.mem_univ c)).trans
      ((hD ⟨g, hg, rfl⟩).trans (le_abs_self _))
  calc sizeTup b (rmul (Ainf F) X g)
      = ∑ a, ∑ i, sizeInf b (∑ c, X c i * g c a) := rfl
    _ ≤ ∑ a, ∑ i, ∑ c, K * sizeInf b (X c i) * sizeInf b (g c a) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun i _ =>
          (size_sum_le b _ _).trans (Finset.sum_le_sum fun c _ => hK _ _)
    _ = ∑ i, ∑ c, K * sizeInf b (X c i) * ∑ a, sizeInf b (g c a) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ i, ∑ c, K * sizeInf b (X c i) * |D| :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun c _ =>
          mul_le_mul_of_nonneg_left (hg' c) (mul_nonneg hK0 (size_nonneg b _))
    _ = K * |D| * sizeTup b X := by
        unfold sizeTup
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ (K * |D| + 1) * sizeTup b X := by
        nlinarith [tup_nonneg b X]

end GlobalTheory.CompanionTheory.SW.SizeScale
