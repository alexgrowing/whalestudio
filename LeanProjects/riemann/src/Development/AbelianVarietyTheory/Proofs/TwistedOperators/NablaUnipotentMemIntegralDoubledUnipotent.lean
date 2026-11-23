import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagOneNegOneConjAntidiagonalStabilizerMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalFixingDoublingMatrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.SplitDblNab

open Matrix

local notation:70 A:70 " ⬝ₘ " B:71 => @HMul.hMul _ _ _ Matrix.instHMulOfFintypeOfMulOfAddCommMonoid A B

section Generic

variable {A : Type} [CommRing A] {ι : Type} [Fintype ι] [DecidableEq ι]

def blkN (N : Matrix ι ι A) : Matrix (ι ⊕ ι) (ι ⊕ ι) A := fromBlocks (1 + N) N (-N) (1 - N)

theorem blkN_mul_neg (N : Matrix ι ι A) : blkN N * blkN (-N) = 1 := by
  rw [blkN, blkN, fromBlocks_multiply, ← fromBlocks_one]
  congr 1 <;> noncomm_ring

theorem neg_mul_blkN (N : Matrix ι ι A) : blkN (-N) * blkN N = 1 := by
  have h := blkN_mul_neg (-N)
  rwa [neg_neg] at h

theorem blkN_eq (N : Matrix ι ι A) :
    1 + (fromRows (1 : Matrix ι ι A) (-1) * N) * (fromRows (1 : Matrix ι ι A) 1)ᵀ = blkN N := by
  rw [fromRows_mul, transpose_fromRows, fromRows_mul_fromCols, ← fromBlocks_one, fromBlocks_add, blkN]
  simp [sub_eq_add_neg]

theorem blkN_anti (N : Matrix ι ι A) : blkN N ⬝ₘ fromRows (1 : Matrix ι ι A) (-1) = fromRows 1 (-1) := by
  rw [blkN, fromBlocks_mul_fromRows]
  congr 1 <;> noncomm_ring

theorem blkN_diag (N : Matrix ι ι A) :
    blkN N ⬝ₘ fromRows (1 : Matrix ι ι A) 1 = fromRows 1 1 + fromRows (1 : Matrix ι ι A) (-1) ⬝ₘ (N + N) := by
  rw [blkN, fromBlocks_mul_fromRows, fromRows_mul]
  ext (i | i) j <;> simp <;> ring

theorem blkN_unitary (s : A →+* A) (J N : Matrix ι ι A) (h : Nᵀ * J + J * N.map s = 0) :
    (blkN N)ᵀ * dbl J * (blkN N).map s = dbl J := by
  have h1 : (1 + N).map s = 1 + N.map s := by
    rw [Matrix.map_add _ (map_add s), Matrix.map_one _ (map_zero s) (map_one s)]
  have h2 : (1 - N).map s = 1 - N.map s := by
    rw [Matrix.map_sub _ (map_sub s), Matrix.map_one _ (map_zero s) (map_one s)]
  have h3 : (-N).map s = - N.map s := by ext i j; simp
  rw [blkN, fromBlocks_map, fromBlocks_transpose, dbl, fromBlocks_multiply, fromBlocks_multiply, h1, h2, h3,
    transpose_add, transpose_sub, transpose_neg, transpose_one]
  generalize Nᵀ = P at h ⊢
  generalize N.map s = Q at h ⊢
  congr 1
  · calc _ = J + (P * J + J * Q) := by noncomm_ring
      _ = J := by rw [h, add_zero]
  · calc _ = P * J + J * Q := by noncomm_ring
      _ = 0 := h
  · calc _ = P * J + J * Q := by noncomm_ring
      _ = 0 := h
  · calc _ = -J + (P * J + J * Q) := by noncomm_ring
      _ = -J := by rw [h, add_zero]

theorem skew_block (s : A →+* A) (J K K' : Matrix ι ι A) (a c : A) (ha : s a = a) (hc : s c = -c)
    (hKK : K * K' = 1) (hKK' : K' * K = 1) (hK : Kᵀ * J * K.map s = J) (hK' : K'ᵀ * J * K'.map s = J) :
    (a • ((1 - c) • (K - 1) - (1 + c) • (K' - 1)))ᵀ * J +
      J * (a • ((1 - c) • (K - 1) - (1 + c) • (K' - 1))).map s = 0 := by
  have e1 : J * K.map s = K'ᵀ * J := by
    calc J * K.map s = (K * K')ᵀ * J * K.map s := by rw [hKK, transpose_one, Matrix.one_mul]
      _ = K'ᵀ * (Kᵀ * J * K.map s) := by rw [transpose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hK]
  have e2 : J * K'.map s = Kᵀ * J := by
    calc J * K'.map s = (K' * K)ᵀ * J * K'.map s := by rw [hKK', transpose_one, Matrix.one_mul]
      _ = Kᵀ * (K'ᵀ * J * K'.map s) := by rw [transpose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hK']
  have e3 : (a • ((1 - c) • (K - 1) - (1 + c) • (K' - 1))).map s =
      a • ((1 + c) • (K.map s - 1) - (1 - c) • (K'.map s - 1)) := by
    ext i j
    have h1 : s ((1 : Matrix ι ι A) i j) = (1 : Matrix ι ι A) i j :=
      congrFun (congrFun (Matrix.map_one s (map_zero _) (map_one _)) i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, map_mul, map_sub, map_add, map_one,
      ha, hc, h1]
    ring
  rw [e3]
  simp only [transpose_smul, transpose_sub, transpose_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, e1, e2]
  rw [← smul_add]
  simp

theorem blkN_mulVec_inl (N : Matrix ι ι A) (z : ι ⊕ ι → A) :
    (fun i => (blkN N *ᵥ z) (Sum.inl i)) =
      (fun i => z (Sum.inl i)) + N *ᵥ (fun i => z (Sum.inl i)) + N *ᵥ (fun i => z (Sum.inr i)) := by
  rw [blkN, fromBlocks_mulVec, add_mulVec, one_mulVec]
  rfl

theorem blkN_mulVec_inr (N : Matrix ι ι A) (z : ι ⊕ ι → A) :
    (fun i => (blkN N *ᵥ z) (Sum.inr i)) =
      -(N *ᵥ (fun i => z (Sum.inl i))) + ((fun i => z (Sum.inr i)) - N *ᵥ (fun i => z (Sum.inr i))) := by
  rw [blkN, fromBlocks_mulVec, sub_mulVec, one_mulVec, neg_mulVec]
  rfl

theorem blkN_sub_one (N : Matrix ι ι A) : blkN N - 1 = fromBlocks N N (-N) (-N) := by
  ext (i | i) (j | j) <;> simp [blkN, Matrix.one_apply]

end Generic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem smul_mem_latAt_of_int {d : ℕ} (W : Spc F E d) (v : Pl F) {x : AF F}
    (hx : evFin F v x ∈ v.adicCompletionIntegers F) {y : Fin d → AE F E}
    (hy : y ∈ GlobalTheory.InertSph.latAt W v) : x • y ∈ GlobalTheory.InertSph.latAt W v := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hv, y, hy, rfl⟩ := hz
    rw [smul_smul]
    refine AddSubgroup.subset_closure ⟨x * a, ?_, ?_, y, hy, rfl⟩
    · intro u hu
      rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u a, ha u hu, mul_zero]
    · rw [map_mul]
      exact mul_mem hx hv
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem evFin_invTwo_mem (v : Pl F) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) :
    evFin F v (⅟(2 : AF F)) ∈ v.adicCompletionIntegers F := by
  have h : evFin F v (⅟(2 : AF F)) * algebraMap F (Fv F v) (algebraMap (𝓞 F) F 2) = 1 := by
    rw [map_ofNat, map_ofNat, ← map_ofNat (evFin F v) 2, ← map_mul, invOf_mul_self, map_one]
  have hv : Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F 2)) = 1 := by
    have := v.valuedAdicCompletion_eq_valuation' (K := F) (algebraMap (𝓞 F) F 2)
    rw [HeightOneSpectrum.valuation_of_algebraMap, (HeightOneSpectrum.intValuation_eq_one_iff).2 h2] at this
    exact this
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h' := congrArg (Valued.v : v.adicCompletion F → _) h
  rw [map_mul, map_one, hv, mul_one] at h'
  exact h'.le

theorem half_smul_mem {d : ℕ} (W : Spc F E d) (v : Pl F) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) {y : Fin d → AE F E}
    (hy : y ∈ GlobalTheory.InertSph.latAt W v) : (GlobalTheory.SplitDblGen.half : AE F E) • y ∈ GlobalTheory.InertSph.latAt W v := by
  rw [GlobalTheory.SplitDblGen.half, algebraMap_smul]
  exact smul_mem_latAt_of_int W v (evFin_invTwo_mem v h2) hy

theorem nMat_mem_NabD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (W : Spc F E d) (v : Pl F), (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ c : AE F E, cA σ c = -c → (∀ z ∈ GlobalTheory.InertSph.latAt W v, c • z ∈ GlobalTheory.InertSph.latAt W v) →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ W v, ∃ n ∈ GlobalTheory.InertDbl.NabD σ W v,
      GlobalTheory.InertDbl.matD n = GlobalTheory.SplitDblGen.nMat c (mat k) (mat k⁻¹) := by
  intro F E _ _ _ _ _ σ d W v h2 c hc hcL k hk
  set N := GlobalTheory.SplitDblGen.splitDoublingNBlock c (mat k) (mat k⁻¹) with hN
  have hKK : mat k * mat k⁻¹ = 1 := congrArg Units.val (mul_inv_cancel (k : GL (Fin d) (AE F E)))
  have hKK' : mat k⁻¹ * mat k = 1 := congrArg Units.val (inv_mul_cancel (k : GL (Fin d) (AE F E)))
  have hhalf : (cA σ) (GlobalTheory.SplitDblGen.half : AE F E) = GlobalTheory.SplitDblGen.half := (cA σ).commutes _
  have hsk : Nᵀ * incM F W.J + incM F W.J * N.map (cA σ : AE F E →+* AE F E) = 0 :=
    skew_block (cA σ : AE F E →+* AE F E) (incM F W.J) (mat k) (mat k⁻¹) _ c
      (by simp only [RingHom.coe_coe, map_mul, hhalf]) hc hKK hKK' k.2 (k⁻¹).2
  have hNL : ∀ z ∈ GlobalTheory.InertSph.latAt W v, N *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
    intro z hz
    have a1 : (mat k - 1) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
      rw [sub_mulVec, one_mulVec]; exact sub_mem (hk.2 z hz).1 hz
    have a2 : (mat k⁻¹ - 1) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
      rw [sub_mulVec, one_mulVec]; exact sub_mem (hk.2 z hz).2 hz
    rw [hN, GlobalTheory.SplitDblGen.splitDoublingNBlock, smul_mulVec, mul_smul, mul_smul, sub_mulVec, smul_mulVec, smul_mulVec, sub_smul,
      add_smul, one_smul, one_smul]
    exact half_smul_mem W v h2 (half_smul_mem W v h2 (half_smul_mem W v h2
      (sub_mem (sub_mem a1 (hcL _ a1)) (add_mem a2 (hcL _ a2)))))
  have hblk : ∀ M : Matrix (Fin d) (Fin d) (AE F E), (∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
      ∀ z ∈ GlobalTheory.InertDbl.latAtD W v, blkN M *ᵥ z ∈ GlobalTheory.InertDbl.latAtD W v := by
    intro M hM z hz
    refine ⟨?_, ?_⟩
    · rw [blkN_mulVec_inl]; exact add_mem (add_mem hz.1 (hM _ hz.1)) (hM _ hz.2)
    · rw [blkN_mulVec_inr]; exact add_mem (neg_mem (hM _ hz.1)) (sub_mem hz.2 (hM _ hz.2))
  refine ⟨⟨⟨blkN N, blkN (-N), blkN_mul_neg N, neg_mul_blkN N⟩,
    blkN_unitary (cA σ : AE F E →+* AE F E) _ N hsk⟩, ⟨⟨fun u hu => ?_, fun z hz => ⟨hblk N hNL z hz, ?_⟩⟩,
      blkN_anti N, N + N, blkN_diag N⟩, (blkN_eq N).symm⟩
  · have b1 : u • (mat k - 1) = 0 := hk.1 u hu
    have b2 : u • (mat k⁻¹ - 1) = 0 := by
      have e1 : mat k⁻¹ - 1 = -(mat k⁻¹ * (mat k - 1)) := by
        rw [Matrix.mul_sub, hKK', Matrix.mul_one, neg_sub]
      rw [e1, smul_neg, ← Matrix.mul_smul, b1, Matrix.mul_zero, neg_zero]
    have b3 : u • N = 0 := by
      rw [hN, GlobalTheory.SplitDblGen.splitDoublingNBlock, smul_comm u, smul_sub u, smul_comm u, smul_comm u (1 + c), b1, b2, smul_zero,
        smul_zero, sub_zero, smul_zero]
    show u • (blkN N - 1) = 0
    rw [blkN_sub_one, fromBlocks_smul, smul_neg, b3, neg_zero, fromBlocks_zero]
  · exact hblk (-N) (fun y hy => by rw [neg_mulVec]; exact neg_mem (hNL y hy)) z hz

end GlobalTheory.SplitDblNab
end
