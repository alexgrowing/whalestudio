import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DHRealAdSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousSlice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix
open scoped Classical

noncomputable section
namespace GlobalTheory.SobClass.Weight
open GlobalTheory.SobClass GlobalTheory.ArchUniq.Coord

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem norm_dH_mul {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (i : κ) (e : mixedEmbedding.mixedSpace F)
    (Φ : (κ → AF F) → ℂ) (z : κ → AF F) :
    ‖dH ψ ((0, archInc F (Pi.single i e)) : (κ → AF F) × (κ → AF F)) Φ z‖ =
      2 * Real.pi * |Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (z i) * e)| * ‖Φ z‖ := by
  set T : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (z i) * e) with hT
  set a : κ → AF F := archInc F (Pi.single i e) with ha
  have key : (fun t : ℝ => schr ψ (realAd F t • ((0, a) : (κ → AF F) × (κ → AF F))) Φ z) =
      fun t : ℝ => Complex.exp (-(2 * Real.pi * Complex.I) * T * t) * Φ z := by
    funext t
    simp only [schr, Prod.smul_fst, Prod.smul_snd, smul_zero, zero_dotProduct, mul_zero, add_zero]
    have hA : At (evI F) (z ⬝ᵥ (realAd F t • a)) := by
      intro u hu
      simp only [dotProduct, smul_eq_mul, Pi.smul_apply, Finset.mul_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      have := at_archInc (Pi.single i e) j u hu
      simp only [smul_eq_mul] at this
      calc _ = z j * realAd F t * (u * archInc F (Pi.single i e) j) := by rw [ha]; ring
        _ = 0 := by rw [this, mul_zero]
    have hE : evI F (z ⬝ᵥ (realAd F t • a)) = t • (evI F (z i) * e) := by
      rw [evI_eq]
      simp only [dotProduct, smul_eq_mul, Pi.smul_apply, map_sum, map_mul, ← evI_eq, evI_realAd, ha, evI_archInc]
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp), Pi.single_eq_same, Algebra.smul_def]
      ring
    rw [hψ.2.2 _ hA, hE, map_smul, ← hT, smul_eq_mul]
    congr 2
    push_cast
    ring
  have hd : HasDerivAt (fun t : ℝ => Complex.exp (-(2 * Real.pi * Complex.I) * T * t) * Φ z)
      (Complex.exp (-(2 * Real.pi * Complex.I) * T * ((0 : ℝ) : ℂ)) * (-(2 * Real.pi * Complex.I) * T * 1) * Φ z) 0 :=
    (((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul (-(2 * Real.pi * Complex.I) * T)).cexp).mul_const (Φ z)
  unfold dH
  rw [key, hd.deriv]
  simp [abs_of_pos Real.pi_pos]

variable (F) in
theorem exists_family : ∃ (n : ℕ) (e : Fin n → mixedEmbedding.mixedSpace F) (c : ℝ), 0 ≤ c ∧ (∀ j, ‖e j‖ ≤ 1) ∧
    ∀ x : mixedEmbedding.mixedSpace F, ‖x‖ ≤ c * ∑ j, |Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x * e j)| := by
  let b := Module.finBasis ℝ (mixedEmbedding.mixedSpace F)
  let e : Fin _ → mixedEmbedding.mixedSpace F := fun j => (1 + ‖b j‖)⁻¹ • b j
  have hp : ∀ j, 0 < 1 + ‖b j‖ := fun j => by positivity
  let f : mixedEmbedding.mixedSpace F →ₗ[ℝ] (Fin _ → ℝ) :=
    LinearMap.pi fun j => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) ∘ₗ LinearMap.mulRight ℝ (e j)
  have hf : ∀ x j, f x j = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x * e j) := fun x j => rfl
  have hker : LinearMap.ker f = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun x hx => eq_zero_of_trace x fun y => ?_
    have h1 : ∀ j, Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x * b j) = 0 := by
      intro j
      have := hf x j
      rw [hx, Pi.zero_apply, mul_smul_comm, map_smul, smul_eq_mul] at this
      exact (mul_eq_zero.1 this.symm).resolve_left (inv_pos.2 (hp j)).ne'
    rw [← b.sum_repr y, Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [mul_smul_comm, map_smul, h1, smul_zero]
  obtain ⟨K, -, hK⟩ := f.exists_antilipschitzWith hker
  refine ⟨_, e, K, K.2, fun j => ?_, fun x => ?_⟩
  · simp only [e]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hp j)), inv_mul_le_iff₀ (hp j)]
    linarith
  · refine (ZeroHomClass.bound_of_antilipschitz f hK x).trans (mul_le_mul_of_nonneg_left ?_ K.2)
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _)).2 fun j => ?_
    rw [hf, Real.norm_eq_abs]
    exact Finset.single_le_sum (f := fun j => |Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x * e j)|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ j)

theorem weight_le_words : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ N : ℕ, ∃ (L : Finset (List ((κ → AF F) × (κ → AF F)))) (K : ℝ), (∀ l ∈ L, l.length ≤ N ∧ ∀ w ∈ l, IsArchUnit w) ∧ ∀ (Φ : (κ → AF F) → ℂ) (z : κ → AF F), ‖Φ z‖ * (1 + ∑ i, ‖evI F (z i)‖) ^ N ≤ K * ∑ l ∈ L, ‖wordH ψ l Φ z‖ := by
  intro F _ _ κ _ ψ hψ N
  obtain ⟨n, e, c, hc, he, hx⟩ := exists_family F
  let m : κ × Fin n → (κ → AF F) × (κ → AF F) := fun p => (0, archInc F (Pi.single p.1 (e p.2)))
  have hm : ∀ p, IsArchUnit (m p) := fun p => isArchUnit_mul _ fun i => by
    by_cases h : i = p.1
    · subst h; simpa using he p.2
    · simp [h]
  have hw : ∀ (Φ : (κ → AF F) → ℂ) (z : κ → AF F),
      ‖Φ z‖ * ∑ i, ‖evI F (z i)‖ ≤ c * ∑ p, ‖dH ψ (m p) Φ z‖ := by
    intro Φ z
    rw [Fintype.sum_prod_type, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    refine (mul_le_mul_of_nonneg_left (hx _) (norm_nonneg _)).trans ?_
    rw [mul_left_comm, Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) hc
    simp only [m]
    rw [norm_dH_mul hψ]
    have h1 := mul_nonneg (norm_nonneg (Φ z))
      (abs_nonneg (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (z i) * e j)))
    nlinarith [Real.two_le_pi]
  suffices h : ∃ (L : Finset (List ((κ → AF F) × (κ → AF F)))) (K : ℝ), 0 ≤ K ∧
      (∀ l ∈ L, l.length ≤ N ∧ ∀ w ∈ l, IsArchUnit w) ∧ ∀ (Φ : (κ → AF F) → ℂ) (z : κ → AF F),
      ‖Φ z‖ * (1 + ∑ i, ‖evI F (z i)‖) ^ N ≤ K * ∑ l ∈ L, ‖wordH ψ l Φ z‖ by
    obtain ⟨L, K, -, h⟩ := h
    exact ⟨L, K, h⟩
  induction N with
  | zero => exact ⟨{[]}, 1, zero_le_one, by simp, by simp⟩
  | succ N ih =>
    obtain ⟨L, K, hK, hL, h⟩ := ih
    let L' := L ∪ Finset.univ.biUnion fun p => L.image (List.cons (m p))
    refine ⟨L', K * (1 + c * Fintype.card (κ × Fin n)), by positivity, fun l hl => ?_, fun Φ z => ?_⟩
    · rcases Finset.mem_union.1 hl with hl | hl
      · exact ⟨(hL l hl).1.trans (Nat.le_succ _), (hL l hl).2⟩
      · obtain ⟨p, -, hl⟩ := Finset.mem_biUnion.1 hl
        obtain ⟨l, hl', rfl⟩ := Finset.mem_image.1 hl
        refine ⟨by simpa using (hL l hl').1, fun w hw => ?_⟩
        rcases List.mem_cons.1 hw with rfl | hw
        · exact hm p
        · exact (hL l hl').2 w hw
    · set S := ∑ l ∈ L', ‖wordH ψ l Φ z‖ with hS
      have h1 : ∑ l ∈ L, ‖wordH ψ l Φ z‖ ≤ S :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun _ _ _ => norm_nonneg _
      have h2 : ∀ p, ∑ l ∈ L, ‖dH ψ (m p) (wordH ψ l Φ) z‖ ≤ S := by
        intro p
        have := Finset.sum_image (s := L) (g := List.cons (m p)) (f := fun l => ‖wordH ψ l Φ z‖)
          (fun _ _ _ _ h => List.cons_injective h)
        simp only [wordH_cons] at this
        rw [← this]
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun l hl => Finset.mem_union_right _ ?_)
          fun _ _ _ => norm_nonneg _
        exact Finset.mem_biUnion.2 ⟨p, Finset.mem_univ _, hl⟩
      have h3 : (∑ l ∈ L, ‖wordH ψ l Φ z‖) * ∑ i, ‖evI F (z i)‖ ≤ c * (Fintype.card (κ × Fin n) * S) := by
        rw [Finset.sum_mul]
        refine (Finset.sum_le_sum fun l _ => hw (wordH ψ l Φ) z).trans ?_
        rw [← Finset.mul_sum, Finset.sum_comm]
        refine mul_le_mul_of_nonneg_left ((Finset.sum_le_sum fun p _ => h2 p).trans ?_) hc
        simp
      have h0 : 0 ≤ 1 + ∑ i, ‖evI F (z i)‖ := by positivity
      calc _ = (‖Φ z‖ * (1 + ∑ i, ‖evI F (z i)‖) ^ N) * (1 + ∑ i, ‖evI F (z i)‖) := by ring
        _ ≤ (K * ∑ l ∈ L, ‖wordH ψ l Φ z‖) * (1 + ∑ i, ‖evI F (z i)‖) := mul_le_mul_of_nonneg_right (h Φ z) h0
        _ = K * (∑ l ∈ L, ‖wordH ψ l Φ z‖ + (∑ l ∈ L, ‖wordH ψ l Φ z‖) * ∑ i, ‖evI F (z i)‖) := by ring
        _ ≤ K * (S + c * (Fintype.card (κ × Fin n) * S)) := mul_le_mul_of_nonneg_left (add_le_add h1 h3) hK
        _ = _ := by ring

end GlobalTheory.SobClass.Weight
end
