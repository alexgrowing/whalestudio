import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryLatticeDenominatorHeightBoundProof
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulIntSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatInvariantUnderIntegralLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatSupportBoundedDenominators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCharacterTrivialOnSmallIdeles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatLevelConductorCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardCharacterTrivialImpliesIntegralTraceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDualLatticeBoundedDenominatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAbsMatrixProductLeHeightsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormBoundedByLocalConstantsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixEntriesBoundedAlmostEverywhereStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory.ThetaDenom

theorem std_char_denom : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∃ D : ℕ, 0 < D ∧
    ∀ ξ : F, (∀ t : AF F, t.1 = 0 → (∀ v, ‖evFin F v t‖ ≤ 1) → ψ (algebraMap F (AF F) ξ * t) = 1) →
      ∃ o : 𝓞 F, (D : F) * ξ = o := by
  intro F _ _ ψ hψ
  obtain ⟨D, hD, h⟩ := GlobalTheory.T.trace_dual_lattice_bounded_denominator (F := F)
  refine ⟨D, hD, fun ξ hξ => h ξ fun o => GlobalTheory.T.standard_character_trivial_implies_integral_trace ψ hψ _ fun t ht0 ht1 => ?_⟩
  have e : algebraMap F (AF F) (ξ * o) * t = algebraMap F (AF F) ξ * (algebraMap F (AF F) o * t) := by
    rw [map_mul, mul_assoc]
  rw [e]
  refine hξ _ ?_ fun v => ?_
  · rw [show (algebraMap F (AF F) (o : F) * t).1 = (algebraMap F (AF F) (o : F)).1 * t.1 from rfl, ht0, mul_zero]
  · rw [map_mul, AlgHom.commutes, norm_mul]
    refine mul_le_one₀ ?_ (norm_nonneg _) (ht1 v)
    refine Valued.toNormedField.norm_le_one_iff.2 ?_
    first
      | (rw [show algebraMap F (Fv F v) (o:F) = ((o : F) : v.adicCompletion F) from rfl, HeightOneSpectrum.valuedAdicCompletion_eq_valuation]; exact v.valuation_le_one o)
      | (rw [show algebraMap F (Fv F v) (o:F) = ((o : F) : v.adicCompletion F) from rfl, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact v.valuation_le_one o)
      | (exact (HeightOneSpectrum.coe_mem_adicCompletionIntegers v o))

open Formalism.UG in

theorem transport_denom : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (e : Matrix (Fin n) (Fin d) (AF F ⊗[F] E) ≃ₗ[AF F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)),
    ∃ C : ℝ, ∀ (g : GL (Fin n) (AF F ⊗[F] E)) (h : GL (Fin d) (AF F ⊗[F] E)), ∃ N : ℕ, 0 < N ∧
      (N : ℝ) ≤ C * ((heightGL F g : ℝ) * heightGL F h) ∧
      ∀ (M : ℕ) (y : Fin n × Fin d → AF F), IsMulInt F (M * N) y →
        IsMulInt F M (e ((g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * e.symm (0, y) * (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E))ᵀ)).1 ∧
        IsMulInt F M (e ((g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * e.symm (0, y) * (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E))ᵀ)).2 := by
  intro F E _ _ _ _ _ n d e
  classical
  set Y : Fin n × Fin d → Matrix (Fin n) (Fin d) (AF F ⊗[F] E) :=
    fun j => e.symm (0, fun k => if j = k then 1 else 0) with hY
  let f1 : Fin n × Fin d → (Matrix (Fin n) (Fin d) (AF F ⊗[F] E) →ₗ[AF F] AF F) :=
    fun i => (LinearMap.proj i).comp ((LinearMap.fst (AF F) _ _).comp e.toLinearMap)
  let f2 : Fin n × Fin d → (Matrix (Fin n) (Fin d) (AF F ⊗[F] E) →ₗ[AF F] AF F) :=
    fun i => (LinearMap.proj i).comp ((LinearMap.snd (AF F) _ _).comp e.toLinearMap)
  choose K1 hK1f hK11 hK1 using fun i => GlobalTheory.T.linear_form_bounded_by_local_constants (f1 i)
  choose K2 hK2f hK21 hK2 using fun i => GlobalTheory.T.linear_form_bounded_by_local_constants (f2 i)
  choose KY hKYf hKY1 hKY using fun j => GlobalTheory.T.matrix_entries_bounded_almost_everywhere (Y j)
  have prod_one : ∀ (K : Fin n × Fin d → HeightOneSpectrum (𝓞 F) → ℝ≥0), (∀ i v, 1 ≤ K i v) →
      ∀ v, 1 ≤ ∏ i, K i v := fun K hK v => Finset.one_le_prod' fun i _ => hK i v
  have prod_fin : ∀ (K : Fin n × Fin d → HeightOneSpectrum (𝓞 F) → ℝ≥0), (∀ i, (Function.mulSupport (K i)).Finite) →
      (Function.mulSupport fun v => ∏ i, K i v).Finite := fun K hK =>
    ((Finset.univ : Finset (Fin n × Fin d)).finite_toSet.biUnion fun i _ => hK i).subset
      (Finset.mulSupport_prod _ _)
  have single_le : ∀ (K : Fin n × Fin d → HeightOneSpectrum (𝓞 F) → ℝ≥0), (∀ i v, 1 ≤ K i v) →
      ∀ i v, K i v ≤ ∏ i, K i v := fun K hK i v => Finset.single_le_prod' (fun j _ => hK j v) (Finset.mem_univ i)
  set Ka : HeightOneSpectrum (𝓞 F) → ℝ≥0 := fun v => (∏ i, K1 i v) * (∏ i, K2 i v) * ∏ j, KY j v with hKa
  have hKa1 : ∀ v, 1 ≤ Ka v := fun v => one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (prod_one K1 hK11 v) (prod_one K2 hK21 v)) (prod_one KY hKY1 v)
  have hKaf : (Function.mulSupport Ka).Finite :=
    ((((prod_fin K1 hK1f).union (prod_fin K2 hK2f)).subset (Function.mulSupport_mul _ _)).union
      (prod_fin KY hKYf)).subset (Function.mulSupport_mul _ _)
  have hle1 : ∀ i j v, K1 i v * KY j v ≤ Ka v := fun i j v =>
    calc K1 i v * KY j v ≤ (∏ i, K1 i v) * ∏ j, KY j v := mul_le_mul' (single_le K1 hK11 i v) (single_le KY hKY1 j v)
      _ ≤ Ka v := by
        show (∏ i, K1 i v) * ∏ j, KY j v ≤ (∏ i, K1 i v) * (∏ i, K2 i v) * ∏ j, KY j v
        rw [mul_right_comm]
        exact le_mul_of_one_le_right' (prod_one K2 hK21 v)
  have hle2 : ∀ i j v, K2 i v * KY j v ≤ Ka v := fun i j v =>
    calc K2 i v * KY j v ≤ (∏ i, K2 i v) * ∏ j, KY j v := mul_le_mul' (single_le K2 hK21 i v) (single_le KY hKY1 j v)
      _ ≤ Ka v := by
        show (∏ i, K2 i v) * ∏ j, KY j v ≤ (∏ i, K1 i v) * (∏ i, K2 i v) * ∏ j, KY j v
        exact mul_le_mul_left (le_mul_of_one_le_left' (prod_one K1 hK11 v)) _
  refine ⟨((∏ᶠ v, Ka v : ℝ≥0) : ℝ), fun g h => ?_⟩
  set B : HeightOneSpectrum (𝓞 F) → ℝ≥0 :=
    fun v => Ka v * htFin F v (bc (compFin F E v) g) * htFin F v (bc (compFin F E v) h) with hB
  have hB1 : ∀ v, 1 ≤ B v := fun v =>
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (hKa1 v) (one_le_htOf _ _)) (one_le_htOf _ _)
  have hgf := finite_mulSupport_htFin F g
  have hhf := finite_mulSupport_htFin F h
  have hBf : (Function.mulSupport B).Finite :=
    (((hKaf.union hgf).subset (Function.mulSupport_mul _ _)).union hhf).subset (Function.mulSupport_mul _ _)
  obtain ⟨N, hN, hNle, hNint⟩ := GlobalTheory.SmoothForms.denom_global B hB1 hBf
  have hfin : ∀ {m : ℕ} (k : GL (Fin m) (AF F ⊗[F] E)), ∏ᶠ v, htFin F v (bc (compFin F E v) k) ≤ heightGL F k :=
    fun k => by
      unfold heightGL
      exact le_mul_of_one_le_left' (Finset.one_le_prod' fun _ _ => one_le_htOf _ _)
  refine ⟨N, hN, ?_, ?_⟩
  · have e1 : ∏ᶠ v, B v = (∏ᶠ v, Ka v) * (∏ᶠ v, htFin F v (bc (compFin F E v) g)) *
        ∏ᶠ v, htFin F v (bc (compFin F E v) h) := by
      rw [hB, finprod_mul_distrib ((hKaf.union hgf).subset (Function.mulSupport_mul _ _)) hhf,
        finprod_mul_distrib hKaf hgf]
    have : (N : ℝ≥0) ≤ (∏ᶠ v, Ka v) * (heightGL F g * heightGL F h) := by
      refine hNle.trans ?_
      rw [e1, mul_assoc]
      exact mul_le_mul_right (mul_le_mul' (hfin g) (hfin h)) _
    exact_mod_cast this
  intro M y hy
  set L : (Fin n × Fin d → AF F) →ₗ[AF F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
    e.toLinearMap ∘ₗ sand (g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) ∘ₗ
      e.symm.toLinearMap ∘ₗ LinearMap.inr (AF F) _ _ with hL
  have hLy : e ((g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * e.symm (0, y) * (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E))ᵀ) =
      ∑ j, y j • L (fun k => if j = k then 1 else 0) := LinearMap.pi_apply_eq_sum_univ L y
  have hsz : ∀ j v, (Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v
      (sand (g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) (Y j) p.1 p.2))) ≤
      htFin F v (bc (compFin F E v) g) * KY j v * htFin F v (bc (compFin F E v) h) := fun j v =>
    Finset.sup_le fun p _ => (GlobalTheory.T.finite_abs_matrix_product_le_heights g (Y j) h v p.1 p.2).trans
      (mul_le_mul_left (mul_le_mul_right (hKY j v) _) _)
  have hcomp : ∀ t : Fin n × Fin d → AF F, (∀ j v, ‖evFin F v (t j)‖₊ ≤ B v) →
      (∑ j, y j * t j).1 = 0 ∧ ∀ v, ‖evFin F v (∑ j, y j * t j)‖ ≤ ‖(M : Fv F v)‖ := by
    intro t ht
    refine ⟨?_, fun v => ?_⟩
    · change fstA F (∑ j, y j * t j) = 0
      rw [map_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [map_mul]
      change (y j).1 * _ = 0
      rw [hy.1 j, zero_mul]
    · rw [map_sum]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun j _ => ?_
      rw [map_mul, norm_mul]
      have h1 := hy.2 v j
      have h2 := hNint v (evFin F v (t j)) (ht j v)
      rw [Nat.cast_mul, norm_mul] at h1
      rw [norm_mul] at h2
      calc ‖evFin F v (y j)‖ * ‖evFin F v (t j)‖ ≤ ‖(M : Fv F v)‖ * ‖(N : Fv F v)‖ * ‖evFin F v (t j)‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = ‖(M : Fv F v)‖ * (‖(N : Fv F v)‖ * ‖evFin F v (t j)‖) := mul_assoc _ _ _
        _ ≤ ‖(M : Fv F v)‖ * 1 := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
        _ = ‖(M : Fv F v)‖ := mul_one _
  have htB : ∀ (f : Matrix (Fin n) (Fin d) (AF F ⊗[F] E) →ₗ[AF F] AF F) (K : HeightOneSpectrum (𝓞 F) → ℝ≥0),
      (∀ X v, ‖evFin F v (f X)‖₊ ≤ K v * Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v (X p.1 p.2))) →
      (∀ j v, K v * KY j v ≤ Ka v) → ∀ j v,
      ‖evFin F v (f (sand (g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) (Y j)))‖₊ ≤ B v := by
    intro f K hf hK j v
    refine (hf _ v).trans ?_
    refine (mul_le_mul_right (hsz j v) _).trans ?_
    calc K v * (htFin F v (bc (compFin F E v) g) * KY j v * htFin F v (bc (compFin F E v) h)) =
        K v * KY j v * htFin F v (bc (compFin F E v) g) * htFin F v (bc (compFin F E v) h) := by ring
      _ ≤ B v := mul_le_mul_left (mul_le_mul_left (hK j v) _) _
  refine ⟨⟨fun i => ?_, fun v i => ?_⟩, ⟨fun i => ?_, fun v i => ?_⟩⟩
  all_goals rw [hLy]
  all_goals simp only [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
  · exact (hcomp _ fun j v => htB (f1 i) (K1 i) (hK1 i) (fun j v => hle1 i j v) j v).1
  · exact (hcomp _ fun j v => htB (f1 i) (K1 i) (hK1 i) (fun j v => hle1 i j v) j v).2 v
  · exact (hcomp _ fun j v => htB (f2 i) (K2 i) (hK2 i) (fun j v => hle2 i j v) j v).1
  · exact (hcomp _ fun j v => htB (f2 i) (K2 i) (hK2 i) (fun j v => hle2 i j v) j v).2 v

end GlobalTheory.ThetaDenom

end
