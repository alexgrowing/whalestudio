import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ActSingleNeZero
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
import Formalism.RealPlaceAnalysis.FinalF
import Formalism.RealPlaceAnalysis.QuotientSettingHolds

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Jet

section
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n j : ℕ}

def sliceIns (α' : Fin j → Fin n × Fin n) (m : Arr V n 1) : Arr V n (j + 1) :=
  WithLp.toLp 2 (fun α : Fin (j + 1) → Fin n × Fin n =>
    if Fin.tail α = α' then m (fun _ => α 0) else 0)

theorem slice_sliceIns (α' β' : Fin j → Fin n × Fin n) (m : Arr V n 1) :
    sliceLin V n β' (sliceIns α' m) = if β' = α' then m else 0 := by
  apply indexArray_ext
  intro β
  rw [firstPositionSlice_apply]
  have hβ : (fun _ : Fin 1 => β 0) = β := by
    funext i
    rw [Fin.fin_one_eq_zero i]
  simp only [sliceIns, PiLp.toLp_apply, Fin.tail_cons, Fin.cons_zero]
  split_ifs with h
  · rw [hβ]
  · rfl

theorem sliceIns_mem {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V}
    {α' : Fin j → Fin n × Fin n} (hα : ∀ i, ε (α' i).1 ≠ ε (α' i).2) {m : Arr V n 1}
    (hm : m ∈ arrV0 ε E u 1) : sliceIns α' m ∈ arrV0 ε E u (j + 1) := by
  rw [mem_admissibleArrays]
  intro α
  by_cases ht : Fin.tail α = α'
  · have hv : (sliceIns α' m) α = m (fun _ => α 0) := by simp [sliceIns, ht]
    rw [hv]
    by_cases h0 : ε (α 0).1 ≠ ε (α 0).2
    · have hall : ∀ i, ε (α i).1 ≠ ε (α i).2 := by
        intro i
        cases i using Fin.cases with
        | zero => exact h0
        | succ k =>
          have hk := hα k
          rw [← ht] at hk
          simpa [Fin.tail] using hk
      rw [if_pos hall]
      exact admissibleArrays_apply_mem hm _
    · rw [admissibleArrays_apply_eq_zero hm _ (fun h => h0 (h 0))]
      split_ifs <;> exact Submodule.zero_mem _
  · have hv : (sliceIns α' m) α = 0 := by simp [sliceIns, ht]
    rw [hv]
    split_ifs <;> exact Submodule.zero_mem _

theorem slice_mem_highest_jets {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V}
    {F : Arr V n (j + 1)} (hF : F ∈ arrV0 ε E u (j + 1)) (α' : Fin j → Fin n × Fin n) :
    sliceLin V n α' F ∈ arrV0 ε E u 1 := by
  rw [mem_admissibleArrays]
  intro β
  rw [firstPositionSlice_apply]
  split_ifs with h
  · exact admissibleArrays_apply_mem hF _
  · rw [admissibleArrays_apply_eq_zero hF _ (fun h' => h (fun i => by rw [Fin.fin_one_eq_zero i]; simpa using h' 0))]
    exact Submodule.zero_mem _

theorem slice_eq_zero_of_compact {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V}
    {F : Arr V n (j + 1)} (hF : F ∈ arrV0 ε E u (j + 1)) (α' : Fin j → Fin n × Fin n)
    (hα : ¬ ∀ i, ε (α' i).1 ≠ ε (α' i).2) : sliceLin V n α' F = 0 := by
  apply indexArray_ext
  intro β
  rw [firstPositionSlice_apply, admissibleArrays_apply_eq_zero hF _ (fun h => hα (fun i => by simpa using h i.succ))]
  rfl

theorem permute_mem_highest_jets {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V}
    {F : Arr V n j} (hF : F ∈ arrV0 ε E u j) (s : Equiv.Perm (Fin j)) :
    permArr V n s F ∈ arrV0 ε E u j := by
  rw [mem_admissibleArrays]
  intro α
  rw [permutePositions_apply]
  split_ifs with h
  · exact admissibleArrays_apply_mem hF _
  · rw [admissibleArrays_apply_eq_zero hF _ (fun h' => h (fun i => by simpa using h' (s.symm i)))]
    exact Submodule.zero_mem _

private theorem finiteDimensional_arrV0_of_finiteDimensional_kSpan (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (u : V) (h : FiniteDimensional ℂ (kSpan ε E u)) :
    FiniteDimensional ℂ (arrV0 ε E u j) := by
  let ψ : arrV0 ε E u j →ₗ[ℂ] ((Fin j → Fin n × Fin n) → kSpan ε E u) :=
    LinearMap.pi fun α => LinearMap.codRestrict (kSpan ε E u)
      ((LinearMap.proj α ∘ₗ arrOf V n j) ∘ₗ (arrV0 ε E u j).subtype)
      (fun F => by simpa [arrOf] using admissibleArrays_apply_mem F.2 α)
  refine Module.Finite.of_injective ψ ?_
  intro F G hFG
  apply Subtype.ext
  apply indexArray_ext
  intro α
  have h1 := congrArg Subtype.val (congrFun hFG α)
  simpa [ψ, arrOf] using h1

private theorem permArr_inv_permArr (s : Equiv.Perm (Fin j)) (F : Arr V n j) : permArr V n s⁻¹ (permArr V n s F) = F := by
  apply indexArray_ext
  intro α
  rw [permutePositions_apply, permutePositions_apply]
  simp

end

theorem jet_map_eq_zero : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (g : ℝ) (u : V) (j : ℕ), GlRel E → IsUnitary ε E → KHighest ε E (LamOf ε lam) u → FiniteDimensional ℂ (kSpan ε E u) → (∀ a b : Fin n, a < b → ε a ≠ ε b → g ≤ lam a - lam b) → 2 * (n : ℝ) < g → ∀ T : Arr V n (j + 1) →ₗ[ℂ] V, (∀ F ∈ arrV0 ε E u (j + 1), T F ∈ kSpan ε E u) → (∀ c d, ε c = ε d → ∀ F ∈ arrV0 ε E u (j + 1), T (arrE E (j + 1) c d F) = E c d (T F)) → (∀ F ∈ arrV0 ε E u (j + 1), ∀ s : Equiv.Perm (Fin (j + 1)), T (permArr V n s F) = T F) → (∀ F ∈ arrV0 ε E u (j + 1), (∀ α', sliceLin V n α' F ∈ Vminus ε E (LamOf ε lam) u) → T F = 0) → ∀ F ∈ arrV0 ε E u (j + 1), T F = 0 := by
  intro V _ _ n ε E lam g u j hgl hun hhi hfd hgap hg T hT hE hS hM
  have hsplit := typesSplit V n ε E (LamOf ε lam) u hgl hun hhi hfd
  have hstab := admissibleArrays_invariant ε E u (j + 1)
  let K : Submodule ℂ (Arr V n (j + 1)) := arrV0 ε E u (j + 1) ⊓ LinearMap.ker T
  have memK : ∀ G, G ∈ arrV0 ε E u (j + 1) → T G = 0 → G ∈ K := fun G h1 h2 => ⟨h1, h2⟩

  have key : ∀ f ∈ arrV0 ε E u (j + 1), (∀ k ∈ K, ⟪k, f⟫_ℂ = 0) → f = 0 := by
    intro f hf horth

    have hsym : f ∈ symSub V n (j + 1) := by
      rw [mem_symmetricArrays]
      intro s
      have hGW : permArr V n s f - f ∈ arrV0 ε E u (j + 1) := sub_mem (permute_mem_highest_jets hf s) hf
      have hGT : T (permArr V n s f - f) = 0 := by rw [map_sub, hS f hf s, sub_self]
      have hGK : permArr V n s f - f ∈ K := memK _ hGW hGT
      have hG'K : permArr V n s⁻¹ (permArr V n s f - f) ∈ K :=
        memK _ (permute_mem_highest_jets hGW s⁻¹) (by rw [hS _ hGW s⁻¹, hGT])
      have h1 : ⟪permArr V n s f - f, permArr V n s f⟫_ℂ = 0 := by
        rw [← inner_permutePositions s⁻¹, permArr_inv_permArr]
        exact horth _ hG'K
      have h2 : ⟪permArr V n s f - f, f⟫_ℂ = 0 := horth _ hGK
      have h3 : ⟪permArr V n s f - f, permArr V n s f - f⟫_ℂ = 0 := by
        rw [inner_sub_right, h1, h2, sub_self]
      exact sub_eq_zero.mp (inner_self_eq_zero.mp h3)

    have hplus : ∀ α' : Fin j → Fin n × Fin n, sliceLin V n α' f ∈ Vplus ε E (LamOf ε lam) u := by
      intro α'
      by_cases hα : ∀ i, ε (α' i).1 ≠ ε (α' i).2
      · have hmem : sliceLin V n α' f ∈ Vplus ε E (LamOf ε lam) u ⊔ Vminus ε E (LamOf ε lam) u := by
          rw [hsplit.2]
          exact slice_mem_highest_jets hf α'
        obtain ⟨p, hp, m, hm, hpm⟩ := Submodule.mem_sup.mp hmem
        have hm0 : m ∈ arrV0 ε E u 1 := by
          rw [← hsplit.2]
          exact Submodule.mem_sup_right hm
        have hGW : sliceIns α' m ∈ arrV0 ε E u (j + 1) := sliceIns_mem hα hm0
        have hGT : T (sliceIns α' m) = 0 := by
          apply hM _ hGW
          intro β'
          rw [slice_sliceIns]
          split_ifs
          · exact hm
          · exact Submodule.zero_mem _
        have hin : ⟪sliceIns α' m, f⟫_ℂ = 0 := horth _ (memK _ hGW hGT)
        have hsum : ∑ β' : Fin j → Fin n × Fin n,
            ⟪sliceLin V n β' (sliceIns α' m), sliceLin V n β' f⟫_ℂ = ⟪m, sliceLin V n α' f⟫_ℂ := by
          rw [Finset.sum_eq_single α']
          · rw [slice_sliceIns, if_pos rfl]
          · intro b _ hb
            rw [slice_sliceIns, if_neg hb, inner_zero_left]
          · intro h
            exact absurd (Finset.mem_univ _) h
        rw [inner_eq_sum_firstPositionSlice, hsum, ← hpm, inner_add_right] at hin
        have hmp : ⟪m, p⟫_ℂ = 0 := by
          rw [← inner_conj_symm, hsplit.1 p hp m hm, map_zero]
        rw [hmp, zero_add] at hin
        have hm' : m = 0 := inner_self_eq_zero.mp hin
        rw [← hpm, hm', add_zero]
        exact hp
      · rw [slice_eq_zero_of_compact hf α' hα]
        exact Submodule.zero_mem _
    have hN : f ∈ Formalism.REAL.Nset ε E (LamOf ε lam) u j := by
      unfold Formalism.REAL.Nset
      exact ⟨⟨hf, hsym⟩, (Submodule.mem_iInf _).mpr fun α' => Submodule.mem_comap.mpr (hplus α')⟩

    have hCasW : CasK ε (arrE E (j + 1)) f ∈ arrV0 ε E u (j + 1) := by
      rw [compactCasimir_apply]
      refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
      split_ifs with hab
      · exact hstab a b hab _ (hstab b a hab.symm _ hf)
      · exact Submodule.zero_mem _
    have hCasT : T (CasK ε (arrE E (j + 1)) f) = CasK ε E (T f) := by
      rw [compactCasimir_apply, compactCasimir_apply, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs with hab
      · rw [hE a b hab _ (hstab b a hab.symm _ hf), hE b a hab.symm _ hf]
      · exact map_zero T
    have hKf : CasK ε E (T f) = ((ckv ε (LamOf ε lam) : ℝ) : ℂ) • T f :=
      kCasSpan V n ε E (LamOf ε lam) u (glRel_kRel ε E hgl) hhi (T f) (hT f hf)
    have hkK : CasK ε (arrE E (j + 1)) f - ((ckv ε (LamOf ε lam) : ℝ) : ℂ) • f ∈ K :=
      memK _ (sub_mem hCasW (Submodule.smul_mem _ _ hf))
        (by rw [map_sub, map_smul, hCasT, hKf, sub_self])
    have hfk : ⟪f, CasK ε (arrE E (j + 1)) f - ((ckv ε (LamOf ε lam) : ℝ) : ℂ) • f⟫_ℂ = 0 := by
      rw [← inner_conj_symm, horth _ hkK, map_zero]
    have hre : (⟪f, CasK ε (arrE E (j + 1)) f⟫_ℂ).re = ckv ε (LamOf ε lam) * ‖f‖ ^ 2 := by
      rw [inner_sub_right, sub_eq_zero] at hfk
      rw [hfk, inner_smul_right, Complex.re_ofReal_mul, re_inner_self_indexArray]

    have hpos := nPos V n ε E lam g u j hgl hun hhi hfd hgap f hN
    rw [hre] at hpos
    have hcoef : 0 < 2 * ((j : ℝ) + 1) * (g - 2 * (n : ℝ)) := by
      have h1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      have h2 : (0 : ℝ) < g - 2 * (n : ℝ) := by linarith
      positivity
    have h4 : 2 * ((j : ℝ) + 1) * (g - 2 * (n : ℝ)) * ‖f‖ ^ 2 ≤ 0 := by nlinarith
    have h5 : ‖f‖ ^ 2 = 0 := le_antisymm (by nlinarith) (by positivity)
    simpa using h5

  haveI : FiniteDimensional ℂ (arrV0 ε E u (j + 1)) := finiteDimensional_arrV0_of_finiteDimensional_kSpan ε E u hfd
  haveI : FiniteDimensional ℂ K := Submodule.finiteDimensional_of_le inf_le_left
  intro F hF
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.exists_add_mem_mem_orthogonal (K := K) F
  have hzW : z ∈ arrV0 ε E u (j + 1) := by
    have hz' : z = F - y := by rw [hyz]; abel
    rw [hz']
    exact sub_mem hF hy.1
  have hz0 : z = 0 := key z hzW (fun k hk => (Submodule.mem_orthogonal K z).mp hz k hk)
  rw [hyz, hz0, add_zero]
  exact hy.2

end GlobalTheory.Jet
