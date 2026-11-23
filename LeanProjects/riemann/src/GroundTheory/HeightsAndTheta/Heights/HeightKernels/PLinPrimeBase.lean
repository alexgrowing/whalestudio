import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcLinear
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

namespace LinearPrimeBase

variable {T : Type} [Fintype T] {k : Type} [Field k]

def firstLin (n : T → ℤ) : MRing (stackedBlocks T) := ∑ t, n t • graphFirst t

theorem linPointMap_firstLin (α : T → k) (M : T → Fin 1 → k) (n : T → ℤ) :
    linPointMap α M (firstLin n) = C (∑ t, n t • α t) * X none := by
  simp only [firstLin, map_sum, map_zsmul, LinPrimeExample.linPointMap_first, Finset.sum_mul, smul_mul_assoc]

theorem exists_comb {α : T → k} (hα : Submodule.span ℤ (Set.range α) = ⊤) (y : k) :
    ∃ n : T → ℤ, ∑ t, n t • α t = y := by
  have hy : y ∈ Submodule.span ℤ (Set.range α) := hα ▸ Submodule.mem_top
  exact (Submodule.mem_span_range_iff_exists_fun ℤ).mp hy

def chartPt (a b : k) : Option (Fin 1) → k := fun o => o.elim a⁻¹ fun _ => b⁻¹

def chartEval (α : T → k) (M : T → Fin 1 → k) (a b : k) : MRing (stackedBlocks T) →+* k :=
  (eval (chartPt a b)).comp (linPointMap α M)

theorem chartEval_firstLin (α : T → k) (M : T → Fin 1 → k) (a b : k) (n : T → ℤ) :
    chartEval α M a b (firstLin n) = (∑ t, n t • α t) * a⁻¹ := by
  simp [chartEval, linPointMap_firstLin, chartPt]

theorem chartEval_first (α : T → k) (M : T → Fin 1 → k) (a b : k) (t : T) :
    chartEval α M a b (graphFirst t) = α t * a⁻¹ := by
  simp [chartEval, LinPrimeExample.linPointMap_first, chartPt]

theorem chartEval_second (α : T → k) (M : T → Fin 1 → k) (a b : k) (t : T) :
    chartEval α M a b (graphSecond t) = M t 0 * b⁻¹ := by
  simp [chartEval, LinPrimeExample.linPointMap_second, chartPt]

theorem chart_equiv (α : T → k) (M : T → Fin 1 → k) (hα : Submodule.span ℤ (Set.range α) = ⊤)
    (c₁ c₂ : T) (h₁ : α c₁ ≠ 0) (h₂ : M c₂ 0 ≠ 0) (J : Ideal (MRing (stackedBlocks T)))
    (hJ₁ : graphFirst c₁ - 1 ∈ J) (hJ₂ : graphSecond c₂ - 1 ∈ J)
    (hJ : J ≤ Ideal.span {graphFirst c₁ - 1, graphSecond c₂ - 1}) :
    Nonempty ((MRing (stackedBlocks T) ⧸ (linPrime α M ⊔ J)) ≃+* k) := by
  classical
  set I := linPrime α M ⊔ J with hI
  set φ := chartEval α M (α c₁) (M c₂ 0) with hφ
  set mk := Ideal.Quotient.mk I with hmk

  have hV : ∀ h, linPointMap α M h = 0 → mk h = 0 := fun h hh =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left (RingHom.mem_ker.mpr hh))
  have hB₁ : mk (graphFirst c₁) = 1 := by
    rw [← map_one mk]; exact Ideal.Quotient.eq.mpr (Ideal.mem_sup_right hJ₁)
  have hB₂ : mk (graphSecond c₂) = 1 := by
    rw [← map_one mk]; exact Ideal.Quotient.eq.mpr (Ideal.mem_sup_right hJ₂)
  set N : Submodule ℤ (MRing (stackedBlocks T) ⧸ I) :=
    Submodule.span ℤ (Set.range fun t => mk (graphFirst t)) with hN
  have hLin : ∀ n : T → ℤ, mk (firstLin n) ∈ N := fun n => by
    rw [firstLin, map_sum]
    refine Submodule.sum_mem _ fun t _ => ?_
    rw [map_zsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)

  have hD : ∀ s t, mk (graphFirst s) * mk (graphFirst t) ∈ N := fun s t => by
    obtain ⟨n, hn⟩ := exists_comb hα (α s * α t / α c₁)
    have key : α c₁ * (α s * α t / α c₁) = α s * α t := by field_simp
    have h0 := hV (graphFirst s * graphFirst t - graphFirst c₁ * firstLin n) (by
      rw [map_sub, map_mul, map_mul, LinPrimeExample.linPointMap_first, LinPrimeExample.linPointMap_first,
        LinPrimeExample.linPointMap_first, linPointMap_firstLin, hn]
      calc C (α s) * X none * (C (α t) * X none) - C (α c₁) * X none * (C (α s * α t / α c₁) * X none)
          = C (α s * α t - α c₁ * (α s * α t / α c₁)) * X none ^ 2 := by
            simp only [map_sub, map_mul]; ring
        _ = 0 := by rw [key, sub_self, map_zero, zero_mul])
    rw [map_sub, map_mul, map_mul, sub_eq_zero, hB₁, one_mul] at h0
    rw [h0]; exact hLin n

  have hE : ∀ t, mk (graphSecond t) ∈ N := fun t => by
    obtain ⟨n, hn⟩ := exists_comb hα (α c₁ * M t 0 / M c₂ 0)
    have key : M c₂ 0 * (α c₁ * M t 0 / M c₂ 0) = M t 0 * α c₁ := by field_simp
    have h0 := hV (graphSecond t * graphFirst c₁ - graphSecond c₂ * firstLin n) (by
      rw [map_sub, map_mul, map_mul, LinPrimeExample.linPointMap_first, LinPrimeExample.linPointMap_second,
        LinPrimeExample.linPointMap_second, linPointMap_firstLin, hn, Fin.sum_univ_one, Fin.sum_univ_one]
      calc C (M t 0) * (X (some (0 : Fin 1)) : MvPolynomial (Option (Fin 1)) k) * (C (α c₁) * X none) -
            C (M c₂ 0) * X (some (0 : Fin 1)) * (C (α c₁ * M t 0 / M c₂ 0) * X none)
          = C (M t 0 * α c₁ - M c₂ 0 * (α c₁ * M t 0 / M c₂ 0)) * (X (some (0 : Fin 1)) * X none) := by
            simp only [map_sub, map_mul]; ring
        _ = 0 := by rw [key, sub_self, map_zero, zero_mul])
    rw [map_sub, map_mul, map_mul, sub_eq_zero, hB₁, mul_one, hB₂, one_mul] at h0
    rw [h0]; exact hLin n
  have hMul : ∀ x y, x ∈ N → y ∈ N → x * y ∈ N := fun x y hx hy => by
    have hxy : x * y ∈ N * N := Submodule.mul_mem_mul hx hy
    rw [hN, Submodule.span_mul_span] at hxy
    refine (Submodule.span_le.mpr ?_) hxy
    rintro _ ⟨_, ⟨s, rfl⟩, _, ⟨t, rfl⟩, rfl⟩
    exact hD s t
  have hOne : (1 : MRing (stackedBlocks T) ⧸ I) ∈ N := hB₁ ▸ Submodule.subset_span ⟨c₁, rfl⟩

  have hAll : ∀ g, mk g ∈ N := fun g => by
    refine MvPolynomial.induction_on (motive := fun g => mk g ∈ N) g (fun a => ?_) (fun p q hp hq => ?_) (fun p v hp => ?_)
    · have hC : (C a : MRing (stackedBlocks T)) = (a : MRing (stackedBlocks T)) := eq_intCast C a
      rw [hC, map_intCast, ← zsmul_one]
      exact Submodule.smul_mem _ _ hOne
    · rw [map_add]; exact Submodule.add_mem _ hp hq
    · rw [map_mul]
      refine hMul _ _ hp ?_
      rcases v with ⟨⟨⟨⟩⟩ | ⟨⟨⟩⟩, t⟩
      · exact Submodule.subset_span ⟨t, rfl⟩
      · exact hE t

  have hIle : I ≤ RingHom.ker φ := by
    refine sup_le (fun x hx => ?_) (hJ.trans (Ideal.span_le.mpr ?_))
    · rw [linPrime, RingHom.mem_ker] at hx
      rw [RingHom.mem_ker]
      simp [hφ, chartEval, hx]
    · rintro x (rfl | rfl)
      · rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, hφ, chartEval_first, mul_inv_cancel₀ h₁,
          sub_self]
      · rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, hφ, chartEval_second, mul_inv_cancel₀ h₂,
          sub_self]
  have hker : I = RingHom.ker φ := by
    apply le_antisymm hIle
    intro g hg
    rw [RingHom.mem_ker] at hg
    obtain ⟨n, hn⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hAll g)
    have hn' : mk (firstLin n) = mk g := by
      rw [← hn, firstLin, map_sum]
      simp only [map_zsmul]
    have hd : g - firstLin n ∈ I := Ideal.Quotient.eq.mp hn'.symm
    have hd' : φ (g - firstLin n) = 0 := RingHom.mem_ker.mp (hIle hd)
    rw [map_sub, hg, zero_sub, neg_eq_zero, hφ, chartEval_firstLin] at hd'
    have hs : ∑ t, n t • α t = 0 := by
      rcases mul_eq_zero.mp hd' with h | h
      · exact h
      · exact absurd h (inv_ne_zero h₁)
    have hl : firstLin n ∈ I :=
      Ideal.mem_sup_left (RingHom.mem_ker.mpr (by rw [linPointMap_firstLin, hs, map_zero, zero_mul]))
    have := I.add_mem hd hl
    rwa [sub_add_cancel] at this
  have hsurj : Function.Surjective φ := fun y => by
    obtain ⟨n, hn⟩ := exists_comb hα (y * α c₁)
    exact ⟨firstLin n, by rw [hφ, chartEval_firstLin, hn, mul_inv_cancel_right₀ h₁]⟩
  exact ⟨(Ideal.quotEquivOfEq hker).trans (RingHom.quotientKerEquivOfSurjective hsurj)⟩

end LinearPrimeBase

open LinearPrimeBase in

theorem LinPrimeBase.proof : LinPrimeBase.Statement := by
  intro T _ k _ α M hα _hM c hc
  have h₁ : α (c (Sum.inl ())) ≠ 0 := fun h => hc (Sum.inl ()) (by
    rw [linPrime, RingHom.mem_ker]
    exact (LinPrimeExample.linPointMap_first α M _).trans (by rw [h, map_zero, zero_mul]))
  have h₂ : M (c (Sum.inr ())) 0 ≠ 0 := fun h => hc (Sum.inr ()) (by
    rw [linPrime, RingHom.mem_ker]
    exact (LinPrimeExample.linPointMap_second α M _).trans (by rw [Fin.sum_univ_one, h, map_zero, zero_mul]))
  refine chart_equiv α M hα (c (Sum.inl ())) (c (Sum.inr ())) h₁ h₂ _
    (Ideal.subset_span ⟨Sum.inl (), rfl⟩) (Ideal.subset_span ⟨Sum.inr (), rfl⟩) (Ideal.span_mono ?_)
  rintro _ ⟨κ, rfl⟩
  rcases κ with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

end

end GroundTheory.Heights₂.Heights
