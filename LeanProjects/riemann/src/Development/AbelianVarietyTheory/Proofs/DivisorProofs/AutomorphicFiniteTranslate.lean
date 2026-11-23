import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Gl2LocalToAdelicEmbedding
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MemSpanCentreTranslates
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.IdTorus GlobalTheory.GLTwoHecke
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut (IsMaxCpt)
open GlobalTheory.StdPar

noncomputable section

namespace GlobalTheory.FinTransl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem commute_line_fin {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) (t : ℝ) {y : GAd σ J}
    (hy : y ∈ finPts σ J) : Commute (γ t) y := by
  obtain ⟨w, τ, Z, -, h⟩ := hγ
  obtain ⟨x, e, -⟩ := h t
  rw [e]; exact commute_embArch σ J x (mem_finPts_iff_forall.1 hy w)

theorem commute_inf_fin {k y : GAd σ J} (hk : k ∈ infPts σ J) (hy : y ∈ finPts σ J) : Commute k y := by
  obtain ⟨a, rfl⟩ := (range_ofInf σ J).ge hk
  obtain ⟨b, rfl⟩ := (range_ofFin σ J).ge hy
  exact commute_ofInf_ofFin σ J a b

theorem foldr_transl {e : GAd σ J} (l : List (ℝ → GAd σ J)) (hl : ∀ γ ∈ l, ∀ t, Commute (γ t) e)
    (f : GAd σ J → ℂ) : l.foldr lineDer (fun y => f (y * e)) = fun y => l.foldr lineDer f (y * e) := by
  induction l with
  | nil => rfl
  | cons γ l ih =>
    rw [List.foldr_cons, ih (fun γ' h => hl γ' (List.mem_cons_of_mem _ h)), List.foldr_cons]
    funext g
    simp only [lineDer]
    congr 1
    funext t
    rw [mul_assoc, (hl γ List.mem_cons_self t).eq, ← mul_assoc]

theorem dop_transl {z : List (ℝ → GAd σ J) →₀ ℂ} (hz : GlobalTheory.UAut.IsCentral σ J z) {e : GAd σ J} (he : e ∈ finPts σ J)
    (f : GAd σ J → ℂ) : GlobalTheory.UAut.dop z (fun y => f (y * e)) = fun y => GlobalTheory.UAut.dop z f (y * e) := by
  funext g
  simp only [GlobalTheory.UAut.dop, Finsupp.sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [foldr_transl l (fun γ h t => commute_line_fin (hz.1 l hl γ h) t he)]

end GlobalTheory.FinTransl

open GlobalTheory.FinTransl in

theorem GlobalTheory.StdPar.isAutOn_mul_finPts : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
    ∀ {K : Subgroup (GAd σ J)}, K ≤ infPts σ J → ∀ {T : Finset (Fin r)} {f : GAd σ J → ℂ}, IsAutOn σ J X Y T K f →
      ∀ y ∈ finPts σ J, IsAutOn σ J X Y T K (fun g => f (g * y)) := by
  intro F E _ _ _ _ _ σ n J r X Y _ _ _ K hK T f h e efin
  refine ⟨fun u hu g => ?_, fun γ hγ hγ' g => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mul_assoc]; exact h.leftN u hu _
  · simp only [mul_assoc]; exact h.leftM γ hγ hγ' _
  · obtain ⟨U, hU, hUφ⟩ := h.level
    refine ⟨U.comap (MulAut.conj e⁻¹).toMonoidHom, ?_, fun k hk hkf g => ?_⟩
    · have : ((U.comap (MulAut.conj e⁻¹).toMonoidHom : Subgroup (GAd σ J)) : Set (GAd σ J)) =
          (fun k => e⁻¹ * k * e⁻¹⁻¹) ⁻¹' (U : Set (GAd σ J)) := rfl
      rw [this]
      exact hU.preimage (by fun_prop)
    · have hk' : e⁻¹ * k * e ∈ U := by simpa using hk
      have hf' : e⁻¹ * k * e ∈ finPts σ J := mul_mem (mul_mem (inv_mem efin) hkf) efin
      have := hUφ _ hk' hf' (g * e)
      simpa [mul_assoc] using this
  · exact h.cont.comp (continuous_id.mul continuous_const)
  · intro k γ hγ g
    have e1 : (fun t : Fin k → ℝ => f (g * (List.ofFn fun i => γ i (t i)).prod * e)) =
        fun t : Fin k → ℝ => f (g * e * (List.ofFn fun i => γ i (t i)).prod) := by
      funext t
      have hc : Commute (List.ofFn fun i => γ i (t i)).prod e :=
        Commute.list_prod_left _ _ fun a ha => by
          obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
          exact commute_line_fin (hγ i) _ efin
      rw [mul_assoc, hc.eq, ← mul_assoc]
    show ContDiff ℝ _ fun t : Fin k → ℝ => f (g * (List.ofFn fun i => γ i (t i)).prod * e)
    rw [e1]
    exact h.smooth k γ hγ (g * e)
  · obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun l hl => ?_⟩
    obtain ⟨C, hC⟩ := hN l hl
    refine ⟨max C 0 * (height σ J e : ℝ) ^ N, fun g => ?_⟩
    rw [foldr_transl l (fun γ h t => commute_line_fin (hl γ h) t efin)]
    have hh : (height σ J (g * e) : ℝ) ≤ (height σ J g : ℝ) * (height σ J e : ℝ) := by
      exact_mod_cast height_mul_le σ J g e
    have h0 : (0 : ℝ) ≤ (height σ J (g * e) : ℝ) := by positivity
    calc ‖l.foldr lineDer f (g * e)‖ ≤ C * (height σ J (g * e) : ℝ) ^ N := hC _
      _ ≤ max C 0 * (height σ J (g * e) : ℝ) ^ N :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max C 0 * ((height σ J g : ℝ) * (height σ J e : ℝ)) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hh N) (le_max_right _ _)
      _ = max C 0 * (height σ J e : ℝ) ^ N * (height σ J g : ℝ) ^ N := by ring
  · have := h.kfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ (Set.range fun k : K => fun g => f (g * k))).map
        (LinearMap.funLeft ℂ ℂ (fun y : GAd σ J => y * e)))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨⟨k, hk⟩, rfl⟩
    refine ⟨fun g => f (g * k), Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩, ?_⟩
    funext g
    simp only [LinearMap.funLeft_apply, Function.comp]
    rw [mul_assoc, mul_assoc, (commute_inf_fin (hK hk) efin).eq]
  · have := h.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ {f' | ∃ z, GlobalTheory.UAut.IsCentral σ J z ∧ f' = GlobalTheory.UAut.dop z f}).map
        (LinearMap.funLeft ℂ ℂ (fun y : GAd σ J => y * e)))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨GlobalTheory.UAut.dop z f, Submodule.subset_span ⟨z, hz, rfl⟩, ?_⟩
    rw [dop_transl hz efin]
    rfl
