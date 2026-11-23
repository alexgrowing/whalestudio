import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.FamilyLogGammaSmallHolds

namespace Formalism.MainNotions.Ext

open Formalism.BasicNotions Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric NumberField

variable (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

theorem exists_conj_OK (a : 𝓞 D.host.K) : ∃ a' : 𝓞 D.host.K, (((a' : D.host.K)) : D.host.E) = D.host.conj ((a : D.host.K) : D.host.E) := by
  have hsq : D.host.conj D.host.sqd ∈ IntermediateField.adjoin ℚ {D.host.sqd} := by
    rw [D.host.gal_sqd]
    exact mul_mem (intCast_mem _ _) (IntermediateField.mem_adjoin_simple_self ℚ _)
  have hmap : IntermediateField.map (D.host.conj : D.host.E →ₐ[ℚ] D.host.E)
      (IntermediateField.adjoin ℚ {D.host.sqd}) ≤ IntermediateField.adjoin ℚ {D.host.sqd} := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    exact IntermediateField.adjoin_simple_le_iff.2 hsq
  have hx : ((a : D.host.K) : D.host.E) ∈ IntermediateField.adjoin ℚ {D.host.sqd} := (a : D.host.K).2
  have hK : D.host.conj ((a : D.host.K) : D.host.E) ∈ D.host.K :=
    hmap ((IntermediateField.mem_map _).2 ⟨_, hx, rfl⟩)
  have hint : IsIntegral ℤ (⟨_, hK⟩ : D.host.K) := by
    rw [← isIntegral_algebraMap_iff (algebraMap D.host.K D.host.E).injective]
    have ha : IsIntegral ℤ ((a : D.host.K) : D.host.E) :=
      (isIntegral_algebraMap_iff (algebraMap D.host.K D.host.E).injective).2 a.isIntegral_coe
    exact ha.map D.host.conj.toAlgHom.toRingHom.toIntAlgHom
  let b : integralClosure ℤ D.host.K := ⟨⟨_, hK⟩, hint⟩
  exact ⟨b, rfl⟩

theorem okp_swap (α : ℂ_[p] × ℂ_[p]) (hα : α ∈ OKp D lam) : α.swap ∈ OKp D lam := by
  have hc : ∀ x : D.host.E, D.host.φ₀ (D.host.conj x) = starRingEnd ℂ (D.host.φ₀ x) := by
    intro x
    simp only [← D.embE_φ₀, RingHom.comp_apply, D.embE_conj, D.starLL_cx]
  unfold OKp at hα ⊢
  refine map_mem_closure continuous_swap hα ?_
  rintro _ ⟨a, rfl⟩
  obtain ⟨a', ha'⟩ := exists_conj_OK D a
  refine ⟨a', ?_⟩
  simp only [tauK, tauKc, ha', Prod.swap_prod_mk, hc, Complex.conj_conj]

omit [Fact p.Prime] in
theorem test_vector_mem_schwartz_bruhat (z : D.host.E) : D.host.φ₀ z ∈ Qbar := by
  have h : IsIntegral ℚ z := Algebra.IsIntegral.isIntegral z
  exact mem_algebraicClosure_iff.2 (h.map D.host.φ₀.toRatAlgHom).isAlgebraic

theorem lamPhi_add (x y : D.host.E) : lamC lam (D.host.φ₀ (x + y)) = lamC lam (D.host.φ₀ x) + lamC lam (D.host.φ₀ y) := by
  unfold lamC
  rw [dif_pos (test_vector_mem_schwartz_bruhat D (x + y)), dif_pos (test_vector_mem_schwartz_bruhat D x), dif_pos (test_vector_mem_schwartz_bruhat D y), ← map_add lam]
  exact congrArg lam (Subtype.ext (by simp))

theorem lamPhi_mul (x y : D.host.E) : lamC lam (D.host.φ₀ (x * y)) = lamC lam (D.host.φ₀ x) * lamC lam (D.host.φ₀ y) := by
  unfold lamC
  rw [dif_pos (test_vector_mem_schwartz_bruhat D (x * y)), dif_pos (test_vector_mem_schwartz_bruhat D x), dif_pos (test_vector_mem_schwartz_bruhat D y), ← map_mul lam]
  exact congrArg lam (Subtype.ext (by simp))

theorem okp_add (α β : ℂ_[p] × ℂ_[p]) (hα : α ∈ OKp D lam) (hβ : β ∈ OKp D lam) : α + β ∈ OKp D lam := by
  unfold OKp at hα hβ ⊢
  refine map_mem_closure₂ (f := fun u v : ℂ_[p] × ℂ_[p] => u + v) continuous_add hα hβ ?_
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  refine ⟨a + b, ?_⟩
  have hab : (((a + b : 𝓞 D.host.K) : D.host.K) : D.host.E)
      = ((a : D.host.K) : D.host.E) + ((b : D.host.K) : D.host.E) := by simp
  simp only [tauK, tauKc, hab, map_add D.host.conj, lamPhi_add, Prod.mk_add_mk]

theorem okp_mul (α β : ℂ_[p] × ℂ_[p]) (hα : α ∈ OKp D lam) (hβ : β ∈ OKp D lam) : α * β ∈ OKp D lam := by
  unfold OKp at hα hβ ⊢
  refine map_mem_closure₂ (f := fun u v : ℂ_[p] × ℂ_[p] => u * v) continuous_mul hα hβ ?_
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  refine ⟨a * b, ?_⟩
  have hab : (((a * b : 𝓞 D.host.K) : D.host.K) : D.host.E)
      = ((a : D.host.K) : D.host.E) * ((b : D.host.K) : D.host.E) := by simp
  simp only [tauK, tauKc, hab, map_mul D.host.conj, lamPhi_mul, Prod.mk_mul_mk]

theorem okp_zero : (0 : ℂ_[p] × ℂ_[p]) ∈ OKp D lam := by
  have h0 : lamC lam (0 : ℂ) = 0 := by
    simpa using lamPhi_add D lam (0 : D.host.E) 0
  unfold OKp
  apply subset_closure
  refine ⟨0, ?_⟩
  simp [tauK, tauKc, h0]

theorem okp_hP {ι : Type} [Fintype ι] (x y : ι → ℂ_[p] × ℂ_[p]) (hx : InOKp D lam x) (hy : InOKp D lam y) :
    hP x y ∈ OKp D lam := by
  show (∑ k, x k * (y k).swap) ∈ OKp D lam
  exact Finset.sum_induction _ (· ∈ OKp D lam) (fun a b ha hb => okp_add D lam a b ha hb)
    (okp_zero D lam) (fun k _ => okp_mul D lam _ _ (hx k) (okp_swap D lam _ (hy k)))

end Formalism.MainNotions.Ext
