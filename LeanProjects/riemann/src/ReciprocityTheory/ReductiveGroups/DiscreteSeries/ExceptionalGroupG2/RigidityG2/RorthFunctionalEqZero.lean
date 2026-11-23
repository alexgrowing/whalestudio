import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.RorthFunctionalEqZero
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CasimirGapAtNoncompactWeight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.LayerBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.BochIneq
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CrossOpSlotBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.NcVOneDecomp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CrossOpEigGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.Numerics
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.KhwEqZeroSharp

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ}

section Alg

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {lam : Fin n → ℝ} {V : Submodule ℂ M}

theorem rorth_functional_eq_zero (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hgap : StdGap ε lam) (f : M →ₗ[ℂ] ℂ) (hfV : ∀ v ∈ V, f v = 0)
    (hfd : ∀ a y, f (E a a y) = (lowK ε lam a : ℂ) * f y)
    (hfl : ∀ a b, a < b → ε a = ε b → ∀ y, f (E b a y) = 0) :
    ∀ y ∈ genSub E V, f y = 0 := by
  intro y hy
  rw [genSub_eq_iSup_layer hE hV.2.1,
    Submodule.mem_iSup_of_directed _ (Monotone.directed_le fun _ _ h => layer_mono h)] at hy
  obtain ⟨k, hk⟩ := hy
  set W := layer ε E V k with hW
  have : FiniteDimensional ℂ W := finiteDimensional_layer hV.1 k
  have : CompleteSpace W := FiniteDimensional.complete ℂ W
  have hWK : IsKStableSub ε E W := layer_kStable hE hV.2.1 k
  obtain ⟨u, hu⟩ : ∃ u : W, ∀ w : W, inner ℂ (u : M) (w : M) = f w := by
    refine ⟨(InnerProductSpace.toDual ℂ W).symm
      (LinearMap.toContinuousLinearMap (f.comp W.subtype)), fun w => ?_⟩
    have := InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (x := w)
      (y := LinearMap.toContinuousLinearMap (f.comp W.subtype))
    exact this
  have hsg : ∀ a b, ε a = ε b → adjSign ε a b = 1 := fun a b h => by simp [adjSign, h]
  have hkhw : IsKHWVec ε E (lowK ε lam) (u : M) := by
    refine ⟨fun a => ?_, fun a b hab h => ?_⟩
    · have hz : E a a u - (lowK ε lam a : ℂ) • (u : M) ∈ W :=
        W.sub_mem (hWK a a rfl _ u.2) (W.smul_mem _ u.2)
      rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℂ)]
      have key : ∀ z ∈ W, inner ℂ (E a a u - (lowK ε lam a : ℂ) • (u : M)) z = 0 := by
        intro z hz
        rw [inner_sub_left, inner_smul_left, hU a a, hsg a a rfl, one_mul,
          hu ⟨_, hWK a a rfl _ hz⟩, hu ⟨z, hz⟩]
        simp [hfd]
      exact key _ hz
    · have hz : E a b u ∈ W := hWK a b h _ u.2
      rw [← inner_self_eq_zero (𝕜 := ℂ), hU a b, hsg a b h, one_mul]
      exact (hu ⟨_, hWK b a h.symm _ hz⟩).trans (hfl a b hab h _)
  have huV : (u : M) ∈ V := khw_lowK_mem hE hU hV hc hgap (layer_le_genSub k u.2) hkhw
  have hu0 : (u : M) = 0 := by
    rw [← inner_self_eq_zero (𝕜 := ℂ), hu u]
    exact hfV _ huV
  rw [← hu ⟨y, hk⟩, hu0, inner_zero_left]

end Alg

section Mat

end Mat

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}

theorem rigid_orth_genSub {lam : Fin n → ℝ} (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ)
    (hD : IsDerivedOn ε σ D E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (j : V →ₗ[ℂ] H)
    (hj : ∀ k ∈ Kset ε, ∀ v w : V, ((w : D) : H) = σ k ((v : D) : H) → j w = σ k (j v))
    (horth : ∀ v v' : V, inner ℂ (j v') ((v : D) : H) = 0) :
    ∀ v' : V, ∀ y ∈ genSub E V, inner ℂ (j v') (y : H) = 0 := by
  obtain ⟨φ, hφ⟩ := rorth_exists_ext hV.1 j
  have hrel := fun a b (h : ε a = ε b) => rorth_inner_E hσ hD hVK j hj φ hφ h
  obtain ⟨w, hwV, hw0, hw⟩ := hV.2.2.2
  have h0 : ∀ y ∈ genSub E V, inner ℂ (j ⟨w, hwV⟩) (y : H) = 0 := by
    refine rorth_functional_eq_zero hD.glRep (isInfUnitary_of_isDerivedOn hσ hD) hV hc hgap
      ((innerₛₗ ℂ (j ⟨w, hwV⟩)).comp D.subtype) (fun v hv => horth ⟨v, hv⟩ _) (fun a y => ?_)
      (fun a b hab h y => ?_)
    · have := hrel a a rfl ⟨w, hwV⟩ y
      simp only [hw.1 a, Submodule.coe_smul, map_smul, inner_smul_left, Complex.conj_ofReal,
        hφ ⟨w, hwV⟩] at this
      exact this.symm
    · have := hrel a b h ⟨w, hwV⟩ y
      simp only [hw.2 a b hab h, Submodule.coe_zero, map_zero, inner_zero_left] at this
      exact this.symm
  let S : Submodule ℂ D :=
    { carrier := {v | v ∈ V ∧ ∀ y ∈ genSub E V, inner ℂ (φ (v : H)) (y : H) = 0}
      add_mem' := fun {u v} hu hv => ⟨V.add_mem hu.1 hv.1, fun y hy => by
        simp [hu.2 y hy, hv.2 y hy]⟩
      zero_mem' := ⟨V.zero_mem, fun y _ => by simp⟩
      smul_mem' := fun c v hv => ⟨V.smul_mem c hv.1, fun y hy => by
        simp [hv.2 y hy]⟩ }
  have hSK : IsKStableSub ε E S := by
    intro a b h v hv
    refine ⟨hV.2.1 a b h v hv.1, fun y hy => ?_⟩
    rw [hrel a b h ⟨v, hv.1⟩ y, ← hφ]
    exact hv.2 _ (rorth_apply_mem_genSub b a hy)
  have hwS : w ∈ S := ⟨hwV, fun y hy => by rw [hφ ⟨w, hwV⟩]; exact h0 y hy⟩
  rcases hV.2.2.1 S (fun v hv => hv.1) hSK with h | h
  · rw [h] at hwS
    exact absurd ((Submodule.mem_bot ℂ).1 hwS) hw0
  · intro v' y hy
    have hv' : (v' : D) ∈ S := by rw [h]; exact v'.2
    rw [← hφ]
    exact hv'.2 y hy

theorem rigid_orth_closure {lam : Fin n → ℝ} (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ)
    (hD : IsDerivedOn ε σ D E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (j : V →ₗ[ℂ] H)
    (hj : ∀ k ∈ Kset ε, ∀ v w : V, ((w : D) : H) = σ k ((v : D) : H) → j w = σ k (j v))
    (horth : ∀ v v' : V, inner ℂ (j v') ((v : D) : H) = 0) :
    ∀ v' : V, ∀ x ∈ ((genSub E V).map D.subtype).topologicalClosure, inner ℂ (j v') x = 0 := by
  intro v' x hx
  have hle : ((genSub E V).map D.subtype).topologicalClosure ≤ (ℂ ∙ j v')ᗮ := by
    refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)
    rintro _ ⟨y, hy, rfl⟩
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.2
      (rigid_orth_genSub hgap hσ hD hV hc hVK j hj horth v' y hy)
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hle hx)

end Rep

end ReciprocityTheory.ChartRestriction.DS.G2
