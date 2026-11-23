import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.BridgeWt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.BridgeExpK
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.BridgeHW
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.BridgeKType
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.ClosGenStable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.RigidUniversal
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Closure
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasimirGapAtNoncompactWeight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.IrredA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.VNormSqLowKSubRootLt

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Data

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}

theorem kType_map_of_inj {μ : Fin n → ℝ} {S : Submodule ℂ H} (hS : Formalism.MainNotions.S.IsKTypeOf ε σ μ S)
    (f : H →ₗ[ℂ] H) (hf : ∀ k ∈ Formalism.REAL.Kset ε, ∀ x, f (σ k x) = σ k (f x))
    (hinj : ∀ x ∈ S, f x = 0 → x = 0) : Formalism.MainNotions.S.IsKTypeOf ε σ μ (S.map f) := by
  obtain ⟨hfd, hst, hirr, ⟨v, hvS, hv0, hvw⟩, hwt⟩ := hS
  have hwt' : ∀ x ∈ S, ∀ ν, Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ ν (f x) →
      Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ ν x := by
    intro x hx ν h θ hθ
    have h1 := h θ hθ
    rw [← hf _ hθ, ← map_smul] at h1
    have := hinj _ (S.sub_mem (hst _ hθ x hx) (S.smul_mem _ hx)) (by rw [map_sub, h1, sub_self])
    exact sub_eq_zero.1 this
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · rintro g hg _ ⟨x, hx, rfl⟩
    exact ⟨σ g x, hst g hg x hx, hf g hg x⟩
  · intro S' hS' hK
    let T : Submodule ℂ H := S ⊓ S'.comap f
    have hT : Formalism.MainNotions.S.IsKStableOn ε σ T := fun g hg x hx =>
      ⟨hst g hg x hx.1, by
        show f (σ g x) ∈ S'
        rw [hf g hg]
        exact hK g hg _ hx.2⟩
    rcases hirr T inf_le_left hT with h | h
    · left
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨x, hx, rfl⟩ := hS' hy
      have hxT : x ∈ T := ⟨hx, hy⟩
      rw [h, Submodule.mem_bot] at hxT
      rw [hxT, map_zero]
      exact Submodule.zero_mem _
    · right
      refine le_antisymm hS' ?_
      rintro _ ⟨x, hx, rfl⟩
      have hxT : x ∈ T := by rw [h]; exact hx
      exact hxT.2
  · refine ⟨f v, Submodule.mem_map_of_mem hvS, fun h => hv0 (hinj v hvS h), fun θ hθ => ?_⟩
    rw [← hf _ hθ, hvw θ hθ, map_smul]
  · rintro ν _ ⟨x, hx, rfl⟩ h0 hν
    exact hwt ν x hx (fun h => h0 (by rw [h, map_zero])) (hwt' x hx ν hν)

theorem exists_khw_genSub_of_kType (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hVf : FiniteDimensional ℂ V) (hVk : IsKStableSub ε E V) {μ : Fin n → ℝ} {S : Submodule ℂ H}
    (hS : S ≤ closGen E V) (hST : Formalism.MainNotions.S.IsKTypeOf ε σ μ S) :
    ∃ w : D, w ∈ genSub E V ∧ w ≠ 0 ∧ IsKHWVec ε E μ w := by
  classical
  have hE := hD.glRep
  obtain ⟨v, hvS, hv0, -⟩ := hST.2.2.2.1
  have hex : ∃ y : D, y ∈ genSub E V ∧ inner ℂ v (y : H) ≠ 0 := by
    by_contra hno
    push Not at hno
    have h1 : (genSub E V).map D.subtype ≤ (ℂ ∙ v)ᗮ := by
      rintro _ ⟨y, hy, rfl⟩
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      exact hno y hy
    have h2 : closGen E V ≤ (ℂ ∙ v)ᗮ :=
      Submodule.topologicalClosure_minimal _ h1 (Submodule.isClosed_orthogonal _)
    have h3 := h2 (hS hvS)
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at h3
    exact hv0 (inner_self_eq_zero.1 h3)
  obtain ⟨y, hyg, hyv⟩ := hex
  obtain ⟨m, hym⟩ := exists_layer_of_mem_genSub hE hVk hyg
  have hLf : FiniteDimensional ℂ (layer ε E V m) := finiteDimensional_layer hVf m
  have hLk := kStable_of_isKStableSub hσ hD (layer ε E V m) hLf (layer_kStable hE hVk m)
  set W : Submodule ℂ H := (layer ε E V m).map D.subtype with hWdef
  have : FiniteDimensional ℂ W := inferInstance
  have : CompleteSpace W := FiniteDimensional.complete ℂ W
  have hWK : ∀ k ∈ Kset ε, ∀ x ∈ W, σ k x ∈ W := by
    rintro k hk _ ⟨u, hu, rfl⟩
    obtain ⟨w, hw, e⟩ := hLk k hk u hu
    exact ⟨w, hw, e⟩
  have hWoK : ∀ k ∈ Kset ε, ∀ x ∈ Wᗮ, σ k x ∈ Wᗮ := by
    intro k hk
    obtain ⟨hk', hkk⟩ := UnitaryGroupOfForm.K_inv hk
    exact UnitaryGroupOfForm.orth_stable hσ (UnitaryGroupOfForm.K_mem_UJ hk) (UnitaryGroupOfForm.K_mem_UJ hk') hkk W (hWK _ hk')
  have hPc : ∀ k ∈ Formalism.REAL.Kset ε, ∀ x, W.starProjection.toLinearMap (σ k x) =
      σ k (W.starProjection.toLinearMap x) := fun k hk x =>
    UnitaryGroupOfForm.proj_comm W (σ k) (hWK k hk) (hWoK k hk) x
  have hyW : (y : H) ∈ W := ⟨y, hym, rfl⟩
  have hinj : ∀ x ∈ S, W.starProjection.toLinearMap x = 0 → x = 0 := by
    intro x hx hPx
    let T : Submodule ℂ H := S ⊓ LinearMap.ker W.starProjection.toLinearMap
    have hT : Formalism.MainNotions.S.IsKStableOn ε σ T := fun g hg z hz =>
      ⟨hST.2.1 g hg z hz.1, LinearMap.mem_ker.2 (by rw [hPc g hg, LinearMap.mem_ker.1 hz.2, map_zero])⟩
    rcases hST.2.2.1 T inf_le_left hT with h | h
    · have hxT : x ∈ T := ⟨hx, hPx⟩
      rw [h, Submodule.mem_bot] at hxT
      exact hxT
    · exfalso
      have hvT : v ∈ T := by rw [h]; exact hvS
      apply hyv
      have e1 : inner ℂ v (y : H) = inner ℂ (W.starProjection v) (y : H) := by
        rw [Submodule.inner_starProjection_left_eq_right, W.starProjection_eq_self_iff.2 hyW]
      rw [e1, show W.starProjection v = 0 from hvT.2, inner_zero_left]
  have hKT := kType_map_of_inj hST W.starProjection.toLinearMap hPc hinj
  have hSD : S.map W.starProjection.toLinearMap ≤ D := by
    rintro _ ⟨x, -, rfl⟩
    obtain ⟨u, -, e⟩ := W.starProjection_apply_mem x
    show W.starProjection x ∈ D
    rw [← e]
    exact u.2
  obtain ⟨w, hwS, hw0, hwK⟩ := exists_isKHWVec_of_isKTypeOf hσ hD hKT hSD
  refine ⟨w, ?_, hw0, hwK⟩
  obtain ⟨x, -, e⟩ := hwS
  obtain ⟨u, hu, e'⟩ := W.starProjection_apply_mem x
  have huw : u = w := Subtype.ext (e'.trans e)
  exact layer_le_genSub m (huw ▸ hu)

theorem data_casValK_gap (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) {μ : Fin n → ℝ} (S : Submodule ℂ H)
    (hS : S ≤ closGen E V) (hST : Formalism.MainNotions.S.IsKTypeOf ε σ μ S) (hμ : μ ≠ lowK ε lam) :
    casValK ε (lowK ε lam) + 2 * (h - n + 1) ≤ casValK ε μ := by
  obtain ⟨w, hwg, hw0, hwK⟩ := exists_khw_genSub_of_kType hσ hD hV.1 hV.2.1 hS hST
  obtain ⟨j, -, hpos, hle⟩ := casimir_gap_at_noncompact_weight hD.glRep (isInfUnitary_of_isDerivedOn hσ hD) hV hc hgap.1 hh hbig
    hwg hw0 hwK hμ
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  nlinarith

theorem data_vogan (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) {μ : Fin n → ℝ} (S : Submodule ℂ H) (hS : S ≤ closGen E V)
    (hST : Formalism.MainNotions.S.IsKTypeOf ε σ μ S) :
    Formalism.MainNotions.S.vNormSq ε (Formalism.QuantumDeterminants.lowK ε lam) ≤ Formalism.MainNotions.S.vNormSq ε μ := by
  obtain ⟨w, hwg, hw0, hwK⟩ := exists_khw_genSub_of_kType hσ hD hV.1 hV.2.1 hS hST
  exact vogan_min hD.glRep (isInfUnitary_of_isDerivedOn hσ hD) hV hc hgap hwg hw0 hwK

theorem data_isKTypeOf (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) : Formalism.MainNotions.S.IsKTypeOf ε σ (lowK ε lam) (V.map D.subtype) := by
  exact isKTypeOf_of_isKIrrHW hσ hD hV hVK (fun μ x hx hx0 hμ =>
    weights_le_of_irr_hw hD.glRep (isInfUnitary_of_isDerivedOn hσ hD) hV hx hx0 hμ)

theorem data_casU (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (x : D) (hx : x ∈ genSub E V) :
    casU ε σ (x : H) = ((casVal lam : ℝ) : ℂ) • (x : H) := by
  rw [casU_eq_casimir hD x, casimir_genSub hD.glRep hc x hx, Submodule.coe_smul]

theorem data_closGen_eq_top (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hirr : Formalism.MainNotions.S.IsIrredOn (UJset ε) σ) (hV0 : V ≠ ⊥) :
    closGen E V = ⊤ := by
  rcases hirr (closGen E V) (Submodule.isClosed_topologicalClosure _)
      (closGen_stable hgap hσ hD hV hc hVK) with h | h
  · exfalso
    obtain ⟨w, hw, hw0, -⟩ := hV.2.2.2
    have hwc : (w : H) ∈ closGen E V := UnitaryGroupOfForm.mem_closGen (E := E) V w hw
    rw [h, Submodule.mem_bot] at hwc
    exact hw0 (by exact_mod_cast hwc)
  · exact h

end Data

section Two

variable {ε : Fin n → Bool} {lam : Fin n → ℝ}
  {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} {D₁ : Submodule ℂ H₁}
  {E₁ : Fin n → Fin n → Module.End ℂ D₁} {V₁ : Submodule ℂ D₁}
  {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
  {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)} {D₂ : Submodule ℂ H₂}
  {E₂ : Fin n → Fin n → Module.End ℂ D₂} {V₂ : Submodule ℂ D₂}

end Two

end ReciprocityTheory.ChartRestriction.DS
