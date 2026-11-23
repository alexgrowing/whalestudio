import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.MemPerpSpanIff

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA

namespace Formalism.L2.SG.LocalCountModules.LocCntCommon

section Transport

theorem graph_transport {D₁ D₂ Dc₁ Dc₂ W₁ W₂ P : Type} (Ψ₁ : D₁ ≃ Dc₁) (Ψ₂ : D₂ ≃ Dc₂)
    (θ : D₁ ≃ D₂) (φ : W₁ → W₂) (Pc₁ : W₁ → P) (Pc₂ : W₂ → P) (Γ₁ : Set (D₁ × W₁))
    (Γ₂ : Set (D₂ × W₂)) (Γc₁ : Set (Dc₁ × P)) (Γc₂ : Set (Dc₂ × P))
    (h1 : (fun p => (Ψ₁ p.1, Pc₁ p.2)) '' Γ₁ = Γc₁) (h2 : (fun p => (Ψ₂ p.1, Pc₂ p.2)) '' Γ₂ = Γc₂)
    (hP : ∀ w, Pc₂ (φ w) = Pc₁ w)
    (hinj : ∀ p ∈ Γ₁, ∀ q ∈ Γ₂, Pc₂ q.2 = Pc₁ p.2 → q.2 = φ p.2) :
    ((fun p => (θ p.1, φ p.2)) '' Γ₁ = Γ₂) ↔
      ((fun p => (Ψ₂ (θ (Ψ₁.symm p.1)), p.2)) '' Γc₁ = Γc₂) := by
  constructor
  · intro h
    rw [← h1, ← h2, ← h, Set.image_image, Set.image_image]
    apply Set.image_congr
    intro p _
    simp [hP]
  · intro h
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hc : (Ψ₂ (θ p.1), Pc₁ p.2) ∈ Γc₂ := by
        rw [← h]
        refine ⟨(Ψ₁ p.1, Pc₁ p.2), ?_, by simp⟩
        rw [← h1]
        exact ⟨p, hp, rfl⟩
      rw [← h2] at hc
      obtain ⟨q', hq', hqe⟩ := hc
      simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at hqe
      have e2 : q'.2 = φ p.2 := hinj p hp q' hq' hqe.2
      have : q' = (θ p.1, φ p.2) := Prod.ext hqe.1 e2
      show (θ p.1, φ p.2) ∈ Γ₂
      rw [← this]
      exact hq'
    · intro hq
      have hc : (Ψ₂ q.1, Pc₂ q.2) ∈ Γc₂ := by
        rw [← h2]
        exact ⟨q, hq, rfl⟩
      rw [← h] at hc
      obtain ⟨c, hc1, hce⟩ := hc
      rw [← h1] at hc1
      obtain ⟨p, hp, rfl⟩ := hc1
      simp only [Prod.mk.injEq, Equiv.symm_apply_apply, EmbeddingLike.apply_eq_iff_eq] at hce
      refine ⟨p, hp, ?_⟩
      have e2 : q.2 = φ p.2 := hinj p hp q hq hce.2.symm
      exact Prod.ext hce.1 e2.symm

end Transport

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)

theorem smul_transport {A B : Type} [AddCommGroup A] [Module E A] [AddCommGroup B] [Module E B]
    (φ : A ≃ₗ[E] B) (c₁ c₂ k₁ k₂ : E) (hk₁ : k₁ * c₁ = 1) (hk₂ : k₂ * c₂ = 1) (a : A) (b : B)
    (e : c₂ • φ a = c₁ • b) : φ (k₁ • a) = k₂ • b := by
  rw [map_smul]
  have h1 : φ a = k₂ • (c₂ • φ a) := by rw [smul_smul, hk₂, one_smul]
  rw [h1, e, smul_smul, smul_smul]
  congr 1
  calc k₁ * k₂ * c₁ = k₂ * (k₁ * c₁) := by ring
    _ = k₂ := by rw [hk₁, mul_one]

variable {r : ℕ}

theorem om'_mem (f f' : Fin (r + 1) → V) : H.om' f f' ∈ H.perp (H.X f) := by
  intro x hx
  refine Submodule.span_induction (p := fun x _ => H.h (H.om' f f') x = 0) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨a, rfl⟩
    unfold HermSp.om'
    rw [h_sum_left]
    have hm := congrFun (congrFun (Matrix.mul_adjugate (H.Zhat f f')) a.castSucc) (Fin.last r)
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply_ne (Fin.castSucc_lt_last a).ne, smul_zero] at hm
    rw [← hm]
    apply Finset.sum_congr rfl
    intro b _
    simp [HermSp.Zhat, mul_comm]
  · exact h_zero_right H _
  · intro x y _ _ hx hy
    rw [h_add_right, hx, hy, add_zero]
  · intro c x _ hx
    rw [h_smul_right, hx, mul_zero]

theorem sends_one {f₁ f₂ : Fin (r + 1) → V} (φ : H.Wb f₁ ≃ₗ[E] H.Wb f₂) (v₁ v₂ : V)
    (h₁ : v₁ ∈ H.perp (H.X f₁)) (h₂ : v₂ ∈ H.perp (H.X f₂))
    (hs : H.SendsTo φ.toLinearMap 1 1 v₁ v₂) : φ (H.mkW f₁ ⟨v₁, h₁⟩) = H.mkW f₂ ⟨v₂, h₂⟩ := by
  have := hs ⟨v₁, h₁⟩ ⟨v₂, h₂⟩ rfl rfl
  simpa using this

theorem sends_omP {f₁ f₁' f₂ f₂' : Fin (r + 1) → V} (φ : H.Wb f₁ ≃ₗ[E] H.Wb f₂)
    (hD₁ : IsUnit (H.Dl f₁ f₁' (r + 1))) (hD₂ : IsUnit (H.Dl f₂ f₂' (r + 1)))
    (hs : H.SendsTo φ.toLinearMap (H.Dl f₂ f₂' (r + 1)) (H.Dl f₁ f₁' (r + 1)) (H.om' f₁ f₁')
      (H.om' f₂ f₂')) :
    φ (H.mkW f₁ ⟨omP H f₁ f₁', omP_mem H f₁ f₁' hD₁⟩) = H.mkW f₂ ⟨omP H f₂ f₂', omP_mem H f₂ f₂' hD₂⟩ := by
  have e := hs ⟨_, om'_mem H f₁ f₁'⟩ ⟨_, om'_mem H f₂ f₂'⟩ rfl rfl
  have e1 : H.mkW f₁ ⟨omP H f₁ f₁', omP_mem H f₁ f₁' hD₁⟩ =
      Ring.inverse (H.Dl f₁ f₁' (r + 1)) • H.mkW f₁ ⟨_, om'_mem H f₁ f₁'⟩ := by
    rw [← LinearMap.map_smul]
    rfl
  have e2 : H.mkW f₂ ⟨omP H f₂ f₂', omP_mem H f₂ f₂' hD₂⟩ =
      Ring.inverse (H.Dl f₂ f₂' (r + 1)) • H.mkW f₂ ⟨_, om'_mem H f₂ f₂'⟩ := by
    rw [← LinearMap.map_smul]
    rfl
  rw [e1, e2]
  exact smul_transport φ _ _ _ _ (Ring.inverse_mul_cancel _ hD₁) (Ring.inverse_mul_cancel _ hD₂) _ _ e

theorem h_omP (f f' : Fin (r + 1) → V) (u : V) :
    H.h u (omP H f f') = ∑ b, M.L.cj ((H.Zhat f f')⁻¹ b (Fin.last r)) * H.h u (f' b) := by
  have hD : H.Dl f f' (r + 1) = (H.Zhat f f').det := by
    unfold HermSp.Dl
    rw [dif_pos le_rfl]
    simp [Fin.castLE_refl]
  unfold omP HermSp.om'
  rw [h_smul_right, h_sum_right, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [← mul_assoc, ← map_mul, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, hD]

end Formalism.L2.SG.LocalCountModules.LocCntCommon
