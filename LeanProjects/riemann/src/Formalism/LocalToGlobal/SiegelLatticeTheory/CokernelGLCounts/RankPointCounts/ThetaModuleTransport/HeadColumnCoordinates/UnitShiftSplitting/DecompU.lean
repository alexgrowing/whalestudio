import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.OmPMemSpan

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
variable {r : ℕ}

theorem h_om'_f'U (f f' : Fin (r + 1) → V) (T' : F) (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') (b : Fin (r + 1)) :
    H.h (H.om' f f') (f' b) = if b = Fin.last r then -algebraMap F E T' * H.Dl f f' r else 0 := by
  unfold HermSp.om'
  rw [h_sum_left]
  obtain ⟨h0, hl⟩ := hF'
  split_ifs with hb
  · subst hb
    rw [Finset.sum_eq_single (Fin.last r)]
    · rw [hl, adj_last]
      ring
    · intro c _ hc
      rw [h0 c (Fin.last r) (Or.inl hc), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · apply Finset.sum_eq_zero
    intro c _
    rw [h0 c b (Or.inr hb), mul_zero]

theorem h_om'_om'U (f f' : Fin (r + 1) → V) (T' : F) (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') :
    H.h (H.om' f f') (H.om' f f') = M.L.cj (H.Dl f f' r) * (-algebraMap F E T' * H.Dl f f' r) := by
  rw [show H.h (H.om' f f') (H.om' f f') =
      H.h (H.om' f f') (∑ b, (H.Zhat f f').adjugate b (Fin.last r) • f' b) from rfl, h_sum_right]
  rw [Finset.sum_eq_single (Fin.last r)]
  · rw [h_om'_f'U H f f' T' hF', if_pos rfl, adj_last]
  · intro b _ hb
    rw [h_om'_f'U H f f' T' hF', if_neg hb, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem mem_X_ofU (f f' : Fin (r + 1) → V) (T T' : F) (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T)
    (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') (hD : IsUnit (H.Dl f f' (r + 1)))
    (hG : IsUnit (H.Dl f f' (r + 1) * M.L.cj (H.Dl f f' (r + 1)) -
      algebraMap F E (T * T') * (H.Dl f f' r * M.L.cj (H.Dl f f' r))))
    (v : V) (hv : v ∈ Submodule.span E (Set.range (Sum.elim f f')))
    (h1 : ∀ a, H.h v (f a) = 0) (h2 : H.h (H.om' f f') v = 0) : v ∈ H.X f := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).mp hv
  have hvxy : v = (∑ a, c (Sum.inl a) • f a) + ∑ b, c (Sum.inr b) • f' b := by
    rw [← hc, Fintype.sum_sum_type]
    rfl
  rw [hvxy] at h1 h2
  rw [hvxy]
  have key1 : ∀ a, Matrix.mulVec (H.Zhat f f') (fun b => c (Sum.inr b)) a =
      if a = Fin.last r then algebraMap F E T * c (Sum.inl (Fin.last r)) else 0 := by
    intro a
    have h := h1 a
    rw [HermSp.h_add_left, h_sum_left, h_sum_left] at h
    have hs : ∑ i, c (Sum.inl i) * H.h (f i) (f a) =
        if a = Fin.last r then c (Sum.inl (Fin.last r)) * -algebraMap F E T else 0 := by
      split_ifs with ha
      · subst ha
        rw [Finset.sum_eq_single (Fin.last r)]
        · rw [hF.2]
        · intro i _ hi
          rw [hF.1 i (Fin.last r) (Or.inl hi), mul_zero]
        · intro h'
          exact absurd (Finset.mem_univ _) h'
      · apply Finset.sum_eq_zero
        intro i _
        rw [hF.1 i a (Or.inr ha), mul_zero]
    have hw : Matrix.mulVec (H.Zhat f f') (fun b => c (Sum.inr b)) a =
        ∑ b, c (Sum.inr b) * H.h (f' b) (f a) := by
      simp only [Matrix.mulVec, dotProduct, HermSp.Zhat, Matrix.of_apply]
      exact Finset.sum_congr rfl (fun b _ => mul_comm _ _)
    rw [hw]
    rw [hs] at h
    split_ifs with ha
    · rw [if_pos ha] at h
      linear_combination h
    · rw [if_neg ha, zero_add] at h
      exact h
  have key2 : ∀ b, H.Dl f f' (r + 1) * c (Sum.inr b) =
      (H.Zhat f f').adjugate b (Fin.last r) * (algebraMap F E T * c (Sum.inl (Fin.last r))) := by
    intro b
    have hm : Matrix.mulVec (H.Zhat f f').adjugate (Matrix.mulVec (H.Zhat f f') (fun b => c (Sum.inr b))) =
        H.Dl f f' (r + 1) • (fun b => c (Sum.inr b)) := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec, dl_full]
    have hb := congrFun hm b
    rw [funext key1] at hb
    rw [Pi.smul_apply, smul_eq_mul] at hb
    rw [← hb]
    simp [Matrix.mulVec, dotProduct]
  have hxl : c (Sum.inl (Fin.last r)) = 0 := by
    rw [h_add_right, h_sum_right, h_sum_right] at h2
    have s1 : ∑ a, M.L.cj (c (Sum.inl a)) * H.h (H.om' f f') (f a) =
        M.L.cj (c (Sum.inl (Fin.last r))) * H.Dl f f' (r + 1) := by
      rw [Finset.sum_eq_single (Fin.last r)]
      · rw [h_om'_f, if_pos rfl, dl_full]
      · intro i _ hi
        rw [h_om'_f, if_neg hi, mul_zero]
      · intro h'
        exact absurd (Finset.mem_univ _) h'
    have s2 : ∑ b, M.L.cj (c (Sum.inr b)) * H.h (H.om' f f') (f' b) =
        M.L.cj (c (Sum.inr (Fin.last r))) * (-algebraMap F E T' * H.Dl f f' r) := by
      rw [Finset.sum_eq_single (Fin.last r)]
      · rw [h_om'_f'U H f f' T' hF', if_pos rfl]
      · intro i _ hi
        rw [h_om'_f'U H f f' T' hF', if_neg hi, mul_zero]
      · intro h'
        exact absurd (Finset.mem_univ _) h'
    rw [s1, s2] at h2
    have k := key2 (Fin.last r)
    rw [adj_last] at k
    have kc := congrArg M.L.cj k
    rw [map_mul, map_mul, map_mul, AlgEquiv.commutes] at kc
    rw [map_mul] at hG
    have hX : M.L.cj (c (Sum.inl (Fin.last r))) *
        (H.Dl f f' (r + 1) * M.L.cj (H.Dl f f' (r + 1)) -
          algebraMap F E T * algebraMap F E T' * (H.Dl f f' r * M.L.cj (H.Dl f f' r))) = 0 := by
      linear_combination M.L.cj (H.Dl f f' (r + 1)) * h2 + (algebraMap F E T' * H.Dl f f' r) * kc
    have hX0 := hG.mul_left_eq_zero.mp hX
    have := congrArg M.L.cj hX0
    rwa [M.L.cj_cj, map_zero] at this
  have hy : ∀ b, c (Sum.inr b) = 0 := by
    intro b
    have k := key2 b
    rw [hxl, mul_zero, mul_zero] at k
    exact hD.mul_right_eq_zero.mp k
  have hy0 : ∑ b, c (Sum.inr b) • f' b = 0 := by
    apply Finset.sum_eq_zero
    intro b _
    rw [hy b, zero_smul]
  rw [hy0, add_zero, Fin.sum_univ_castSucc, hxl, zero_smul, add_zero]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem nu_mul (f f' : Fin (r + 1) → V) (T' : F) (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T')
    (hD : IsUnit (H.Dl f f' (r + 1))) :
    H.h (omP H f f') (omP H f f') * (H.Dl f f' (r + 1) * M.L.cj (H.Dl f f' (r + 1))) =
      -algebraMap F E T' * (H.Dl f f' r * M.L.cj (H.Dl f f' r)) := by
  rw [omP, H.h_smul_left, h_smul_right, h_om'_om'U H f f' T' hF']
  have h1 : Ring.inverse (H.Dl f f' (r + 1)) * H.Dl f f' (r + 1) = 1 := Ring.inverse_mul_cancel _ hD
  have h2 : M.L.cj (Ring.inverse (H.Dl f f' (r + 1))) * M.L.cj (H.Dl f f' (r + 1)) = 1 := by
    rw [← map_mul, h1, map_one]
  linear_combination (-algebraMap F E T' * (H.Dl f f' r * M.L.cj (H.Dl f f' r)) *
    M.L.cj (Ring.inverse (H.Dl f f' (r + 1))) * M.L.cj (H.Dl f f' (r + 1))) * h1 +
    (-algebraMap F E T' * (H.Dl f f' r * M.L.cj (H.Dl f f' r))) * h2

theorem eta_unit (f f' : Fin (r + 1) → V) (T T' : F) (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T')
    (hD : IsUnit (H.Dl f f' (r + 1)))
    (hG : IsUnit (H.Dl f f' (r + 1) * M.L.cj (H.Dl f f' (r + 1)) -
      algebraMap F E (T * T') * (H.Dl f f' r * M.L.cj (H.Dl f f' r)))) :
    IsUnit (1 + algebraMap F E T * H.h (omP H f f') (omP H f f')) := by
  have key : (1 + algebraMap F E T * H.h (omP H f f') (omP H f f')) *
      (H.Dl f f' (r + 1) * M.L.cj (H.Dl f f' (r + 1))) =
      H.Dl f f' (r + 1) * M.L.cj (H.Dl f f' (r + 1)) -
        algebraMap F E (T * T') * (H.Dl f f' r * M.L.cj (H.Dl f f' r)) := by
    rw [map_mul]
    linear_combination (algebraMap F E T) * nu_mul H f f' T' hF' hD
  have : IsUnit ((1 + algebraMap F E T * H.h (omP H f f') (omP H f f')) *
      (H.Dl f f' (r + 1) * M.L.cj (H.Dl f f' (r + 1)))) := by rw [key]; exact hG
  exact isUnit_of_mul_isUnit_left this

private theorem h_sub_left' (x y z : V) : H.h (x - y) z = H.h x z - H.h y z := by
  rw [sub_eq_add_neg, H.h_add_left, ← neg_one_smul E y, H.h_smul_left]
  ring

theorem decompU (f f' : Fin (r + 1) → V) (T T' : F) (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T)
    (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') (hD : IsUnit (H.Dl f f' (r + 1)))
    (hG : IsUnit (H.Dl f f' (r + 1) * M.L.cj (H.Dl f f' (r + 1)) -
      algebraMap F E (T * T') * (H.Dl f f' r * M.L.cj (H.Dl f f' r))))
    (u : V) (hu : u ∈ Submodule.span E (Set.range (Sum.elim f f'))) (hX : u ∈ H.perp (H.X f))
    (α β : E)
    (hα : α * (1 + algebraMap F E T * H.h (omP H f f') (omP H f f')) =
      H.h u (omP H f f') - H.h (omP H f f') (omP H f f') * H.h u (f (Fin.last r)))
    (hβ : β = H.h u (f (Fin.last r)) + algebraMap F E T * α) :
    u - (α • f (Fin.last r) + β • omP H f f') ∈ H.X f := by
  have hom'eq : H.om' f f' = H.Dl f f' (r + 1) • omP H f f' := by
    unfold omP
    rw [smul_smul, Ring.mul_inverse_cancel _ hD, one_smul]
  apply mem_X_ofU H f f' T T' hF hF' hD hG
  · refine Submodule.sub_mem _ hu (Submodule.add_mem _ (Submodule.smul_mem _ _ ?_)
      (Submodule.smul_mem _ _ (omP_mem_span H f f')))
    exact Submodule.subset_span ⟨Sum.inl (Fin.last r), rfl⟩
  · intro a
    rw [h_sub_left', HermSp.h_add_left, HermSp.h_smul_left, HermSp.h_smul_left,
      h_omP_f H f f' hD a]
    by_cases ha : a = Fin.last r
    · subst ha
      rw [if_pos rfl, hF.2, hβ]
      ring
    · rw [if_neg ha, hF.1 (Fin.last r) a (Or.inr ha)]
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr ha
      rw [(mem_perpX_iff H f u).mp hX i]
      ring
  · have hw : H.h (u - (α • f (Fin.last r) + β • omP H f f')) (omP H f f') = 0 := by
      rw [h_sub_left', HermSp.h_add_left, HermSp.h_smul_left, HermSp.h_smul_left,
        h_z_omP H f f' hD, hβ]
      linear_combination -hα
    rw [hom'eq, HermSp.h_smul_left, H.h_herm _ (omP H f f'), hw, map_zero, mul_zero]

theorem mkW_decompU (f f' : Fin (r + 1) → V) (T T' : F) (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T)
    (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') (hD : IsUnit (H.Dl f f' (r + 1)))
    (hG : IsUnit (H.Dl f f' (r + 1) * M.L.cj (H.Dl f f' (r + 1)) -
      algebraMap F E (T * T') * (H.Dl f f' r * M.L.cj (H.Dl f f' r))))
    (u : ↥(H.perp (H.X f))) (hu : (u : V) ∈ Submodule.span E (Set.range (Sum.elim f f'))) (α : E)
    (hα : α * (1 + algebraMap F E T * H.h (omP H f f') (omP H f f')) =
      H.h u (omP H f f') - H.h (omP H f f') (omP H f f') * H.h u (f (Fin.last r))) :
    H.mkW f u = α • H.mkW f ⟨f (Fin.last r), z_mem H f T hF⟩ +
      (H.h u (f (Fin.last r)) + algebraMap F E T * α) • H.mkW f ⟨omP H f f', omP_mem H f f' hD⟩ := by
  have hmem := decompU H f f' T T' hF hF' hD hG (u : V) hu u.2 α
    (H.h u (f (Fin.last r)) + algebraMap F E T * α) hα rfl
  rw [← map_smul, ← map_smul, ← map_add]
  simp only [HermSp.mkW, Submodule.mkQ_apply]
  rw [Submodule.Quotient.eq, Submodule.mem_comap]
  simpa using hmem

theorem nu_eq (f₁ f₁' f₂ f₂' : Fin (r + 1) → V) (T' : F) (hF₁' : Formalism.MainNotions.ThinScalesBound.FrameK H f₁' T')
    (hF₂' : Formalism.MainNotions.ThinScalesBound.FrameK H f₂' T') (hD₁ : IsUnit (H.Dl f₁ f₁' (r + 1))) (hD₂ : IsUnit (H.Dl f₂ f₂' (r + 1)))
    (hrel : H.Dl f₁ f₁' r * H.Dl f₂ f₂' (r + 1) = H.Dl f₂ f₂' r * H.Dl f₁ f₁' (r + 1)) :
    H.h (omP H f₁ f₁') (omP H f₁ f₁') = H.h (omP H f₂ f₂') (omP H f₂ f₂') := by
  have e₁ := nu_mul H f₁ f₁' T' hF₁' hD₁
  have e₂ := nu_mul H f₂ f₂' T' hF₂' hD₂
  have crel : M.L.cj (H.Dl f₁ f₁' r) * M.L.cj (H.Dl f₂ f₂' (r + 1)) =
      M.L.cj (H.Dl f₂ f₂' r) * M.L.cj (H.Dl f₁ f₁' (r + 1)) := by
    rw [← map_mul, ← map_mul, hrel]
  have hN : IsUnit ((H.Dl f₁ f₁' (r + 1) * M.L.cj (H.Dl f₁ f₁' (r + 1))) *
      (H.Dl f₂ f₂' (r + 1) * M.L.cj (H.Dl f₂ f₂' (r + 1)))) :=
    (hD₁.mul (hD₁.map M.L.cj)).mul (hD₂.mul (hD₂.map M.L.cj))
  apply hN.mul_right_cancel
  linear_combination (H.Dl f₂ f₂' (r + 1) * M.L.cj (H.Dl f₂ f₂' (r + 1))) * e₁ -
    (H.Dl f₁ f₁' (r + 1) * M.L.cj (H.Dl f₁ f₁' (r + 1))) * e₂ -
    algebraMap F E T' * (M.L.cj (H.Dl f₁ f₁' r) * M.L.cj (H.Dl f₂ f₂' (r + 1))) * hrel -
    algebraMap F E T' * (H.Dl f₂ f₂' r * H.Dl f₁ f₁' (r + 1)) * crel

theorem mkW_transport {f₁ f₁' f₂ f₂' : Fin (r + 1) → V} {T T' : F}
    (hF₁ : Formalism.MainNotions.ThinScalesBound.FrameK H f₁ T) (hF₁' : Formalism.MainNotions.ThinScalesBound.FrameK H f₁' T')
    (hF₂ : Formalism.MainNotions.ThinScalesBound.FrameK H f₂ T) (hF₂' : Formalism.MainNotions.ThinScalesBound.FrameK H f₂' T')
    (hD₁ : IsUnit (H.Dl f₁ f₁' (r + 1))) (hD₂ : IsUnit (H.Dl f₂ f₂' (r + 1)))
    (hG₁ : IsUnit (H.Dl f₁ f₁' (r + 1) * M.L.cj (H.Dl f₁ f₁' (r + 1)) -
      algebraMap F E (T * T') * (H.Dl f₁ f₁' r * M.L.cj (H.Dl f₁ f₁' r))))
    (hG₂ : IsUnit (H.Dl f₂ f₂' (r + 1) * M.L.cj (H.Dl f₂ f₂' (r + 1)) -
      algebraMap F E (T * T') * (H.Dl f₂ f₂' r * M.L.cj (H.Dl f₂ f₂' r))))
    (hν : H.h (omP H f₁ f₁') (omP H f₁ f₁') = H.h (omP H f₂ f₂') (omP H f₂ f₂'))
    (φ : H.Wb f₁ ≃ₗ[E] H.Wb f₂)
    (hz : φ (H.mkW f₁ ⟨f₁ (Fin.last r), z_mem H f₁ T hF₁⟩) = H.mkW f₂ ⟨f₂ (Fin.last r), z_mem H f₂ T hF₂⟩)
    (ho : φ (H.mkW f₁ ⟨omP H f₁ f₁', omP_mem H f₁ f₁' hD₁⟩) = H.mkW f₂ ⟨omP H f₂ f₂', omP_mem H f₂ f₂' hD₂⟩)
    (u₁ : ↥(H.perp (H.X f₁))) (hu₁ : (u₁ : V) ∈ Submodule.span E (Set.range (Sum.elim f₁ f₁')))
    (u₂ : ↥(H.perp (H.X f₂))) (hu₂ : (u₂ : V) ∈ Submodule.span E (Set.range (Sum.elim f₂ f₂')))
    (c1 : H.h u₂ (f₂ (Fin.last r)) = H.h u₁ (f₁ (Fin.last r)))
    (c2 : H.h u₂ (omP H f₂ f₂') = H.h u₁ (omP H f₁ f₁')) :
    H.mkW f₂ u₂ = φ (H.mkW f₁ u₁) := by
  have e1 := eta_unit H f₁ f₁' T T' hF₁' hD₁ hG₁
  obtain ⟨α, hα₁⟩ : ∃ α : E, α * (1 + algebraMap F E T * H.h (omP H f₁ f₁') (omP H f₁ f₁')) =
      H.h u₁ (omP H f₁ f₁') - H.h (omP H f₁ f₁') (omP H f₁ f₁') * H.h u₁ (f₁ (Fin.last r)) :=
    ⟨(H.h u₁ (omP H f₁ f₁') - H.h (omP H f₁ f₁') (omP H f₁ f₁') * H.h u₁ (f₁ (Fin.last r))) *
      Ring.inverse (1 + algebraMap F E T * H.h (omP H f₁ f₁') (omP H f₁ f₁')),
      by rw [mul_assoc, Ring.inverse_mul_cancel _ e1, mul_one]⟩
  have hα₂ : α * (1 + algebraMap F E T * H.h (omP H f₂ f₂') (omP H f₂ f₂')) =
      H.h u₂ (omP H f₂ f₂') - H.h (omP H f₂ f₂') (omP H f₂ f₂') * H.h u₂ (f₂ (Fin.last r)) := by
    rw [← hν, c1, c2]
    exact hα₁
  rw [mkW_decompU H f₂ f₂' T T' hF₂ hF₂' hD₂ hG₂ u₂ hu₂ α hα₂, c1,
    mkW_decompU H f₁ f₁' T T' hF₁ hF₁' hD₁ hG₁ u₁ hu₁ α hα₁, map_add, map_smul, map_smul, hz, ho]

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG
