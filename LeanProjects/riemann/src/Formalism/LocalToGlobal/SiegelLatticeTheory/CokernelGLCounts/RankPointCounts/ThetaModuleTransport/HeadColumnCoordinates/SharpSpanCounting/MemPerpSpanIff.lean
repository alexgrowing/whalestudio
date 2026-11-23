import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.HSumRight

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA

namespace Formalism.L2.SG.LocalCountModules.LocCntCommon

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)

theorem mem_perp_span_iff {ι : Type} (s : ι → V) (v : V) :
    v ∈ H.perp (Submodule.span E (Set.range s)) ↔ ∀ i, H.h v (s i) = 0 := by
  constructor
  · intro hv i
    exact hv _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro hv x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hv i
    | zero => exact h_zero_right H v
    | add x y _ _ hx hy => rw [h_add_right, hx, hy, add_zero]
    | smul a x _ hx => rw [h_smul_right, hx, mul_zero]

theorem mem_perpX_iff {r : ℕ} (f : Fin (r + 1) → V) (v : V) :
    v ∈ H.perp (H.X f) ↔ ∀ a : Fin r, H.h v (f a.castSucc) = 0 :=
  mem_perp_span_iff H _ v

variable {r : ℕ}

theorem h_om'_f (f f' : Fin (r + 1) → V) (a : Fin (r + 1)) :
    H.h (H.om' f f') (f a) = if a = Fin.last r then (H.Zhat f f').det else 0 := by
  have : H.h (H.om' f f') (f a) = ((H.Zhat f f') * (H.Zhat f f').adjugate) a (Fin.last r) := by
    unfold HermSp.om'
    rw [h_sum_left, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [mul_comm]; rfl
  rw [this, Matrix.mul_adjugate, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

theorem h_om_f' (f f' : Fin (r + 1) → V) (b : Fin (r + 1)) :
    H.h (H.om f f') (f' b) = if b = Fin.last r then M.L.cj (H.Zhat f f').det else 0 := by
  have : H.h (H.om f f') (f' b) =
      M.L.cj (((H.Zhat f f').adjugate * (H.Zhat f f')) (Fin.last r) b) := by
    unfold HermSp.om
    rw [h_sum_left, Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, H.h_herm (f' b) (f a)]
    rfl
  rw [this, Matrix.adjugate_mul, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases h : b = Fin.last r
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h, mul_zero, map_zero]

def omP (f f' : Fin (r + 1) → V) : V := Ring.inverse (H.Dl f f' (r + 1)) • H.om' f f'

def omQ (f f' : Fin (r + 1) → V) : V := M.L.cj (Ring.inverse (H.Dl f f' (r + 1))) • H.om f f'

theorem h_omP_f (f f' : Fin (r + 1) → V) (hD : IsUnit (H.Dl f f' (r + 1))) (a : Fin (r + 1)) :
    H.h (omP H f f') (f a) = if a = Fin.last r then 1 else 0 := by
  rw [omP, H.h_smul_left, h_om'_f, ← dl_full]
  split_ifs
  · exact Ring.inverse_mul_cancel _ hD
  · exact mul_zero _

theorem h_omQ_f' (f f' : Fin (r + 1) → V) (hD : IsUnit (H.Dl f f' (r + 1))) (b : Fin (r + 1)) :
    H.h (omQ H f f') (f' b) = if b = Fin.last r then 1 else 0 := by
  rw [omQ, H.h_smul_left, h_om_f', ← dl_full]
  split_ifs
  · rw [← map_mul, Ring.inverse_mul_cancel _ hD, map_one]
  · exact mul_zero _

theorem omP_mem (f f' : Fin (r + 1) → V) (hD : IsUnit (H.Dl f f' (r + 1))) :
    omP H f f' ∈ H.perp (H.X f) := by
  rw [mem_perpX_iff]
  intro a
  rw [h_omP_f H f f' hD, if_neg (Fin.castSucc_lt_last a).ne]

theorem omQ_mem (f f' : Fin (r + 1) → V) (hD : IsUnit (H.Dl f f' (r + 1))) :
    omQ H f f' ∈ H.perp (H.X f') := by
  rw [mem_perpX_iff]
  intro a
  rw [h_omQ_f' H f f' hD, if_neg (Fin.castSucc_lt_last a).ne]

theorem z_mem (f : Fin (r + 1) → V) (T : F) (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T) :
    f (Fin.last r) ∈ H.perp (H.X f) := by
  rw [mem_perpX_iff]
  intro a
  exact hF.1 _ _ (Or.inr (Fin.castSucc_lt_last a).ne)

theorem h_X_perp (f : Fin (r + 1) → V) (v : V) (hv : v ∈ H.perp (H.X f)) (x : V) (hx : x ∈ H.X f) :
    H.h x v = 0 := by
  rw [H.h_herm v x, hv x hx, map_zero]

def coordW (f : Fin (r + 1) → V) (v v' : V) (hv : v ∈ H.perp (H.X f)) (hv' : v' ∈ H.perp (H.X f)) :
    H.Wb f →ₗ[E] E × E :=
  Submodule.liftQ _ (((hLm H v).prod (hLm H v')).comp (H.perp (H.X f)).subtype) (by
    intro x hx
    rw [Submodule.mem_comap] at hx
    rw [LinearMap.mem_ker]
    exact Prod.ext (h_X_perp H f v hv _ hx) (h_X_perp H f v' hv' _ hx))

theorem coordW_mk (f : Fin (r + 1) → V) (v v' : V) (hv : v ∈ H.perp (H.X f))
    (hv' : v' ∈ H.perp (H.X f)) (x : ↥(H.perp (H.X f))) :
    coordW H f v v' hv hv' (H.mkW f x) = (H.h x v, H.h x v') := rfl

theorem coordW_comp {f₁ f₂ : Fin (r + 1) → V} (φ : H.Wb f₁ ≃ₗ[E] H.Wb f₂) (hφ : H.IsIsomW φ)
    (v₁ v₁' v₂ v₂' : V) (h₁ : v₁ ∈ H.perp (H.X f₁)) (h₁' : v₁' ∈ H.perp (H.X f₁))
    (h₂ : v₂ ∈ H.perp (H.X f₂)) (h₂' : v₂' ∈ H.perp (H.X f₂))
    (e : φ (H.mkW f₁ ⟨v₁, h₁⟩) = H.mkW f₂ ⟨v₂, h₂⟩) (e' : φ (H.mkW f₁ ⟨v₁', h₁'⟩) = H.mkW f₂ ⟨v₂', h₂'⟩)
    (w : H.Wb f₁) : coordW H f₂ v₂ v₂' h₂ h₂' (φ w) = coordW H f₁ v₁ v₁' h₁ h₁' w := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ w
  obtain ⟨x₂, hx₂⟩ := Submodule.mkQ_surjective _ (φ (H.mkW f₁ x))
  have hx₂' : φ (H.mkW f₁ x) = H.mkW f₂ x₂ := hx₂.symm
  change coordW H f₂ v₂ v₂' h₂ h₂' (φ (H.mkW f₁ x)) = coordW H f₁ v₁ v₁' h₁ h₁' (H.mkW f₁ x)
  rw [hx₂', coordW_mk, coordW_mk]
  exact Prod.ext (hφ x ⟨v₁, h₁⟩ x₂ ⟨v₂, h₂⟩ hx₂' e) (hφ x ⟨v₁', h₁'⟩ x₂ ⟨v₂', h₂'⟩ hx₂' e')

end Formalism.L2.SG.LocalCountModules.LocCntCommon
