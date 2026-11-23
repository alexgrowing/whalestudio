import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.TvMapApply
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.ExistsMulEqOneAddSmulOfRowsGe

noncomputable section

open scoped Classical

namespace PI.NRL

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

theorem smul_coe (o : 𝓞 E) (w : S.V) : (o : E) • w = o • w := by
  exact IsScalarTower.algebraMap_smul E o w

theorem herm_eq (x y : S.V) : S.hT y x = star (S.hT x y) := by
  first
    | exact (S.herm x y).symm
    | exact (S.herm.eq x y).symm
    | (rw [← S.herm x y]; rfl)
    | (rw [← S.herm.eq x y]; rfl)

theorem tvMap_isom (e v : S.V) (l : E) (hee : S.hT e e = 0) (hev : S.hT e v = 0)
    (hl : l + star l = -S.hT v v) (x y : S.V) :
    S.hT (tvMap e v l x) (tvMap e v l y) = S.hT x y := by
  have hve : S.hT v e = 0 := by rw [herm_eq, hev, star_zero]
  have hxe : S.hT x e = star (S.hT e x) := herm_eq e x
  have hxv : S.hT x v = star (S.hT v x) := herm_eq v x
  rw [tvMap_apply, tvMap_apply]
  simp only [map_add, map_sub, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, hee, hev, hve, hxe, hxv, smul_eq_mul, starRingEnd_apply, star_mul',
    mul_zero, zero_mul, add_zero, sub_zero, zero_add]
  linear_combination (star (S.hT e x) * S.hT e y) * hl

def IntLat (Λ : Submodule (𝓞 E) S.V) : Prop := ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ o : 𝓞 E, S.hT x y = (o : E)

theorem tvMap_mem {Λ : Submodule (𝓞 E) S.V} (hint : IntLat Λ) {e v : S.V} (he : e ∈ Λ) (hv : v ∈ Λ)
    (l : 𝓞 E) {y : S.V} (hy : y ∈ Λ) : tvMap e v (l : E) y ∈ Λ := by
  obtain ⟨oa, ha⟩ := hint v hv y hy
  obtain ⟨ob, hb⟩ := hint e he y hy
  rw [tvMap_apply, ha, hb, mul_smul]
  simp only [smul_coe]
  exact Λ.add_mem (Λ.sub_mem (Λ.add_mem hy (Λ.smul_mem oa he)) (Λ.smul_mem ob hv))
    (Λ.smul_mem l (Λ.smul_mem ob he))

theorem gmap_eq_iff (n : S.V ≃ₗ[E] S.V) (Λ : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap n Λ = Λ ↔ (∀ y ∈ Λ, n y ∈ Λ) ∧ (∀ y ∈ Λ, ∃ w ∈ Λ, n w = y) := by
  unfold Formalism.HermitianLatticesTheory.gmap
  constructor
  · intro h
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · rw [← h]
      exact Submodule.mem_map_of_mem hy
    · rw [← h] at hy
      obtain ⟨w, hw, hwy⟩ := Submodule.mem_map.mp hy
      exact ⟨w, hw, hwy⟩
  · rintro ⟨h1, h2⟩
    apply le_antisymm
    · intro x hx
      obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hx
      exact h1 w hw
    · intro y hy
      obtain ⟨w, hw, hwy⟩ := h2 y hy
      exact Submodule.mem_map.mpr ⟨w, hw, hwy⟩

def tvEquiv (e v : S.V) (l : E) (hee : S.hT e e = 0) (hev : S.hT e v = 0) (hve : S.hT v e = 0) :
    S.V ≃ₗ[E] S.V :=
  LinearEquiv.ofLinearMap (tvMap e v l) (tvMap e (-v) (-S.hT v v - l))
    (by
      ext y
      have h := tvMap_comp e (-v) (-S.hT v v - l) l hee (by simp [hev]) (by simp [hve]) y
      rw [neg_neg] at h
      have hc : -S.hT v v - l + S.hT (-v) (-v) + l = 0 := by
        simp only [map_neg, LinearMap.neg_apply, neg_neg]; ring
      simp only [LinearMap.comp_apply, LinearMap.id_apply, h, hc]
      simp)
    (by
      ext y
      have h := tvMap_comp e v l (-S.hT v v - l) hee hev hve y
      have hc : l + S.hT v v + (-S.hT v v - l) = 0 := by ring
      simp only [LinearMap.comp_apply, LinearMap.id_apply, h, hc]
      simp)

theorem tvEquiv_apply (e v : S.V) (l : E) (hee hev hve) (y : S.V) :
    tvEquiv (S := S) e v l hee hev hve y = tvMap e v l y := rfl

theorem span_zero {s : Set S.V} {φ : S.V →ₗ[E] E} (h : ∀ y ∈ s, φ y = 0) {x : S.V}
    (hx : x ∈ Submodule.span E s) : φ x = 0 := by
  have hle : Submodule.span E s ≤ LinearMap.ker φ :=
    Submodule.span_le.mpr fun y hy => LinearMap.mem_ker.mpr (h y hy)
  exact LinearMap.mem_ker.mp (hle hx)

variable {r : ℕ} {T : E}

theorem e_mem_Xflag (F : LFlag S r T) (a : Fin r) (j : ℕ) (h : a.val < j) : F.fl.e a ∈ Xflag F j := by
  show F.fl.e a ∈ Submodule.span E (F.fl.e '' {i | i.1 < j})
  exact Submodule.subset_span ⟨a, h, rfl⟩

theorem e_mem_Xsp (F : LFlag S r T) (a : Fin r) : F.fl.e a ∈ Xsp F := by
  show F.fl.e a ∈ Submodule.span E (Set.range F.fl.e)
  exact Submodule.subset_span ⟨a, rfl⟩

theorem hT_e_frame (F : LFlag S r T) (a : Fin r) (b : Fin (r + 1)) : S.hT (F.fl.e a) (frame F b) = 0 := by
  show S.hT (F.fl.e a) (Fin.snoc (α := fun _ => S.V) F.fl.e F.fl.z b) = 0
  cases b using Fin.lastCases with
  | last =>
    rw [Fin.snoc_last]
    exact F.fl.z_orth a
  | cast c =>
    rw [Fin.snoc_castSucc]
    exact F.fl.e_iso a c

theorem tv_mem_NLam (Λ : Submodule (𝓞 E) S.V) (hint : IntLat Λ) (F : LFlag S r T) (a : Fin r)
    (hea : F.fl.e a ∈ Λ) (v : S.V) (hv : v ∈ Λ) (hperp : ∀ i : Fin r, i ≤ a → S.hT v (F.fl.e i) = 0)
    (l : 𝓞 E) (hl : (l : E) + star (l : E) = -S.hT v v) (hee hev hve) :
    tvEquiv (F.fl.e a) v (l : E) hee hev hve ∈ NLam Λ F := by
  simp only [NLam, IsAutLam, Set.mem_setOf_eq]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro x y
    exact tvMap_isom (F.fl.e a) v (l : E) hee hev hl x y
  · rw [gmap_eq_iff]
    refine ⟨fun y hy => tvMap_mem hint hea hv l hy, fun y hy => ?_⟩
    obtain ⟨ov, hov⟩ := hint v hv v hv
    refine ⟨tvMap (F.fl.e a) (-v) ((-ov - l : 𝓞 E) : E) y,
      tvMap_mem hint hea (Λ.neg_mem hv) (-ov - l) hy, ?_⟩
    have hc : ((-ov - l : 𝓞 E) : E) = -S.hT v v - (l : E) := by
      first
        | (rw [hov]; push_cast; ring)
        | (rw [hov]; push_cast)
        | simp [hov]
    have h := tvMap_comp (F.fl.e a) (-v) (-S.hT v v - (l : E)) (l : E) hee (by simp [hev])
      (by simp [hve]) y
    rw [neg_neg] at h
    have hz : -S.hT v v - (l : E) + S.hT (-v) (-v) + (l : E) = 0 := by
      simp only [map_neg, LinearMap.neg_apply, neg_neg]
      ring
    rw [tvEquiv_apply, hc, h, hz, mul_zero, zero_smul, add_zero]
  · intro j x hx
    have hex : S.hT (F.fl.e a) x = 0 :=
      span_zero (fun y hy => by
        obtain ⟨i, _, rfl⟩ := hy
        exact F.fl.e_iso a i) hx
    rw [tvEquiv_apply, tvMap_apply, hex, zero_smul, sub_zero, mul_zero, zero_smul, add_zero,
      add_sub_cancel_left]
    by_cases haj : a.val < j
    · exact Submodule.smul_mem _ _ (e_mem_Xflag F a j haj)
    · have hvx : S.hT v x = 0 :=
        span_zero (φ := S.hT v) (fun y hy => by
          obtain ⟨i, hi, rfl⟩ := hy
          have hi' : i.val < j + 1 := hi
          exact hperp i (by rw [Fin.le_def]; omega)) hx
      rw [hvx, zero_smul]
      exact Submodule.zero_mem _
  · intro x hx
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx
    have hex : S.hT (F.fl.e a) x = 0 := hx _ (e_mem_Xsp F a)
    rw [tvEquiv_apply, tvMap_apply, hex, zero_smul, sub_zero, mul_zero, zero_smul, add_zero,
      add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (e_mem_Xsp F a)

def ActsBy {n : ℕ} (φ : S.V ≃ₗ[E] S.V) (f : Fin n → S.V) (M : Matrix (Fin n) (Fin n) (𝓞 E)) : Prop :=
  ∀ b, φ (f b) = frameAct f M b

theorem actsBy_frameAct {n : ℕ} {φ : S.V ≃ₗ[E] S.V} {f : Fin n → S.V} {M : Matrix (Fin n) (Fin n) (𝓞 E)}
    (h : ActsBy φ f M) (ξ : Matrix (Fin n) (Fin n) (𝓞 E)) (b : Fin n) :
    φ (frameAct f ξ b) = frameAct f (M * ξ) b := by
  have hcoe : ∀ c, ((((M * ξ) c b : 𝓞 E)) : E) = ∑ a, (M c a : E) * (ξ a b : E) := by
    intro c
    rw [Matrix.mul_apply]
    first
      | (push_cast; rfl)
      | push_cast
      | simp
  unfold ActsBy at h
  simp only [frameAct, map_sum, map_smul, h, Finset.smul_sum, smul_smul, hcoe, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => by rw [mul_comm]

theorem actsBy_mul {n : ℕ} {φ ψ : S.V ≃ₗ[E] S.V} {f : Fin n → S.V} {M N : Matrix (Fin n) (Fin n) (𝓞 E)}
    (h1 : ActsBy φ f M) (h2 : ActsBy ψ f N) : ActsBy (φ * ψ) f (M * N) := by
  intro b
  show φ (ψ (f b)) = _
  rw [h2 b, actsBy_frameAct h1 N b]

theorem frameAct_one {n : ℕ} (f : Fin n → S.V) (b : Fin n) : frameAct f 1 b = f b := by
  unfold frameAct
  rw [Finset.sum_eq_single b]
  · simp
  · intro a _ hab
    simp [Matrix.one_apply_ne hab]
  · simp

theorem actsBy_one {n : ℕ} (f : Fin n → S.V) : ActsBy (1 : S.V ≃ₗ[E] S.V) f 1 := by
  intro b
  exact (frameAct_one f b).symm

theorem tv_actsBy (F : LFlag S r T) (a : Fin r) (v : S.V) (l : E) (hee hev hve)
    (w : Fin (r + 1) → 𝓞 E) (hw : ∀ c, S.hT v (frame F c) = (w c : E)) :
    ActsBy (tvEquiv (F.fl.e a) v l hee hev hve) (frame F) (1 + rowMat (Fin.castSucc a) w) := by
  intro c
  rw [tvEquiv_apply, tvMap_apply, hT_e_frame, hw c, zero_smul, sub_zero, mul_zero, zero_smul,
    add_zero]
  have hfa := frameAct_one (frame F) c
  have hfr : frame F (Fin.castSucc a) = F.fl.e a := by
    show Fin.snoc (α := fun _ => S.V) F.fl.e F.fl.z (Fin.castSucc a) = F.fl.e a
    exact Fin.snoc_castSucc ..
  unfold frameAct at hfa ⊢
  simp only [smul_coe] at hfa ⊢
  simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib, hfa, rowMat, ite_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, hfr]

end PI.NRL
