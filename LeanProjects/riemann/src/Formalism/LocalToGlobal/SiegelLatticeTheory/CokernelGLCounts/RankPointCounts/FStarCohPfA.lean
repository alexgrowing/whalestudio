import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.LinQRawRange

noncomputable section

open ValuativeRel Matrix

namespace Formalism.MainNotions.S.Loc.HermSp.CohU

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)

def hL (y : V) : V →ₗ[E] E where
  toFun x := H.h x y
  map_add' x x' := H.h_add_left x x' y
  map_smul' a x := by simpa using H.h_smul_left a x y

theorem hL_apply (x y : V) : hL H y x = H.h x y := rfl

def GramInv {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → V) : Prop :=
  ∃ N : Matrix ι ι E, (∀ i j, N i j ∈ M.L.O) ∧ N * H.gram v = 1

variable {H}

theorem h_right_zero {ι : Type} {v : ι → V} {w : V} (hw : ∀ i, H.h w (v i) = 0) {y : V}
    (hy : y ∈ Submodule.span E (Set.range v)) : H.h w y = 0 := by
  have hspan : Submodule.span E (Set.range v) ≤ LinearMap.ker (hL H w) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, hL_apply, H.h_herm, hw i, map_zero]
  have hy' : H.h y w = 0 := by
    have h1 := hspan hy
    rwa [LinearMap.mem_ker, hL_apply] at h1
  rw [H.h_herm, hy', map_zero]

private theorem h_fintype_sum_smul_left {ι : Type} [Fintype ι] (v : ι → V) (c : ι → E) (y : V) :
    H.h (∑ j, c j • v j) y = ∑ j, c j * H.h (v j) y := by
  have h1 := map_sum (hL H y) (fun j => c j • v j) Finset.univ
  simp only [map_smul, smul_eq_mul, hL_apply] at h1
  exact h1

private theorem h_sum_smul_eq_gram_mulVec {ι : Type} [Fintype ι] (v : ι → V) (c : ι → E) (i : ι) :
    H.h (∑ j, c j • v j) (v i) = (H.gram v *ᵥ c) i := by
  rw [h_fintype_sum_smul_left]
  show ∑ j, c j * H.h (v j) (v i) = ∑ j, H.h (v j) (v i) * c j
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem eq_zero_of_orth {ι : Type} [Fintype ι] [DecidableEq ι] {v : ι → V} (hN : GramInv H v) {z : V}
    (hz : z ∈ Submodule.span E (Set.range v)) (h0 : ∀ i, H.h z (v i) = 0) : z = 0 := by
  obtain ⟨N, -, hNG⟩ := hN
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (R := E)).1 hz
  have hc : H.gram v *ᵥ c = 0 := by
    funext i
    rw [← h_sum_smul_eq_gram_mulVec v c i]
    exact h0 i
  have hc0 : c = 0 := by
    rw [← Matrix.one_mulVec c, ← hNG, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_zero]
  subst hc0
  simp

private theorem h_sub_left' (x y z : V) : H.h (x - y) z = H.h x z - H.h y z := by
  have h1 := (hL H z).map_sub x y
  rw [hL_apply, hL_apply, hL_apply] at h1
  exact h1

theorem decomp {ι : Type} [Fintype ι] [DecidableEq ι] {v : ι → V} (hN : GramInv H v) {Λ : Submodule M.L.O V}
    (hI : ∀ x ∈ Λ, ∀ y ∈ Λ, H.h x y ∈ M.L.O) (hv : ∀ i, v i ∈ Λ) {x : V} (hx : x ∈ Λ) :
    ∃ c : ι → E, (∀ j, c j ∈ M.L.O) ∧ ∀ i, H.h (x - ∑ j, c j • v j) (v i) = 0 := by
  obtain ⟨N, hNO, hNG⟩ := hN
  have hGN : H.gram v * N = 1 := by
    first
      | exact mul_eq_one_comm.1 hNG
      | (rw [← Matrix.inv_eq_left_inv hNG]
         exact Matrix.mul_nonsing_inv _ (Matrix.isUnit_det_of_left_inverse hNG))
  refine ⟨N *ᵥ fun k => H.h x (v k), fun j => ?_, fun i => ?_⟩
  · show ∑ k, N j k * H.h x (v k) ∈ M.L.O
    exact sum_mem fun k _ => mul_mem (hNO j k) (hI x hx (v k) (hv k))
  · rw [h_sub_left', h_sum_smul_eq_gram_mulVec v _ i, Matrix.mulVec_mulVec, hGN, Matrix.one_mulVec]
    exact sub_self _

theorem comb_mem_span {ι : Type} [Fintype ι] (v : ι → V) (c : ι → E) :
    ∑ j, c j • v j ∈ Submodule.span E (Set.range v) :=
  Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem comb_mem_lat {ι : Type} [Fintype ι] {v : ι → V} {Λ : Submodule M.L.O V} (hv : ∀ i, v i ∈ Λ) {c : ι → E}
    (hc : ∀ j, c j ∈ M.L.O) : ∑ j, c j • v j ∈ Λ :=
  Submodule.sum_mem _ fun j _ => Λ.smul_mem (⟨c j, hc j⟩ : M.L.O) (hv j)

theorem le_of_Lset {r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {v : ι → V} (hN : GramInv H v)
    {f : Fin (r + 1) → V} (hX : H.X f ≤ Submodule.span E (Set.range v)) {Λ₁ Λ₂ : Submodule M.L.O V}
    (hI1 : ∀ x ∈ Λ₁, ∀ y ∈ Λ₁, H.h x y ∈ M.L.O) (hI2 : ∀ x ∈ Λ₂, ∀ y ∈ Λ₂, H.h x y ∈ M.L.O)
    (hv1 : ∀ i, v i ∈ Λ₁) (hv2 : ∀ i, v i ∈ Λ₂) (hL : H.Lset Λ₁ f ⊆ H.Lset Λ₂ f) : Λ₁ ≤ Λ₂ := by
  intro x hx
  obtain ⟨c, hcO, hc⟩ := decomp hN hI1 hv1 hx
  have hs2 : ∑ j, c j • v j ∈ Λ₂ := comb_mem_lat hv2 hcO
  have hperp : x - ∑ j, c j • v j ∈ H.perp (H.X f) := by
    show ∀ z ∈ H.X f, H.h (x - ∑ j, c j • v j) z = 0
    intro z hz
    exact h_right_zero hc (hX hz)
  have hx0 : x - ∑ j, c j • v j ∈ Λ₁ := Λ₁.sub_mem hx (comb_mem_lat hv1 hcO)
  have hmem : H.mkW f ⟨x - ∑ j, c j • v j, hperp⟩ ∈ H.Lset Λ₁ f :=
    ⟨⟨x - ∑ j, c j • v j, hperp⟩, hx0, rfl⟩
  obtain ⟨y, hyΛ, hyeq⟩ := hL hmem
  obtain ⟨d, hdO, hd⟩ := decomp hN hI2 hv2 hyΛ
  have ht2 : ∑ j, d j • v j ∈ Λ₂ := comb_mem_lat hv2 hdO
  have hdiff : (y : V) - (x - ∑ j, c j • v j) ∈ H.X f := by
    have hk := LinearMap.sub_mem_ker_iff.2 hyeq
    rw [Formalism.MainNotions.S.Loc.HermSp.mkW, Submodule.ker_mkQ, Submodule.mem_comap] at hk
    simpa using hk
  have hzero : (x - ∑ j, c j • v j) - ((y : V) - ∑ j, d j • v j) = 0 := by
    apply eq_zero_of_orth hN
    · have h1 : (y : V) - (x - ∑ j, c j • v j) ∈ Submodule.span E (Set.range v) := hX hdiff
      have h2 : ∑ j, d j • v j ∈ Submodule.span E (Set.range v) := comb_mem_span v d
      have h3 : (x - ∑ j, c j • v j) - ((y : V) - ∑ j, d j • v j) =
          ∑ j, d j • v j - ((y : V) - (x - ∑ j, c j • v j)) := by abel
      rw [h3]
      exact Submodule.sub_mem _ h2 h1
    · intro i
      rw [h_sub_left', hc i, hd i, sub_zero]
  have hx0' : x - ∑ j, c j • v j ∈ Λ₂ := by
    rw [sub_eq_zero.1 hzero]
    exact Λ₂.sub_mem hyΛ ht2
  have h4 := Λ₂.add_mem hx0' hs2
  rwa [sub_add_cancel] at h4

theorem lat_eq_of_Lset {r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {v : ι → V} (hN : GramInv H v)
    {f : Fin (r + 1) → V} (hX : H.X f ≤ Submodule.span E (Set.range v)) {Λ₁ Λ₂ : Submodule M.L.O V}
    (h1 : H.IsSelfDual Λ₁) (h2 : H.IsSelfDual Λ₂) (hv1 : ∀ i, v i ∈ Λ₁) (hv2 : ∀ i, v i ∈ Λ₂)
    (hL : H.Lset Λ₁ f = H.Lset Λ₂ f) : Λ₁ = Λ₂ := by
  have hI1 : ∀ x ∈ Λ₁, ∀ y ∈ Λ₁, H.h x y ∈ M.L.O := fun x hx => (h1.2.2 x).1 hx
  have hI2 : ∀ x ∈ Λ₂, ∀ y ∈ Λ₂, H.h x y ∈ M.L.O := fun x hx => (h2.2.2 x).1 hx
  exact le_antisymm (le_of_Lset hN hX hI1 hI2 hv1 hv2 hL.subset)
    (le_of_Lset hN hX hI2 hI1 hv2 hv1 hL.symm.subset)

theorem f_mem_MMfam {r : ℕ} (t : Term V M r) (a : Fin (r + 1)) : t.f a ∈ Set.range (H.MMfam t) := by
  refine ⟨Sum.inl a, ?_⟩
  unfold Formalism.MainNotions.S.Loc.HermSp.MMfam
  first
    | (generalize M.split = s
       cases s <;> rfl)
    | (rcases hs : M.split with _ | g <;> simp [hs])

theorem X_le_MMfam {r : ℕ} (t : Term V M r) : H.X t.f ≤ Submodule.span E (Set.range (H.MMfam t)) := by
  unfold Formalism.MainNotions.S.Loc.HermSp.X
  apply Submodule.span_mono
  rintro _ ⟨a, rfl⟩
  exact f_mem_MMfam (H := H) t a.castSucc

end Formalism.MainNotions.S.Loc.HermSp.CohU
