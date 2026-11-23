import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumACut

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA

namespace Formalism.L2.SG.LocalCountModules.LocCntCommon

section O

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem cj_mem_O (L : LocE F E) {x : E} (hx : x ∈ L.O) : L.cj x ∈ L.O := by
  rw [L.O_def] at hx ⊢
  exact hx.map ((L.cj : E →ₐ[F] E).restrictScalars 𝒪[F])

end O

section Pair

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)

theorem h_add_right (x y y' : V) : H.h x (y + y') = H.h x y + H.h x y' := by
  rw [H.h_herm (y + y') x, H.h_add_left, map_add, ← H.h_herm, ← H.h_herm]

theorem h_smul_right (a : E) (x y : V) : H.h x (a • y) = M.L.cj a * H.h x y := by
  rw [H.h_herm (a • y) x, H.h_smul_left, map_mul, ← H.h_herm]

theorem h_zero_right (x : V) : H.h x 0 = 0 := by
  rw [H.h_herm 0 x, H.h_zero_left, map_zero]

def hLm (y : V) : V →ₗ[E] E where
  toFun v := H.h v y
  map_add' x x' := H.h_add_left x x' y
  map_smul' a x := by simp [H.h_smul_left]

theorem h_sum_left {ι : Type} (s : Finset ι) (c : ι → E) (g : ι → V) (y : V) :
    H.h (∑ i ∈ s, c i • g i) y = ∑ i ∈ s, c i * H.h (g i) y := by
  have := map_sum (hLm H y) (fun i => c i • g i) s
  simp only [map_smul, smul_eq_mul] at this
  exact this

def pairing {ι : Type} (g : ι → V) : V →ₗ[E] (ι → E) where
  toFun v i := H.h v (g i)
  map_add' x y := by funext i; simp [H.h_add_left]
  map_smul' a x := by funext i; simp [H.h_smul_left]

def gramH {ι : Type} (g : ι → V) : Matrix ι ι E := Matrix.of fun i j => H.h (g i) (g j)

theorem pairing_sum {ι : Type} [Fintype ι] (g : ι → V) (c : ι → E) :
    pairing H g (∑ i, c i • g i) = Matrix.vecMul c (gramH H g) := by
  funext j
  simp [pairing, gramH, Matrix.vecMul, dotProduct, h_sum_left H]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def pairSpan (g : ι → V) : Submodule.span E (Set.range g) →ₗ[E] (ι → E) :=
  (pairing H g).comp (Submodule.span E (Set.range g)).subtype

theorem pairSpan_bij (g : ι → V) (hG : IsUnit (gramH H g).det) :
    Function.Bijective (pairSpan H g) := by
  constructor
  · intro x y hxy
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 x.2
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 y.2
    have h1 : Matrix.vecMul c (gramH H g) = Matrix.vecMul d (gramH H g) := by
      rw [← pairing_sum, ← pairing_sum, hc, hd]; exact hxy
    have h2 : c = d := by
      have := congrArg (fun w => Matrix.vecMul w (gramH H g)⁻¹) h1
      simpa [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hG] using this
    apply Subtype.ext
    rw [← hc, ← hd, h2]
  · intro y
    refine ⟨⟨∑ i, (Matrix.vecMul y (gramH H g)⁻¹) i • g i,
      (Submodule.mem_span_range_iff_exists_fun E).2 ⟨_, rfl⟩⟩, ?_⟩
    show pairing H g (∑ i, (Matrix.vecMul y (gramH H g)⁻¹) i • g i) = y
    rw [pairing_sum, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hG, Matrix.vecMul_one]

def pairEquiv (g : ι → V) (hG : IsUnit (gramH H g).det) :
    Submodule.span E (Set.range g) ≃ₗ[E] (ι → E) :=
  LinearEquiv.ofBijective (pairSpan H g) (pairSpan_bij H g hG)

theorem pairEquiv_apply (g : ι → V) (hG : IsUnit (gramH H g).det)
    (x : Submodule.span E (Set.range g)) (i : ι) : pairEquiv H g hG x i = H.h x (g i) := rfl

end Pair

section Sharp

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)

theorem mem_MMsharp_iff {r : ℕ} (t : Term V M r) (u : V) :
    u ∈ MMsharp H t ↔ u ∈ Submodule.span E (Set.range (H.MMfam t)) ∧
      ∀ i, H.h u (H.MMfam t i) ∈ M.L.O := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun i => h2 _ (Submodule.subset_span ⟨i, rfl⟩)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun m hm => ?_⟩
    induction hm using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact h2 i
    | zero => rw [h_zero_right]; exact M.L.O.zero_mem
    | add x y _ _ hx hy => rw [h_add_right]; exact M.L.O.add_mem hx hy
    | smul a x _ hx =>
      rw [Subring.smul_def, h_smul_right]; exact M.L.O.mul_mem (cj_mem_O M.L a.2) hx

theorem mem_MMo_iff {r : ℕ} (t : Term V M r) (u : V) :
    u ∈ MMo H t ↔ ∃ c : Fin (r + 1) ⊕ Fin (r + 1) → M.L.O, ∑ i, (c i : E) • H.MMfam t i = u := by
  unfold MMo
  rw [Submodule.mem_span_range_iff_exists_fun]
  simp only [Subring.smul_def]

def sharpEquiv {r : ℕ} (t : Term V M r) (hG : IsUnit (gramH H (H.MMfam t)).det) :
    ↥(MMsharp H t) ≃ₗ[M.L.O] (Fin (r + 1) ⊕ Fin (r + 1) → M.L.O) where
  toFun u i := ⟨H.h u (H.MMfam t i), ((mem_MMsharp_iff H t u).1 u.2).2 i⟩
  map_add' x y := by funext i; apply Subtype.ext; simp [H.h_add_left]
  map_smul' a x := by
    funext i; apply Subtype.ext
    simp [Subring.smul_def, H.h_smul_left]
  invFun y := ⟨(pairEquiv H (H.MMfam t) hG).symm (fun i => (y i : E)), by
    rw [mem_MMsharp_iff]
    refine ⟨Submodule.coe_mem _, fun i => ?_⟩
    have := congrFun ((pairEquiv H (H.MMfam t) hG).apply_symm_apply (fun i => (y i : E))) i
    rw [pairEquiv_apply] at this
    rw [this]; exact (y i).2⟩
  left_inv u := by
    apply Subtype.ext
    have hs : (u : V) ∈ Submodule.span E (Set.range (H.MMfam t)) :=
      ((mem_MMsharp_iff H t u).1 u.2).1
    have : (pairEquiv H (H.MMfam t) hG).symm (fun i => H.h u (H.MMfam t i)) = ⟨u, hs⟩ := by
      rw [LinearEquiv.symm_apply_eq]; funext i; rfl
    simp only [this]
  right_inv y := by
    funext i; apply Subtype.ext
    have := congrFun ((pairEquiv H (H.MMfam t) hG).apply_symm_apply (fun i => (y i : E))) i
    rw [pairEquiv_apply] at this
    exact this

theorem sharpEquiv_apply {r : ℕ} (t : Term V M r) (hG : IsUnit (gramH H (H.MMfam t)).det)
    (u : ↥(MMsharp H t)) (i) : (sharpEquiv H t hG u i : E) = H.h u (H.MMfam t i) := rfl

def relSub {r : ℕ} (t : Term V M r) : Submodule M.L.O (Fin (r + 1) ⊕ Fin (r + 1) → M.L.O) where
  carrier := {y | ∃ c : Fin (r + 1) ⊕ Fin (r + 1) → M.L.O,
    ∀ j, (y j : E) = ∑ i, (c i : E) * H.h (H.MMfam t i) (H.MMfam t j)}
  add_mem' := by
    rintro a b ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨c + d, fun j => ?_⟩
    simp only [Pi.add_apply, Subring.coe_add, hc j, hd j, add_mul, Finset.sum_add_distrib]
  zero_mem' := ⟨0, fun j => by simp⟩
  smul_mem' := by
    rintro a y ⟨c, hc⟩
    refine ⟨a • c, fun j => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, Subring.coe_mul, hc j, Finset.mul_sum, mul_assoc]

theorem map_sharp_MMo {r : ℕ} (t : Term V M r) (hG : IsUnit (gramH H (H.MMfam t)).det) :
    ((MMo H t).comap (MMsharp H t).subtype).map (sharpEquiv H t hG : _ →ₗ[M.L.O] _) =
      relSub H t := by
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨c, hc⟩ := (mem_MMo_iff H t u).1 hu
    refine ⟨c, fun j => ?_⟩
    rw [LinearEquiv.coe_coe, sharpEquiv_apply, ← hc, h_sum_left]
  · rintro ⟨c, hc⟩
    have hs : (∑ i, (c i : E) • H.MMfam t i) ∈ MMsharp H t := by
      rw [mem_MMsharp_iff]
      refine ⟨Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
        (Submodule.subset_span ⟨i, rfl⟩), fun j => ?_⟩
      rw [h_sum_left, ← hc j]; exact (y j).2
    refine ⟨⟨_, hs⟩, (mem_MMo_iff H t _).2 ⟨c, rfl⟩, ?_⟩
    funext j; apply Subtype.ext
    rw [LinearEquiv.coe_coe, sharpEquiv_apply, h_sum_left, ← hc j]

def ddEquiv {r : ℕ} (t : Term V M r) (hG : IsUnit (gramH H (H.MMfam t)).det) :
    DDt H t ≃ₗ[M.L.O] (Fin (r + 1) ⊕ Fin (r + 1) → M.L.O) ⧸ relSub H t :=
  Submodule.Quotient.equiv _ _ (sharpEquiv H t hG) (map_sharp_MMo H t hG)

theorem ddEquiv_mk {r : ℕ} (t : Term V M r) (hG : IsUnit (gramH H (H.MMfam t)).det)
    (u : ↥(MMsharp H t)) :
    ddEquiv H t hG (ddMk H t u) = Submodule.Quotient.mk (sharpEquiv H t hG u) := rfl

end Sharp

end Formalism.L2.SG.LocalCountModules.LocCntCommon
