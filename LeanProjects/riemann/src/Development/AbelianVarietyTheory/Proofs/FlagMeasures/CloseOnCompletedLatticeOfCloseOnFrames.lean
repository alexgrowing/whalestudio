import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToLePerp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalExtend
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIntegralOfQuad
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.LatClose

section
variable {K R : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [CommRing R] [Algebra K R] [TopologicalSpace R]
  (L : LocE K R) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) R)

theorem hf_add_right (x a b : Fin n → R) : hf L Hm x (a + b) = hf L Hm x a + hf L Hm x b := by
  simp [hf, mul_add, Finset.sum_add_distrib]

theorem hf_smul_right (x : Fin n → R) (c : R) (a : Fin n → R) : hf L Hm x (c • a) = L.cj c * hf L Hm x a := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hf_zero_right (x : Fin n → R) : hf L Hm x 0 = 0 := by simp [hf]
end

theorem form_sub_sum {E : Type} [Field E] {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) {ι : Type} [Fintype ι] (x : Fin n → E) (a : ι → E)
    (v : ι → Fin n → E) (s : Fin n → E) :
    ∑ i, ∑ j, (x - ∑ k, a k • v k) i * Hm i j * s j =
      (∑ i, ∑ j, x i * Hm i j * s j) - ∑ k, a k * ∑ i, ∑ j, v k i * Hm i j * s j := by
  simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib,
    Finset.sum_mul, Finset.mul_sum]
  congr 1
  calc _ = ∑ i, ∑ k, ∑ j, a k * v k i * Hm i j * s j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) {n : ℕ}

theorem bc_add (x y : Fin n → E) : A.bc p (x + y) = A.bc p x + A.bc p y := by
  funext i; simp [Places.bc]
theorem bc_smul (c : E) (x : Fin n → E) : A.bc p (c • x) = (A.loc p).ιE c • A.bc p x := by
  funext i; simp [Places.bc]
theorem bc_sum {ι : Type} (s : Finset ι) (x : ι → Fin n → E) :
    A.bc p (∑ i ∈ s, x i) = ∑ i ∈ s, A.bc p (x i) := by
  funext j; simp [Places.bc, Finset.sum_apply]
theorem bc_mem_lat (Λ : Submodule (𝓞 E) (Fin n → E)) {x : Fin n → E} (hx : x ∈ Λ) :
    A.bc p x ∈ A.lat p Λ :=
  Submodule.subset_span ⟨x, hx, rfl⟩

end

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}

theorem step (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) {n m : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (D : ℤ) (h : (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep))
    (g : Fin m → Fin n → E) (Mx : Matrix (Fin m) (Fin m) (A.loc p).Ep) (t : (A.loc p).Fp)
    (hg : ∀ j, h (A.bc p (g j)) = ∑ i, Mx i j • A.bc p (g i))
    (hMx : ∀ i j, ∃ o ∈ (A.L p).O, (Mx - 1) i j =
      algebraMap (A.loc p).Fp (A.loc p).Ep (t * (D : (A.loc p).Fp) ^ 3) * o)
    (hgΛ : ∀ i, (D : 𝓞 E) • g i ∈ Λ) (a : E) (ha : ∃ o : 𝓞 E, (D : E) ^ 2 * a = o) (j : Fin m) :
    ∃ z ∈ A.lat p Λ, (A.loc p).ιE a • (h (A.bc p (g j)) - A.bc p (g j)) =
      algebraMap (A.loc p).Fp (A.loc p).Ep t • z := by
  obtain ⟨oa, hoa⟩ := ha
  choose o ho hoeq using hMx
  have hdiff : h (A.bc p (g j)) - A.bc p (g j) = ∑ i, (Mx - 1) i j • A.bc p (g i) := by
    rw [hg]
    simp [Matrix.sub_apply, Matrix.one_apply, sub_smul, Finset.sum_sub_distrib]
  refine ⟨∑ i, (⟨o i j, ho i j⟩ : (A.L p).O) • A.bc p (oa • ((D : 𝓞 E) • g i)),
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (bc_mem_lat A p Λ (Λ.smul_mem _ (hgΛ i))), ?_⟩
  rw [hdiff, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e1 : (oa • ((D : 𝓞 E) • g i) : Fin n → E) = ((D : E) ^ 3 * a) • g i := by
    change (oa : E) • (((D : 𝓞 E) : E) • g i) = _
    have hD : ((D : 𝓞 E) : E) = (D : E) := by simp
    rw [smul_smul, ← hoa, hD]
    congr 1
    ring
  rw [Subring.smul_def, e1, bc_smul, hoeq, smul_smul, smul_smul, smul_smul]
  congr 1
  simp only [map_mul, map_pow, map_intCast]
  ring
end

theorem close_on_lattice : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k) (Λ : G.Lt) (D : ℤ) (p : HeightOneSpectrum (𝓞 F)) (h : (G.S p).GLV) (M M' : Matrix (Fin (r + 1)) (Fin (r + 1)) (A.loc p).Ep) (t : (A.loc p).Fp), (Matrix.of fun k l : Fin (r + 1) ⊕ Fin (r + 1) => ∑ i, ∑ j, Sum.elim G.f G.f' k i * G.Hm i j * sig (Sum.elim G.f G.f' l j))⁻¹ * (Matrix.of fun k l : Fin (r + 1) ⊕ Fin (r + 1) => ∑ i, ∑ j, Sum.elim G.f G.f' k i * G.Hm i j * sig (Sum.elim G.f G.f' l j)) = 1 → (∀ k l, ∃ o : 𝓞 E, (D : E) * (Matrix.of fun k l : Fin (r + 1) ⊕ Fin (r + 1) => ∑ i, ∑ j, Sum.elim G.f G.f' k i * G.Hm i j * sig (Sum.elim G.f G.f' l j))⁻¹ k l = o) → (∀ x ∈ Λ, ∀ l, ∃ o : 𝓞 E, (D : E) * ∑ a, ∑ b, x a * G.Hm a b * sig (Sum.elim G.f G.f' l b) = o) → (∀ l, (D : 𝓞 E) • Sum.elim G.f G.f' l ∈ Λ) → h ∈ (G.S p).St → (∀ j, h (A.bc p (G.f j)) = ∑ i, M i j • A.bc p (G.f i)) → (∀ j, h (A.bc p (G.f' j)) = ∑ i, M' i j • A.bc p (G.f' i)) → (∀ i j, ∃ o ∈ (A.L p).O, (M - 1) i j = algebraMap (A.loc p).Fp (A.loc p).Ep (t * (D : (A.loc p).Fp) ^ 3) * o) → (∀ i j, ∃ o ∈ (A.L p).O, (M' - 1) i j = algebraMap (A.loc p).Fp (A.loc p).Ep (t * (D : (A.loc p).Fp) ^ 3) * o) → ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, h x - x = algebraMap (A.loc p).Fp (A.loc p).Ep t • y := by
  intro F E _ _ _ _ _ sig A r k G Λ D p h M M' t hΓ hΓD hb hDu hh hM hM' hM1 hM1'
  haveI := (A.loc p).lf
  haveI := (A.loc p).char0
  have key : ∀ l ∈ Λ, ∃ y ∈ A.lat p Λ,
      h (A.bc p l) - A.bc p l = algebraMap (A.loc p).Fp (A.loc p).Ep t • y := by
    intro l hl
    set Γ : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E :=
      Matrix.of fun k l => ∑ i, ∑ j, Sum.elim G.f G.f' k i * G.Hm i j * sig (Sum.elim G.f G.f' l j)
      with hΓdef
    have hbl : ∀ m, ∃ o : 𝓞 E, (D : E) * ∑ i, ∑ j, l i * G.Hm i j * sig (Sum.elim G.f G.f' m j) = o :=
      hb l hl
    choose ob hob using hbl
    choose og hog using hΓD
    let b : Fin (r + 1) ⊕ Fin (r + 1) → E := fun m => ∑ i, ∑ j, l i * G.Hm i j * sig (Sum.elim G.f G.f' m j)
    let α := Matrix.vecMul b Γ⁻¹
    let w := l - ∑ q, α q • Sum.elim G.f G.f' q
    have hw0 : ∀ m, ∑ i, ∑ j, w i * G.Hm i j * sig (Sum.elim G.f G.f' m j) = 0 := by
      intro m
      rw [form_sub_sum]
      have e : ∑ q, α q * ∑ i, ∑ j, Sum.elim G.f G.f' q i * G.Hm i j * sig (Sum.elim G.f G.f' m j) =
          Matrix.vecMul α Γ m := rfl
      rw [e, Matrix.vecMul_vecMul, hΓ, Matrix.vecMul_one, sub_self]
    have hwloc : ∀ m, hf (A.L p) (G.S p).Hm (A.bc p w) (A.bc p (Sum.elim G.f G.f' m)) = 0 := by
      intro m
      rw [G.Hm_eq p, (RatExt.rational_extend A (k + 2 * r + 1) p).2.2.2.2.1, hw0, map_zero]
    have hwW : A.bc p w ∈ (G.S p).W0 := by
      have hME : (G.S p).ME = Submodule.span _ (Set.range (Sum.elim (G.S p).f (G.S p).f')) := by
        rw [Frames.ME, FrameStab.spanTo_top, FrameStab.spanTo_top, Set.Sum.elim_range, Submodule.span_union]
      change ∀ y ∈ (G.S p).ME, hf (A.L p) (G.S p).Hm (A.bc p w) y = 0
      intro y hy
      rw [hME] at hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨q, rfl⟩ := hy
        rcases q with a | a
        · have e := G.f_eq p a
          have h0 := hwloc (Sum.inl a)
          simp only [Sum.elim_inl] at h0 ⊢
          rw [← e, hf_smul_right, AlgEquiv.commutes] at h0
          exact ((((G.c p).isUnit.pow _).map (algebraMap _ _)).mul_right_eq_zero).1 h0
        · have e := G.f'_eq p a
          have h0 := hwloc (Sum.inr a)
          simp only [Sum.elim_inr] at h0 ⊢
          rw [← e, hf_smul_right, AlgEquiv.commutes] at h0
          exact ((((G.c p).isUnit.pow _).map (algebraMap _ _)).mul_right_eq_zero).1 h0
      | zero => exact hf_zero_right _ _ _
      | add x y _ _ hx hy => rw [hf_add_right, hx, hy, add_zero]
      | smul c x _ hx => rw [hf_smul_right, hx, mul_zero]
    have hhw : h (A.bc p w) = A.bc p w := (FrameStab.stab_eq (A.L p) r k (G.S p)).1 h hh _ hwW
    have hl' : l = w + ∑ q, α q • Sum.elim G.f G.f' q := by simp only [w, sub_add_cancel]
    have hsplit : h (A.bc p l) - A.bc p l = ∑ q, (A.loc p).ιE (α q) •
        (h (A.bc p (Sum.elim G.f G.f' q)) - A.bc p (Sum.elim G.f G.f' q)) := by
      rw [hl', bc_add, bc_sum, map_add, map_sum, hhw]
      simp only [bc_smul, map_smul, smul_sub, Finset.sum_sub_distrib]
      abel
    have hα : ∀ q, ∃ o : 𝓞 E, (D : E) ^ 2 * α q = o := by
      intro q
      refine ⟨∑ m, ob m * og m q, ?_⟩
      have e : ((∑ m, ob m * og m q : 𝓞 E) : E) = ∑ m, ((ob m : 𝓞 E) : E) * ((og m q : 𝓞 E) : E) := by
        simp
      rw [e]
      simp only [α, Matrix.vecMul, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      linear_combination ((D : E) * Γ⁻¹ m q) * hob m + ((ob m : 𝓞 E) : E) * hog m q
    have hper : ∀ q, ∃ z ∈ A.lat p Λ, (A.loc p).ιE (α q) •
        (h (A.bc p (Sum.elim G.f G.f' q)) - A.bc p (Sum.elim G.f G.f' q)) =
          algebraMap (A.loc p).Fp (A.loc p).Ep t • z := by
      rintro (j | j)
      · exact step A p Λ D h G.f M t hM hM1 (fun i => hDu (Sum.inl i)) (α (Sum.inl j)) (hα _) j
      · exact step A p Λ D h G.f' M' t hM' hM1' (fun i => hDu (Sum.inr i)) (α (Sum.inr j)) (hα _) j
    choose z hz hze using hper
    exact ⟨∑ q, z q, Submodule.sum_mem _ fun q _ => hz q, by
      rw [hsplit, Finset.smul_sum]; exact Finset.sum_congr rfl fun q _ => hze q⟩
  intro x hx
  change x ∈ Submodule.span _ _ at hx
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨l, hl, rfl⟩ := hx; exact key l hl
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add a b _ _ ha hb' =>
    obtain ⟨y1, hy1, e1⟩ := ha
    obtain ⟨y2, hy2, e2⟩ := hb'
    exact ⟨y1 + y2, add_mem hy1 hy2, by rw [map_add, smul_add, ← e1, ← e2]; abel⟩
  | smul c a _ ha =>
    obtain ⟨y, hy, e⟩ := ha
    refine ⟨c • y, Submodule.smul_mem _ c hy, ?_⟩
    rw [Subring.smul_def, Subring.smul_def, map_smul, ← smul_sub, e, smul_comm]

end GlobalTheory.HL.LatClose
