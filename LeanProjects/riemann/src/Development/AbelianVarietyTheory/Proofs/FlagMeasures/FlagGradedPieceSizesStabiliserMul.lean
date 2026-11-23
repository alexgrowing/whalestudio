import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivariance
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsSatFlagOne

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.FlagSizeInv

open GlobalTheory.PointEquivariance

theorem mem_span_of_image {E : Type} [Field E] {n : ℕ} (φ : E →+* ℂ) (s : Set (Fin n → E)) (z : Fin n → E)
    (h : (fun l => φ (z l)) ∈ Submodule.span ℂ ((fun y : Fin n → E => fun l => φ (y l)) '' s)) :
    z ∈ Submodule.span E s := by
  by_contra hz
  obtain ⟨f, hfz, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hz inferInstance
  have hf0 : ∀ y ∈ s, f y = 0 := fun y hy => by
    have hm : f y ∈ (Submodule.span E s).map f := Submodule.mem_map_of_mem (Submodule.subset_span hy)
    rw [hf] at hm
    simpa using hm
  have hfx : ∀ y : Fin n → E, f y = ∑ l, y l * f (fun j => if l = j then 1 else 0) := fun y => by
    rw [LinearMap.pi_apply_eq_sum_univ f y]
    simp only [smul_eq_mul]
  let F : (Fin n → ℂ) →ₗ[ℂ] ℂ := ∑ l, φ (f (fun j => if l = j then 1 else 0)) • LinearMap.proj l
  have hF : ∀ y : Fin n → E, F (fun l => φ (y l)) = φ (f y) := fun y => by
    rw [hfx y, map_sum]
    simp only [F, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, LinearMap.coe_proj,
      Function.eval, smul_eq_mul, map_mul]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  have hle : Submodule.span ℂ ((fun y : Fin n → E => fun l => φ (y l)) '' s) ≤ LinearMap.ker F := by
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    show F _ = 0
    rw [hF, hf0 y hy, map_zero]
  have h0 : φ (f z) = 0 := by
    rw [← hF]
    exact LinearMap.mem_ker.1 (hle h)
  exact hfz ((map_eq_zero_iff φ φ.injective).1 h0)

theorem mulVec_mem_span (I : AutInst) {a : ℕ} (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E))
    (v : InfinitePlace I.F) (k : Fin (a + 1)) (γ : Matrix (Fin I.n) (Fin I.n) I.E)
    (h : ∀ y ∈ flagAt I S v k, ((I.P v)⁻¹ * γ.map (I.φ v) * I.P v) *ᵥ y ∈ flagAt I S v k)
    (y : Fin I.n → I.E) (hy : y ∈ S k) : γ *ᵥ y ∈ Submodule.span I.E (S k : Set (Fin I.n → I.E)) := by
  have hP : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have hmem : (I.P v)⁻¹ *ᵥ (fun l => I.φ v (y l)) ∈ flagAt I S v k := by
    unfold flagAt
    exact Submodule.subset_span ⟨y, hy, rfl⟩
  have h1 := h _ hmem
  have hcomp : ((I.P v)⁻¹ * γ.map (I.φ v) * I.P v) *ᵥ ((I.P v)⁻¹ *ᵥ (fun l => I.φ v (y l))) =
      (I.P v)⁻¹ *ᵥ (fun l => I.φ v ((γ *ᵥ y) l)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hP, Matrix.mul_one,
      ← Matrix.mulVec_mulVec]
    congr 1
    funext l
    exact (RingHom.map_mulVec (I.φ v) γ y l).symm
  rw [hcomp] at h1
  unfold flagAt at h1
  have h2 := Submodule.mem_map_of_mem (f := Matrix.toLin' (I.P v)) h1
  rw [Submodule.map_span, Set.image_image] at h2
  simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hP,
    Matrix.one_mulVec] at h2
  exact mem_span_of_image (I.φ v) _ _ h2

theorem ratIso_eq (I : AutInst) (γ : GL (Fin I.n) I.E) (Λ N : Submodule (𝓞 I.E) (Fin I.n → I.E))
    (hΛ : ratIso I γ Λ = Λ) (hN : ∀ y, y ∈ N ↔ y ∈ Λ ∧ y ∈ Submodule.span I.E (N : Set (Fin I.n → I.E)))
    (h : ∀ y ∈ N, (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y ∈ Submodule.span I.E (N : Set (Fin I.n → I.E))) :
    ratIso I γ N = N := by
  rw [ratIso_apply] at hΛ ⊢
  have hinj : Function.Injective (Matrix.toLin' (γ : Matrix (Fin I.n) (Fin I.n) I.E)) := by
    intro y y' hyy
    have hc := congrArg (Matrix.toLin' ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E)) hyy
    simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec] using hc
  have hWle : (Submodule.span I.E (N : Set (Fin I.n → I.E))).map
      (Matrix.toLin' (γ : Matrix (Fin I.n) (Fin I.n) I.E)) ≤ Submodule.span I.E (N : Set (Fin I.n → I.E)) := by
    rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
    intro y hy
    exact h y hy
  have hW : (Submodule.span I.E (N : Set (Fin I.n → I.E))).map
      (Matrix.toLin' (γ : Matrix (Fin I.n) (Fin I.n) I.E)) = Submodule.span I.E (N : Set (Fin I.n → I.E)) := by
    refine Submodule.eq_of_le_of_finrank_eq hWle ?_
    have e := LinearEquiv.finrank_map_eq (ratEquiv I γ) (Submodule.span I.E (N : Set (Fin I.n → I.E)))
    exact e
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    simp only [LinearMap.restrictScalars_apply, Matrix.toLin'_apply]
    have hy' := (hN y).1 hy
    refine (hN _).2 ⟨?_, h y hy⟩
    rw [← hΛ]
    exact ⟨y, hy'.1, by simp⟩
  · intro y hy
    obtain ⟨hyΛ, hyW⟩ := (hN y).1 hy
    rw [← hΛ] at hyΛ
    obtain ⟨y', hy'Λ, hy'⟩ := hyΛ
    rw [← hW] at hyW
    obtain ⟨y'', hy''W, hy''⟩ := hyW
    have hyy : y'' = y' := hinj (by rw [hy'', ← hy']; rfl)
    subst hyy
    exact ⟨y'', (hN y'').2 ⟨hy'Λ, hy''W⟩, hy'⟩

theorem sizesAt_mul : ∀ (I : AutInst) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ)
    (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I (1, xf)) j S →
    ∀ γ ∈ flagGroup I xf S, ∀ g : I.Ginf, sizesAt I xf S (γ * g) = sizesAt I xf S g := by
  intro I xf a j S hS γ hγ g
  obtain ⟨⟨δ, hδ, hδ1, hδK⟩, hkeep⟩ := hγ
  obtain ⟨c, -, hc1, hc2⟩ := hδ
  unfold IsSatFlag at hS
  obtain ⟨-, -, -, hsat, -⟩ := hS
  have hL : lamX I (δ * (1, xf)) = lamX I (1, xf) := by
    have hk := (lamX_mul_eq_iff I (1, xf) (1, xf⁻¹ * δ.2 * xf)).1 hδK
    have h2 : (δ * (1, xf)).2 = ((1, xf) * (1, xf⁻¹ * δ.2 * xf) : I.GA).2 := by
      simp [mul_assoc]
    rw [← hk, lamX_eq, lamX_eq, h2]
  have hlat : ratIso I c (lamX I (1, xf)) = lamX I (1, xf) := by
    rw [← lamX_rat I (1, xf) δ c hc2, hL]
  obtain ⟨v₀⟩ := (inferInstance : Nonempty (InfinitePlace I.F))
  have hfix : ∀ k, ratIso I c (S k) = S k := fun k =>
    ratIso_eq I c _ (S k) hlat (hsat k) fun y hy =>
      mulVec_mem_span I S v₀ k (c : Matrix (Fin I.n) (Fin I.n) I.E)
        (fun x hx => by rw [← hc1 v₀, hδ1]; exact hkeep v₀ k x hx) y hy
  have hcond : ∀ v, uMat (((γ, 1) : I.GA).1 v) =
      (I.P v)⁻¹ * (c : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v := fun v => by
    show uMat (γ v) = _
    rw [← hδ1]
    exact hc1 v
  have hax : ((γ, 1) : I.GA) * (g, xf) = (γ * g, xf) := by simp
  unfold sizesAt
  funext i
  have key := sizeQ_eq (bas I) (frm I (g, xf)) (frm I (γ * g, xf)) (ratIso I c)
    (fun N => by rw [← hax]; exact zl_ratIso I (g, xf) (γ, 1) c hcond N) (rkK_ratIso I c)
    (S i.succ) (S i.castSucc)
  rw [hfix, hfix] at key
  exact key

end GlobalTheory.FlagSizeInv
