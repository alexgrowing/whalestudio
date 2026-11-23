import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
open NumberField Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

theorem suLie_finrank_ge : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (G : Matrix (Fin r) (Fin r) E), (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 →
    ∃ e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E,
      (∀ i, (e i).trace = 0 ∧ ∀ x y, herm G (e i *ᵥ x) y + herm G x (e i *ᵥ y) = 0) ∧
      LinearIndependent (maximalRealSubfield E) e := by
  intro E _ _ _ r G hG hdet
  let F := maximalRealSubfield E
  have cc_mul : ∀ x y : E, cc (x * y) = cc x * cc y := fun x y => map_mul (IsCMField.complexConj E) x y
  have cc_add : ∀ x y : E, cc (x + y) = cc x + cc y := fun x y => map_add (IsCMField.complexConj E) x y
  have cc_cc : ∀ x : E, cc (cc x) = x := fun x => IsCMField.complexConj_apply_apply E x
  have cc_F : ∀ (c : F) (x : E), cc (c • x) = c • cc x := by
    intro c x
    have hc : cc (c : E) = c := (IsCMField.complexConj_eq_self_iff E _).mpr c.2
    show cc ((c : E) * x) = (c : E) * cc x
    rw [cc_mul, hc]
  have hs : ∀ (f : Fin r → E), cc (∑ i, f i) = ∑ i, cc (f i) := fun f => map_sum (IsCMField.complexConj E) f _
  haveI : FiniteDimensional F E :=
    Module.finite_of_finrank_eq_succ (Algebra.IsQuadraticExtension.finrank_eq_two F E)
  have hV : Module.finrank F (Matrix (Fin r) (Fin r) E) = r * r * 2 := by
    rw [Module.finrank_matrix, Algebra.IsQuadraticExtension.finrank_eq_two F E]; simp

  let conjL : Matrix (Fin r) (Fin r) E →ₗ[F] Matrix (Fin r) (Fin r) E :=
    { toFun := fun X => X.map cc
      map_add' := fun X Y => by ext a b; simp [cc_add]
      map_smul' := fun c X => by ext a b; simp [cc_F] }
  let φ : Matrix (Fin r) (Fin r) E →ₗ[F] Matrix (Fin r) (Fin r) E :=
    { toFun := fun X => Xᵀ * G + G * conjL X
      map_add' := fun X Y => by simp only [map_add, transpose_add, Matrix.add_mul, Matrix.mul_add]; abel
      map_smul' := fun c X => by
        simp only [map_smul, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, RingHom.id_apply, smul_add] }

  let H : Submodule F (Matrix (Fin r) (Fin r) E) :=
    { carrier := {M | ∀ a b, cc (M a b) = M b a}
      add_mem' := fun {M N} hM hN a b => by simp [cc_add, hM a b, hN a b]
      zero_mem' := fun a b => by simp [cc]
      smul_mem' := fun c M hM a b => by simp [cc_F, hM a b] }
  have hφH : LinearMap.range φ ≤ H := by
    rintro _ ⟨X, rfl⟩ a b
    have hφX : φ X = Xᵀ * G + G * X.map cc := rfl
    show cc ((φ X) a b) = (φ X) b a
    rw [hφX]
    simp only [Matrix.add_apply, Matrix.mul_apply, transpose_apply, map_apply, cc_add]
    rw [hs, hs, add_comm]
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;> simp only [cc_mul, cc_cc, hG] <;> ring

  obtain ⟨y, hy⟩ := DFunLike.ne_iff.mp (IsCMField.complexConj_ne_one E)
  have hy' : cc y ≠ y := hy
  set δ : E := y - cc y with hδdef
  have hδ : cc δ = -δ := by rw [hδdef, show cc (y - cc y) = cc y - cc (cc y) from map_sub _ _ _, cc_cc]; ring
  have hδ0 : δ ≠ 0 := fun h => hy' (sub_eq_zero.mp h).symm
  let Dm : Matrix (Fin r) (Fin r) E →ₗ[F] Matrix (Fin r) (Fin r) E :=
    { toFun := fun M => δ • M
      map_add' := fun M N => smul_add δ M N
      map_smul' := fun c M => smul_comm δ c M }
  have hDm : Function.Injective Dm := fun M N h => smul_right_injective _ hδ0 h
  have hinf : H ⊓ H.map Dm = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro M ⟨hM, N, hN, rfl⟩
    have hN0 : ∀ a b, N a b = 0 := by
      intro a b
      have h := hM b a
      change cc (δ * N b a) = δ * N a b at h
      rw [cc_mul, hδ, hN b a] at h
      have : δ * N a b = 0 := by linear_combination (-1/2 : E) * h
      exact (mul_eq_zero.mp this).resolve_left hδ0
    ext a b
    show δ * N a b = 0
    rw [hN0, mul_zero]
  have hHmap : Module.finrank F (H.map Dm) = Module.finrank F H :=
    (Submodule.equivMapOfInjective Dm hDm H).finrank_eq.symm
  have h1 := LinearMap.finrank_range_add_finrank_ker φ
  have h2 := Submodule.finrank_mono hφH
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq H (H.map Dm)
  have h4 := Submodule.finrank_le (H ⊔ H.map Dm)
  rw [hinf, finrank_bot] at h3
  have hK : r * r ≤ Module.finrank F (LinearMap.ker φ) := by omega

  let t : Matrix (Fin r) (Fin r) E →ₗ[F] E := Matrix.traceLinearMap (Fin r) F E
  let f := t.domRestrict (LinearMap.ker φ)
  have hu : IsUnit G.det := isUnit_iff_ne_zero.mpr hdet
  have hf : LinearMap.range f ≤ Submodule.span F {δ} := by
    rintro _ ⟨⟨X, hX⟩, rfl⟩
    have hX' : Xᵀ * G + G * X.map cc = 0 := hX
    have hbar : X.map cc = -(G⁻¹ * (Xᵀ * G)) := by
      have : G * X.map cc = -(Xᵀ * G) := eq_neg_of_add_eq_zero_right hX'
      calc X.map cc = G⁻¹ * (G * X.map cc) := by
            rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul G hu, Matrix.one_mul]
        _ = -(G⁻¹ * (Xᵀ * G)) := by rw [this, Matrix.mul_neg]
    have htr : cc X.trace = -X.trace := by
      have e1 : (X.map cc).trace = cc X.trace := by
        simp only [Matrix.trace, Matrix.diag, map_apply]; exact (hs _).symm
      rw [← e1, hbar, Matrix.trace_neg, Matrix.trace_mul_comm, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv G hu, Matrix.mul_one, Matrix.trace_transpose]
    have hz : cc (X.trace / δ) = X.trace / δ := by
      rw [show cc (X.trace / δ) = cc X.trace / cc δ from map_div₀ (IsCMField.complexConj E) _ _, htr, hδ,
        neg_div_neg_eq]
    rw [Submodule.mem_span_singleton]
    refine ⟨⟨X.trace / δ, (IsCMField.complexConj_eq_self_iff E _).mp hz⟩, ?_⟩
    show X.trace / δ * δ = X.trace
    exact div_mul_cancel₀ _ hδ0

  have hv : ∀ u v : Fin r → E, herm G u v = u ⬝ᵥ (G *ᵥ fun b => cc (v b)) := by
    intro u v
    simp only [herm, dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hcv : ∀ (X : Matrix (Fin r) (Fin r) E) (y : Fin r → E),
      (fun b => cc ((X *ᵥ y) b)) = X.map cc *ᵥ fun b => cc (y b) := by
    intro X y; ext b
    simp only [mulVec, dotProduct, map_apply]
    exact (hs _).trans (Finset.sum_congr rfl fun c _ => cc_mul _ _)
  have skew : ∀ X : Matrix (Fin r) (Fin r) E, Xᵀ * G + G * X.map cc = 0 →
      ∀ x y, herm G (X *ᵥ x) y + herm G x (X *ᵥ y) = 0 := by
    intro X hX x y
    rw [hv, hv, hcv, ← vecMul_transpose X x, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec,
      ← dotProduct_add, ← add_mulVec, hX, zero_mulVec, dotProduct_zero]

  have h5 := LinearMap.finrank_range_add_finrank_ker f
  have h6 := (Submodule.finrank_mono hf).trans (finrank_span_singleton hδ0).le
  have hle : r ^ 2 - 1 ≤ Module.finrank F (LinearMap.ker f) := by rw [sq]; omega
  let b := Module.finBasis F (LinearMap.ker f)
  let g : LinearMap.ker f →ₗ[F] Matrix (Fin r) (Fin r) E :=
    (LinearMap.ker φ).subtype ∘ₗ (LinearMap.ker f).subtype
  have hg : LinearMap.ker g = ⊥ :=
    LinearMap.ker_eq_bot.mpr (Subtype.val_injective.comp Subtype.val_injective)
  refine ⟨fun i => g (b (Fin.castLE hle i)), fun i => ?_,
    (b.linearIndependent.comp _ (Fin.castLE_injective hle)).map' g hg⟩
  have hx1 : f (b (Fin.castLE hle i)).1 = 0 := (b (Fin.castLE hle i)).2
  have hx2 : φ (b (Fin.castLE hle i)).1.1 = 0 := (b (Fin.castLE hle i)).1.2
  exact ⟨hx1, skew _ hx2⟩

end GlobalTheory
