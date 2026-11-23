import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActMatApply

set_option autoImplicit false

noncomputable section

open scoped Pointwise

namespace GlobalTheory.ChainPts.SysB

open GlobalTheory.RingChain GlobalTheory.PerfdLat

theorem exists_linear_extend_pi {A R : Type} [CommRing A] [CommRing R] (φ : A →+* R) {n r : ℕ}
    (g : (Fin n → A) →ₗ[A] (Fin r → A)) :
    ∃ G : (Fin n → R) →ₗ[R] (Fin r → R), ∀ v, G (fun i => φ (v i)) = fun l => φ (g v l) := by
  refine ⟨Matrix.toLin' ((LinearMap.toMatrix' g).map φ), fun v => funext fun l => ?_⟩
  conv_rhs => rw [← Matrix.toLin'_toMatrix' g]
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, RingHom.map_mulVec]
  rfl

theorem kerRSt : KerRSt := by
  intro p A _ n o π γ Lie Om _ _ _ _ C R _ _ φ hπ r f
  haveI := C.projective 0
  let q : C.L 0 →ₗ[A] Qt (C.L 0) (baseOf π n) ⧸ LinearMap.range C.j := Submodule.mkQ _ ∘ₗ Submodule.mkQ _
  have hq : ∀ x, q x = Submodule.Quotient.mk (Submodule.Quotient.mk x) := fun _ => rfl
  have hqs : Function.Surjective q := (Submodule.mkQ_surjective _).comp (Submodule.mkQ_surjective _)
  have hq0 : ∀ x, q x = 0 ↔ Submodule.Quotient.mk x ∈ LinearMap.range C.j := fun x => by
    rw [hq, Submodule.Quotient.mk_eq_zero]
  have hpi : ∀ v : Fin n → A, piMap φ (Fin n) v = fun i => φ (v i) := fun _ => rfl
  set K := Submodule.span R {v : Fin r → R | ∃ w, C.ρ w = 0 ∧ v = fun l => φ (f.repr w l)} with hK
  ext c
  constructor
  · rintro ⟨x, hx, hc⟩
    obtain ⟨σ, hσ⟩ := Module.projective_lifting_property C.ρ q C.ρ_surj
    have hσ' : ∀ x, C.ρ (σ x) = q x := fun x => LinearMap.congr_fun hσ x
    let μ : (Fin n → A) →ₗ[A] C.L 0 := LinearMap.codRestrict (C.L 0) (π • LinearMap.id) fun v =>
      C.base_le 0 (Submodule.smul_mem_pointwise_smul v π ⊤ trivial)
    have hμ : ∀ y : C.L 0, μ y.1 = π • y := fun y => rfl
    obtain ⟨G, hG⟩ := exists_linear_extend_pi φ (f.equivFun.toLinearMap ∘ₗ σ ∘ₗ μ)
    have hG' : ∀ y : C.L 0, G (piMap φ (Fin n) y.1) = φ π • fun l => φ (f.repr (σ y) l) := fun y => by
      rw [hpi, hG]
      funext l
      simp [hμ]
    have h1 : ∀ z ∈ Submodule.span R
        {z | ∃ x₀ : C.L 0, Submodule.Quotient.mk x₀ ∈ LinearMap.range C.j ∧ z = piMap φ _ x₀.1},
        ∃ k ∈ K, G z = φ π • k := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨y, hy, rfl⟩ := hz
        exact ⟨_, Submodule.subset_span ⟨σ y, by rw [hσ', (hq0 y).2 hy], rfl⟩, hG' y⟩
      | zero => exact ⟨0, K.zero_mem, by simp⟩
      | add a b _ _ ha hb =>
        obtain ⟨k, hk, e⟩ := ha
        obtain ⟨k', hk', e'⟩ := hb
        exact ⟨k + k', K.add_mem hk hk', by rw [map_add, e, e', smul_add]⟩
      | smul s a _ ha =>
        obtain ⟨k, hk, e⟩ := ha
        exact ⟨s • k, K.smul_mem s hk, by rw [map_smul, e, smul_comm]⟩
    obtain ⟨k, hk, e⟩ := h1 _ hc
    have e2 : (∑ l, c l • fun m => φ (f.repr (σ (x l)) m)) = k := by
      apply smul_right_injective (Fin r → R) hπ
      change φ π • _ = φ π • _
      rw [← e, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul, hG', smul_comm]
    have e3 : c = k + ∑ l, c l • fun m => φ (f.repr (f l - σ (x l)) m) := by
      rw [← e2, ← Finset.sum_add_distrib]
      funext m
      simp [Finset.sum_apply, mul_sub, Finsupp.single_apply, apply_ite φ]
    rw [e3]
    refine K.add_mem hk (K.sum_mem fun l _ => K.smul_mem _ (Submodule.subset_span ⟨_, ?_, rfl⟩))
    rw [map_sub, hσ', hx, hq, sub_self]
  · intro hc
    choose x hx using fun l => hqs (C.ρ (f l))
    refine ⟨x, fun l => (hx l).symm, ?_⟩
    replace hc : c ∈ K := hc
    induction hc using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨w, hw, rfl⟩ := hz
      refine Submodule.subset_span ⟨∑ l, f.repr w l • x l, (hq0 _).1 ?_, ?_⟩
      · rw [← hw]
        conv_rhs => rw [← f.sum_repr w]
        simp only [map_sum, map_smul, hx]
      · funext i
        simp [hpi, Finset.sum_apply]
    | zero => simp
    | add a b _ _ ha hb =>
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      exact Submodule.add_mem _ ha hb
    | smul s a _ ha =>
      simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum]
      exact Submodule.smul_mem _ _ ha

end GlobalTheory.ChainPts.SysB

end
