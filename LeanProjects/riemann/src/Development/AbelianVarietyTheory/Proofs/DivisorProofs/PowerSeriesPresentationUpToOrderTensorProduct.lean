import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesEvalAtNilpotentXEqCoordinateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesAlgHomExtOfIsNilpotentXStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilpotentEvalCommutesSubstAndAlgebraMapStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.TensPres

variable {k : Type} [CommRing k]

def ordIdeal (ρ : Type) (N : ℕ) : Ideal (MvPowerSeries ρ k) where
  carrier := {f | (N : ℕ∞) ≤ f.order}
  add_mem' {f g} hf hg := MvPowerSeries.le_order fun d hd => by
    rw [map_add, MvPowerSeries.coeff_of_lt_order (hd.trans_le hf),
      MvPowerSeries.coeff_of_lt_order (hd.trans_le hg), add_zero]
  zero_mem' := by simp
  smul_mem' c f hf := by
    change (N : ℕ∞) ≤ (c * f).order
    exact hf.trans (le_add_self.trans (MvPowerSeries.le_order_mul (f := c) (g := f)))

theorem mem_ordIdeal_order {ρ : Type} {N : ℕ} {f : MvPowerSeries ρ k} :
    f ∈ ordIdeal (k := k) ρ N ↔ (N : ℕ∞) ≤ f.order := Iff.rfl

theorem mem_ordIdeal {ρ : Type} {N : ℕ} {f : MvPowerSeries ρ k} :
    f ∈ ordIdeal (k := k) ρ N ↔ ∀ α : ρ →₀ ℕ, α.degree < N → coeff α f = 0 := by
  constructor
  · intro h α hα
    exact MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le (Nat.cast_lt.2 hα) ((mem_ordIdeal_order).1 h))
  · intro h
    exact (mem_ordIdeal_order).2 (MvPowerSeries.nat_le_order h)

theorem one_le_order_X {ρ : Type} (t : ρ) : (1 : ℕ∞) ≤ (X t : MvPowerSeries ρ k).order := by
  have := MvPowerSeries.nat_le_order (f := (X t : MvPowerSeries ρ k)) (n := 1) fun d hd => by
    have : d = 0 := by
      rw [← Finsupp.degree_eq_zero_iff]; omega
    subst this; simp
  exact_mod_cast this

theorem subst_mem_ordIdeal {ρ ρ' : Type} [Finite ρ] (e : ρ → ρ') {N : ℕ}
    {f : MvPowerSeries ρ k} (hf : f ∈ ordIdeal (k := k) ρ N) :
    subst (fun i => (X (e i) : MvPowerSeries ρ' k)) f ∈ ordIdeal (k := k) ρ' N := by
  have ha : HasSubst (fun i => (X (e i) : MvPowerSeries ρ' k)) :=
    hasSubst_of_constantCoeff_zero fun i => constantCoeff_X _
  have h1 : (1 : ℕ∞) ≤ ⨅ i, ((fun i => (X (e i) : MvPowerSeries ρ' k)) i).order :=
    le_iInf fun i => one_le_order_X (e i)
  have h2 := MvPowerSeries.le_order_subst ha f
  refine (mem_ordIdeal_order).2 ?_
  calc (N : ℕ∞) ≤ f.order := (mem_ordIdeal_order).1 hf
    _ = 1 * f.order := (one_mul _).symm
    _ ≤ _ := by gcongr
    _ ≤ _ := h2

end GlobalTheory.TensPres

open GlobalTheory.TensPres in

theorem GlobalTheory.evA_tensor_presents : ∀ (k : Type) [CommRing k] (σ τ : Type) [Finite σ] [Finite τ] (A B : Type) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] (x : σ → A) (hx : ∀ i, IsNilpotent (x i)) (y : τ → B) (hy : ∀ i, IsNilpotent (y i)) (hz : ∀ i, IsNilpotent (Sum.elim (fun i => x i ⊗ₜ[k] (1 : B)) (fun j => (1 : A) ⊗ₜ[k] y j) i)), Function.Surjective (evA k x hx) → Function.Surjective (evA k y hy) → Function.Surjective (evA k _ hz) ∧ ∀ N : ℕ, (∀ f, evA k x hx f = 0 → ∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) → (∀ f, evA k y hy f = 0 → ∀ α : τ →₀ ℕ, α.degree < N → coeff α f = 0) → ∀ f, evA k _ hz f = 0 → ∀ α : (σ ⊕ τ) →₀ ℕ, α.degree < N → coeff α f = 0 := by
  intro k _ σ τ _ _ A B _ _ _ _ x hx y hy hz hsx hsy
  have hX : ∀ t, evA k _ hz (X t) =
      Sum.elim (fun i => x i ⊗ₜ[k] (1 : B)) (fun j => (1 : A) ⊗ₜ[k] y j) t :=
    fun t => GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate k (σ ⊕ τ) (A ⊗[k] B) _ hz t
  have hzX : ∀ t, IsNilpotent (evA k _ hz (X t)) := fun t => by rw [hX]; exact hz t
  have hxl : ∀ i, IsNilpotent (x i ⊗ₜ[k] (1 : B)) := fun i => hz (Sum.inl i)
  have hyr : ∀ j, IsNilpotent ((1 : A) ⊗ₜ[k] y j) := fun j => hz (Sum.inr j)
  have hL : ∀ f : MvPowerSeries σ k,
      evA k _ hz (subst (fun i => (X (Sum.inl i) : MvPowerSeries (σ ⊕ τ) k)) f) =
        evA k x hx f ⊗ₜ[k] (1 : B) := by
    intro f
    rw [(GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k σ (A ⊗[k] B)).1 (σ ⊕ τ) (evA k _ hz) hzX _
      (fun i => constantCoeff_X _) _ hxl (fun i => by rw [hX]; rfl) f]
    exact ((GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k σ A).2 (A ⊗[k] B) (Algebra.TensorProduct.includeLeft (S := k))
      x hx _ hxl (fun i => rfl) f).symm
  have hR : ∀ g : MvPowerSeries τ k,
      evA k _ hz (subst (fun j => (X (Sum.inr j) : MvPowerSeries (σ ⊕ τ) k)) g) =
        (1 : A) ⊗ₜ[k] evA k y hy g := by
    intro g
    rw [(GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k τ (A ⊗[k] B)).1 (σ ⊕ τ) (evA k _ hz) hzX _
      (fun j => constantCoeff_X _) _ hyr (fun j => by rw [hX]; rfl) g]
    exact ((GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k τ B).2 (A ⊗[k] B) Algebra.TensorProduct.includeRight
      y hy _ hyr (fun j => rfl) g).symm
  refine ⟨?_, ?_⟩
  · intro w
    induction w using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul a b =>
      obtain ⟨f, rfl⟩ := hsx a
      obtain ⟨g, rfl⟩ := hsy b
      refine ⟨subst (fun i => (X (Sum.inl i) : MvPowerSeries (σ ⊕ τ) k)) f *
        subst (fun j => (X (Sum.inr j) : MvPowerSeries (σ ⊕ τ) k)) g, ?_⟩
      rw [map_mul, hL, hR, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add u v hu hv =>
      obtain ⟨f, rfl⟩ := hu
      obtain ⟨g, rfl⟩ := hv
      exact ⟨f + g, map_add _ _ _⟩
  · intro N hNx hNy f hf α hα
    let J := ordIdeal (k := k) (σ ⊕ τ) N
    let mk := Ideal.Quotient.mkₐ k J
    have haL : HasSubst (fun i => (X (Sum.inl i) : MvPowerSeries (σ ⊕ τ) k)) :=
      hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
    have haR : HasSubst (fun j => (X (Sum.inr j) : MvPowerSeries (σ ⊕ τ) k)) :=
      hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
    let φA : MvPowerSeries σ k →ₐ[k] _ := mk.comp (substAlgHom haL)
    let φB : MvPowerSeries τ k →ₐ[k] _ := mk.comp (substAlgHom haR)
    have hkA : ∀ g ∈ RingHom.ker (evA k x hx), φA g = 0 := by
      intro g hg
      rw [RingHom.mem_ker] at hg
      simp only [φA, mk, AlgHom.comp_apply, coe_substAlgHom, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem]
      exact subst_mem_ordIdeal Sum.inl (mem_ordIdeal.2 (hNx g hg))
    have hkB : ∀ g ∈ RingHom.ker (evA k y hy), φB g = 0 := by
      intro g hg
      rw [RingHom.mem_ker] at hg
      simp only [φB, mk, AlgHom.comp_apply, coe_substAlgHom, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem]
      exact subst_mem_ordIdeal Sum.inr (mem_ordIdeal.2 (hNy g hg))
    let ΨA : A →ₐ[k] _ := (Ideal.Quotient.liftₐ _ φA hkA).comp
      (Ideal.quotientKerAlgEquivOfSurjective hsx).symm.toAlgHom
    let ΨB : B →ₐ[k] _ := (Ideal.Quotient.liftₐ _ φB hkB).comp
      (Ideal.quotientKerAlgEquivOfSurjective hsy).symm.toAlgHom
    have hΨA : ∀ g, ΨA (evA k x hx g) = φA g := by
      intro g
      have : (Ideal.quotientKerAlgEquivOfSurjective hsx).symm (evA k x hx g) =
          Ideal.Quotient.mk _ g := by
        rw [AlgEquiv.symm_apply_eq]; rfl
      change Ideal.Quotient.liftₐ _ φA hkA ((Ideal.quotientKerAlgEquivOfSurjective hsx).symm (evA k x hx g)) = _
      rw [this]
      rfl
    have hΨB : ∀ g, ΨB (evA k y hy g) = φB g := by
      intro g
      have : (Ideal.quotientKerAlgEquivOfSurjective hsy).symm (evA k y hy g) =
          Ideal.Quotient.mk _ g := by
        rw [AlgEquiv.symm_apply_eq]; rfl
      change Ideal.Quotient.liftₐ _ φB hkB ((Ideal.quotientKerAlgEquivOfSurjective hsy).symm (evA k y hy g)) = _
      rw [this]
      rfl
    let Ψ := Algebra.TensorProduct.lift ΨA ΨB (fun _ _ => Commute.all _ _)
    have hnil : ∀ t, IsNilpotent (mk (X t)) := by
      intro t
      refine ⟨N, ?_⟩
      rw [← map_pow]
      simp only [mk, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      refine (mem_ordIdeal_order).2 ?_
      calc (N : ℕ∞) = N • (1 : ℕ∞) := by simp
        _ ≤ N • (X t : MvPowerSeries (σ ⊕ τ) k).order := by gcongr; exact one_le_order_X t
        _ ≤ _ := MvPowerSeries.le_order_pow _
    have huniq := GlobalTheory.T.mvPowerSeries_algHom_ext_of_isNilpotent_X k (σ ⊕ τ) _ mk (Ψ.comp (evA k _ hz)) hnil (by
      intro t
      rw [AlgHom.comp_apply, hX]
      cases t with
      | inl i =>
        simp only [Sum.elim_inl, Ψ, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
        rw [← GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate k σ A x hx i, hΨA]
        simp only [φA, AlgHom.comp_apply, coe_substAlgHom, subst_X haL]
      | inr j =>
        simp only [Sum.elim_inr, Ψ, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
        rw [← GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate k τ B y hy j, hΨB]
        simp only [φB, AlgHom.comp_apply, coe_substAlgHom, subst_X haR])
    have hmk : mk f = 0 := by
      rw [huniq, AlgHom.comp_apply, hf, map_zero]
    simp only [mk, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at hmk
    exact mem_ordIdeal.1 hmk α hα
