import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
open NumberField GlobalTheory.HTLat GlobalTheory.EigenSplit Classical
open scoped TensorProduct NNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EigGlue

section Alg

variable {O R ι : Type} [CommRing O] [Field R] [DecidableEq ι] {σ : ι → O →+* R}

theorem eq_smul_idem (h : IsSplitting σ) (i : ι) (z : R ⊗[ℤ] O)
    (hz : ∀ a, (1 ⊗ₜ a) * z = σ i a • z) : z = splitMap σ z i • idem h i := by
  apply h.1
  funext k
  rw [map_smul, splitMap_idem, Pi.smul_apply, smul_eq_mul]
  by_cases hk : k = i
  · subst hk; simp
  · rw [Pi.single_eq_of_ne hk, mul_zero]
    have hne : σ k ≠ σ i := fun e => hk (h.injective e)
    obtain ⟨a, ha⟩ : ∃ a, σ k a ≠ σ i a := by
      by_contra hc
      push Not at hc
      exact hne (RingHom.ext hc)
    have e := congrArg (fun t => splitMap σ t k) (hz a)
    simp only [map_mul, Pi.mul_apply, splitMap_tmul, one_mul, map_smul, Pi.smul_apply, smul_eq_mul] at e
    have : (σ k a - σ i a) * splitMap σ z k = 0 := by rw [sub_mul, e, sub_self]
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 ha)

end Alg

section Act

variable {p : ℕ} [Fact p.Prime] (C : Type) [Field C] [Algebra ℤ_[p] C] {E : Type} [Field E]
  {T : Type} [AddCommGroup T] [Module ℤ_[p] T] (ρ : 𝓞 E →+* Module.End ℤ_[p] T)

def inclC : ℤ_[p] ⊗[ℤ] 𝓞 E →ₐ[ℤ_[p]] C ⊗[ℤ] 𝓞 E :=
  Algebra.TensorProduct.map (Algebra.ofId ℤ_[p] C) (AlgHom.id ℤ (𝓞 E))

theorem inclC_tmul (r : ℤ_[p]) (a : 𝓞 E) : inclC C (r ⊗ₜ a) = algebraMap ℤ_[p] C r ⊗ₜ a := by
  simp [inclC, Algebra.ofId_apply]

theorem tensorAction_inclC (z : ℤ_[p] ⊗[ℤ] 𝓞 E) (x : C ⊗[ℤ_[p]] T) :
    tensorAction (baseChangeAction C ρ) (inclC C z) x = (tensorAction ρ z).baseChange C x := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add y z hy hz => simp only [map_add, LinearMap.add_apply, hy, hz, LinearMap.baseChange_add]
  | tmul r a =>
    have e : tensorAction ρ (r ⊗ₜ a) = r • ρ a := LinearMap.ext fun y => by
      rw [tensorAction_tmul, LinearMap.smul_apply]
    rw [inclC_tmul, tensorAction_tmul, e, LinearMap.baseChange_smul,
      LinearMap.smul_apply, algebraMap_smul, baseChangeAction_apply]

variable {m : ℕ} (ℓ : Fin m → (T →ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] 𝓞 E))

def coordC (j : Fin m) : C ⊗[ℤ_[p]] T →ₗ[C] C ⊗[ℤ] 𝓞 E :=
  ((inclC C).toLinearMap ∘ₗ ℓ j).liftBaseChange C

theorem coordC_tmul (j : Fin m) (c : C) (t : T) : coordC C ℓ j (c ⊗ₜ t) = c • inclC C (ℓ j t) := by
  rw [coordC, LinearMap.liftBaseChange_tmul]
  rfl

variable {ρ ℓ}

theorem coordC_act (hℓ : ∀ j a t, ℓ j (ρ a t) = (1 ⊗ₜ a) * ℓ j t) (j : Fin m) (a : 𝓞 E)
    (x : C ⊗[ℤ_[p]] T) : coordC C ℓ j (baseChangeAction C ρ a x) = (1 ⊗ₜ a) * coordC C ℓ j x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, mul_add]
  | tmul c t =>
    rw [baseChangeAction_apply, LinearMap.baseChange_tmul, coordC_tmul, coordC_tmul, hℓ, map_mul,
      mul_smul_comm]
    congr 2
    simp [inclC]

theorem baseChange_eq_sum {u : Fin m → T} {e : ℤ_[p] ⊗[ℤ] 𝓞 E}
    (hE : ∀ t, tensorAction ρ e t = ∑ j, tensorAction ρ (ℓ j t) (u j)) (x : C ⊗[ℤ_[p]] T) :
    (tensorAction ρ e).baseChange C x =
      ∑ j, tensorAction (baseChangeAction C ρ) (coordC C ℓ j x) (1 ⊗ₜ u j) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, LinearMap.add_apply, Finset.sum_add_distrib]
  | tmul c t =>
    rw [LinearMap.baseChange_tmul, hE, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [coordC_tmul, map_smul, LinearMap.smul_apply, tensorAction_inclC, LinearMap.baseChange_tmul,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end Act

section Point

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
  {E : Type} [Field E]

theorem splitMap_inclC (hv : v.Integers O) (φ : E →+* C) (e : ℤ_[p] ⊗[ℤ] 𝓞 E) :
    splitMap (fun ψ : E →+* C => (algebraMap O C).comp (embO hv ψ)) (inclC C e) φ =
      algebraMap O C (ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.tauExt (embO hv φ) e) := by
  induction e using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  | tmul r a =>
    rw [inclC_tmul, splitMap_tmul]
    simp [ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.tauExt, Algebra.ofId_apply, IsScalarTower.algebraMap_apply ℤ_[p] O C]

def intPart (O C E : Type) [CommRing O] [Field C] [Algebra O C] [Field E] :
    Submodule O (C ⊗[ℤ] 𝓞 E) :=
  Submodule.span O (Set.range fun a : 𝓞 E => (1 : C) ⊗ₜ[ℤ] a)

theorem inclC_mem_intPart (z : ℤ_[p] ⊗[ℤ] 𝓞 E) : inclC C z ∈ intPart O C E := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | tmul r a =>
    rw [inclC_tmul, IsScalarTower.algebraMap_apply ℤ_[p] O C, ← mul_one (algebraMap O C _),
      ← Algebra.smul_def, ← TensorProduct.smul_tmul']
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem exists_fin_of_mem_intPart {z : C ⊗[ℤ] 𝓞 E} (hz : z ∈ intPart O C E) :
    ∃ (n : ℕ) (r : Fin n → O) (a : Fin n → 𝓞 E), z = ∑ k, algebraMap O C (r k) ⊗ₜ[ℤ] a k := by
  obtain ⟨n, f, g, hfg⟩ := Submodule.mem_span_set'.1 hz
  refine ⟨n, f, fun k => (g k).2.choose, ?_⟩
  rw [← hfg]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← (g k).2.choose_spec, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]

end Point

theorem mem_latTQuot_of_smul_mem_latT : ∀ {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] (P : Point p v O (𝓞 E)) (φ : E →+* C) (d : C), d ≠ 0 → (∀ (n : ℕ) (r : Fin n → O) (a : Fin n → 𝓞 E) (s : C), (∀ σ : E →+* C, ∑ k, algebraMap O C (r k) * σ (a k) = if σ = φ then s else 0) → v s ≤ v d) → ∀ (m : ℕ) (u : Fin m → P.T) (ℓ : Fin m → (P.T →ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] 𝓞 E)) (e : ℤ_[p] ⊗[ℤ] 𝓞 E), (∀ j a t, ℓ j (P.actT a t) = (1 ⊗ₜ a) * ℓ j t) → ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.tauExt (embO P.integers φ) e = 1 → (∀ t, tensorAction P.actT e t = ∑ j, tensorAction P.actT (ℓ j t) (u j)) → ∀ w : P.V, w ∈ P.eigV (embO P.integers φ) → d • w ∈ P.latT → w ∈ P.latTQuot (σ := fun ψ : E →+* C => embO P.integers ψ) (isSplitting_embO P.integers) φ := by
  intro p _ C _ _ _ v O _ _ _ _ _ E _ _ _ P φ d hd hδ m u ℓ e hℓ he hE w hw hdw
  let σf : (E →+* C) → 𝓞 E →+* C := fun ψ => (algebraMap O C).comp (embO P.integers ψ)
  have h : IsSplitting σf := isSplitting_embO P.integers
  have hyV : d • w ∈ eigenSub P.actV (σf φ) := Submodule.smul_mem _ d hw
  have hact : P.actV = baseChangeAction C P.actT := rfl

  have h1 : (tensorAction P.actT e).baseChange C (d • w) = d • w := by
    rw [← tensorAction_inclC, ← hact, tensorAction_of_mem (σ := σf) (i := φ) hyV,
      splitMap_inclC P.integers φ e, he, map_one, one_smul]

  have h2 : ∀ j, ∃ o : O, coordC C ℓ j (d • w) = (d * algebraMap O C o) • idem h φ := by
    intro j
    have hz : ∀ a, (1 ⊗ₜ a) * coordC C ℓ j (d • w) = σf φ a • coordC C ℓ j (d • w) := by
      intro a
      rw [← coordC_act C hℓ, ← hact, mem_eigenSub.1 hyV a, map_smul]
    have heq := eq_smul_idem h φ _ hz
    set s := splitMap σf (coordC C ℓ j (d • w)) φ with hs
    have hmem : coordC C ℓ j (d • w) ∈ intPart O C E := by
      obtain ⟨x, hx⟩ := hdw
      rw [← hx]
      clear hx
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => rw [map_add, map_add]; exact Submodule.add_mem _ hx hy
      | tmul c t =>
        rw [Point.inclT_tmul, coordC_tmul, algebraMap_smul]
        exact Submodule.smul_mem _ _ (inclC_mem_intPart _)
    obtain ⟨n, r, a, hra⟩ := exists_fin_of_mem_intPart hmem
    have hvs : v s ≤ v d := by
      refine hδ n r a s fun ψ => ?_
      have e1 : splitMap σf (coordC C ℓ j (d • w)) ψ = s * (Pi.single φ 1 : (E →+* C) → C) ψ := by
        conv_lhs => rw [heq]
        rw [map_smul, splitMap_idem, Pi.smul_apply, smul_eq_mul]
      have e2 : splitMap σf (coordC C ℓ j (d • w)) ψ =
          ∑ k, algebraMap O C (r k) * ψ (a k) := by
        rw [hra, map_sum, Finset.sum_apply]
        simp only [splitMap_tmul, σf, RingHom.comp_apply, algebraMap_embO]
      rw [← e2, e1]
      by_cases hψ : ψ = φ
      · subst hψ; simp
      · simp [hψ]
    have hvd : v (s * d⁻¹) ≤ 1 := by
      rw [map_mul, map_inv₀]
      exact mul_inv_le_one_of_le₀ hvs zero_le
    obtain ⟨o, ho⟩ := P.integers.exists_of_le_one hvd
    refine ⟨o, ?_⟩
    rw [heq, ho, mul_comm s, ← mul_assoc, mul_inv_cancel₀ hd, one_mul]
  choose o ho using h2

  have h3 : d • w = d • proj h P.actV φ (∑ j, o j • ((1 : C) ⊗ₜ[ℤ_[p]] u j)) := by
    conv_lhs => rw [← h1, baseChange_eq_sum C hE]
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ho, ← hact, map_smul, LinearMap.smul_apply, ← proj, ← algebraMap_smul C (o j), map_smul,
      smul_smul]
  have hw' := smul_right_injective _ hd h3
  refine (mem_eigQuotLat _ _).2 ⟨_, Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (P.one_tmul_mem_latT _), hw'.symm⟩

end GlobalTheory.EigGlue
