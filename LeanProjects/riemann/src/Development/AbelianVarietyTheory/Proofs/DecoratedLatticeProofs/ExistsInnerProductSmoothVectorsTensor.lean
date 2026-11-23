import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PiTensorInner

variable {ι : Type} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]

def ellA (a : ∀ i, E i) : (⨂[ℂ] i, E i) →ₗ[ℂ] ℂ :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap fun i => innerₛₗ ℂ (a i))

theorem ellA_tprod (a b : ∀ i, E i) : ellA a (PiTensorProduct.tprod ℂ b) = ∏ i, ⟪a i, b i⟫_ℂ := by
  simp [ellA]

theorem prod_inner_update [DecidableEq ι] (a b : ∀ i, E i) (i : ι) (z : E i) :
    ∏ j, ⟪Function.update a i z j, b j⟫_ℂ = ⟪z, b i⟫_ℂ * ∏ j ∈ Finset.univ \ {i}, ⟪a j, b j⟫_ℂ := by
  have : (fun j => ⟪Function.update a i z j, b j⟫_ℂ) = Function.update (fun j => ⟪a j, b j⟫_ℂ) i ⟪z, b i⟫_ℂ := by
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  rw [this, Finset.prod_update_of_mem (Finset.mem_univ i)]

theorem ellA_update_add [DecidableEq ι] (a : ∀ i, E i) (i : ι) (x y : E i) :
    ellA (Function.update a i (x + y)) = ellA (Function.update a i x) + ellA (Function.update a i y) := by
  apply PiTensorProduct.ext
  ext b
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.add_apply, ellA_tprod, prod_inner_update, inner_add_left, add_mul]

theorem ellA_update_smul [DecidableEq ι] (a : ∀ i, E i) (i : ι) (c : ℂ) (x : E i) :
    ellA (Function.update a i (c • x)) = conj c • ellA (Function.update a i x) := by
  apply PiTensorProduct.ext
  ext b
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.smul_apply, ellA_tprod, prod_inner_update, inner_smul_left, smul_eq_mul, mul_assoc]

def ellC (a : ∀ i, E i) : (⨂[ℂ] i, E i) →ₗ⋆[ℂ] ℂ :=
  (starLinearEquiv ℂ : ℂ ≃ₗ⋆[ℂ] ℂ).toLinearMap.comp (ellA a)

theorem ellC_apply (a : ∀ i, E i) (w : ⨂[ℂ] i, E i) : ellC a w = conj (ellA a w) := rfl

theorem ellC_tprod (a b : ∀ i, E i) : ellC a (PiTensorProduct.tprod ℂ b) = ∏ i, ⟪b i, a i⟫_ℂ := by
  rw [ellC_apply, ellA_tprod, map_prod]; simp

def ellM : MultilinearMap ℂ E ((⨂[ℂ] i, E i) →ₗ⋆[ℂ] ℂ) where
  toFun := ellC
  map_update_add' a i x y := by
    ext w; simp [ellC_apply, ellA_update_add]
  map_update_smul' a i c x := by
    ext w; simp [ellC_apply, ellA_update_smul]

def ipT : (⨂[ℂ] i, E i) →ₗ[ℂ] (⨂[ℂ] i, E i) →ₗ⋆[ℂ] ℂ := PiTensorProduct.lift ellM

theorem ipT_tprod (a b : ∀ i, E i) :
    ipT (PiTensorProduct.tprod ℂ a) (PiTensorProduct.tprod ℂ b) = ∏ i, ⟪b i, a i⟫_ℂ := by
  simp [ipT, ellM, ellC_tprod]

theorem ipT_herm (w w' : ⨂[ℂ] i, E i) : ipT w w' = conj (ipT w' w) := by
  induction w using PiTensorProduct.induction_on generalizing w' with
  | smul_tprod r a =>
    induction w' using PiTensorProduct.induction_on with
    | smul_tprod s b =>
      simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, ipT_tprod, smul_eq_mul, map_mul, map_prod, inner_conj_symm,
        RingHomCompTriple.comp_apply, RingHom.id_apply, Complex.conj_conj]
      ring
    | add x y hx hy => rw [map_add, hx, hy, map_add, LinearMap.add_apply, map_add]
  | add x y hx hy => simp [map_add, LinearMap.add_apply, hx, hy]

end GlobalTheory.PiTensorInner

noncomputable section

namespace GlobalTheory.PiTensorInner

variable {ι : Type} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]

theorem ipT_map {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace ℂ (G i)]
    (f : ∀ i, G i →ₗ[ℂ] E i) (hf : ∀ i x y, ⟪f i x, f i y⟫_ℂ = ⟪x, y⟫_ℂ) (x y : ⨂[ℂ] i, G i) :
    ipT (PiTensorProduct.map f x) (PiTensorProduct.map f y) = ipT x y := by
  induction x using PiTensorProduct.induction_on generalizing y with
  | smul_tprod r a =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod s b =>
      simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, PiTensorProduct.map_tprod, ipT_tprod, hf]
    | add x y hx hy => simp only [map_add, hx, hy]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

theorem ipT_pos_fd [∀ i, FiniteDimensional ℂ (E i)] (x : ⨂[ℂ] i, E i) (hx : x ≠ 0) : 0 < (ipT x x).re := by
  classical
  let e := fun i => stdOrthonormalBasis ℂ (E i)
  let B := Basis.piTensorProduct fun i => (e i).toBasis
  have hB : ∀ p q, ipT (B p) (B q) = if p = q then 1 else 0 := by
    intro p q
    simp only [B, Basis.piTensorProduct_apply, OrthonormalBasis.coe_toBasis, ipT_tprod]
    split_ifs with h
    · subst h; simp [OrthonormalBasis.inner_eq_ite]
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [OrthonormalBasis.inner_eq_ite, Ne.symm hi])
  set c := B.repr x
  have hsum : ipT x x = ∑ p, c p * conj (c p) := by
    conv_lhs => rw [← B.sum_repr x]
    simp only [map_sum, map_smul, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, hB, smul_eq_mul]
    simp [Finset.mul_sum, c]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have hc : c ≠ 0 := by
    intro h; apply hx
    rw [← B.sum_repr x]; simp [c] at h; simp [h]
  obtain ⟨p, hp⟩ : ∃ p, c p ≠ 0 := by
    by_contra h; push_neg at h; exact hc (Finsupp.ext h)
  rw [hsum, Complex.re_sum]
  refine Finset.sum_pos' (fun q _ => ?_) ⟨p, Finset.mem_univ p, ?_⟩
  · rw [Complex.mul_conj]; simp [Complex.normSq_nonneg]
  · rw [Complex.mul_conj]; simpa using Complex.normSq_pos.mpr hp

end GlobalTheory.PiTensorInner

noncomputable section

namespace GlobalTheory.PiTensorInner

variable {ι : Type} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]

theorem exists_fd (w : ⨂[ℂ] i, E i) : ∃ F : ∀ i, Submodule ℂ (E i), (∀ i, FiniteDimensional ℂ (F i)) ∧
    ∃ w₀ : ⨂[ℂ] i, F i, PiTensorProduct.map (fun i => (F i).subtype) w₀ = w := by
  induction w using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    refine ⟨fun i => ℂ ∙ a i, fun i => inferInstance, r • PiTensorProduct.tprod ℂ (fun i => ⟨a i, Submodule.mem_span_singleton_self _⟩), ?_⟩
    simp
  | add x y hx hy =>
    obtain ⟨F₁, h₁, x₀, rfl⟩ := hx
    obtain ⟨F₂, h₂, y₀, rfl⟩ := hy
    refine ⟨fun i => F₁ i ⊔ F₂ i, fun i => inferInstance,
      PiTensorProduct.map (fun i => Submodule.inclusion (le_sup_left : F₁ i ≤ F₁ i ⊔ F₂ i)) x₀ +
      PiTensorProduct.map (fun i => Submodule.inclusion (le_sup_right : F₂ i ≤ F₁ i ⊔ F₂ i)) y₀, ?_⟩
    rw [map_add, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
    rfl

theorem ipT_pos (w : ⨂[ℂ] i, E i) (hw : w ≠ 0) : 0 < (ipT w w).re := by
  obtain ⟨F, hF, w₀, rfl⟩ := exists_fd w
  have h0 : w₀ ≠ 0 := by rintro rfl; exact hw (map_zero _)
  rw [ipT_map (fun i => (F i).subtype) (fun i x y => rfl)]
  exact ipT_pos_fd w₀ h0

end GlobalTheory.PiTensorInner

namespace GlobalTheory.ChainOnto

theorem exists_ipD_smT : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), ∃ ipD : SmT M →ₗ[ℂ] SmT M →ₗ⋆[ℂ] ℂ,
    (∀ v v' : M.Vec, ipD (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v') = ∏ τ, ⟪(v' τ : M.H τ), (v τ : M.H τ)⟫_ℂ) ∧
    (∀ w w', ipD w w' = conj (ipD w' w)) ∧ ∀ w, w ≠ 0 → 0 < (ipD w w).re := by
  intro D V S M
  exact ⟨GlobalTheory.PiTensorInner.ipT, fun v v' => GlobalTheory.PiTensorInner.ipT_tprod v v', GlobalTheory.PiTensorInner.ipT_herm,
    GlobalTheory.PiTensorInner.ipT_pos⟩

end GlobalTheory.ChainOnto
