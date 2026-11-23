import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIwVecTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ParahoricSph

open Matrix

section Contract

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

lemma rid_lTensor_map (φ : W →ₗ[ℂ] ℂ) (A : V →ₗ[ℂ] V) (B : W →ₗ[ℂ] W) (y : V ⊗[ℂ] W) :
    TensorProduct.rid ℂ V (φ.lTensor V (TensorProduct.map A B y)) =
      A (TensorProduct.rid ℂ V ((φ ∘ₗ B).lTensor V y)) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v w => simp
  | add y z hy hz => simp only [map_add, hy, hz]

lemma lid_rTensor_map (ψ : V →ₗ[ℂ] ℂ) (A : V →ₗ[ℂ] V) (B : W →ₗ[ℂ] W) (y : V ⊗[ℂ] W) :
    TensorProduct.lid ℂ W (ψ.rTensor W (TensorProduct.map A B y)) =
      B (TensorProduct.lid ℂ W ((ψ ∘ₗ A).rTensor W y)) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v w => simp
  | add y z hy hz => simp only [map_add, hy, hz]

lemma exists_rid_ne_zero {x : V ⊗[ℂ] W} (hx : x ≠ 0) :
    ∃ φ : W →ₗ[ℂ] ℂ, TensorProduct.rid ℂ V (φ.lTensor V x) ≠ 0 := by
  classical
  let b := Module.Free.chooseBasis ℂ W
  let e := TensorProduct.equivFinsuppOfBasisRight (M := V) b
  have he : e x ≠ 0 := by
    intro h; exact hx (e.injective (by rw [h, map_zero]))
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp he
  refine ⟨b.coord i, ?_⟩
  have key : ∀ w : V ⊗[ℂ] W, TensorProduct.rid ℂ V ((b.coord i).lTensor V w) = e w i := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul v y => simp [e, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
    | add y z hy hz => simp only [map_add, hy, hz, Finsupp.add_apply]
  rw [key]; simpa using hi

lemma exists_lid_ne_zero {x : V ⊗[ℂ] W} (hx : x ≠ 0) :
    ∃ ψ : V →ₗ[ℂ] ℂ, TensorProduct.lid ℂ W (ψ.rTensor W x) ≠ 0 := by
  have hc : TensorProduct.comm ℂ V W x ≠ 0 := fun h =>
    hx ((TensorProduct.comm ℂ V W).injective (by rw [h, map_zero]))
  obtain ⟨ψ, hψ⟩ := exists_rid_ne_zero hc
  refine ⟨ψ, ?_⟩
  have key : ∀ y : V ⊗[ℂ] W, TensorProduct.lid ℂ W (ψ.rTensor W y) =
      TensorProduct.rid ℂ W (ψ.lTensor W (TensorProduct.comm ℂ V W y)) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v w => simp
    | add y z hy hz => simp only [map_add, hy, hz]
  rw [key]; exact hψ

end Contract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valuation_det_of_mem_KO {n : Type} [Fintype n] [DecidableEq n] {g : GL n k}
    (hg : g ∈ KO k n) : valuation k ((GeneralLinearGroup.det g : kˣ) : k) = 1 := by
  obtain ⟨g, rfl⟩ := hg
  have h1 : ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap 𝒪[k] k) g) : kˣ) : k) =
      algebraMap 𝒪[k] k (GeneralLinearGroup.det g : 𝒪[k]ˣ) :=
    ((algebraMap 𝒪[k] k).map_det _).symm
  rw [h1]
  exact (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit _)

theorem emb₂_mem_KO {r t : ℕ} {m₁ : GL (Fin r) k} {m₂ : GL (Fin t) k} (h₁ : m₁ ∈ KO k (Fin r))
    (h₂ : m₂ ∈ KO k (Fin t)) :
    emb₂ k (stdSum (rfl : r + t = r + t)) (m₁, m₂) ∈ KO k (Fin (r + t)) := by
  obtain ⟨g₁, rfl⟩ := h₁
  obtain ⟨g₂, rfl⟩ := h₂
  refine ⟨emb₂ 𝒪[k] (stdSum (rfl : r + t = r + t)) (g₁, g₂), ?_⟩
  ext i j
  obtain ⟨i, rfl⟩ := (stdSum (rfl : r + t = r + t)).surjective i
  obtain ⟨j, rfl⟩ := (stdSum (rfl : r + t = r + t)).surjective j
  have hv := val_emb₂ 𝒪[k] (stdSum (rfl : r + t = r + t)) (g₁, g₂)
  have hw := val_emb₂ k (stdSum (rfl : r + t = r + t)) (GeneralLinearGroup.map (algebraMap 𝒪[k] k) g₁, GeneralLinearGroup.map (algebraMap 𝒪[k] k) g₂)
  show algebraMap 𝒪[k] k ((emb₂ 𝒪[k] (stdSum (rfl : r + t = r + t)) (g₁, g₂)).val _ _) = _
  rw [hv, hw]
  rcases i with i | i <;> rcases j with j | j <;> simp [GeneralLinearGroup.map]

theorem extTensor_apply_eq {r t : ℕ} {χ : kˣ →* ℂˣ} {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {σ₁ : Representation ℂ (GL (Fin r) k) V}
    {σ₂ : Representation ℂ (GL (Fin t) k) W} {f : _} (hf : IsParahoricVec χ (prod₂ σ₁ σ₂) f)
    {m₁ : GL (Fin r) k} {m₂ : GL (Fin t) k} (h₁ : m₁ ∈ KO k (Fin r)) (h₂ : m₂ ∈ KO k (Fin t)) :
    extTensor σ₁ σ₂ (m₁, m₂) (f.1.1 1) = (χ (GeneralLinearGroup.det m₂) : ℂ) • f.1.1 1 := by
  have hmem := emb₂_mem_KO h₁ h₂
  have hv := val_emb₂ k (stdSum (rfl : r + t = r + t)) (m₁, m₂)
  have hll : ∀ (i : Fin t) (j : Fin r),
      valuation k ((emb₂ k (stdSum (rfl : r + t = r + t)) (m₁, m₂)).val (Fin.natAdd r i) (Fin.castAdd t j)) < 1 := by
    intro i j
    have h0 : (emb₂ k (stdSum (rfl : r + t = r + t)) (m₁, m₂)).val (Fin.natAdd r i) (Fin.castAdd t j) = 0 := by
      have hi : Fin.natAdd r i = (stdSum (rfl : r + t = r + t)) (Sum.inr i) := by ext; simp
      have hj : Fin.castAdd t j = (stdSum (rfl : r + t = r + t)) (Sum.inl j) := by ext; simp
      rw [hv, hi, hj]
      simp
    rw [h0, map_zero]
    exact zero_lt_one
  have hdet : ((GeneralLinearGroup.det m₂ : kˣ) : k) =
      ((emb₂ k (stdSum (rfl : r + t = r + t)) (m₁, m₂)).val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det := by
    have hs : (emb₂ k (stdSum (rfl : r + t = r + t)) (m₁, m₂)).val.submatrix (Fin.natAdd r) (Fin.natAdd r) = m₂.val := by
      ext i j
      have hi : Fin.natAdd r i = (stdSum (rfl : r + t = r + t)) (Sum.inr i) := by ext; simp
      have hj : Fin.natAdd r j = (stdSum (rfl : r + t = r + t)) (Sum.inr j) := by ext; simp
      rw [submatrix_apply, hv, hi, hj]
      simp
    rw [hs]
    rfl
  have H := congrArg (fun F => F.1.1 (1 : GL (Fin (r + t)) k)) (hf _ hmem hll _ hdet)
  let p : parab k (two (stdSum (rfl : r + t = r + t))) := ⟨leviEmb k (two (stdSum (rfl : r + t = r + t))) (leviTwo k (Fin r) (Fin t) (m₁, m₂)),
    leviEmb_mem_parab k (two (stdSum (rfl : r + t = r + t))) _⟩
  have H2 := parInd_law (two (stdSum (rfl : r + t = r + t)))
    ((extTensor σ₁ σ₂).comp (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) f p 1
  have hδ : (deltaHalf k (Two (Fin r) (Fin t)) (leviTwo k (Fin r) (Fin t) (m₁, m₂)) : ℂ) = 1 := by
    rw [deltaHalf_two, isUnram_absPow k _ _ (valuation_det_of_mem_KO h₁),
      isUnram_absPow k _ _ (valuation_det_of_mem_KO h₂), mul_one, Units.val_one]
  rw [leviProj_leviEmb, hδ, one_smul] at H2
  have E1 : f.1.1 ((p : GL (Fin (r + t)) k) * 1) = f.1.1 (1 * emb₂ k (stdSum (rfl : r + t = r + t)) (m₁, m₂)) := by
    rw [mul_one, one_mul]; rfl
  rw [E1] at H2
  change f.1.1 (1 * emb₂ k (stdSum (rfl : r + t = r + t)) (m₁, m₂)) = (χ _ : ℂ) • f.1.1 1 at H
  rw [H] at H2
  rw [H2]
  simp

theorem isSpherical_of_isParahoricVec : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (W : Type) [AddCommGroup W] [Module ℂ W] (σ₁ : Representation ℂ (GL (Fin r) k) V)
    (σ₂ : Representation ℂ (GL (Fin t) k) W) (f : _), IsParahoricVec χ (prod₂ σ₁ σ₂) f →
    f.1.1 1 ≠ 0 → IsSpherical σ₁ ∧ IsSpherical (twist σ₂ (detChar (Fin t) χ⁻¹)) := by
  intro k _ _ _ _ r t χ V _ _ W _ _ σ₁ σ₂ f hf h0
  constructor
  · obtain ⟨φ, hφ⟩ := exists_rid_ne_zero h0
    refine (Submodule.ne_bot_iff _).2 ⟨_, ?_, hφ⟩
    rintro ⟨m, hm⟩
    have H := extTensor_apply_eq hf hm (one_mem (KO k (Fin t)))
    change TensorProduct.map (σ₁ m) (σ₂ 1) (f.1.1 1) = _ at H
    show σ₁ m _ = ((1 : KO k (Fin r) →* ℂˣ) ⟨m, hm⟩ : ℂ) • _
    rw [MonoidHom.one_apply, Units.val_one, one_smul]
    have H' := congrArg (fun y => TensorProduct.rid ℂ V (φ.lTensor V y)) H
    rw [rid_lTensor_map] at H'
    simpa [Module.End.one_eq_id] using H'
  · obtain ⟨ψ, hψ⟩ := exists_lid_ne_zero h0
    refine (Submodule.ne_bot_iff _).2 ⟨_, ?_, hψ⟩
    rintro ⟨m, hm⟩
    have H := extTensor_apply_eq hf (one_mem (KO k (Fin r))) hm
    change TensorProduct.map (σ₁ 1) (σ₂ m) (f.1.1 1) = _ at H
    show twist σ₂ (detChar (Fin t) χ⁻¹) m _ = ((1 : KO k (Fin t) →* ℂˣ) ⟨m, hm⟩ : ℂ) • _
    rw [MonoidHom.one_apply, Units.val_one, one_smul, twist_apply]
    have H' := congrArg (fun y => TensorProduct.lid ℂ W (ψ.rTensor W y)) H
    rw [lid_rTensor_map] at H'
    simp [Module.End.one_eq_id] at H'
    rw [H', smul_smul, ← Units.val_mul]
    simp

end GlobalTheory.ParahoricSph
