import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntLocConjIntLocConj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open scoped TensorProduct
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdelicU GlobalTheory.TamOne

namespace GlobalTheory.TamOne

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem algebraMap_locAlg_tmul (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    (a : v.adicCompletionIntegers (maximalRealSubfield E)) :
    algebraMap (v.adicCompletionIntegers (maximalRealSubfield E)) (GlobalTheory.SelfDualGenus.LocAlg v) a =
      (a : Fv (maximalRealSubfield E) v) ⊗ₜ[maximalRealSubfield E] (1 : E) := rfl

theorem coe_intLoc_eq_locOrder (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) :
    ((intLoc (maximalRealSubfield E) E v : Subring _) :
        Set (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E)) =
      ((GlobalTheory.SelfDualGenus.locOrder v : Subalgebra _ _) : Set (GlobalTheory.SelfDualGenus.LocAlg v)) := by
  apply Set.Subset.antisymm
  · intro z hz
    have h : (intLoc (maximalRealSubfield E) E v).toAddSubgroup ≤
        (GlobalTheory.SelfDualGenus.locOrder v).toSubring.toAddSubgroup := by
      change AddSubgroup.closure _ ≤ _
      rw [AddSubgroup.closure_le]
      rintro _ ⟨a, ha, x, rfl⟩
      have e : (a ⊗ₜ[maximalRealSubfield E] (x : E) : GlobalTheory.SelfDualGenus.LocAlg v) =
          algebraMap (v.adicCompletionIntegers (maximalRealSubfield E)) (GlobalTheory.SelfDualGenus.LocAlg v)
            ⟨a, ha⟩ * GlobalTheory.SelfDualGenus.locEmb v x := by
        rw [GlobalTheory.SelfDualGenus.locEmb_apply, algebraMap_locAlg_tmul,
          Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      change _ ∈ GlobalTheory.SelfDualGenus.locOrder v
      rw [e]
      exact mul_mem (Subalgebra.algebraMap_mem _ _) (GlobalTheory.SelfDualGenus.locEmb_mem_locOrder v x)
    exact h hz
  · intro z hz
    change z ∈ GlobalTheory.SelfDualGenus.locOrder v at hz
    induction hz using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact tmul_mem_intLoc (one_mem _) a
    | algebraMap a =>
      rw [algebraMap_locAlg_tmul]
      exact tmul_mem_intLoc (F := maximalRealSubfield E) (E := E) (v := v) a.2 (1 : 𝓞 E)
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy

theorem coe_latLoc_eq_locLattice (Λ : Submodule (𝓞 E) (Fin r → E))
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) :
    ((latLoc (maximalRealSubfield E) Λ v : Submodule _ _) :
        Set (Fin r → Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E)) =
      (GlobalTheory.SelfDualGenus.locLattice v Λ : Set (Fin r → GlobalTheory.SelfDualGenus.LocAlg v)) := by
  apply Set.Subset.antisymm
  · intro z hz
    have hz' : z ∈ AddSubgroup.closure {y : Fin r → Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E |
        ∃ a ∈ v.adicCompletionIntegers (maximalRealSubfield E), ∃ x ∈ Λ,
          y = fun i => a ⊗ₜ[maximalRealSubfield E] x i} := hz
    refine (AddSubgroup.closure_le (K := (GlobalTheory.SelfDualGenus.locLattice v Λ).toAddSubgroup)).2 ?_ hz'
    rintro _ ⟨a, ha, x, hx, rfl⟩
    have e : (fun i => a ⊗ₜ[maximalRealSubfield E] x i : Fin r → GlobalTheory.SelfDualGenus.LocAlg v) =
        (⟨a, ha⟩ : v.adicCompletionIntegers (maximalRealSubfield E)) •
          (fun i => GlobalTheory.SelfDualGenus.locEmb v (x i)) := by
      funext i
      rw [Pi.smul_apply, Algebra.smul_def, algebraMap_locAlg_tmul, GlobalTheory.SelfDualGenus.locEmb_apply,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, hx, rfl⟩)
  · intro z hz
    change z ∈ GlobalTheory.SelfDualGenus.locLattice v Λ at hz
    induction hz using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      exact AddSubgroup.subset_closure ⟨1, one_mem _, x, hx, rfl⟩
    | zero => exact zero_mem (latLoc (maximalRealSubfield E) Λ v)
    | add x y _ _ hx hy => exact (latLoc (maximalRealSubfield E) Λ v).add_mem hx hy
    | smul c x _ hx =>
      have := (latLoc (maximalRealSubfield E) Λ v).smul_mem
        (⟨(c : Fv (maximalRealSubfield E) v) ⊗ₜ[maximalRealSubfield E] ((1 : 𝓞 E) : E),
          tmul_mem_intLoc c.2 1⟩ : intLoc (maximalRealSubfield E) E v) hx
      have e : c • x = (⟨(c : Fv (maximalRealSubfield E) v) ⊗ₜ[maximalRealSubfield E] ((1 : 𝓞 E) : E),
          tmul_mem_intLoc c.2 1⟩ : intLoc (maximalRealSubfield E) E v) • x := by
        funext i
        rw [Pi.smul_apply, Algebra.smul_def, algebraMap_locAlg_tmul]
        rfl
      rw [e]
      exact this

end GlobalTheory.TamOne

open GlobalTheory.TamOne in

theorem GlobalTheory.TamOne.exists_orthonormal_frame_latLoc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), Unr E → SelfDualLat G Λ → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), ∃ h : GL (Fin r) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E), Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv (maximalRealSubfield E) v) (cj E)) (h : Matrix (Fin r) (Fin r) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E)) * JR (F := maximalRealSubfield E) (Fv (maximalRealSubfield E) v) Gᵀ * (h : Matrix (Fin r) (Fin r) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E)) = 1 ∧ ∀ z : Fin r → Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E, z ∈ latLoc (maximalRealSubfield E) Λ v ↔ ∀ i, (((h⁻¹ : GL (Fin r) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E)) : Matrix (Fin r) (Fin r) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E)) *ᵥ z) i ∈ intLoc (maximalRealSubfield E) E v := by
  intro E _ _ _ r G Λ hU hSD v
  haveI : Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) := hU
  obtain ⟨hG, hd, hfg, hspan, hsd⟩ := hSD
  obtain ⟨h, h1, h2⟩ := GlobalTheory.SelfDualGenus.exists_orthonormal_frame hG hd ⟨hfg, hspan⟩
    (fun x => (hsd x).symm) v
  refine ⟨h, ?_, fun z => ?_⟩
  · have e := congrArg Matrix.transpose h1
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one,
      ← Matrix.mul_assoc, ← Matrix.transpose_map] at e
    exact e
  · have hz := h2 z
    rw [← SetLike.mem_coe, coe_latLoc_eq_locLattice]
    refine hz.trans (forall_congr' fun i => ?_)
    rw [← SetLike.mem_coe (x := (_ : GlobalTheory.SelfDualGenus.LocAlg v)) (p := GlobalTheory.SelfDualGenus.locOrder v),
      ← coe_intLoc_eq_locOrder, SetLike.mem_coe]
