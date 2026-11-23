import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActEquivSymmApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RallisCusp

open GlobalTheory.MixModel

variable {D : D7}

theorem mem_span_cols {n s : ℕ} (I : Matrix (Fin n) (Fin s) D.host.E) (v : Fin n → D.host.E) :
    v ∈ Submodule.span D.host.E (Set.range I.transpose) ↔ ∃ a, I *ᵥ a = v := by
  change v ∈ Submodule.span D.host.E (Set.range I.col) ↔ _
  rw [← Matrix.range_mulVecLin]; rfl

theorem exists_mul_eq_mul {n s : ℕ} (I : Matrix (Fin n) (Fin s) D.host.E) (M : Matrix (Fin n) (Fin n) D.host.E)
    (h : ∀ v ∈ Submodule.span D.host.E (Set.range I.transpose),
      M *ᵥ v ∈ Submodule.span D.host.E (Set.range I.transpose)) :
    ∃ A : Matrix (Fin s) (Fin s) D.host.E, M * I = I * A := by
  have h1 : ∀ j, ∃ b, I *ᵥ b = M *ᵥ I.transpose j := fun j =>
    (mem_span_cols I _).1 (h _ (Submodule.subset_span ⟨j, rfl⟩))
  choose f hf using h1
  refine ⟨Matrix.of fun i j => f j i, ?_⟩
  refine Matrix.ext fun k j => ?_
  have := congrFun (hf j) k
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply] at this
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simpa using this.symm

theorem frame_gram_mul {n s : ℕ} (I : Matrix (Fin n) (Fin s) D.host.E) (J c c' : Matrix (Fin n) (Fin n) D.host.E)
    (hc : c * c' = 1) (hu : cᴴ * J * c = J) : Iᴴ * J * c = (c' * I)ᴴ * J := by
  have h1 : (c * c')ᴴ = 1 := by rw [hc, Matrix.conjTranspose_one]
  calc Iᴴ * J * c = Iᴴ * (c * c')ᴴ * J * c := by rw [h1, Matrix.mul_one]
    _ = Iᴴ * c'ᴴ * (cᴴ * J * c) := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = (c' * I)ᴴ * J := by rw [hu, Matrix.conjTranspose_mul]

theorem mul_mul_mul_eq_zero {R : Type} [CommRing R] {n s : ℕ} (C C' m : Matrix (Fin n) (Fin n) R)
    (I : Matrix (Fin n) (Fin s) R) (A' : Matrix (Fin s) (Fin s) R) (h : C' * I = I * A') (h0 : m * I = 0) :
    C * m * C' * I = 0 := by
  rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, Matrix.mul_assoc C, h0, Matrix.mul_zero, Matrix.zero_mul]

theorem mul_mul_mul_eq_zero' {R : Type} [CommRing R] {n s : ℕ} (C C' m : Matrix (Fin n) (Fin n) R)
    (K : Matrix (Fin s) (Fin n) R) (A' : Matrix (Fin s) (Fin s) R) (h : K * C = A' * K) (h0 : K * m = 0) :
    K * (C * m * C') = 0 := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h, Matrix.mul_assoc A', h0, Matrix.mul_zero, Matrix.zero_mul]

set_option maxHeartbeats 2000000 in

theorem conj_mem_NI : ∀ (D : D7) (W : HSp D) (Y : Lag W) (s : ℕ) (I : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W I → Submodule.span D.host.E (Set.range I.transpose) = Y.1.comap (LinearMap.inl D.host.E _ _) → ∀ γ : GQ W, GlobalTheory.RallisCusp.lagAct W γ Y = Y → ∀ n ∈ NI W I, (γ : GA D W) * n * (γ : GA D W)⁻¹ ∈ NI W I := by
  intro D W Y s I _ hS γ hY n hn
  set c := gqMat W γ with hc_def
  set c' := gqMat W γ⁻¹ with hc'_def
  have hcc' : c * c' = 1 := gqMat_mul_inv W γ
  have hc'c : c' * c = 1 := gqMat_inv_mul W γ
  have memS : ∀ v, v ∈ Submodule.span D.host.E (Set.range I.transpose) ↔ ((v, 0) : _ × _) ∈ Y.1 := by
    intro v; rw [hS, Submodule.mem_comap, LinearMap.inl_apply]
  have memY : ∀ y, y ∈ Y.1 ↔ (c' *ᵥ y.1, y.2) ∈ Y.1 := by
    intro y; conv_lhs => rw [← hY]
    exact mem_lagAct W γ Y y
  have hcS : ∀ v ∈ Submodule.span D.host.E (Set.range I.transpose),
      c *ᵥ v ∈ Submodule.span D.host.E (Set.range I.transpose) := by
    intro v hv
    rw [memS, memY]
    simpa [Matrix.mulVec_mulVec, hc'c] using (memS v).1 hv
  have hc'S : ∀ v ∈ Submodule.span D.host.E (Set.range I.transpose),
      c' *ᵥ v ∈ Submodule.span D.host.E (Set.range I.transpose) := by
    intro v hv
    rw [memS]
    exact (memY _).1 ((memS v).1 hv)
  obtain ⟨A, hA⟩ := exists_mul_eq_mul I c' hc'S
  obtain ⟨B, hB⟩ := exists_mul_eq_mul I c hcS
  have hIc : Iᴴ * W.gram * c = Aᴴ * (Iᴴ * W.gram) := by
    rw [frame_gram_mul I W.gram c c' hcc' (gqMat_unitary W γ), hA, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hIc' : Iᴴ * W.gram * c' = Bᴴ * (Iᴴ * W.gram) := by
    rw [frame_gram_mul I W.gram c' c hc'c (gqMat_unitary W γ⁻¹), hB, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hrat : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) D.host.E), M.map (incA D) = rat M := fun _ => rfl
  have hγ : mt W (γ : GA D W) = rat c := (rat_gqMat W γ).symm
  have hγ' : mt W ((γ : GA D W)⁻¹) = rat c' := (rat_gqMat W γ⁻¹).symm
  have hle : NI W I ≤ (NI W I).comap (MulAut.conj (γ : GA D W)).toMonoidHom := by
    unfold NI
    rw [Subgroup.closure_le]
    intro g hg
    obtain ⟨h1, h2, h3⟩ := hg
    apply Subgroup.subset_closure
    have hm : (matHom W ((MulAut.conj (γ : GA D W)).toMonoidHom g)).1 - 1 = rat c * ((matHom W g).1 - 1) * rat c' := by
      change mt W ((γ : GA D W) * g * (γ : GA D W)⁻¹) - 1 = rat c * (mt W g - 1) * rat c'
      rw [mt_mul, mt_mul, hγ, hγ', Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ← rat_mul, hcc', rat_one]
    rw [cT_sig, hrat] at h2 h3
    rw [hrat] at h1
    have hA' : rat c' ⬝ rat I = rat I ⬝ rat A := by rw [← rat_mul, hA, rat_mul]
    have hIc2 : rat (Iᴴ * W.gram) ⬝ rat c = rat Aᴴ ⬝ rat (Iᴴ * W.gram) := by rw [← rat_mul, hIc, rat_mul]
    have hB' : rat c ⬝ rat I = rat I ⬝ rat B := by rw [← rat_mul, hB, rat_mul]
    refine ⟨?_, ?_, ?_⟩
    · rw [hm, hrat]
      exact mul_mul_mul_eq_zero (rat c) (rat c') _ (rat I) (rat A) hA' h1
    · rw [hm, cT_sig, hrat]
      exact mul_mul_mul_eq_zero' (rat c) (rat c') _ (rat (Iᴴ * W.gram)) (rat Aᴴ) hIc2 h2
    · intro x hx
      rw [cT_sig] at hx
      have hx' : (Iᴴ * W.gram) *ᵥ (c' *ᵥ x) = 0 := by
        rw [Matrix.mulVec_mulVec, hIc', ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
      obtain ⟨a, ha⟩ := h3 (c' *ᵥ x) hx'
      refine ⟨rat B *ᵥ a, ?_⟩
      have hv : rat c' *ᵥ (fun i => incA D (x i)) = fun i => incA D ((c' *ᵥ x) i) := by
        funext i; exact (RingHom.map_mulVec (incA D) c' x i).symm
      rw [hm, hrat, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, ha, Matrix.mulVec_mulVec, hB',
        Matrix.mulVec_mulVec]
  exact hle hn

end GlobalTheory.RallisCusp

end
