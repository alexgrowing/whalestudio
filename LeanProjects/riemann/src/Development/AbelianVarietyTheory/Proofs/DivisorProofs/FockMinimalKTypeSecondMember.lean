import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDualPairSwapSymmetryStatement

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.FockAlg.MinSecond

section Transport

variable {p q : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem isHW_equiv (e : V ≃ₗ[ℂ] W) (a : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (b : Mat p q →ₗ[ℂ] Module.End ℂ W) (h : ∀ Z v, e (a Z v) = b Z (e v))
    (μ : Ix p q → ℚ) (v : V) (hv : IsHW a μ v) : IsHW b μ (e v) := by
  obtain ⟨h0, h1⟩ := hv
  refine ⟨fun h' => h0 (e.map_eq_zero_iff.mp h'), ?_⟩
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at h1 ⊢
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rw [← h, ← map_smul, ← map_sub, h1.1 i, map_zero]
  · rw [← h, h1.2 i j hij, map_zero]

theorem symm_equivariant (e : V ≃ₗ[ℂ] W) (a : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (b : Mat p q →ₗ[ℂ] Module.End ℂ W) (h : ∀ Z v, e (a Z v) = b Z (e v)) (Z : Mat p q) (w : W) :
    e.symm (b Z w) = a Z (e.symm w) := by
  apply e.injective
  rw [h, e.apply_symm_apply, e.apply_symm_apply]

theorem ofType_equiv (e : V ≃ₗ[ℂ] W) (a : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (b : Mat p q →ₗ[ℂ] Module.End ℂ W) (h : ∀ Z v, e (a Z v) = b Z (e v))
    (μ : Ix p q → ℚ) (v : V) (hv : OfType a μ v) : OfType b μ (e v) := by
  obtain ⟨U, hf, hvU, hst, hw⟩ := hv
  refine ⟨U.map (e : V →ₗ[ℂ] W), inferInstance, ⟨v, hvU, rfl⟩, ?_, ?_⟩
  · rintro X hX _ ⟨u, hu, rfl⟩
    exact ⟨a X u, hst X hX u hu, h X u⟩
  · rintro ν _ ⟨u, hu, rfl⟩ hν
    refine hw ν u hu ?_
    have := isHW_equiv e.symm b a (symm_equivariant e a b h) ν _ hν
    simpa using this

theorem genSub_map (e : V →ₗ[ℂ] W) (a : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (b : Mat p q →ₗ[ℂ] Module.End ℂ W) (h : ∀ Z v, e (a Z v) = b Z (e v))
    (S : Set V) (T : Set W) (hST : ∀ v ∈ S, e v ∈ T) (v : V) (hv : v ∈ genSub a S) :
    e v ∈ genSub b T := by
  simp only [genSub, Submodule.mem_sInf, Set.mem_ofPred_eq] at hv ⊢
  intro N hN
  refine hv (N.comap e) ⟨fun x hx => hN.1 (hST x hx), fun Z y hy => ?_⟩
  rw [Submodule.mem_comap, h]
  exact hN.2 Z _ hy

end Transport

noncomputable def swapPol (p q r s : ℕ) : Pol p q r s ≃ₗ[ℂ] Pol r s p q :=
  (renameEquiv ℂ (Equiv.prodComm (Ix p q) (Ix r s))).toLinearEquiv

end GlobalTheory.FockAlg.MinSecond

open GlobalTheory.FockAlg.MinSecond in

theorem GlobalTheory.FockAlg.min_second : ∀ (p q r s : ℕ) (M1 : GKMod p q) (M2 : GKMod r s) (f : Pol p q r s →ₗ[ℂ] TensorProduct ℂ M1.V M2.V), IrrGK M2 → AdmGK M2 → Intw M1 M2 f → f ≠ 0 → ∀ (μ' : Ix r s → ℚ), (∃ v, IsHW M2.act μ' v) → (∀ ν w, IsHW M2.act ν w → degW (cPair p q) μ' ≤ degW (cPair p q) ν) → (∃ (μ : Ix p q → ℚ) (P : Pol p q r s), P ∈ jointHarm p q r s ∧ IsHW (fockAct1 p q r s) μ P ∧ IsHW (fockAct2 p q r s) μ' P ∧ f P ≠ 0) ∧ ∀ P, OfType (fockAct2 p q r s) μ' P → f P ∈ Submodule.map f (genSub (fockAct1 p q r s) {Q | Q ∈ jointHarm p q r s ∧ OfType (fockAct2 p q r s) μ' Q}) := by
  intro p q r s M1 M2 f hirr hadm hf hf0 μ' hμ hmin
  obtain ⟨s1, s2, s3⟩ := GlobalTheory.T.fock_dualPair_swap_symmetry r s p q
  set e := swapPol r s p q with he
  have h1 : ∀ Z v, e (fockAct1 r s p q Z v) = fockAct2 p q r s Z (e v) := s1
  have h2 : ∀ Z v, e (fockAct2 r s p q Z v) = fockAct1 p q r s Z (e v) := s2
  have hJ : ∀ P, P ∈ jointHarm r s p q → e P ∈ jointHarm p q r s := fun P hP =>
    ⟨(s3 P).1.mp hP.2, (s3 P).2.mp hP.1⟩
  set c := TensorProduct.comm ℂ M1.V M2.V with hc
  let g : Pol r s p q →ₗ[ℂ] TensorProduct ℂ M2.V M1.V :=
    (c : _ →ₗ[ℂ] _) ∘ₗ f ∘ₗ (e : _ →ₗ[ℂ] _)
  have hg : ∀ P, g P = c (f (e P)) := fun _ => rfl
  have hcm : ∀ (A : Module.End ℂ M1.V) (B : Module.End ℂ M2.V) x,
      c (TensorProduct.map A B x) = TensorProduct.map B A (c x) := by
    intro A B x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hc]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hgI : Intw M2 M1 g := by
    refine ⟨fun X => LinearMap.ext fun P => ?_, fun X => LinearMap.ext fun P => ?_⟩
    · have := LinearMap.congr_fun (hf.2 X) (e P)
      simp only [LinearMap.comp_apply] at this ⊢
      rw [hg, hg, h1, this, hcm]
    · have := LinearMap.congr_fun (hf.1 X) (e P)
      simp only [LinearMap.comp_apply] at this ⊢
      rw [hg, hg, h2, this, hcm]
  have hg0 : g ≠ 0 := by
    intro h
    apply hf0
    refine LinearMap.ext fun P => ?_
    have := LinearMap.congr_fun h (e.symm P)
    rw [hg, e.apply_symm_apply, LinearMap.zero_apply] at this
    exact c.map_eq_zero_iff.mp this
  obtain ⟨⟨μ, P, hP, hP1, hP2, hP0⟩, hB⟩ := GlobalTheory.T.exists_jointHarm_highestWeight_and_map_mem_genSub r s p q M2 M1 g hirr hadm hgI hg0 μ' hμ hmin
  refine ⟨⟨μ, e P, hJ P hP, isHW_equiv e _ _ h2 _ _ hP2, isHW_equiv e _ _ h1 _ _ hP1, ?_⟩, ?_⟩
  · intro h
    apply hP0
    rw [hg, h, map_zero]
  · intro R hR
    obtain ⟨Q, hQ, hQe⟩ := hB (e.symm R)
      (ofType_equiv e.symm _ _ (symm_equivariant e _ _ h1) _ _ hR)
    refine ⟨e Q, ?_, ?_⟩
    · exact genSub_map e.toLinearMap (fockAct2 r s p q) (fockAct1 p q r s) h2 _
        {Q | Q ∈ jointHarm p q r s ∧ OfType (fockAct2 p q r s) μ' Q}
        (fun v hv => ⟨hJ v hv.1, ofType_equiv e _ _ h1 _ _ hv.2⟩) Q hQ
    · rw [hg, hg, e.apply_symm_apply] at hQe
      exact c.injective hQe
