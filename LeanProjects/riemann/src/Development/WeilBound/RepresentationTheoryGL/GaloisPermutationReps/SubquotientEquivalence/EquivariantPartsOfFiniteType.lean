import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.IsTypeMap

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.DzCount

lemma pow_pow_pow_add (z : ℂ) (q a b : ℕ) : (z ^ q ^ a) ^ q ^ b = z ^ q ^ (a + b) := by
  rw [← pow_mul, ← pow_add]

lemma eigenvector_maps_power {V : Type} [AddCommGroup V] [Module ℂ V] (q : ℕ) (M G : Module.End ℂ V)
    (hMG : M * G = G * M ^ q) (z : ℂ) (v : V) (hv : M v = z • v) : M (G v) = z ^ q • G v := by
  have hpow : ∀ k : ℕ, (M ^ k) v = z ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hv, smul_smul, pow_succ]
  have h := congrArg (fun T : Module.End ℂ V => T v) hMG
  simp only [Module.End.mul_apply] at h
  rw [h, hpow, map_smul]

lemma eigenvector_iterate_power {V : Type} [AddCommGroup V] [Module ℂ V] (q : ℕ) (M G : Module.End ℂ V)
    (hMG : M * G = G * M ^ q) (z : ℂ) (v : V) (hv : M v = z • v) :
    ∀ i : ℕ, M ((G ^ i) v) = z ^ q ^ i • (G ^ i) v := by
  intro i
  induction i with
  | zero => simpa using hv
  | succ i ih =>
    rw [pow_succ', Module.End.mul_apply, eigenvector_maps_power q M G hMG _ _ ih, ← pow_mul, ← pow_succ]

theorem st1a : St1a := by
  classical
  intro V _ _ _ q M G hM hG hMG hirr
  obtain ⟨hnt, hU⟩ := hirr
  have hGinj : ∀ i : ℕ, Function.Injective (G ^ i) := fun i =>
    ((Module.End.isUnit_iff _).mp (hG.pow i)).1
  have hMinj : Function.Injective M := ((Module.End.isUnit_iff _).mp hM).1
  have hfin : Set.Finite {μ | M.HasEigenvalue μ} := M.finite_hasEigenvalue
  have hstep : ∀ μ, M.HasEigenvalue μ → M.HasEigenvalue (μ ^ q) := by
    intro μ hμ
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    have hv' : M v = μ • v := Module.End.mem_eigenspace_iff.mp hv.1
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := G v) ⟨?_, ?_⟩
    · exact Module.End.mem_eigenspace_iff.mpr (eigenvector_maps_power q M G hMG μ v hv')
    · intro h0
      apply hv.2
      have h1 := hGinj 1
      rw [pow_one] at h1
      exact h1 (by rw [h0, map_zero])
  obtain ⟨z0, hz0⟩ := M.exists_eigenvalue
  have hall : ∀ i : ℕ, M.HasEigenvalue (z0 ^ q ^ i) := by
    intro i
    induction i with
    | zero => simpa using hz0
    | succ i ih =>
      have h := hstep _ ih
      rwa [← pow_mul, ← pow_succ] at h
  obtain ⟨a, b, hab, heq⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem
    (f := fun i : ℕ => z0 ^ q ^ i) (t := {μ | M.HasEigenvalue μ}) (fun i => hall i) hfin
  have hzE : M.HasEigenvalue (z0 ^ q ^ a) := hall a
  have hper : (z0 ^ q ^ a) ^ q ^ (b - a) = z0 ^ q ^ a := by
    rw [pow_pow_pow_add, show a + (b - a) = b by omega, ← heq]
  generalize z0 ^ q ^ a = z at hzE hper
  have hP : ∃ e : ℕ, 0 < e ∧ z ^ q ^ e = z := ⟨b - a, by omega, hper⟩
  obtain ⟨d, ⟨hd0, hzd⟩, hdmin⟩ : ∃ d : ℕ, (0 < d ∧ z ^ q ^ d = z) ∧
      ∀ e < d, ¬ (0 < e ∧ z ^ q ^ e = z) :=
    ⟨Nat.find hP, Nat.find_spec hP, fun e he => Nat.find_min hP he⟩

  have hmaps : ∀ x ∈ M.eigenspace z, (G ^ d) x ∈ M.eigenspace z := by
    intro x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    rw [eigenvector_iterate_power q M G hMG z x hx d, hzd]
  have hne : M.eigenspace z ≠ ⊥ := hzE
  have : Nontrivial (M.eigenspace z) := Submodule.nontrivial_iff_ne_bot.mpr hne
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (LinearMap.restrict (G ^ d) hmaps)
  obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
  have hw1 : LinearMap.restrict (G ^ d) hmaps w = μ • w := Module.End.mem_eigenspace_iff.mp hw.1
  set v : V := (w : V) with hv_def
  have hGd : (G ^ d) v = μ • v := by
    have h := congrArg Subtype.val hw1
    simpa [LinearMap.restrict_apply] using h
  have hvE : M v = z • v := Module.End.mem_eigenspace_iff.mp w.2
  have hv0 : v ≠ 0 := by
    intro h
    apply hw.2
    exact Subtype.ext h

  let bb : Fin d → V := fun i => (G ^ (i : ℕ)) v
  have hb_eig : ∀ i : Fin d, M (bb i) = z ^ q ^ (i : ℕ) • bb i := fun i =>
    eigenvector_iterate_power q M G hMG z v hvE i
  have hb_ne : ∀ i : Fin d, bb i ≠ 0 := by
    intro i h
    apply hv0
    exact hGinj i (by rw [map_zero]; exact h)
  have key : ∀ i j : ℕ, i < j → j < d → z ^ q ^ i = z ^ q ^ j → False := by
    intro i j hij hjd hij'
    have h1 : z ^ q ^ (j - i) = z := by
      calc z ^ q ^ (j - i) = (z ^ q ^ d) ^ q ^ (j - i) := by rw [hzd]
        _ = (z ^ q ^ j) ^ q ^ (d - i) := by
          rw [pow_pow_pow_add, pow_pow_pow_add, show j + (d - i) = d + (j - i) by omega]
        _ = (z ^ q ^ i) ^ q ^ (d - i) := by rw [hij']
        _ = z ^ q ^ d := by rw [pow_pow_pow_add, show i + (d - i) = d by omega]
        _ = z := hzd
    exact hdmin (j - i) (by omega) ⟨by omega, h1⟩
  have hinj : Function.Injective (fun i : Fin d => z ^ q ^ (i : ℕ)) := by
    intro i j hij
    simp only at hij
    rcases lt_trichotomy (i : ℕ) (j : ℕ) with h | h | h
    · exact (key i j h j.2 hij).elim
    · exact Fin.ext h
    · exact (key j i h i.2 hij.symm).elim
  have hli : LinearIndependent ℂ bb :=
    Module.End.eigenvectors_linearIndependent' M (fun i : Fin d => z ^ q ^ (i : ℕ)) hinj bb
      (fun i => ⟨Module.End.mem_eigenspace_iff.mpr (hb_eig i), hb_ne i⟩)
  set W : Submodule ℂ V := Submodule.span ℂ (Set.range bb) with hW_def
  have hvW : v ∈ W := Submodule.subset_span ⟨⟨0, hd0⟩, by simp [bb]⟩
  have hMW : ∀ x ∈ W, M x ∈ W := by
    have hle : W ≤ W.comap M := by
      rw [hW_def, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, hb_eig i]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    exact fun x hx => hle hx
  have hGW : ∀ x ∈ W, G x ∈ W := by
    have hle : W ≤ W.comap G := by
      rw [hW_def, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      show G ((G ^ (i : ℕ)) v) ∈ W
      rw [← Module.End.mul_apply, ← pow_succ']
      by_cases h : (i : ℕ) + 1 < d
      · exact Submodule.subset_span ⟨⟨(i : ℕ) + 1, h⟩, rfl⟩
      · rw [show (i : ℕ) + 1 = d by omega, hGd]
        exact Submodule.smul_mem _ _ hvW
    exact fun x hx => hle hx
  have hWtop : W = ⊤ := by
    rcases hU W hMW hGW with h | h
    · exfalso
      apply hv0
      have := hvW
      rw [h] at this
      exact (Submodule.mem_bot ℂ).mp this
    · exact h
  have hfr : Module.finrank ℂ V = d := by
    have h := finrank_span_eq_card hli
    rw [← hW_def, hWtop, finrank_top, Fintype.card_fin] at h
    exact h
  refine ⟨z, hzE, ?_⟩
  rw [hfr]
  refine ⟨?_, hzd, fun e he0 hed h => hdmin e hed ⟨he0, h⟩⟩
  intro hz
  apply hv0
  apply hMinj
  rw [hvE, hz, zero_smul, map_zero]

end PositivityTheory.Rg.DzCount

end
