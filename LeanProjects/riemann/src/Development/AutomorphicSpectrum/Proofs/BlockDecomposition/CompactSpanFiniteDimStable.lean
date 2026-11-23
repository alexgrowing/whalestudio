import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmMemArchSmooth
import Development.AutomorphicSpectrum.Proofs.HermitianForms.CasOfCapelliVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmegaOpCommLiB
set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

noncomputable section

namespace GlobalTheory.CompanionTheory.HCRep

open AutomorphicForm GlobalTheory.CompanionTheory.ArchSmooth

theorem exists_skew_curve {E : Type} [Field E] [NumberField E] {a : ℕ} (S : Matrix (Fin a) (Fin a) (Cinf E)) :
    ∃ c : ℝ → GL (Fin a) (Cinf E), c 0 = 1 ∧ HasDerivAt (fun t => toL (c t).val) (toL S) 0 ∧
      (S.conjTranspose = -S → ∀ t, (c t).val ∈ Matrix.unitaryGroup (Fin a) (Cinf E)) := by
  refine ⟨fun t => (Matrix.isUnit_exp (t • S)).unit, Units.ext (by simp), ?_, fun hS t => ?_⟩
  · open scoped Matrix.Norms.Operator in
    have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) S (0 : ℝ)
    rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
    exact h
  · rw [IsUnit.unit_spec, Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose,
      Matrix.conjTranspose_smul, hS, star_trivial, smul_neg,
      ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • S)).neg_left, neg_add_cancel, NormedSpace.exp_zero]

theorem liB_skew_mem_span : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a)
    (Z : (AutomorphicForm.isExpLieAlgebra E a).lieSubalgebra),
    Matrix.conjTranspose (AutomorphicForm.mat (Z : AutomorphicForm.ArchMatrix E a)) =
      -AutomorphicForm.mat (Z : AutomorphicForm.ArchMatrix E a) →
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)) →
    ∀ ψ ∈ Submodule.span ℂ (Set.range fun k => cptRep E a k φ),
      GlobalTheory.CompanionTheory.HCRep.liB Z ψ ∈ Submodule.span ℂ (Set.range fun k => cptRep E a k φ) := by
  intro E _ _ _ a φ Z hZ hfd ψ hψ
  set W := Submodule.span ℂ (Set.range fun k => cptRep E a k φ) with hW
  have hst : ∀ k : Kinf E a, ∀ w ∈ W, cptRep E a k w ∈ W := by
    intro k w hw
    refine Submodule.span_induction (p := fun w _ => cptRep E a k w ∈ W) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨k', rfl⟩
      refine Submodule.subset_span ⟨k * k', ?_⟩
      change cptRep E a (k * k') φ = cptRep E a k (cptRep E a k' φ)
      rw [map_mul, Module.End.mul_apply]
    · rw [map_zero]; exact W.zero_mem
    · intro x y _ _ hx hy; rw [map_add]; exact W.add_mem hx hy
    · intro r x _ hx; rw [map_smul]; exact W.smul_mem r hx
  let S : Matrix (Fin a) (Fin a) (Cinf E) := Matrix.of (mMap E a (Z : ArchMatrix E a))
  have hS : S.conjTranspose = -S := by
    ext i j w
    have h := congrFun (congrFun hZ i) j
    have h2 := congrFun (congrArg Prod.snd h) ⟨w, IsTotallyComplex.isComplex w⟩
    exact h2
  obtain ⟨c, h0, hc, hu⟩ := exists_skew_curve S
  let W' : Submodule ℂ (GA E a → ℂ) := W.map (Sm E a).subtype
  have hW' : FiniteDimensional ℂ W' := inferInstance
  have hF : ∀ t, (fun g => ψ.1 (g * infGL E a (c t))) ∈ W' := fun t =>
    ⟨cptRep E a ⟨(c t).val, hu hS t⟩ ψ, hst _ _ hψ, funext fun g => by
      have e : Unitary.toUnits (⟨(c t).val, hu hS t⟩ : Kinf E a) = c t := Units.ext rfl
      change ψ.1 (g * infGL E a (Unitary.toUnits _)) = _
      rw [e]⟩
  have hd : ∀ g : GA E a, HasDerivAt (fun t : ℝ => ψ.1 (g * infGL E a (c t))) ((liB Z ψ).1 g) 0 :=
    fun g => hasDerivAt_curve ψ g c (toL S) h0 hc
  obtain ⟨w, hw, e⟩ := AutomorphicForm.mem_of_hasDerivAt W' hF hd
  rwa [show liB Z ψ = w from Subtype.ext e.symm]

end GlobalTheory.CompanionTheory.HCRep

end
