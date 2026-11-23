import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.VanishKato

theorem tw_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (a b : Γ →* kˣ) :
    tw (tw r a) b = tw r (b * a) := by
  ext1 s
  apply Units.ext
  simp only [tw_val, smul_smul, MonoidHom.mul_apply, Units.val_mul]

theorem cont_of_ker {Γ H : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] (f : Γ →* H) (U : Set Γ) (hU : IsOpen U) (h1 : 1 ∈ U)
    (h : ∀ s ∈ U, f s = 1) : Continuous f := by
  refine continuous_of_continuousAt_one f ?_
  refine (continuousAt_const (y := (1 : H))).congr ?_
  filter_upwards [hU.mem_nhds h1] with s hs
  exact (h s hs).symm

theorem cont_kills {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (M : ℕ) (hM : 1 ≤ M) (φ : G ℚ Ω →* (Qbar l)ˣ) (hφ : KillsMu M φ) : Continuous φ := by
  have hfin : {ζ : Ω | ζ ^ M = 1}.Finite := by
    classical
    refine (Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_
    simpa [Polynomial.mem_nthRoots hM] using hζ
  refine cont_of_ker φ (⋂ ζ ∈ {ζ : Ω | ζ ^ M = 1}, (MulAction.stabilizer (Ω ≃ₐ[ℚ] Ω) ζ : Set (Ω ≃ₐ[ℚ] Ω)))
    (hfin.isOpen_biInter fun ζ _ => stabilizer_isOpen_of_isIntegral ζ) ?_ ?_
  · simp only [Set.mem_iInter]
    exact fun ζ _ => Subgroup.one_mem _
  · intro s hs
    simp only [Set.mem_iInter] at hs
    exact hφ s fun ζ hζ => hs ζ hζ

end GlobalTheory.Ord2.VanishKato

namespace GlobalTheory.Ord2

end GlobalTheory.Ord2

end
