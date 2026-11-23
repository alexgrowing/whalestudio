import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL

noncomputable section

namespace GlobalTheory.ChainOnto.SatHeckeChar

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun

theorem heckeVec_eq_smul_of_isSatVecGL :
    ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (B : Multiset ℂˣ),
      ∀ φ ∈ Hecke ℂ (KGL w n), ∃ z : ℂ, ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
        (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (x : V),
          IsSatVecGL w ρ x B → heckeVec ρ (KGL w n) φ x = z • x := by
  intro E _ _ w n B φ hφ
  by_cases hB : B.card = n
  · obtain ⟨α, rfl⟩ : ∃ α : Fin n → ℂˣ, Finset.univ.val.map α = B := by
      obtain ⟨l, rfl⟩ := Quot.exists_rep B
      obtain rfl : l.length = n := hB
      exact ⟨l.get, by rw [Fin.univ_val_map, List.ofFn_get]; rfl⟩
    obtain ⟨x₀, hx₀⟩ := (hasSatGL_psFunGL (w := w) α).exists_vec
    obtain ⟨z, hz, -⟩ := SatCompare.exists_eigenvalue_GL hx₀ hx₀ φ hφ
    refine ⟨z, fun V _ _ ρ x hx => ?_⟩
    obtain ⟨c, e1, e2⟩ := SatCompare.exists_eigenvalue_GL hx₀ hx φ hφ
    have e : z = c := smul_left_injective ℂ hx₀.1 (hz.symm.trans e1)
    rw [e2, e]
  · exact ⟨0, fun V _ _ ρ x hx => absurd hx.2.2.1 hB⟩

end GlobalTheory.ChainOnto.SatHeckeChar

end
