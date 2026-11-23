import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.testOp_pf :
    UpperTheory.Gal.Gen.GlobOp → UpperTheory.Gal.Gen.SymEx → UpperTheory.Gal.Gen.SatEx → UpperTheory.Gal.Gen.TestOp := by
  intro hG hS hX E _ _ _ a K w hw hK Φ
  obtain ⟨p, hp, hpe, -⟩ := hS a Φ
  obtain ⟨C, hC⟩ := hG E a K w hw hK
  obtain ⟨f, hloc, -, -, hact⟩ := hC p hp
  classical
  obtain ⟨η, hη⟩ : ∃ η : Submodule ℂ (UA E a → ℂ) → ℂ,
      ∀ U (h : ∃ z, SatAt U w z), η U = evalAt h.choose p :=
    ⟨fun U => if h : ∃ z, SatAt U w z then evalAt h.choose p else 0, fun U h => dif_pos h⟩
  refine ⟨f, η, fun g hg => (Subgroup.mem_inf.1 (hloc g hg)).1, fun U hU => ⟨?_, ?_⟩⟩
  · intro φ hφ hfix
    by_cases h0 : φ = 0
    · subst h0
      simp [opOf]
    · have hz := hX E a K w hw hK U hU ⟨φ, hφ, h0, hfix⟩
      rw [hη U hz]
      exact hact U hU _ hz.choose_spec φ hφ hfix
  · rintro ⟨φ, hφ, h0, hfix⟩
    have hz := hX E a K w hw hK U hU ⟨φ, hφ, h0, hfix⟩
    have key : ∀ z, SatAt U w z → evalAt z p = η U := by
      intro z hzz
      have h1 := hact U hU z hzz φ hφ hfix
      have h2 := hact U hU _ hz.choose_spec φ hφ hfix
      rw [hη U hz]
      exact smul_left_injective ℂ h0 (h1.symm.trans h2)
    constructor
    · intro hne z hzz
      rw [← key z hzz, hpe z] at hne
      simpa using Finset.prod_ne_zero_iff.1 hne 1 (Finset.mem_univ _)
    · intro hgen
      obtain ⟨z, hzz⟩ := hz
      rw [← key z hzz, hpe z]
      refine Finset.prod_ne_zero_iff.2 fun σ _ => ?_
      have hs : SatAt U w (z ∘ σ) := by
        obtain ⟨τ, h1, h2⟩ := hzz
        refine ⟨τ, h1, ?_⟩
        have hm : Finset.univ.val.map (z ∘ σ) = Finset.univ.val.map z := by
          rw [← Multiset.map_map, Multiset.map_univ_val_equiv]
        rw [hm]
        exact h2
      exact hgen _ hs
