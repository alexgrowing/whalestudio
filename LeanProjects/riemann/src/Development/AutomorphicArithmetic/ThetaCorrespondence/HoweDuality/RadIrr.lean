import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.FactorApply
import Development.WeilBound.ThetaLifts.SphericalLattices.ThetaSubSup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelInfAlt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsGaussianTransform
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsOrbitKernel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsGaussianIdentity

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open UpperTheory.Lit.HoweDuality GlobalTheory.HoweGlobalPair

theorem UpperTheory.Lit.HoweDuality.radIrr :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {om : Rep σ X W} {v : Pl F} {ω : UA σ X.J × UA σ W.J → Module.End ℂ (PositivityTheory.ThK.Fn F n d v)} {ρ : Matrix (Fin n) (Fin d) (AE F E) → Module.End ℂ (PositivityTheory.ThK.Fn F n d v)}, PositivityTheory.ThK.IsLocRep M ψ om v ω ρ → PositivityTheory.Sph.IrrAt om v → ∀ K : Submodule ℂ ↥(SB (Fin n × Fin d → Fv F v)), relFin om v ≤ K → Stable (opFin om v) K → K ≠ ⊤ → Rad (opFin om v) (relFin om v) K := by
  intro F E _ _ _ _ _ σ n d X W M ψ om v ω ρ hL hI K hrel hst hne
  have one_mem : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := by
    show At _ (mat 1 - 1)
    have h1 : mat (1 : UA σ X.J) = 1 := Matrix.ext fun i => congrFun rfl
    rw [h1, sub_self]
    intro _ _
    simp
  have aug_le : augAt om v ≤ SB (Fin n × Fin d → Fv F v) := by
    refine Submodule.span_le.mpr ?_
    rintro z ⟨g, -, φ, hφ, φ₁, hφ₁, -, rfl⟩
    exact Submodule.sub_mem _ hφ₁ hφ
  have key : ∀ P : Submodule ℂ ↥(SB (Fin n × Fin d → Fv F v)), relFin om v ≤ P →
      Stable (opFin om v) P → P = relFin om v ∨ P = ⊤ := by
    intro P hP hPs
    have hT : GlobalTheory.Published.ThetaSub om v (P.map (SB (Fin n × Fin d → Fv F v)).subtype) := by
      refine ⟨?_, ?_, ?_⟩
      · intro z hz
        have hzS := aug_le hz
        refine ⟨⟨z, hzS⟩, hP ?_, rfl⟩
        simpa [relFin] using hz
      · rintro _ ⟨k, -, rfl⟩
        exact k.2
      · rintro h hh _ ⟨k, hk, rfl⟩ φ₁ hφ₁ hA
        have hφ₁eq : φ₁ = ω (1, h) k := (hL.acts 1 one_mem h hh k k.2 φ₁).mp hA
        let g : Module.End ℂ ↥(SB (Fin n × Fin d → Fv F v)) :=
          { toFun := fun x => ⟨ω (1, h) x, hL.pres 1 one_mem h hh x x.2⟩
            map_add' := fun x y => by ext1; simp
            map_smul' := fun c x => by ext1; simp }
        have hg : g ∈ opFin om v := by
          refine ⟨h, hh, fun φ => ?_⟩
          exact (hL.acts 1 one_mem h hh φ φ.2 _).mpr rfl
        refine ⟨g k, hPs g hg k hk, ?_⟩
        simp [g, hφ₁eq]
    rcases hI _ hT with h1 | h1
    · left
      ext x
      constructor
      · intro hx
        have hx' : (x : (Fin n × Fin d → Fv F v) → ℂ) ∈ augAt om v := by
          rw [← h1]
          exact ⟨x, hx, rfl⟩
        simpa [relFin] using hx'
      · intro hx
        exact hP hx
    · right
      rw [eq_top_iff]
      intro x _
      have hx' : (x : (Fin n × Fin d → Fv F v) → ℂ) ∈ P.map (SB (Fin n × Fin d → Fv F v)).subtype := by
        rw [h1]
        exact x.2
      obtain ⟨y, hy, hyx⟩ := hx'
      have hyx' : y = x := Subtype.ext hyx
      rw [← hyx']
      exact hy
  have hK : K = relFin om v := by
    rcases key K hrel hst with h | h
    · exact h
    · exact absurd h hne
  obtain ⟨s, hs⟩ : ∃ s, s ∉ relFin om v := by
    by_contra hc
    push_neg at hc
    apply hne
    rw [hK, eq_top_iff]
    intro x _
    exact hc x
  refine ⟨s, ?_, ?_⟩
  · intro P hP hPs hsP
    rcases key P hP hPs with h | h
    · rw [h] at hsP
      exact absurd hsP hs
    · exact h
  · intro k hk
    refine ⟨1, Subalgebra.one_mem _, rfl, ?_⟩
    rw [hK] at hk
    simpa using hk
