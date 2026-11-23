import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.mem_maximalCompact_and_congruent_of_mem_principalCongruence :
    ∀ (F : Type) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (n M : ℕ), ∀ g ∈ UpperTheory.V.Af.KLoc F w n M,
    g ∈ GlobalTheory.SplitWeil.KO (w.adicCompletion F) (Fin n) ∧
    ∀ i j, valuation (w.adicCompletion F) ((g.val - 1) i j) ≤ valuation (w.adicCompletion F) (M : w.adicCompletion F) := by
  intro F _ _ w n M g hg
  obtain ⟨k, hk, hkg⟩ := hg
  haveI : (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have hint : ∀ x : UpperTheory.V.Af.Ohat F,
      valuation (w.adicCompletion F) (GlobalTheory.CuspRep.pLoc F w x.1) ≤ 1 := fun x => by
    have h1 : Valued.v (GlobalTheory.CuspRep.pLoc F w x.1) ≤ 1 := Subring.mem_iInf.1 x.2 w
    rw [← map_one (valuation (w.adicCompletion F)), ← Valuation.Compatible.vle_iff_le,
      Valuation.Compatible.vle_iff_le
        (v := (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ)))), map_one]
    exact h1
  let φ : UpperTheory.V.Af.Ohat F →+* w.adicCompletion F := (GlobalTheory.CuspRep.pLoc F w).comp (UpperTheory.V.Af.Ohat F).subtype
  let ψ : UpperTheory.V.Af.Ohat F →+* 𝒪[w.adicCompletion F] := φ.codRestrict _ fun x => hint x
  have hent : ∀ i j, g.val i j = φ (k.val i j) := fun i j => by
    have h1 := GlobalTheory.CuspRep.pLoc_locGL w g
    rw [← hkg] at h1
    rw [← h1]
    rfl
  refine ⟨⟨Matrix.GeneralLinearGroup.map ψ k, ?_⟩, fun i j => ?_⟩
  · ext i j
    rw [hent]
    rfl
  · have h1 : Ideal.Quotient.mk (Ideal.span {(M : UpperTheory.V.Af.Ohat F)}) (k.val i j) =
        (1 : Matrix (Fin n) (Fin n) _) i j :=
      congrArg (fun u : GL (Fin n) (UpperTheory.V.Af.Ohat F ⧸ Ideal.span {(M : UpperTheory.V.Af.Ohat F)}) => u.val i j)
        (MonoidHom.mem_ker.1 hk)
    have h2 : (k.val - 1) i j ∈ Ideal.span {(M : UpperTheory.V.Af.Ohat F)} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, Matrix.sub_apply, map_sub, h1, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h2
    have h3 : (g.val - 1) i j = φ y * M := by
      rw [← map_natCast φ, ← map_mul, hy, Matrix.sub_apply, Matrix.sub_apply, map_sub, hent, Matrix.one_apply,
        Matrix.one_apply]
      split_ifs <;> simp
    rw [h3, map_mul]
    exact mul_le_of_le_one_left' (hint y)
