import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicConjMaxCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFiniteTranslate
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU

theorem GlobalTheory.StdPar.isCuspOn_transl_compact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)) (K : Subgroup (GAd σ J)), K ≤ infPts σ J →
      ∀ ψ : GAd σ J → ℂ, GlobalTheory.StdPar.IsCuspOn σ J X Y S K ψ → ∀ C : Subgroup (GAd σ J), IsCompact (C : Set (GAd σ J)) →
        (∀ y ∈ C, ofInf σ J (projInf σ J y) ∈ K) →
        (∀ y ∈ C, GlobalTheory.StdPar.IsCuspOn σ J X Y S K (fun g => ψ (g * y))) ∧
          FiniteDimensional ℂ (Submodule.span ℂ {f : GAd σ J → ℂ | ∃ y ∈ C, f = fun g => ψ (g * y)}) := by
  intro F E _ _ _ _ _ σ hCM n J hJ r X Y hW S K hK ψ hψ C hC hCK
  have hfin : ∀ y : GAd σ J, ofFin σ J (projFin σ J y) ∈ finPts σ J := fun y =>
    (range_ofFin σ J).le ⟨_, rfl⟩
  refine ⟨fun y hy => ?_, ?_⟩
  · have h1 : GlobalTheory.StdPar.IsCuspOn σ J X Y S K (fun g => ψ (g * ofFin σ J (projFin σ J y))) :=
      ⟨GlobalTheory.StdPar.isAutOn_mul_finPts hCM hJ hW hK hψ.1 _ (hfin y), fun S' hS' μ 𝓕 h1 h2 h3 g => by
        have := hψ.2 S' hS' μ 𝓕 h1 h2 h3 (g * ofFin σ J (projFin σ J y))
        simpa only [mul_assoc, Pi.zero_apply] using this⟩
    have hk := hCK y hy
    have h2 := GlobalTheory.StdPar.RealConj.isCuspOn_realConj (K₁ := K) (K₂ := K) hCM (hK hk)
      (fun k => ⟨fun h => mul_mem (mul_mem hk h) (inv_mem hk), fun h => by
        have := mul_mem (mul_mem (inv_mem hk) h) hk
        simpa [mul_assoc] using this⟩) h1
    simpa only [mul_assoc, ofInf_projInf_mul_ofFin_projFin] using h2
  · obtain ⟨U, hU, hUψ⟩ := hψ.1.level
    have := hψ.1.kfin
    let V : GAd σ J → Set (GAd σ J) := fun x => {y | ofFin σ J (projFin σ J (x⁻¹ * y)) ∈ U}
    have hV : ∀ x ∈ (C : Set (GAd σ J)), V x ∈ 𝓝 x := fun x _ => by
      refine IsOpen.mem_nhds (hU.preimage ((continuous_ofFin σ J).comp ((continuous_projFin σ J).comp
        (continuous_const.mul continuous_id)))) ?_
      show ofFin σ J (projFin σ J (x⁻¹ * x)) ∈ U
      simp [one_mem]
    obtain ⟨t, htC, ht⟩ := hC.elim_nhds_subcover V hV
    refine Submodule.finiteDimensional_of_le
      (S₂ := t.sup fun x => (Submodule.span ℂ (Set.range fun k : K => fun g => ψ (g * k))).map
        (LinearMap.funLeft ℂ ℂ (fun y : GAd σ J => y * x)))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (ht hy)
    have hu : x⁻¹ * y ∈ C := mul_mem (inv_mem (htC x hx)) hy
    refine (Finset.le_sup (f := fun x => (Submodule.span ℂ (Set.range fun k : K => fun g => ψ (g * k))).map
        (LinearMap.funLeft ℂ ℂ (fun y : GAd σ J => y * x))) hx) ?_
    refine ⟨fun g => ψ (g * ofInf σ J (projInf σ J (x⁻¹ * y))), Submodule.subset_span ⟨⟨_, hCK _ hu⟩, rfl⟩, ?_⟩
    funext g
    simp only [LinearMap.funLeft_apply, Function.comp]
    rw [← hUψ _ hyx (hfin _) (g * x * ofInf σ J (projInf σ J (x⁻¹ * y))), mul_assoc (g * x),
      ofInf_projInf_mul_ofFin_projFin]
    simp [mul_assoc]
