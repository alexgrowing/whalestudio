import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GenUIsGenFam
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

theorem PositivityTheory.Xgp.t_c_fm_exists_flags_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω Ω' : Type) [Field Ω] [Field Ω'] (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) (x : (Σ k, J k) → Ω) (x' : (Σ k, J' k) → Ω') (A : HodgeCpt Y S x) (A' : HodgeCpt Y S x') (h : A'.X ⟶ A.X) (i : Ω →+* Ω') (j : A.Li →+ A'.Li) (d : ℕ), HodgeOver A' A h i j → A.IsCover d → ∃ ι : A'.Ω₀ →+* Ω, i.comp ι = A'.fn ∧ GlobalTheory.CompanionTheory.Ar.Dominates A.ξ A'.ξ₀ A.f ι ∧ letI := ι.toAlgebra; Module.finrank A'.Ω₀ Ω = d := by
  intro E _ _ _ H D l Xo c Y S Ω Ω' _ _ K K' _ _ J J' x x' A A' h i j d hov hcov
  obtain ⟨hd, hf, -⟩ := hov
  have hgen : genPt A'.ξ₀ = genPt A.ξ₀ := by
    have h1 := RegAtDom.map_genPt hd
    have h2 := RegAtDom.map_genPt A.fn_over
    have h3 := RegAtDom.map_genPt A'.fn_over
    rw [← h2, ← h3, ← h1, hf]
    rfl
  obtain ⟨ψ, hψ⟩ := FlagPull.exists_iso A'.gen₀ A.gen₀ hgen
  have e1 : spMap A'.fn ≫ A'.ξ₀ = A'.ξ ≫ A'.f := A'.fn_over.symm
  have e2 : spMap A.fn ≫ A.ξ₀ = A.ξ ≫ A.f := A.fn_over.symm
  have e3 : A'.ξ ≫ h = spMap i ≫ A.ξ := hd
  have e5 : spMap (A.fn.comp ψ.toRingHom) ≫ A'.ξ₀ = A.ξ ≫ A.f := by
    rw [FlagPull.spMap_comp, Category.assoc, hψ, e2]
  refine ⟨A.fn.comp ψ.toRingHom, ?_, e5.symm, ?_⟩
  · haveI := FlagPull.mono_of_isCptGen A'.gen₀
    have e4 : spMap (i.comp (A.fn.comp ψ.toRingHom)) = spMap A'.fn := by
      refine (cancel_mono A'.ξ₀).1 ?_
      rw [FlagPull.spMap_comp, Category.assoc, e5, e1, hf, ← Category.assoc, ← e3, Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e4)
  · letI := A.fn.toAlgebra
    letI := (A.fn.comp ψ.toRingHom).toAlgebra
    exact (Algebra.finrank_eq_of_equiv_equiv ψ (RingEquiv.refl Ω) (RingHom.ext fun _ => rfl)).trans hcov.2
