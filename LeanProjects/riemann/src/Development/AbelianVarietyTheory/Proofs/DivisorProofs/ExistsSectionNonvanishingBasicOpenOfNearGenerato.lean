import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleOfLocallyAmpleOnAffineCover
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqBasicOpen

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LBGerm GlobalTheory.AmpleOverBase

namespace GlobalTheory.GenNearExtend

theorem exists_sec_of_gen_near : ∀ (Z X : Scheme.{0}) (e : X ⟶ Z), IsOpenImmersion e → CompactSpace X →
    QuasiSeparatedSpace X → ∀ (M : LB Z), M.IsLB → ∀ (r : Γ(X, ⊤)) (O : Z.Opens),
    (∀ x ∈ X.basicOpen r, e x ∈ O) → ∀ t : LB.Gen (M.pull O.ι), t.IsGen →
    ∃ σ : LB.Sec (M.pull e), X.basicOpen r ≤ nonzeroLocus σ := by
  intro Z X e _ _ _ M hM r O hO t ht
  have hL : (M.pull e).IsLB := LB.isLB_pull hM e
  let f : (X.basicOpen r).toScheme ⟶ X := (X.basicOpen r).ι
  have hrange : Set.range (f ≫ e).base ⊆ Set.range O.ι.base := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hO _ y.2
  let ψ : (X.basicOpen r).toScheme ⟶ O.toScheme := IsOpenImmersion.lift O.ι (f ≫ e) hrange
  have hψ : ψ ≫ O.ι = f ≫ e := IsOpenImmersion.lift_fac _ _ _
  have hpt : ∀ y, O.ι (ψ y) = e (f y) := fun y => by
    rw [← Scheme.Hom.comp_apply, hψ, Scheme.Hom.comp_apply]
  let a : ChartPull (lbPow ((M.pull e).pull f) 1) (M.pull O.ι) ψ :=
    { idx := fun J _ => J PUnit.unit PUnit.unit PUnit.unit
      le := fun J y hy => by
        have h1 := mem_pull.1 (mem_pull.1 (mem_powChart.1 hy))
        show ψ y ∈ (M.pull O.ι).U _
        rw [mem_pull, hpt]
        exact h1
      g := fun y J J' hJ hJ' => by
        have h1 := mem_powChart.1 hJ
        have h2 := mem_powChart.1 hJ'
        have h1' : (𝟙 _ ≫ f) y ∈ (M.pull e).U (J PUnit.unit PUnit.unit) := mem_pull.1 h1
        have h2' : (𝟙 _ ≫ f) y ∈ (M.pull e).U (J' PUnit.unit PUnit.unit) := mem_pull.1 h2
        have h3 : ψ y ∈ (M.pull O.ι).U (fun _ => J PUnit.unit PUnit.unit PUnit.unit) := by
          rw [mem_pull, hpt]; exact mem_pull.1 (mem_pull.1 h1)
        have h4 : ψ y ∈ (M.pull O.ι).U (fun _ => J' PUnit.unit PUnit.unit PUnit.unit) := by
          rw [mem_pull, hpt]; exact mem_pull.1 (mem_pull.1 h2)
        refine (gm_lbPow_g 1 (𝟙 _) y J J' hJ hJ').trans ?_
        rw [pow_one, gm_pull_g ((M.pull e)) f (𝟙 _) y _ _ h1 h2, gm_pull_g M e (𝟙 _ ≫ f) y _ _ h1' h2',
          gm_pull_g M O.ι ψ y _ _ h3 h4, hψ, Category.id_comp] }
  let s0 : (M.pull O.ι).Sec := ⟨fun i => (t.s i).val, fun i j => congrArg Units.val (ht i j)⟩
  let t' := chartSec a s0
  have ht' : ∀ y, y ∈ nonzeroLocus t' := fun y => by
    obtain ⟨i, hi⟩ := exists_chart hM (e (f y))
    have hJ : y ∈ (lbPow ((M.pull e).pull f) 1).U (fun _ _ _ => i) :=
      mem_powChart.2 (mem_pull.2 (mem_pull.2 hi))
    rw [mem_nonzeroLocus_iff_isUnit t' hJ, gs_chartSec a s0 (𝟙 _) y _ hJ]
    have hm : (𝟙 _ ≫ ψ) y ∈ (M.pull O.ι).U (a.idx (fun _ _ _ => i)) := a.le _ hJ
    rw [gs_unit _ y _ hm]
    exact Units.isUnit _
  have hr : X.basicOpen r = f.opensRange := (Scheme.Opens.opensRange_ι _).symm
  have hs₀ : nonzeroLocus (secOfFn (M.pull e) r) = f.opensRange := (nonzeroLocus_secOfFn hL r).trans hr
  obtain ⟨T, hT, hTu⟩ := exists_push f (nonzeroLocus (secOfFn (M.pull e) r)) hs₀ t'
  obtain ⟨N, hN⟩ := exists_sec_eq_pow_mul hL (secOfFn (M.pull e) r) T hT
  obtain ⟨u, hu⟩ := hN N le_rfl
  have key : ∀ (y' : (X.basicOpen r).toScheme) (J : PUnit → (M.pull e).ι), f y' ∈ powChart (M.pull e) J →
      (f y' ∈ nonzeroLocus u ↔ y' ∈ nonzeroLocus t') := fun y' J hJ => by
    have hs : f y' ∈ nonzeroLocus (secOfFn (M.pull e) r) := hs₀ ▸ ⟨y', rfl⟩
    have hy : f y' ∈ nonzeroLocus (secOfFn (M.pull e) r) ⊓ powChart (M.pull e) J := ⟨hs, hJ⟩
    have e' := congrArg (gs (𝟙 X) (f y') _) (hu J)
    rw [gs_res (𝟙 X) (f y') _ hy, gs_mul (𝟙 X) (f y') _ hy, gs_pow (𝟙 X) (f y') _ hy,
      gs_res (𝟙 X) (f y') _ hy] at e'
    rw [mem_nonzeroLocus_iff_powFn u hJ, e', IsUnit.mul_iff, hTu y' J hJ]
    exact and_iff_right (((mem_nonzeroLocus_iff_powFn _ hJ).1 hs).pow N)
  refine ⟨secOfPowOne (secCast (by omega) u), ?_⟩
  rw [nonzeroLocus_secOfPowOne, nonzeroLocus_secCast]
  intro x hx
  obtain ⟨y, rfl⟩ : ∃ y, f y = x := ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨i, hi⟩ := exists_chart hL (f y)
  exact (key y (fun _ => i) (mem_powChart.2 hi)).2 (ht' y)

end GlobalTheory.GenNearExtend
