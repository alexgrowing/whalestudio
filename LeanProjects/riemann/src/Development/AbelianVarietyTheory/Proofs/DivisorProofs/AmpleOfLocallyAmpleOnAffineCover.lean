import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRingHom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmpleOfLocalAffineCover

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.BdDim.GenCover
open TopologicalSpace ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.LBGerm GlobalTheory.AmpleOverBase
variable {X Y : Scheme.{0}}

theorem exists_sec_of_pull [CompactSpace X] [QuasiSeparatedSpace X] {L : LB X} (hL : L.IsLB) (f : Y ⟶ X)
    [IsOpenImmersion f] (r : Γ(X, ⊤)) (hr : X.basicOpen r = f.opensRange) {n : ℕ} (t : (lbPow (L.pull f) n).Sec)
    (y : Y) (hty : y ∈ nonzeroLocus t) : ∃ s : (lbPow L n).Sec, f y ∈ nonzeroLocus s := by
  have hs₀ : nonzeroLocus (secOfFn L r) = f.opensRange := (nonzeroLocus_secOfFn hL r).trans hr
  obtain ⟨T, hT, hTu⟩ := exists_push f (nonzeroLocus (secOfFn L r)) hs₀ t
  obtain ⟨N, hN⟩ := exists_sec_eq_pow_mul hL (secOfFn L r) T hT
  obtain ⟨u, hu⟩ := hN N le_rfl
  have key : ∀ (y' : Y) (J : PUnit → L.ι), f y' ∈ powChart L J →
      (f y' ∈ nonzeroLocus u ↔ y' ∈ nonzeroLocus t) := fun y' J hJ => by
    have hs : f y' ∈ nonzeroLocus (secOfFn L r) := hs₀ ▸ ⟨y', rfl⟩
    have hy : f y' ∈ nonzeroLocus (secOfFn L r) ⊓ powChart L J := ⟨hs, hJ⟩
    have e := congrArg (gs (𝟙 X) (f y') _) (hu J)
    rw [gs_res (𝟙 X) (f y') _ hy, gs_mul (𝟙 X) (f y') _ hy, gs_pow (𝟙 X) (f y') _ hy, gs_res (𝟙 X) (f y') _ hy] at e
    rw [mem_nonzeroLocus_iff_powFn u hJ, e, IsUnit.mul_iff, hTu y' J hJ]
    exact and_iff_right (((mem_nonzeroLocus_iff_powFn _ hJ).1 hs).pow N)
  obtain ⟨i, hi⟩ := exists_chart hL (f y)
  refine ⟨secCast (by omega) u, ?_⟩
  rw [nonzeroLocus_secCast]
  exact (key y (fun _ => i) (mem_powChart.2 hi)).2 hty

theorem exists_isGenerated_pow_of_basicOpen_cover : ∀ (X : Scheme.{0}) (O : Type) [CommRing O] (I : Type) [Finite I]
    (Y : I → Scheme.{0}) (s : X ⟶ Sp O) (u : ∀ i, Y i ⟶ X) (a : I → O) (L : LB X),
    CompactSpace X → QuasiSeparatedSpace X → L.IsLB → Ideal.span (Set.range a) = ⊤ →
    (∀ i, IsOpenImmersion (u i)) → (∀ i, Set.range (u i) = s ⁻¹' {x : Sp O | a i ∉ x.asIdeal}) →
    (∀ i, ∃ N : ℕ, 0 < N ∧ IsGenerated (lbPow (L.pull (u i)) N)) → ∃ m : ℕ, 0 < m ∧ IsGenerated (lbPow L m) := by
  intro X O _ I _ Y s u a L hX hXs hL hspan hu hrange hgen
  have hc : ∀ x : X, ∃ i y, u i y = x := fun x => by
    have : ∃ i, a i ∉ (s x).asIdeal := by
      by_contra hne
      push Not at hne
      apply (s x).isPrime.ne_top
      rw [eq_top_iff, ← hspan]
      exact Ideal.span_le.2 (Set.range_subset_iff.2 hne)
    obtain ⟨i, hi⟩ := this
    have hx : x ∈ Set.range (u i) := by
      rw [hrange i]
      exact hi
    obtain ⟨y, hy⟩ := hx
    exact ⟨i, y, hy⟩
  have hpt : ∀ x : X, ∃ n, 1 ≤ n ∧ ∃ σ : (lbPow L n).Sec, x ∈ nonzeroLocus σ := fun x => by
    obtain ⟨i, y, rfl⟩ := hc x
    have hr : X.basicOpen ((s.appTop) ((Scheme.ΓSpecIso (CommRingCat.of O)).inv (a i))) = (u i).opensRange := by
      apply SetLike.coe_injective
      rw [basicOpen_eq O s (a i), ← hrange i]
      rfl
    obtain ⟨N, hN, hg⟩ := hgen i
    obtain ⟨t, ht⟩ := hg.exists_mem y
    exact ⟨N, hN, exists_sec_of_pull hL (u i) _ hr t y ht⟩
  choose n hn σ hσ using hpt
  obtain ⟨T, hT⟩ := exists_finset_iSup_eq_top (fun x => nonzeroLocus (σ x)) hσ
  obtain ⟨N, hN, t, ht⟩ := exists_common_pow (fun x : T => n x) (fun x => hn x) (fun x => σ x)
  exact ⟨N, hN, isGenerated_of_finite t ((iSup_congr ht).trans hT)⟩

end GlobalTheory.BdDim.GenCover

end
