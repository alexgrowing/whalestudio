import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjFsBasisOfUnitary
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace GlobalTheory.DivPullback

theorem vanishingIdeal_preimage {X S : Scheme.{0}} (f : X ⟶ S) [Smooth f] (C : Closeds S) (U : S.affineOpens)
    (t : Γ(S, U.1)) (ht : (Scheme.IdealSheafData.vanishingIdeal C).ideal U = Ideal.span {t}) (V : X.affineOpens)
    (e : V.1 ≤ f ⁻¹ᵁ U.1) :
    (Scheme.IdealSheafData.vanishingIdeal (C.preimage f.continuous)).ideal V = Ideal.span {f.appLE U.1 V.1 e t} := by
  have hU : IsAffineOpen U.1 := U.2
  have hV : IsAffineOpen V.1 := V.2
  have hC : hU.fromSpec ⁻¹' (C : Set S) = PrimeSpectrum.zeroLocus {t} := by
    rw [← PrimeSpectrum.zeroLocus_span, ← ht, Scheme.IdealSheafData.vanishingIdeal_ideal,
      PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    exact (C.isClosed.preimage hU.fromSpec.continuous).closure_eq.symm
  have hset : hV.fromSpec ⁻¹' ((C.preimage f.continuous : Closeds X) : Set X) =
      PrimeSpectrum.zeroLocus {f.appLE U.1 V.1 e t} := by
    ext q
    have h1 : f (hV.fromSpec q) = hU.fromSpec (Spec.map (f.appLE U.1 V.1 e) q) := by
      rw [← Scheme.Hom.comp_apply, ← IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e, Scheme.Hom.comp_apply]
    change f (hV.fromSpec q) ∈ (C : Set S) ↔ _
    rw [h1, ← Set.mem_preimage, hC]
    refine Set.singleton_subset_iff.trans (Iff.trans ?_ Set.singleton_subset_iff.symm)
    exact Iff.rfl
  have hrad : (Ideal.span {f.appLE U.1 V.1 e t}).IsRadical := by
    have h0 : (Ideal.span {t}).IsRadical := by
      rw [← ht, Scheme.IdealSheafData.vanishingIdeal_ideal]
      exact PrimeSpectrum.isRadical_vanishingIdeal _
    have hs := f.smooth_appLE hU hV e
    algebraize [(f.appLE U.1 V.1 e).hom]
    have : _root_.IsReduced (Γ(S, U.1) ⧸ Ideal.span {t}) := (Ideal.isRadical_iff_quotient_reduced _).1 h0
    have : _root_.IsReduced (TensorProduct Γ(S, U.1) (Γ(S, U.1) ⧸ Ideal.span {t}) Γ(X, V.1)) :=
      GlobalTheory.isReduced_algebra_of_smooth_of_isReduced (Γ(S, U.1) ⧸ Ideal.span {t}) _
    have e1 : Ideal.map (algebraMap Γ(S, U.1) Γ(X, V.1)) (Ideal.span {t}) = Ideal.span {f.appLE U.1 V.1 e t} := by
      rw [Ideal.map_span, Set.image_singleton]; rfl
    rw [Ideal.isRadical_iff_quotient_reduced, ← e1]
    let ψ : (Γ(X, V.1) ⧸ Ideal.map (algebraMap Γ(S, U.1) Γ(X, V.1)) (Ideal.span {t})) ≃+*
        TensorProduct Γ(S, U.1) (Γ(S, U.1) ⧸ Ideal.span {t}) Γ(X, V.1) :=
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot Γ(X, V.1) (Ideal.span {t})).toRingEquiv.trans
        (Algebra.TensorProduct.comm Γ(S, U.1) Γ(X, V.1) _).toRingEquiv
    exact isReduced_of_injective ψ.toRingHom ψ.injective
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
  refine (congrArg PrimeSpectrum.vanishingIdeal hset).trans ?_
  rw [← PrimeSpectrum.zeroLocus_span, PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, hrad.radical]

end GlobalTheory.DivPullback

namespace GlobalTheory.DivPullback

open GlobalTheory.CxPts GlobalTheory.ShFam ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem isDivNorm_comp {k k' : Type} [CommRing k] [CommRing k'] {Y Y' : Scheme.{0}} {p : Y ⟶ Sp k}
    {p' : Y' ⟶ Sp k'} {σ : k →+* ℂ} {σ' : k' →+* ℂ} {d d' : ℕ} (f : Y' ⟶ Y) [Smooth f]
    {m : CxPts p' σ' → CxPts p σ} (hm : ∀ z, (m z).1 = z.1 ≫ f) {R : AnRead p σ d} (R' : AnRead p' σ' d')
    {C : Closeds Y} {n : CxPts p σ → ℝ} (h : IsDivNorm R C n) :
    IsDivNorm R' (C.preimage f.continuous) (n ∘ m) := by
  refine ⟨fun y => h.1 (m y), fun z => ?_⟩
  obtain ⟨V, t, g, hy, ht, hg, e⟩ := h.2 (m z)
  have hz : z ∈ ptsIn p' σ' (f ⁻¹ᵁ V.1) := (mem_ptsIn_preimage hm).2 hy
  obtain ⟨W, hW, hzW, hWle⟩ := Opens.isBasis_iff_nbhd.1 Y'.isBasis_affineOpens (mem_ptsIn.1 hz)
  have hsub : ∀ z' ∈ ptsIn p' σ' W, m z' ∈ ptsIn p σ V.1 := fun z' hz' =>
    (mem_ptsIn_preimage hm).1 (ptsIn_mono hWle hz')
  have hev : ∀ z' ∈ ptsIn p' σ' W, ev p' σ' W (f.appLE V.1 W hWle t) z' = ev p σ V.1 t (m z') := fun z' hz' => by
    rw [ev_of_comp hm, ← ev_res hWle hz']
    rfl
  refine ⟨⟨W, hW⟩, f.appLE V.1 W hWle t, g ∘ m, mem_ptsIn.2 hzW,
    vanishingIdeal_preimage f C V t ht ⟨W, hW⟩ hWle,
    (hg.comp_map (isOpen_ptsIn _) hm R').mono hsub, fun z' hz' => ?_⟩
  rw [hev z' hz']
  exact e (m z') (hsub z' hz')

end GlobalTheory.DivPullback

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O

namespace GlobalTheory.DivPullback

theorem isDivNorm_flag : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (σ : D.what₂.LL →+* ℂ) (C : Closeds (gen s.T.Z : Scheme.{0})) (n : CxPts (genStr s.T.Z) (embOf κ.e σ) → ℝ), Smooth (Φ.C k).π → IsDivNorm (manifold s.T.Z (embOf κ.e σ)) C n → IsDivNorm ((Φ.C k).Y.an σ) (C.preimage (Φ.C k).π.continuous) (fun z => n ((Φ.C k).down z)) := by
  intro D A N j S κ s Φ k σ C n hπ h
  haveI := hπ
  exact isDivNorm_comp (Φ.C k).π (m := (Φ.C k).down) (fun _ => rfl) _ h

end GlobalTheory.DivPullback
