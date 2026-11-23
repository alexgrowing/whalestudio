import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealGeneratedByPolyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.ChartGlue
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.LocForm

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

def evS (y : CxPts p σ) : X.presheaf.stalk y.pt →+* ℂ := (Scheme.stalkClosedPointTo y.1).hom

theorem evS_germ {y : CxPts p σ} {U : X.Opens} (h : y.pt ∈ U) (a : Γ(X, U)) :
    evS y (X.presheaf.germ U _ h a) = ev p σ U a y := by
  rw [ev_eq (mem_ptsIn.2 h)]
  exact congrArg (fun φ => φ.hom a) (Points.germ_stalkClosedPointTo_eq_valMap y.1 U (mem_ptsIn.2 h))

theorem evS_ne_zero_iff (y : CxPts p σ) (a : X.presheaf.stalk y.pt) : evS y a ≠ 0 ↔ IsUnit a :=
  have : IsLocalHom (Scheme.stalkClosedPointTo y.1).hom := Scheme.isLocalHom_stalkClosedPointTo' y.1
  isUnit_iff_ne_zero.symm.trans (@isUnit_map_iff _ _ _ _ _ _ _ _ this a)

theorem exists_alg (h : IsArithVar p 1) (c : AlgChart p σ 1) {W : X.Opens} (f : Γ(X, W)) (hf : f ≠ 0)
    {y : CxPts p σ} (hy : y ∈ ptsIn p σ c.U) (hW : y.pt ∈ W) :
    ∃ (P : Polynomial k) (V : X.Opens) (hV : y.pt ∈ V) (g : Γ(X, V)) (hVW : V ≤ W) (hVU : V ≤ c.U),
      ev p σ V g y ≠ 0 ∧
      resG X hVW f = g * resG X hVU (P.eval₂ (algX p c.U) (c.x 0)) ^ germOrd f hW ∧
      P.eval₂ σ (ev p σ c.U (c.x 0) y) = 0 ∧
      (germOrd f hW = 0 ∨ P.derivative.eval₂ σ (ev p σ c.U (c.x 0) y) ≠ 0) := by
  classical
  have := h.isDomain; have := h.finite; have := h.isIntegral
  have hz : y.pt ∈ c.U := mem_ptsIn.1 hy
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨y.pt, hz⟩ : c.U)
  haveI : IsLocalization.AtPrime (X.presheaf.stalk y.pt) (c.affine.primeIdealOf ⟨y.pt, hz⟩).asIdeal :=
    c.affine.isLocalization_stalk ⟨y.pt, hz⟩
  have hgerm : ∀ a : Γ(X, c.U), algebraMap Γ(X, c.U) (X.presheaf.stalk y.pt) a =
      X.presheaf.germ c.U y.pt hz a := fun _ => rfl
  set φ := MvPolynomial.eval₂Hom (algX p c.U) c.x with hφ
  have hφC : φ.comp MvPolynomial.C = algX p c.U :=
    RingHom.ext fun a => MvPolynomial.eval₂Hom_C _ _ a
  have hφX : φ (MvPolynomial.X 0) = c.x 0 := MvPolynomial.eval₂Hom_X' _ _ 0
  have he : (evHom hy).comp (algX p c.U) = σ :=
    RingHom.ext fun a => (ev_eq hy _).symm.trans (ev_algX hy a)
  have hσ : Function.Injective σ := GlobalTheory.RegGenSmooth.injective_of_charZero σ
  have hq : (c.affine.primeIdealOf ⟨y.pt, hz⟩).asIdeal = RingHom.ker (evHom hy) := by
    ext a
    rw [RingHom.mem_ker, ← IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk y.pt) _ a,
      ← ev_eq hy, hgerm, ← evS_germ hz a, ← not_iff_not, IsLocalRing.notMem_maximalIdeal]
    exact (evS_ne_zero_iff y _).symm
  obtain ⟨P, hmax, hder⟩ := GlobalTheory.T.maximal_ideal_generated_by_poly k Γ(X, c.U) (X.presheaf.stalk y.pt) φ c.etale (evHom hy)
    (by rw [hφC, he]; exact hσ) _ hq
  rw [hφC, hφX, hgerm] at hmax
  rw [hφC, he, hφX, ← ev_eq hy] at hder
  set t := P.eval₂ (algX p c.U) (c.x 0) with ht_def
  set tR := X.presheaf.germ c.U y.pt hz t with htR

  haveI : IsNoetherianRing k := isNoetherian_of_tower ℤ inferInstance
  haveI hA : IsNoetherianRing Γ(X, c.U) := by
    letI := φ.toAlgebra
    haveI : Algebra.Etale (MvPolynomial (Fin 1) k) Γ(X, c.U) := c.etale
    exact Algebra.FiniteType.isNoetherianRing (MvPolynomial (Fin 1) k) _
  haveI : IsLocalization (c.affine.primeIdealOf ⟨y.pt, hz⟩).asIdeal.primeCompl (X.presheaf.stalk y.pt) :=
    ‹IsLocalization.AtPrime _ _›
  haveI : IsNoetherianRing (X.presheaf.stalk y.pt) :=
    IsLocalization.isNoetherianRing (c.affine.primeIdealOf ⟨y.pt, hz⟩).asIdeal.primeCompl _ hA
  set F := X.presheaf.germ W y.pt hW f with hF
  have hF0 : F ≠ 0 := fun h0 => hf (germ_injective_of_isIntegral X y.pt hW (h0.trans (map_zero _).symm))
  have key : ∃ (n : ℕ) (u : (X.presheaf.stalk y.pt)ˣ), F = u * tR ^ n ∧ germOrd f hW = n := by
    by_cases ht : tR = 0
    · have hbot : IsLocalRing.maximalIdeal (X.presheaf.stalk y.pt) = ⊥ := by
        rw [hmax, ht, Ideal.span_singleton_eq_bot]
      have hu : IsUnit F := by
        by_contra hn
        have hm := (IsLocalRing.mem_maximalIdeal F).2 hn
        rw [hbot, Ideal.mem_bot] at hm
        exact hF0 hm
      refine ⟨0, hu.unit, by simp, ?_⟩
      rw [germOrd, ← hF, Ring.ord_of_isUnit hu]
      rfl
    · have hnf : ¬ IsField (X.presheaf.stalk y.pt) := fun hfld => ht (by
        have := (IsLocalRing.isField_iff_maximalIdeal_eq.1 hfld)
        have hm : tR ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y.pt) := by
          rw [hmax]; exact Ideal.subset_span (Set.mem_singleton _)
        simpa [this] using hm)
      haveI : IsDiscreteValuationRing (X.presheaf.stalk y.pt) :=
        ((IsDiscreteValuationRing.TFAE (X.presheaf.stalk y.pt) hnf).out 0 4).2
          (⟨⟨tR, hmax⟩⟩ : (IsLocalRing.maximalIdeal (X.presheaf.stalk y.pt)).IsPrincipal)
      have hirr : Irreducible tR := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmax
      obtain ⟨n, u, hfu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hF0 hirr
      refine ⟨n, u, hfu, ?_⟩
      rw [germOrd, ← hF, hfu, Ring.ord_eq_addVal, IsDiscreteValuationRing.addVal_def' u hirr n]
      rfl
  obtain ⟨n, u, hFu, hn⟩ := key

  obtain ⟨V₀, hV₀, g₀, hg₀⟩ := X.presheaf.germ_exist (x := y.pt) (u : X.presheaf.stalk y.pt)
  have hV₁ : y.pt ∈ V₀ ⊓ c.U := ⟨hV₀, hz⟩
  have hgerm₁ : X.presheaf.germ W y.pt hW f = X.presheaf.germ (V₀ ⊓ c.U) y.pt hV₁
      (resG X inf_le_left g₀ * resG X inf_le_right t ^ n) := by
    rw [← hF, hFu, map_mul, map_pow, Cartier.germ_resG, Cartier.germ_resG, hg₀]
  obtain ⟨V, hV, iU, iV, heqV⟩ := X.presheaf.germ_eq y.pt hW hV₁ f _ hgerm₁
  have hVW : V ≤ W := leOfHom iU
  have hV1 : V ≤ V₀ ⊓ c.U := leOfHom iV
  have hVU : V ≤ c.U := hV1.trans inf_le_right
  have hevt : ev p σ c.U t y = P.eval₂ σ (ev p σ c.U (c.x 0) y) := by
    rw [ev_eq hy, ev_eq hy, ht_def, Polynomial.hom_eval₂, he]
  refine ⟨P, V, hV, resG X (hV1.trans inf_le_left) g₀, hVW, hVU, ?_, ?_, ?_, ?_⟩
  · rw [← evS_germ hV, Cartier.germ_resG, hg₀]
    exact (evS_ne_zero_iff y _).2 u.isUnit
  · have e1 : resG X hVW f = resG X hV1 (resG X inf_le_left g₀ * resG X inf_le_right t ^ n) := heqV
    rw [e1, map_mul, map_pow, Cartier.resG_resG, Cartier.resG_resG, hn]
  · rw [← hevt, ← evS_germ hz]
    by_contra hne
    have hu := (evS_ne_zero_iff y _).1 hne
    have hm : tR ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y.pt) := by
      rw [hmax]; exact Ideal.subset_span (Set.mem_singleton _)
    exact (IsLocalRing.mem_maximalIdeal _).1 hm hu
  · rcases hder with hP | hd
    · left
      rw [hn]
      by_contra hn0
      have ht0 : tR = 0 := by simp [htR, ht_def, hP]
      exact hF0 (by rw [hFu, ht0, zero_pow hn0, mul_zero])
    · exact Or.inr hd

theorem locForm : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsArithVar p 1 →
    ∀ (σ : k →+* ℂ) (c : AlgChart p σ 1) (W : X.Opens) (f : Γ(X, W)), f ≠ 0 →
    ∀ (y : CxPts p σ), y ∈ c.e.source → ∀ hW : y.pt ∈ W, ∃ u : ReciprocityTheory.L2DbarEstimates.V 1 → ℂ,
      (∀ᶠ v in 𝓝 (c.e y), DifferentiableAt ℂ u v) ∧ u (c.e y) ≠ 0 ∧
      ∀ᶠ v in 𝓝 (c.e y), ev p σ W f (c.e.symm v) = u v * (v 0 - c.e y 0) ^ germOrd f hW := by
  intro k _ X p h σ c W f hf y hy hW
  have hyU := c.source_subset hy
  obtain ⟨P, V, hV, g, hVW, hVU, hg, heq, hroot, hder⟩ := exists_alg h c f hf hyU hW
  set w := c.e y 0 with hw_def
  have hw : ev p σ c.U (c.x 0) y = w := (c.apply_eq y hy 0).symm
  rw [hw] at hroot hder
  set Q := P.map σ /ₘ (Polynomial.X - Polynomial.C w)
  have hroot' : (P.map σ).IsRoot w := by rw [Polynomial.IsRoot, Polynomial.eval_map]; exact hroot
  have hPQ : (Polynomial.X - Polynomial.C w) * Q = P.map σ :=
    Polynomial.mul_divByMonic_eq_iff_isRoot.2 hroot'
  have hQw : germOrd f hW = 0 ∨ Q.eval w ≠ 0 := by
    refine hder.imp id fun hd => ?_
    have e := congrArg (fun r => (Polynomial.derivative r).eval w) hPQ
    simp only [Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_X,
      Polynomial.derivative_C, sub_zero, one_mul, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_mul, add_zero,
      Polynomial.derivative_map, Polynomial.eval_map] at e
    rw [e]; exact hd
  have hVpt : y ∈ ptsIn p σ V := mem_ptsIn.2 hV
  have hN : c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ V ∈ 𝓝 (c.e y) :=
    (isOpen_over c.e (isOpen_ptsIn V)).mem_nhds (mem_over c.e hy hVpt)
  have hproj : Differentiable ℂ (fun v : ReciprocityTheory.L2DbarEstimates.V 1 => v 0) :=
    (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 1)).differentiable
  refine ⟨fun v => ev p σ V g (c.e.symm v) * Q.eval (v 0) ^ germOrd f hW, ?_, ?_, ?_⟩
  · filter_upwards [hN] with v hv
    exact ((c.holo V g).differentiableAt ((isOpen_over c.e (isOpen_ptsIn V)).mem_nhds hv)).mul
      ((Q.differentiable.comp hproj).pow _ v)
  · simp only [c.e.left_inv hy]
    refine mul_ne_zero hg ?_
    rcases hQw with h0 | h0
    · rw [h0, pow_zero]; exact one_ne_zero
    · exact pow_ne_zero _ h0
  · filter_upwards [hN] with v hv
    have hs : c.e.symm v ∈ c.e.source := c.e.map_target hv.1
    have hsV : c.e.symm v ∈ ptsIn p σ V := hv.2
    have hsU : c.e.symm v ∈ ptsIn p σ c.U := c.source_subset hs
    have hx : ev p σ c.U (c.x 0) (c.e.symm v) = v 0 := by
      rw [← c.apply_eq _ hs 0, c.e.right_inv hv.1]
    have ht : ev p σ V (resG X hVU (P.eval₂ (algX p c.U) (c.x 0))) (c.e.symm v) =
        (v 0 - w) * Q.eval (v 0) := by
      rw [ev_res hVU hsV, ev_eq hsU, Polynomial.hom_eval₂, ← ev_eq hsU, hx]
      have he : (evHom hsU).comp (algX p c.U) = σ :=
        RingHom.ext fun a => (ev_eq hsU _).symm.trans (ev_algX hsU a)
      rw [he, ← Polynomial.eval_map, ← hPQ, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C]
    rw [← ev_res hVW hsV, heq, ev_eq hsV, map_mul, map_pow, ← ev_eq hsV, ← ev_eq hsV, ht]
    have key : ∀ (a b x : ℂ) (m : ℕ), a * ((x - w) * b) ^ m = a * b ^ m * (x - w) ^ m := by
      intro a b x m; rw [mul_pow, mul_comm ((x - w) ^ m), ← mul_assoc]
    exact key _ _ _ _

end GlobalTheory.LocForm
