import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemRadicalOfHolomorphicRatioTendstoStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.BdArc

theorem spMap_fromSpec_mem_basicOpen {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {K : Type} [Field K]
    (ψ : Γ(X, U) →+* K) (p : Γ(X, U)) (s : Sp K) :
    (spMap ψ ≫ (show Sp Γ(X, U) ⟶ X from hU.fromSpec)) s ∈ X.basicOpen p ↔ ψ p ≠ 0 := by
  have h : spMap ψ s ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen p ↔ ψ p ≠ 0 := by
    rw [hU.fromSpec_preimage_basicOpen]
    change ψ p ∉ (show PrimeSpectrum K from s).asIdeal ↔ _
    rw [Ideal.eq_bot_of_prime (show PrimeSpectrum K from s).asIdeal, Ideal.mem_bot]
  exact h

theorem spMap_fromSpec_mem {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {K : Type} [CommRing K]
    (ψ : Γ(X, U) →+* K) (s : Sp K) :
    (spMap ψ ≫ (show Sp Γ(X, U) ⟶ X from hU.fromSpec)) s ∈ U := by
  have h : hU.fromSpec (spMap ψ s) ∈ (U : Set X) := hU.range_fromSpec ▸ ⟨_, rfl⟩
  exact h

theorem exists_fnOf_eq_mul_pow {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} (hU : IsAffineOpen U)
    (h : genericPoint X ∈ U) (p : Γ(X, U)) (hp : fnOf U h p ≠ 0) {f : X.functionField}
    (hf : ∀ x ∈ X.basicOpen p, RegAt x f) : ∃ (a : Γ(X, U)) (m : ℕ), fnOf U h a = f * fnOf U h (p ^ m) := by
  have hg : genericPoint X ∈ X.basicOpen p := (unitAt_fnOf_iff h h p).1 (unitAt_genericPoint hp)
  obtain ⟨c, rfl⟩ := exists_fnOf_eq hg hf
  have := hU.isLocalization_basicOpen p
  obtain ⟨⟨a, _, m, rfl⟩, e⟩ := IsLocalization.surj (Submonoid.powers p) c
  refine ⟨a, m, ?_⟩
  have e' := congrArg (fnOf _ hg) e
  rw [map_mul] at e'
  exact ((fnOf_resG (X.basicOpen_le p) hg a).symm.trans e'.symm).trans
    (congrArg _ (fnOf_resG (X.basicOpen_le p) hg _))

theorem mem_H0_and_vanishOn_of_tendsto : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (Y : GlobalTheory.ProjVar.Var F) (Δ bd : Y.Dv) (g : Y.Fn), Y.Eff bd → (∀ y : Y.X, y ∉ Y.supp bd → Δ.RegularAt y g) → (∀ y ∈ Y.supp bd, ∀ V : Y.X.Opens, y ∈ V → ∃ (U : Y.X.Opens) (hU : IsAffineOpen U) (hy : y ∈ U) (t : Y.Fnˣ), U ≤ V ∧ (∀ y' ∈ U, Δ.IsEqn y' t) ∧ ∀ (a b : Γ(Y.X, U)) (ψ : ℂ → (Γ(Y.X, U) →+* ℂ)) (r : ℝ), IsHolPts ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, spMap (ψ u) ≫ (show Sp Γ(Y.X, U) ⟶ Y.X from hU.fromSpec) ≫ Y.str = spMap σ) → (∀ s, (spMap (ψ 0) ≫ (show Sp Γ(Y.X, U) ⟶ Y.X from hU.fromSpec)) s ∈ Y.supp bd) → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ∀ s, (spMap (ψ u) ≫ (show Sp Γ(Y.X, U) ⟶ Y.X from hU.fromSpec)) s ∉ Y.supp bd) → fnOf U (gen_mem hy) a = g * t * fnOf U (gen_mem hy) b → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ψ u b ≠ 0) → Tendsto (fun u => ψ u a / ψ u b) (𝓝[≠] 0) (𝓝 0)) → g ∈ Y.H0 Δ ∧ Y.vanishOn Δ g (Y.supp bd) := by
  intro F _ σ Y Δ bd g hbd hreg H
  have key : Y.vanishOn Δ g (Y.supp bd) := by
    intro y hy
    obtain ⟨V, hV, q, hq⟩ := bd.exists_isEqn_nhds y
    obtain ⟨U, hU, hyU, t, hUV, ht, H⟩ := H y hy V hV
    obtain ⟨p, hp⟩ := exists_fnOf_eq (gen_mem hyU)
      fun x hx => CartierDiv.eff_iff.1 hbd x q (hq x (hUV hx))
    have hsupp (x : Y.X) (hx : x ∈ U) : x ∈ Y.supp bd ↔ x ∉ Y.X.basicOpen p := by
      rw [← unitAt_fnOf_iff hx (gen_mem hyU), hp]
      exact (hq x (hUV hx)).mem_supp_iff
    have hp0 : fnOf U (gen_mem hyU) p ≠ 0 := hp ▸ q.ne_zero
    obtain ⟨a, m, ha⟩ := exists_fnOf_eq_mul_pow hU (gen_mem hyU) p hp0 (f := g * t) fun x hx =>
      (ht x (Y.X.basicOpen_le p hx)).regularAt_iff.1
        (hreg x fun h => (hsupp x (Y.X.basicOpen_le p hx)).1 h hx)
    have hφ : Spec.map (Spec.preimage (hU.fromSpec ≫ Y.str)) = hU.fromSpec ≫ Y.str := Spec.map_preimage _
    have := SmoothOfRelativeDimension.smooth Y.dim Y.str
    have hsm : RingHom.Smooth (Spec.preimage (hU.fromSpec ≫ Y.str)).hom :=
      (HasRingHomProperty.Spec_iff (P := @Smooth)).mp (by rw [hφ]; infer_instance)
    letI : Algebra F Γ(Y.X, U) := (Spec.preimage (hU.fromSpec ≫ Y.str)).hom.toAlgebra
    have : Nonempty U := ⟨⟨y, hyU⟩⟩
    obtain ⟨b, hb, n, hn⟩ := GlobalTheory.T.mem_radical_of_holomorphic_ratio_tendsto F Γ(Y.X, U) hsm σ p a m (fun e => hp0 (by rw [e, map_zero]))
      fun ψ r hψ hσ h0 h1 => H a (p ^ m) ψ r hψ
        (fun u hu => by
          rw [← hσ u hu]
          exact (congrArg (spMap (ψ u) ≫ ·) hφ.symm).trans (Spec.map_comp _ _).symm)
        (fun s => (hsupp _ (spMap_fromSpec_mem hU _ s)).2 fun h =>
          (spMap_fromSpec_mem_basicOpen hU _ p s).1 h h0)
        (fun u hu hu0 s h => (hsupp _ (spMap_fromSpec_mem hU _ s)).1 h
          ((spMap_fromSpec_mem_basicOpen hU _ p s).2 (h1 u hu hu0)))
        ha (fun u hu hu0 => by rw [map_pow]; exact pow_ne_zero _ (h1 u hu hu0))
    have e : g * t = fnOf U (gen_mem hyU) b := by
      rw [hb, map_mul] at ha
      exact (mul_right_cancel₀ (by rw [map_pow]; exact pow_ne_zero _ hp0) ha).symm
    refine ⟨t, ht y hyU, e ▸ zeroAt_iff.2 ⟨regAt_fnOf hyU _ b, fun hu => (hsupp y hyU).1 hy ?_⟩⟩
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hn
    rw [unitAt_fnOf_iff hyU, Y.X.mem_basicOpen b y hyU] at hu
    rw [Y.X.mem_basicOpen p y hyU]
    have h := hu.pow n
    rw [← map_pow, ← hc, map_mul] at h
    exact isUnit_of_mul_isUnit_right h
  refine ⟨ProjVar.Var.mem_riemannRochSpace_iff_regularAt_everywhere.2 fun y => ?_, key⟩
  by_cases hy : y ∈ Y.supp bd
  · exact (key y hy).regularAt
  · exact hreg y hy

end GlobalTheory.ShFam.BdArc
