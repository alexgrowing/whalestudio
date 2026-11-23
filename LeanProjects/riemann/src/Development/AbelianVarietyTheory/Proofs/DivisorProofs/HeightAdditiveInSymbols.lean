import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightWeightRootChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqnRatio
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightOfInducedBundle
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosedPointGeometricFibresFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MetsOfParOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFormulaRationalFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalHeightSupportFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquationRatioUnitLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogMetricNormDivisorSumStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad ReciprocityTheory.ChartRestriction.G.Geo.Tor
open CategoryTheory AlgebraicGeometry IsDedekindDomain GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HtAdd

theorem alg {ι κ : Type} [Fintype κ] (s : Finset ι) (n : ι → ℝ) (P : ι → κ → ℝ) (Q : κ → ℝ) (Fi : ι → ℝ) (R K : ℝ)
    (h : ∑ k, Q k + R = 0) :
    -((∑ k, (∑ i ∈ s, n i * P i k + Q k)) + (∑ i ∈ s, n i * Fi i + R)) / K =
      ∑ i ∈ s, n i * (-((∑ k, P i k) + Fi i) / K) := by
  have e₁ : ∑ k, (∑ i ∈ s, n i * P i k + Q k) = ∑ i ∈ s, n i * ∑ k, P i k + ∑ k, Q k := by
    rw [Finset.sum_add_distrib, Finset.sum_comm]
    simp only [Finset.mul_sum]
  have e₂ : ∑ i ∈ s, n i * (-((∑ k, P i k) + Fi i) / K) =
      -(∑ i ∈ s, n i * ∑ k, P i k + ∑ i ∈ s, n i * Fi i) / K := by
    rw [← Finset.sum_add_distrib, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e₁, e₂]
  linear_combination (-1 / K) * h
end GlobalTheory.HtAdd

namespace GlobalTheory.HtAdd

theorem isClosed_below_alg {F : Type} [Field F] [NumberField F] {Y : Var F} (y : AlgPt Y) :
    IsClosed ({below y.1} : Set Y.X) := by
  have hint : IsIntegralHom (y.1 ≫ Y.str) := by
    rw [y.2]
    exact IsIntegralHom.SpecMap_iff.2 fun z => Algebra.IsIntegral.isIntegral z
  have hp : IsIntegralHom y.1 := IsIntegralHom.of_comp y.1 Y.str
  have hc : IsClosed ({IsLocalRing.closedPoint (AlgebraicClosure F)} : Set (Sp (AlgebraicClosure F))) :=
    IsLocalRing.isClosed_singleton_closedPoint _
  have := y.1.isClosedMap _ hc
  exact (Set.image_singleton (f := ⇑y.1) (a := IsLocalRing.closedPoint (AlgebraicClosure F))) ▸ this

open Classical in

theorem ht_comb {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F} {ι : Type} (s : Finset ι) (n : ι → ℤ)
    (Bw : Adl C Y) (B : ι → Adl C Y) (hnw : Bw.n = 1) (hn : ∀ i, (B i).n = 1) {x : Y.X}
    (hx : IsClosed ({x} : Set Y.X)) (g : Y.Fn)
    (hcx : ∀ σ (z : Pts Y σ), under z = x →
      Real.log (C.pn Y σ Bw.D (Bw.m σ) (C.cx Y σ ((eqn Bw.D x)⁻¹ : Y.Fnˣ)) z) / 2 -
          (Bw.n : ℕ) * Bw.ci (InfinitePlace.mk σ) =
        ∑ i ∈ s, (n i : ℝ) * (Real.log (C.pn Y σ (B i).D ((B i).m σ) (C.cx Y σ ((eqn (B i).D x)⁻¹ : Y.Fnˣ)) z) / 2 -
          ((B i).n : ℕ) * (B i).ci (InfinitePlace.mk σ)) + Real.log ‖ratVal g z‖)
    (hlg : ∀ v (ε : Ext v) (y : AlgPt Y), below y.1 = x →
      Bw.lg v ε y = ∑ i ∈ s, (n i : ℝ) * (B i).lg v ε y + Real.log (ε.w (valAt y.1 g)))
    (hS : ∀ i ∈ s, (Function.support fun v : HeightOneSpectrum (𝓞 F) => if h : Nonempty (Ext v) then
        ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), (B i).lg v h.some y else 0).Finite)
    (hg : (Function.support fun v : HeightOneSpectrum (𝓞 F) => if h : Nonempty (Ext v) then
        ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), Real.log (h.some.w (valAt y.1 g)) else 0).Finite)
    (hpf : (∑ σ : F →+* ℂ, ∑ᶠ (z : Pts Y σ) (_ : under z = x), Real.log ‖ratVal g z‖) +
      ∑ᶠ v : HeightOneSpectrum (𝓞 F), (if h : Nonempty (Ext v) then
        ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), Real.log (h.some.w (valAt y.1 g)) else 0) = 0) :
    Bw.ht x = ∑ i ∈ s, (n i : ℝ) * (B i).ht x := by
  obtain ⟨hne, hfin⟩ := ExtConj.pts Y x hx
  have := Fintype.ofFinite {y : AlgPt Y // below y.1 = x}
  have hC (σ : F →+* ℂ) : ∑ᶠ (z : Pts Y σ) (_ : under z = x),
      (Real.log (C.pn Y σ Bw.D (Bw.m σ) (C.cx Y σ ((eqn Bw.D x)⁻¹ : Y.Fnˣ)) z) / 2 -
        (Bw.n : ℕ) * Bw.ci (InfinitePlace.mk σ)) =
      ∑ i ∈ s, (n i : ℝ) * ∑ᶠ (z : Pts Y σ) (_ : under z = x),
        (Real.log (C.pn Y σ (B i).D ((B i).m σ) (C.cx Y σ ((eqn (B i).D x)⁻¹ : Y.Fnˣ)) z) / 2 -
          ((B i).n : ℕ) * (B i).ci (InfinitePlace.mk σ)) +
      ∑ᶠ (z : Pts Y σ) (_ : under z = x), Real.log ‖ratVal g z‖ := by
    rw [finsum_congr fun z => finsum_congr fun hz => hcx σ z hz, finsum_under_add σ hx, finsum_under_sum s σ hx]
    congr 1
    exact Finset.sum_congr rfl fun i _ => finsum_under_mul σ hx _ _
  have hF (v : HeightOneSpectrum (𝓞 F)) : (if h : Nonempty (Ext v) then
      ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), Bw.lg v h.some y else 0) =
      ∑ i ∈ s, (n i : ℝ) * (if h : Nonempty (Ext v) then
        ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), (B i).lg v h.some y else 0) +
      (if h : Nonempty (Ext v) then
        ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), Real.log (h.some.w (valAt y.1 g)) else 0) := by
    have h : Nonempty (Ext v) := inferInstance
    simp only [dif_pos h]
    rw [finsum_congr fun y => finsum_congr fun hy => hlg v _ y hy]
    simp only [← finsum_subtype_eq_finsum_cond, finsum_eq_sum_of_fintype, Finset.sum_add_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hsum : ∑ᶠ v : HeightOneSpectrum (𝓞 F), (if h : Nonempty (Ext v) then
      ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), Bw.lg v h.some y else 0) =
      ∑ i ∈ s, (n i : ℝ) * ∑ᶠ v : HeightOneSpectrum (𝓞 F), (if h : Nonempty (Ext v) then
        ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), (B i).lg v h.some y else 0) +
      ∑ᶠ v : HeightOneSpectrum (𝓞 F), (if h : Nonempty (Ext v) then
        ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), Real.log (h.some.w (valAt y.1 g)) else 0) := by
    have hS' (i) (hi : i ∈ s) : (Function.support fun v : HeightOneSpectrum (𝓞 F) => (n i : ℝ) *
        (if h : Nonempty (Ext v) then ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), (B i).lg v h.some y else 0)).Finite :=
      (hS i hi).subset (Function.support_mul_subset_right _ _)
    rw [finsum_congr hF, finsum_add_distrib ?_ hg, finsum_sum_comm s _ hS']
    · exact congrArg (· + _) (Finset.sum_congr rfl fun i _ => (mul_finsum _ _).symm)
    · refine ((s.finite_toSet.biUnion fun i hi => hS' i hi)).subset ?_
      intro v hv
      by_contra hn'
      apply hv
      simp only [Set.mem_iUnion, not_exists] at hn'
      exact Finset.sum_eq_zero fun i hi => by
        by_contra h0
        exact hn' i hi h0
  unfold Adl.ht
  rw [Finset.sum_congr rfl fun σ _ => hC σ, hsum]
  simp only [hnw, hn]
  exact alg s _ _ _ _ _ _ hpf

end GlobalTheory.HtAdd

namespace GlobalTheory.HtAdd

open Classical in

theorem fs_line : ∀ (D : D7) (O : Setup D) (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y), O.Reads A T H →
    ∀ (c : O.s.Comp) (a : Sym D.host.E), a.1 = (fun _ => false) → a.2.1 = none →
    ∀ x : (O.var c).X, IsClosed ({x} : Set (O.var c).X) →
    (Function.support fun v : HeightOneSpectrum (𝓞 D.what₂.LL) => if h : Nonempty (Ext v) then
        ∑ᶠ (y : AlgPt (O.var c)) (_ : below y.1 = x),
          (adlOf (O.Φ.C c) (O.met.hm c) (Finsupp.single a 1)).lg v h.some y else 0).Finite := by
  intro D O A T H hR c a h1 h2 x hx
  obtain ⟨a1, a2, st⟩ := a
  simp only at h1 h2
  subst h1 h2
  have hind : ArIn.ind ∅ = (fun _ => false) := funext fun q => by simp [ArIn.ind]
  cases hs : (letterOf O.S.Dw st).isSome

  ·
    set Y := O.Φ.C c
    set w : Sym D.host.E →₀ ℤ := Finsupp.single ((fun _ => false), none, st) 1 with hw
    have hex : expo O.S.Dw w = 0 := funext fun z => by
      rw [hw, expo_single]
      have : letterOf O.S.Dw st ≠ some z := fun h => by simp [h] at hs
      simp [this]
    have hd : divOf Y (0 : Letter O.S.Dw → ℤ) = 0 := by simp [divOf]
    set g : Y.Y.Fn := (↑((eqn (0 : Y.Y.Dv) x)⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn) with hg
    have hgu : UnitAt x g := by
      have := (Base.isEqn_eqn (0 : Y.Y.Dv) x).iff_unitAt.1 (CartierDiv.isEqn_zero x)
      simpa [hg] using this
    refine (GlobalTheory.T.product_formula_rational_function _ (O.var c) x hx g hgu).1.subset fun v hv => ?_
    have hne : Nonempty (Ext v) := inferInstance
    rw [Function.mem_support, dif_pos hne] at hv ⊢
    intro h0
    apply hv
    by_cases hp : (resP v).Prime
    · rw [← h0]
      refine finsum_congr fun y => finsum_congr fun hy => ?_
      change lgOf Y w v hne.some y = _
      rw [lgOf, dif_pos hp]
      simp only [hex, Pi.zero_apply, zpow_zero, Finset.prod_const_one, one_mul, hd, hy]
      rw [hw, Finsupp.sum_single_index (by simp)]
      rcases st with ⟨τ, k⟩ | k
      · have hk : ¬ k < O.S.Dw.mult τ := fun h => by simp [letterOf, h] at hs
        simp [lnStep, hk, hg]
      · have hk : ¬ k < (letters O.S.Dw).length := fun h => by simp [letterOf, h] at hs
        simp [lnStep, hk, hg]
    · have h3 : ∀ y : AlgPt (O.var c), (adlOf (O.Φ.C c) (O.met.hm c) w).lg v hne.some y = 0 := fun y => by
        change lgOf Y w v hne.some y = 0
        rw [lgOf, dif_neg hp]
      simp [h3]
  · have hI := (hR.mdl ∅ c).line_spec ∅ (Finset.Subset.refl _) st hs
    rw [hind] at hI
    exact GlobalTheory.T.local_height_support_finite _ _ _ _ _ _ _ one_ne_zero hI x hx

end GlobalTheory.HtAdd

namespace GlobalTheory.HtAdd

theorem ht_adlOf_sum : ∀ (D : D7) (O : Setup D), O.Core → ∀ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y), O.Reads A T H →
    ∀ (c : O.s.Comp) (x : (O.var c).X) {ι : Type} (s : Finset ι) (a : ι → Sym D.host.E) (n : ι → ℤ),
    (∀ i ∈ s, (a i).1 = (fun _ => false) ∧ (a i).2.1 = none) →
    (adlOf (O.Φ.C c) (O.met.hm c) (∑ i ∈ s, Finsupp.single (a i) (n i))).ht x =
      ∑ i ∈ s, (n i : ℝ) * (adlOf (O.Φ.C c) (O.met.hm c) (Finsupp.single (a i) 1)).ht x := by
  classical
  intro D O hO A T H hR c x ι s a n ha
  by_cases hx : IsClosed ({x} : Set (O.var c).X)
  swap
  · have hE : IsEmpty {y : AlgPt (O.var c) // below y.1 = x} := ⟨fun y => hx (y.2 ▸ isClosed_below_alg y.1)⟩
    have h0 : (Nat.card {y : AlgPt (O.var c) // below y.1 = x} : ℝ) = 0 := by
      rw [Nat.card_of_isEmpty, Nat.cast_zero]
    simp only [Adl.ht, h0, mul_zero, div_zero, Finset.sum_const_zero]
  obtain ⟨hGu, hLG⟩ := GlobalTheory.T.equation_ratio_unit_local (O.Φ.C c) s a n x
  obtain ⟨hGs, hPF⟩ := GlobalTheory.T.product_formula_rational_function D.what₂.LL (O.var c) x hx _ hGu
  refine ht_comb s n _ _ rfl (fun _ => rfl) hx _ (fun σ z hz => ?_) (fun v ε y hy => hLG v ε y hy)
    (fun i hi => fs_line D O A T H hR c (a i) (ha i hi).1 (ha i hi).2 x hx) hGs hPF
  have := GlobalTheory.T.log_metric_norm_divisor_sum D O hO c s a n (fun i hi => (ha i hi).2) x σ z hz
  have e₁ : ∀ w, (adlOf (O.Φ.C c) (O.met.hm c) w).ci = 0 := fun _ => rfl
  have e₂ : ∀ w, (adlOf (O.Φ.C c) (O.met.hm c) w).n = 1 := fun _ => rfl
  simp only [e₁, e₂, Pi.zero_apply, mul_zero, sub_zero]
  exact this

end GlobalTheory.HtAdd
