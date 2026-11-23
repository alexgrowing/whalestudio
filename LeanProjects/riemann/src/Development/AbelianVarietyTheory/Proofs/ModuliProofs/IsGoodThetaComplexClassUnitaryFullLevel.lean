import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GoodThetaClassOfLatticeFamiliesStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TransportThetaLevelUniformisationCoordinates
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ImAdjointOfSpan
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteMarkedDataInGenus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPELObjectOfPrimitivePeriodMapUniformisedStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPeriodsComplexPELObjectStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PelObjectClassPrimAndIsoClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsTypeFnOfRank
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPeriodDomainParam
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PelGood

theorem exists_domain {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D D' : Datum H) {g : ℕ}
    (ty : Fin g → (E →+* ℂ)) (hty : IsTypeFn H D.p D.q ty) (hp : D'.p = D.p) (hq : D'.q = D.q) :
    ∃ (B : Set (Fin D.dim → ℂ)) (P : (Fin D.dim → ℂ) → (D'.La →+ (Fin g → ℂ))), IsOpen B ∧ Convex ℝ B ∧
      IsHolPeriods D' ty B P ∧ ∀ P', IsPeriod D' ty P' →
        ∃! b, b ∈ B ∧ ∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ a, P' a = h (P b a) := by
  have hd : D.dim = D'.dim := by rw [Datum.dim, Datum.dim, hp, hq]
  rw [hd]
  exact exists_period_domain_param E H D' g ty (by rw [hp, hq]; exact hty)

theorem isPeriod_comp {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D D' : Datum H} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} {Q : D.La →+ (Fin g → ℂ)} (hQ : IsPeriod D ty Q) (e : D.La ≃ₗ[𝓞 E] D'.La)
    (he : ∀ x y, D'.EF (e x) (e y) = D.EF x y) :
    IsPeriod D' ty (Q.comp e.symm.toAddEquiv.toAddMonoidHom) := by
  obtain ⟨h1, h2, h3, h4, Hm, h5, h6, h7⟩ := hQ
  have hr : Set.range (Q.comp e.symm.toAddEquiv.toAddMonoidHom) = Set.range Q :=
    e.symm.surjective.range_comp Q
  have hr' : (Q.comp e.symm.toAddEquiv.toAddMonoidHom).range = Q.range :=
    SetLike.ext' hr
  refine ⟨fun a x i => ?_, h2.comp e.symm.injective, by rw [hr']; exact h3, by rw [hr]; exact h4, Hm, h5, h6,
    fun x y => ?_⟩
  · change Q (e.symm (a • x)) i = _ * Q (e.symm x) i
    rw [map_smul, h1]
  · change (hermForm Hm (Q (e.symm x)) (Q (e.symm y))).im = _
    rw [h7, ← he, e.apply_symm_apply, e.apply_symm_apply]

theorem exp_eq_zpow (k : ℕ) (hk : 0 < k) (m ν s : ℤ) (h : (k : ℤ) ∣ m - ν * s) :
    Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / (k : ℂ)) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (ν : ℂ) / k) ^ s := by
  obtain ⟨c, hc⟩ := h
  have hm : m = ν * s + k * c := by linarith
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [← Complex.exp_int_mul, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-c, ?_⟩
  rw [hm]
  push_cast
  field_simp
  ring

theorem goodClass_pelClass : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∃ (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ), ∀ n : ℕ, n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ N' : ℕ, N' = n ^ j → ∀ (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (ρ : o), em ρ = H.rt0 → GoodClass em (PELClass (b := b) D a bas ρ em) Mat κ w w' D.dim := by
  intro L1 L2 hΘ hU E _ _ _ H D g J _ a w w' bas hpq hbas hw hw' _
  obtain ⟨ty, hty⟩ := exists_isTypeFn_of_rank E H D g ⟨bas⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : ℕ, ∀ (j : J) (τ : E →+* ℂ), ‖τ (a j : E)‖ ^ 2 < κ := by
    obtain ⟨M, hM⟩ := (Set.finite_range (fun x : J × (E →+* ℂ) => ‖x.2 (a x.1 : E)‖ ^ 2)).bddAbove
    obtain ⟨κ, hκ⟩ := exists_nat_gt M
    exact ⟨κ, fun j τ => (hM ⟨(j, τ), rfl⟩).trans_lt hκ⟩
  let Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ :=
    fun j i' i => bas.symm (a j • bas (Pi.single i 1)) i'
  have hMat : ∀ j i, a j • bas (Pi.single i 1) = ∑ i', Mat j i' i • bas (Pi.single i' 1) := by
    intro j i
    apply bas.symm.injective
    rw [map_sum]
    simp only [map_smul, LinearEquiv.symm_apply_apply]
    ext i₀
    simp [Mat, Finset.sum_apply, Pi.single_apply]
  refine ⟨Mat, κ, fun n hn hodd => ?_⟩
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.goodThetaClass_of_lattice_families L1 L2 hΘ hU g J Mat κ n w w' hn hodd
  refine ⟨j₀, fun j hj N' hN o _ b em ρ hρ => ?_⟩
  have hk : 0 < N' ^ 2 := by rw [hN]; exact pow_pos (pow_pos hn.pos _) _
  obtain ⟨r, Di, fi, νi, hfam, hall⟩ := MarkedGenus.finite_marked_data_in_genus E H D (N' ^ 2) (em (b.ζ : o)) hk
  choose B P hBo hBc hBh hBu using fun i => exists_domain D (Di i) ty hty (hfam i).1.1 (hfam i).1.2.1
  have hH : ∀ i bb, ∃ Hm : Matrix (Fin g) (Fin g) ℂ, bb ∈ B i →
      (Function.Injective (P i bb) ∧ DiscreteTopology (P i bb).range ∧ Submodule.span ℝ (Set.range (P i bb)) = ⊤ ∧
        Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
        ∀ x y, (hermForm Hm (P i bb x) (P i bb y)).im = (Di i).EF x y) := by
    intro i bb
    by_cases hb : bb ∈ B i
    · obtain ⟨-, h2, h3, h4, Hm, h5⟩ := (hBh i).1 bb hb
      exact ⟨Hm, fun _ => ⟨h2, h3, h4, h5⟩⟩
    · exact ⟨0, fun h => (hb h).elim⟩
  choose Hm hHm using hH
  refine hj₀ j hj N' hN o b em _ D.dim r (fun i => (Di i).La) (fun i => (Di i).EF)
    (fun i i₁ => fi i (N' ^ 2) (bas (Pi.single i₁ 1))) (fun i j x => a j • x) B P Hm
    (fun t t' ht hm => (pelClass_prim_and_iso E H D o g _ J b em w w' a bas ρ t ht).2 t' hm)
    (fun t ht => (pelClass_prim_and_iso E H D o g _ J b em w w' a bas ρ t ht).1 hw hw') (fun i => ?_) (fun t ht => ?_)
  · refine ⟨(Di i).unimod, hBo i, (hBc i).isPreconnected, (hBh i).2, fun x => ?_, fun x y => ?_, fun i₁ i₂ => ?_,
      fun j₁ i₁ => ⟨0, ?_⟩, fun bb hb => ⟨hHm i bb hb, fun j₁ => ?_⟩, fun bb hb z hz hh => ?_, fun bb hb t hu hp => ?_⟩
    · rw [← add_smul, hw, hw', HostModel.cmHost_bar_halfIntegerGenerator, add_sub_cancel, one_smul]
    · rw [hw, hw', (Di i).adj]
    · rw [(hfam i).2]
      apply exp_eq_zpow _ hk
      rw [← hbas]
      exact (hfam i).1.2.2.2.2 _ hk _ _
    · rw [smul_zero, add_zero, ← map_smul, hMat, map_sum]
      simp only [map_zsmul]
    · exact ConjBound.exists_action_lt E H (Di i) g ty (P i bb) (Hm i bb) (a j₁) κ ((hBh i).1 bb hb).1 (hHm i bb hb)
        (hκ j₁)
    · exact (hBu i _ ((hBh i).1 z hz)).unique ⟨hb, hh⟩ ⟨hz, LinearEquiv.refl _ _, fun _ => rfl⟩
    · exact GlobalTheory.T.isPELObject_of_primitive_periodMap_uniformised L1 L2 hΘ hU E H D o g _ J b em w w' a bas ρ ty t (Di i) (fi i) (νi i) (P i bb) (Hm i bb)
        hpq hw hρ hty (hfam i).1 (hfam i).2 ((hBh i).1 bb hb) (hHm i bb hb) hu hp
  · obtain ⟨D', f, ν, Q, Hm', hgen, hζ, hper, hpol, hu⟩ :=
      GlobalTheory.T.exists_periods_complexPELObject L1 L2 hΘ hU E H D o g _ J b em w w' a bas ρ ty t hw hw' hρ hty ht
    obtain ⟨i, e, he, hef⟩ := hall D' f ν hgen hζ
    obtain ⟨bb, ⟨hb, h, hh⟩, -⟩ := hBu i _ (isPeriod_comp hper e he)
    refine ⟨i, bb, hb, ?_⟩
    refine UnifTransport.transport_uniformisation o g (N' ^ 2) J b em w w' t D'.La D'.EF
      (fun i₁ => f (N' ^ 2) (bas (Pi.single i₁ 1))) (fun j x => a j • x) Q Hm' (Di i).La (Di i).EF
      (fun i₁ => fi i (N' ^ 2) (bas (Pi.single i₁ 1))) (fun j x => a j • x) (P i bb) (Hm i bb) e.toAddEquiv h.symm
      hpol (hHm i bb hb) (fun x => ?_) he (fun j x => e.map_smul _ _) (fun i₁ => hef _) hu
    rw [LinearEquiv.eq_symm_apply, ← hh]
    exact congrArg Q (e.symm_apply_apply x)

end GlobalTheory.PelGood
