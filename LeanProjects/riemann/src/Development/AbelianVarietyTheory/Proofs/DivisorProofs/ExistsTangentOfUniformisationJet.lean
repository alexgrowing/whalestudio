import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicPointExtOfIsSeparated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalAtFnEqValAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalAtNatural
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecMapValHomFromSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFirstOrderJetAlgHom
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AnPer

theorem exists_tangent_of_jet : ∀ {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g), A.left.IsSeparated → ∀ (W : Opens (Tot Empty g)) (x : Sp (Hol W) ⟶ A.left), (∀ (p : Tot Empty g) (hp : p ∈ W), spMap (Hol.ev p hp).toRingHom ≫ x = (u.ex p.2).left) → x ≫ A.hom = spMap (algebraMap ℂ (Hol W)) → (0 : Tot Empty g) ∈ W → ∀ (w : Fin g → ℂ) (ρ : Hol W →ₐ[ℂ] DualNumber ℂ), (∀ h, (ρ h).fst = h.fn 0 ∧ (ρ h).snd = fderiv ℂ h.fn 0 (0, w)) → ∃ v : epsR ℂ ⟶ A, v.left = spMap ρ.toRingHom ≫ x ∧ IsTangent v ∧ u.IsDiff w v := by
  intro A _ L g u hsep W x hx hxA h0 w ρ hρ
  have hw : (spMap ρ.toRingHom ≫ x) ≫ A.hom = spMap (algebraMap ℂ (DualNumber ℂ)) := by
    rw [Category.assoc, hxA, ← Cris.spMap_comp]
    congr 1
    exact RingHom.ext fun c ↦ ρ.commutes c
  have hfst : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap ρ.toRingHom ≫ x = (u.ex 0).left := by
    have e : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp ρ.toRingHom = (Hol.ev 0 h0).toRingHom :=
      RingHom.ext fun f ↦ (hρ f).1.trans (Hol.ev_apply 0 h0 f).symm
    rw [← Category.assoc, ← Cris.spMap_comp, e]
    exact hx 0 h0
  refine ⟨Over.homMk (spMap ρ.toRingHom ≫ x) hw, rfl, ?_, ?_⟩
  · change spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap ρ.toRingHom ≫ x = _
    rw [hfst, (u.ker 0).2 u.Λ.zero_mem, Hom.one_def, toUnit_unit, Category.id_comp]
  · intro U h f
    change ⊤ ≤ (spMap ρ.toRingHom ≫ x) ⁻¹ᵁ U at h
    change (evalAt (spMap ρ.toRingHom ≫ x) U h f).snd = _
    have hU0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := by
      rw [← hfst]
      exact fun q _ ↦ h (Set.mem_univ ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) q))
    let q₀ : Sp ℂ := (default : PrimeSpectrum ℂ)
    obtain ⟨U', hU', hq, hle⟩ := exists_isAffineOpen_mem_and_subset
      (x := (u.ex 0).left q₀) (U := U) (hU0 (Set.mem_univ q₀))
    have hU0' : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U' := fun q _ ↦ by
      have : q = q₀ := Subsingleton.elim (α := PrimeSpectrum ℂ) q q₀
      subst this
      exact hq
    let W' : Opens (Tot Empty g) :=
      W ⊓ ⟨{p | ⊤ ≤ (u.ex p.2).left ⁻¹ᵁ U'}, (u.hol U' 0).1.preimage continuous_snd⟩
    have h0' : (0 : Tot Empty g) ∈ W' := ⟨h0, hU0'⟩
    obtain ⟨x', hx'U, hx'⟩ := exists_pt_of_affine (fibUnif u) W' (fun _ _ ↦ trivial) U' hU' (fun p hp ↦ hp.2)
    let res : Hol W →ₐ[ℂ] Hol W' := Hol.comap id analyticOnNhd_id fun p hp ↦ hp.1
    have hres : ∀ (k : Hol W), ∀ p ∈ W', (res k).fn p = k.fn p := fun k p hp ↦ Hol.fn_comap _ _ _ k hp
    have hxx : spMap res.toRingHom ≫ x = x' := by
      refine point_hol_ext_of_isSeparated W' hsep _ _ fun p hp ↦ ?_
      have e : (Hol.ev p hp).toRingHom.comp res.toRingHom = (Hol.ev p hp.1).toRingHom :=
        RingHom.ext fun _ ↦ rfl
      rw [hx' p hp, ← Category.assoc, ← Cris.spMap_comp, e]
      exact hx p hp.1
    obtain ⟨ρ', hρ'⟩ := Hol.exists_jet_algHom W' 0 h0' ((0, w) : Tot Empty g)
    have hρρ : ρ'.toRingHom.comp res.toRingHom = ρ.toRingHom := RingHom.ext fun k ↦ by
      change ρ' (res k) = ρ k
      refine TrivSqZeroExt.ext ?_ ?_
      · rw [(hρ' _).1, (hρ _).1, hres k 0 h0']
      · rw [(hρ' _).2, (hρ _).2, Hol.fderiv_fn_congr _ (hres k) h0']
    have hv : spMap ρ.toRingHom ≫ x = spMap ρ'.toRingHom ≫ x' := by
      rw [← hρρ, Cris.spMap_comp, Category.assoc, hxx]
    have hx'U' : ⊤ ≤ x' ⁻¹ᵁ U := fun q hq ↦ hle (hx'U hq)
    obtain ⟨h', hev, -⟩ := GlobalTheory.EvalNat.evalAt_natural ρ'.toRingHom x' U hx'U'
    have e1 : evalAt (spMap ρ.toRingHom ≫ x) U h f = ρ' (evalAt x' U hx'U' f) := by
      refine Eq.trans ?_ (hev f)
      congr 2
    have e2 : ∀ p ∈ W', (evalAt x' U hx'U' f).fn p = valAt' (u.ex p.2).left U f := fun p hp ↦ by
      rw [(evalAt_fn_eq_valAt' W' x' U hx'U' f p hp).2, hx' p hp]
      rfl
    have hd : DifferentiableAt ℂ (fun z ↦ valAt' (u.ex z).left U f) 0 :=
      (u.hol U f).2.differentiableAt ((u.hol U f).1.mem_nhds hU0)
    rw [e1, (hρ' _).2, Hol.fderiv_fn_congr _ e2 h0']
    have hc : HasFDerivAt (fun p : Tot Empty g ↦ valAt' (u.ex p.2).left U f)
        ((fderiv ℂ (fun z ↦ valAt' (u.ex z).left U f) 0).comp (ContinuousLinearMap.snd ℂ _ _)) 0 :=
      HasFDerivAt.comp (0 : Tot Empty g) (g := fun z ↦ valAt' (u.ex z).left U f) (f := Prod.snd)
        hd.hasFDerivAt hasFDerivAt_snd
    rw [hc.fderiv]
    rfl

end GlobalTheory.AnPer
