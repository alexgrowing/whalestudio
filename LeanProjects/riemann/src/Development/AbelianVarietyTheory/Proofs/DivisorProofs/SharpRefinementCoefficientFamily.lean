import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaIdealFamilyUniversalProperty
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenericObjectMinimalPrimeModuliChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidificationPullbackCompatibleIso
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedThetaConstantEqScalarRootMulUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorThetaConstantsFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem fibre_theta_consts_in_subfield : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ : ℕ) (J : Type) (l : ℕ), l.Prime → Odd l → ∀ j : ℕ, 1 ≤ j →
  ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) →
  ∀ (Q : Data V), Q.g = gQ → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X),
  SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁),
  (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) →
  ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
  (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) →
  ∀ (bT : TBase k₀ ((l ^ j) ^ 2)) (t : TObj (8 * gQ) ((l ^ j) ^ 2) J bT (spMap k₀.subtype))
    (ψ : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ t.A.left),
    IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) t.A (𝟙 _) ψ →
    LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (t.L.pull ψ) →
    ∃ v : Ix (8 * gQ) ((l ^ j) ^ 2) → k₀, t.HasTh (𝟙 _) (fun a => k₀.subtype (v a)) := by
  intro W _ gQ J l hl hlo j hj V V₁ _ _ _ _ _ hCN hlu Q _ ρ _ D e _ C u mo hmo hT K _ _ ev k₀ hk₀ hrat bT t ψ hψ hL
  haveI : IsAlgClosed k₀ := hk₀
  obtain ⟨v₀, hv₀⟩ := GlobalTheory.FamRep.exists_hasTh_field GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 hlo.pow t K (𝟙 _)
  obtain ⟨th, κ, hth, hκ, hy⟩ := GlobalTheory.T.exists_generator_thetaConstants_fibre V₁ D K ev k₀ (8 * gQ) (l ^ j) J bT _ t ψ hψ hL v₀ hv₀
  obtain ⟨M, lam, hM, hA⟩ := GlobalTheory.T.normalisedThetaConstant_eq_scalar_root_mul_unit l hl hlo j hj V₁ hCN hlu D _ C e u mo hmo hT K ev D.rig D.rig_gen th hth
  obtain ⟨c', hc'⟩ := (hmo 0).2
  have hev : ev (u 0 c') ≠ 0 := (hc'.map ev).ne_zero
  have key : ∀ a, ∃ w : K, w ∈ k₀ ∧ κ * v₀ a = lam * ev (u 0 c') * w := by
    intro a
    obtain ⟨y, hya⟩ := hy a
    obtain ⟨c₀, ζ, hζ, hc⟩ := hA y _ hya
    obtain ⟨r, hr, hr'⟩ := hrat 0 c₀ c' hc'
    have hζk : ζ ∈ k₀ := Frames.mem_of_pow_mem k₀ hM (by rw [hζ]; exact k₀.one_mem)
    exact ⟨ζ * r, k₀.mul_mem hζk hr, by rw [hc, hr']; ring⟩
  choose w hw hkw using key
  by_cases hlam : lam = 0
  · refine ⟨fun _ => 0, ?_⟩
    refine GlobalTheory.GenericObject.hasTh_unit_mul t (𝟙 _) v₀ _ 1 isUnit_one (fun a => ?_) hv₀
    have := hkw a
    rw [hlam, zero_mul, zero_mul] at this
    simp [(mul_eq_zero.1 this).resolve_left hκ]
  · refine ⟨fun a => ⟨w a, hw a⟩, ?_⟩
    refine GlobalTheory.GenericObject.hasTh_unit_mul t (𝟙 _) v₀ _ ((lam * ev (u 0 c'))⁻¹ * κ)
      (IsUnit.mk0 _ (mul_ne_zero (inv_ne_zero (mul_ne_zero hlam hev)) hκ)) (fun a => ?_) hv₀
    show w a = _
    rw [_root_.mul_assoc, hkw a, ← _root_.mul_assoc, inv_mul_cancel₀ (mul_ne_zero hlam hev), _root_.one_mul]

end GlobalTheory.Poinc.Sep
