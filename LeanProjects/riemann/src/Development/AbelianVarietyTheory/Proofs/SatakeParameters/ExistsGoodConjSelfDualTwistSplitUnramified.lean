import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgebraicHeckeCharOfRegularAlgebraicPolarizedP
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicHeckeCharSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalTwistOfContragredientConjugateStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharUnrAtOfSphericalAndTwistSphericalStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharUnrAtUnderOfCompNormUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadraticHeckeCharUnramifiedOfIsUnramifiedAtStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section
namespace GlobalTheory.GoodCsdTwist

open GlobalTheory.ContraPair

theorem unrAt_mul {K : Type} [Field K] [NumberField K] {χ χ' : HChar K} {v : HeightOneSpectrum (𝓞 K)}
    (h : χ.UnrAt v) (h' : χ'.UnrAt v) : (χ * χ').UnrAt v := fun x hx => by
  change χ.loc v x * χ'.loc v x = 1
  rw [h x hx, h' x hx, mul_one]

theorem unrAt_inv {K : Type} [Field K] [NumberField K] {χ : HChar K} {v : HeightOneSpectrum (𝓞 K)}
    (h : χ.UnrAt v) : (χ⁻¹).UnrAt v := fun x hx => by
  change (χ.loc v x)⁻¹ = 1
  rw [h x hx, inv_one]

theorem unrAt_pow {K : Type} [Field K] [NumberField K] {χ : HChar K} {v : HeightOneSpectrum (𝓞 K)}
    (h : χ.UnrAt v) : ∀ k : ℕ, (χ ^ k).UnrAt v
  | 0 => fun _ _ => rfl
  | k + 1 => by rw [pow_succ]; exact unrAt_mul (unrAt_pow h k) h

theorem isAlgPos_mul {F : Type} [Field F] [NumberField F] {χ χ' : HChar F} {n n' : (F →+* ℂ) → ℤ}
    (h : IsAlgPos χ n) (h' : IsAlgPos χ' n') : IsAlgPos (χ * χ') (n + n') := fun k hk => by
  have e : (χ * χ').inf k = χ.inf k * χ'.inf k := rfl
  rw [e, Units.val_mul, h k hk, h' k hk, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun φ _ => (zpow_add₀ ((map_ne_zero φ).2 k.ne_zero) _ _).symm

theorem regAlg_twist {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {n : ℕ} {P : CuspSub K n}
    (h : (CG.mk P).IsRegAlg) {κ : HChar K} {m : (K →+* ℂ) → ℤ} (hκ : κ.IsAlg m) : (CG.mk (P.twist κ)).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
  have e := ((ParLaws.hasInfChar_infChar (CG.mk P) τ).twist κ).infChar_eq
  rw [CG.twist_mk] at e
  rw [e, (InfType.expo_of_infType K κ).1 m hκ τ]
  refine ⟨(h τ).1.map (add_left_injective _), fun z hz => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
  obtain ⟨k, rfl⟩ := (h τ).2 y hy
  exact ⟨k + m τ, by push_cast; ring⟩

theorem neg_one_zpow_natAbs (z : ℤ) : ((-1 : ℂˣ) ^ z.natAbs) = (-1 : ℂˣ) ^ (-z) := by
  rcases Int.even_or_odd z with h | h
  · rw [h.neg.neg_one_zpow, (Int.natAbs_even.2 h).neg_one_pow]
  · rw [h.neg.neg_one_zpow, (Int.natAbs_odd.2 h).neg_one_pow]

theorem exists_goodCsd_twist : AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), InScope .good l π χ → ∀ w₀ : HeightOneSpectrum (𝓞 E),
    GlobalTheory.UnitaryBC.IsSplitAt w₀ → ∃ (κ : HChar E) (m : (E →+* ℂ) → ℤ), κ.IsAlg m ∧ κ.UnrAt w₀ ∧
    InScope .csd l (π.twist κ) (quadChar E ^ a) := by
  intro _ E _ _ _ l a ha π χ ⟨hreg, hpol, hgood⟩ w₀ hw₀
  obtain ⟨n, hn⟩ := GlobalTheory.RegAlgCharAlg.isAlgPos_of_polarizedPair E a ha π χ hreg hpol
  obtain ⟨φ₀⟩ : Nonempty (maximalRealSubfield E →+* ℂ) := inferInstance
  have hb : IsAlgPos χ (fun _ => n φ₀) := by
    rw [show (fun _ => n φ₀) = n from funext fun φ => UpperTheory.heckeChar_parallel_weight _ χ n hn φ₀ φ]
    exact hn
  have hinv : IsAlgPos χ⁻¹ (fun _ => -n φ₀) := fun k hk => by
    rw [HChar.inf_inv, Units.val_inv_eq_inv_val, hb k hk, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun φ _ => (zpow_neg _ _).symm
  have ho : (quadChar E ^ (a + (n φ₀).natAbs)).OrderDvd 2 := by
    unfold HChar.OrderDvd
    rw [← pow_mul, mul_comm, pow_mul]
    have : (quadChar E) ^ 2 = 1 := by
      refine Subtype.ext (MonoidHom.ext fun x => ?_)
      change (Units.map (Int.castRingHom ℂ).toMonoidHom (GlobalTheory.IdeleNormChar.normSign E x)) ^ 2 = 1
      rw [← map_pow, Int.units_sq, map_one]
    rw [this, one_pow]
  have hpos := isAlgPos_mul hinv (isAlgPos_zero_of_orderDvd two_pos ho)
  rw [add_zero] at hpos
  have hsign : ∀ v, (χ⁻¹ * quadChar E ^ (a + (n φ₀).natAbs)).locInf v (-1) = (-1) ^ (-n φ₀) := fun v => by
    rw [HChar.locInf_mul, locInf_pow, quadChar_locInf]
    change (χ.locInf v (-1))⁻¹ * _ = _
    rw [hpol.sign v, pow_add, inv_mul_cancel_left, neg_one_zpow_natAbs]
  have halg := UpperTheory.heckeChar_algebraic_of_sign _ _ (-n φ₀) hpos hsign
  have hunr : ∀ w : HeightOneSpectrum (𝓞 E), ¬ GlobalTheory.UnitaryBC.IsSplitAt w →
      Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal ∧
      (χ⁻¹ * quadChar E ^ (a + (n φ₀).natAbs)).UnrAt (w.under (𝓞 (maximalRealSubfield E))) := fun w hw => by
    obtain ⟨-, hu, hsat⟩ := hgood.2.2 w hw
    have h1 := GlobalTheory.T.heckeChar_unrAt_of_spherical_and_twist_spherical E a ha π _ w hsat (GlobalTheory.T.isSpherical_twist_of_contragredient_conjugate E a ha π _ hpol.dual w hw hsat)
    replace h1 := unrAt_inv h1
    rw [inv_inv] at h1
    exact ⟨hu, unrAt_mul (unrAt_inv (GlobalTheory.T.heckeChar_unrAt_under_of_compNorm_unramified E χ w hw hu h1)) (unrAt_pow (GlobalTheory.T.quadraticHeckeChar_unramified_of_isUnramifiedAt E w hu) _)⟩
  obtain ⟨κ, m, hκ, hres, hκ0, hκu⟩ := GlobalTheory.T.exists_algebraic_hecke_char_split E _ (-n φ₀) halg hunr w₀ hw₀
  refine ⟨κ, m, hκ, hκ0, regAlg_twist hreg hκ, ⟨fun v => ?_, ?_⟩, ⟨hgood.1, hgood.2.1, fun w hw => ?_⟩, rfl⟩
  · rw [locInf_pow, quadChar_locInf]
  · rw [map_pow, compNorm_quadChar, one_pow, dualIsConjBy_one]
    exact UpperTheory.V.Af.Cq.csdTwist E a π _ κ hpol.dual
      (by rw [hres, map_mul, map_inv, map_pow, compNorm_quadChar, one_pow, mul_one])
  · obtain ⟨h1, h2, B, hB⟩ := hgood.2.2 w hw
    refine ⟨h1, h2, B.map (· * κ.val w), ?_⟩
    rw [CG.hasSat_mk] at hB ⊢
    exact GlobalTheory.SphGal.hasSatGL_twist E a π κ w B (hκu w hw) hB

end GlobalTheory.GoodCsdTwist
