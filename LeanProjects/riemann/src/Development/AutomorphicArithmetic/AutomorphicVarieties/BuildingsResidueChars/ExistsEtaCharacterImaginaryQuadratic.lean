import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.AdjointEta.EtaOK
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GluePlaces
import GroundTheory.GlobalFields.GlobalReciprocity.General
import GroundTheory.GlobalFields.ClassFieldConsequences.RayClassFieldLocal

section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Z.Gam
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.SemiLocal
open scoped Classical

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad.Eta

private theorem count_one {A : Type} [CommGroup A] (U : Subgroup A) (l : ℕ) (hl : l.Prime) (η θ : A →* ℂˣ)
    (hη : ∀ x, η x ^ l = 1) (hθ : ∀ x ∈ U, η x = 1 → θ x = 1) (u : A) (hu : u ∈ U) (h1 : η u ≠ 1) :
    ((Finset.range l).filter fun j => ∀ x ∈ U, θ x * η x ^ j = 1).card = 1 := by
  haveI : Fact l.Prime := ⟨hl⟩
  haveI : NeZero l := ⟨hl.ne_zero⟩
  have hp : IsPrimitiveRoot (η u) l := by
    rw [← orderOf_eq_prime (hη u) h1]
    exact IsPrimitiveRoot.orderOf _
  have h2 : (θ u)⁻¹ ∈ rootsOfUnity l ℂ := by
    rw [mem_rootsOfUnity, inv_pow, ← map_pow, hθ _ (U.pow_mem hu l) (by rw [map_pow, hη]), inv_one]
  obtain ⟨j, hj, e⟩ := hp.eq_pow_of_mem_rootsOfUnity h2
  rw [Finset.card_eq_one]
  refine ⟨j, Finset.eq_singleton_iff_unique_mem.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, fun x hx => ?_⟩, fun i hi => ?_⟩⟩
  · obtain ⟨m, -, hm⟩ := hp.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity l (η x)).2 (hη x))
    have h3 := hθ (x * (u ^ m)⁻¹) (U.mul_mem hx (U.inv_mem (U.pow_mem hu m)))
      (by rw [map_mul, map_inv, map_pow, hm, mul_inv_cancel])
    rw [map_mul, map_inv, mul_inv_eq_one, map_pow] at h3
    rw [h3, ← hm, ← pow_mul, mul_comm m, pow_mul, e, ← mul_pow, mul_inv_cancel, one_pow]
  · obtain ⟨hi, h⟩ := Finset.mem_filter.1 hi
    refine hp.pow_inj (Finset.mem_range.1 hi) hj ?_
    rw [e]
    exact (eq_inv_of_mul_eq_one_right (h u hu))

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] {v : HeightOneSpectrum (𝓞 K)}

private theorem fdeg_eq (w : PlacesOver L v) : fdeg w = w.1.asIdeal.inertiaDeg (𝓞 K) := by
  have := w.1.isMaximal
  have := v.isMaximal
  exact Ideal.inertiaDeg'_eq_inertiaDeg _ _

private theorem fdeg_pos (w : PlacesOver L v) : 0 < fdeg w := by
  have := w.1.isPrime
  rw [fdeg_eq]
  exact Ideal.inertiaDeg_pos _ _

private theorem ord_nm (w : PlacesOver L v) (x : (w.1.adicCompletion L)ˣ) :
    ord ((nm w x : (v.adicCompletion K)ˣ) : v.adicCompletion K) = fdeg w * ord (x : w.1.adicCompletion L) := by
  rw [fdeg_eq, ← inertiaDeg_integer v w.1]
  exact ord_norm (x : w.1.adicCompletion L)

private theorem unr_iff (θ : (v.adicCompletion K)ˣ →* ℂˣ) :
    IsUnram θ ↔ ∀ x ∈ unitFiltrationUnits (v.adicCompletion K) 0, θ x = 1 :=
  forall_congr' fun _ => by rw [mem_unitFiltrationUnits_zero_iff]

private theorem unr_nm (w : PlacesOver L v) (θ : (v.adicCompletion K)ˣ →* ℂˣ) :
    IsUnram (θ.comp (nm w)) ↔ ∀ x ∈ unitFiltrationUnits (v.adicCompletion K) 0, x ∈ (nm w).range → θ x = 1 := by
  rw [unr_iff]
  constructor
  · rintro h _ hx ⟨y, rfl⟩
    refine h y ?_
    rw [← ord_eq_zero_iff_mem, ord_nm] at hx
    exact ord_eq_zero_iff_mem.1 ((mul_eq_zero.1 hx).resolve_left (by exact_mod_cast (fdeg_pos w).ne'))
  · intro h y hy
    refine h _ ?_ ⟨y, rfl⟩
    rw [← ord_eq_zero_iff_mem, ord_nm, ord_eq_zero_iff_mem.2 hy, mul_zero]

private theorem sum_ef (v : HeightOneSpectrum (𝓞 K)) :
    ∑ w : PlacesOver L v, w.1.asIdeal.ramificationIdx (𝓞 K) * fdeg w = Module.finrank K L := by
  have := v.isMaximal
  rw [Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 K) K (𝓞 L) L,
    ← Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 L)]
  exact Fintype.sum_equiv (placesOverEquiv L v) _ _ fun w => by rw [fdeg_eq]; rfl

private theorem gal_e [IsGalois K L] (w w' : PlacesOver L v) :
    w.1.asIdeal.ramificationIdx (𝓞 K) = w'.1.asIdeal.ramificationIdx (𝓞 K) ∧ fdeg w = fdeg w' := by
  have := w.1.isPrime
  have := w'.1.isPrime
  have hw : w.1.asIdeal.LiesOver v.asIdeal := w.2
  have e : w.1.asIdeal.under (𝓞 K) = w'.1.asIdeal.under (𝓞 K) := w.2.over.symm.trans w'.2.over
  obtain ⟨σ, hσ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 K) (𝓞 L) (L ≃ₐ[K] L) _ _ e
  rw [fdeg_eq, fdeg_eq, hσ]
  exact ⟨(Ideal.ramificationIdx_smul _ _ σ).symm, (Ideal.inertiaDeg_smul _ _ σ).symm⟩

private theorem prim (η : HChar K) (w : PlacesOver L v) (hk : (η.loc v).ker = (nm w).range)
    (hu : unitFiltrationUnits (v.adicCompletion K) 0 ≤ (η.loc v).ker) :
    η.UnrAt v ∧ IsPrimitiveRoot (η.val v) (fdeg w) := by
  have h1 : η.UnrAt v := fun x hx => hu (mem_unitFiltrationUnits_zero_iff_valued.2 hx)
  obtain ⟨π, hπ, hπ'⟩ := exists_ord_eq_one_valued v
  obtain ⟨ϖ, hϖ⟩ := exists_ord_eq_one_units (w.1.adicCompletion L)
  refine ⟨h1, ?_⟩
  rw [← η.val_eq h1 π hπ']
  constructor
  · have h2 : π ^ (fdeg w : ℤ) * (nm w ϖ)⁻¹ ∈ (η.loc v).ker := by
      apply hu
      rw [← ord_eq_zero_iff_mem, Units.val_mul, ord_mul (Units.ne_zero _) (Units.ne_zero _), ← map_inv, ord_nm,
        ord_zpow_units hπ, ← zpow_neg_one, ord_zpow_units hϖ]
      ring
    have h3 : nm w ϖ ∈ (η.loc v).ker := hk ▸ ⟨ϖ, rfl⟩
    rw [MonoidHom.mem_ker] at h2 h3
    rwa [map_mul, map_inv, h3, inv_one, mul_one, zpow_natCast, map_pow] at h2
  · intro m hm
    rw [← map_pow, ← MonoidHom.mem_ker, hk] at hm
    obtain ⟨y, hy⟩ := hm
    have h4 := ord_nm w y
    rw [hy, ← zpow_natCast, ord_zpow_units hπ] at h4
    exact Int.natCast_dvd_natCast.1 ⟨_, h4⟩

private theorem sym_props [IsAbelianGalois K L] (η : HChar K) (ι : (L ≃ₐ[K] L) →* ℂˣ) (hι : Function.Injective ι)
    (v : HeightOneSpectrum (𝓞 K)) (e : η.loc v = ι.comp (localSymbol L v)) :
    (∀ x, η.loc v x ^ Module.finrank K L = 1) ∧
      ∀ w : PlacesOver L v, (η.loc v).ker = (nm w).range ∧
        (unitFiltrationUnits (v.adicCompletion K) 0 ≤ (nm w).range ↔ w.1.asIdeal.ramificationIdx (𝓞 K) = 1) := by
  have hc : Nat.card (L ≃ₐ[K] L) = Module.finrank K L := IsGalois.card_aut_eq_finrank K L
  rw [e]
  refine ⟨fun x => by rw [MonoidHom.comp_apply, ← map_pow, ← hc, pow_card_eq_one', map_one], fun w => ?_⟩
  have hk : (localSymbol L v).ker = (nm w).range := ker_localSymbol L v w
  refine ⟨by rw [MonoidHom.ker_comp_of_injective _ _ hι, hk], ?_⟩
  rw [← hk]
  refine ⟨fun h => ramificationIdx_eq_one_of_units_le_ker_localSymbol v h w.1, fun h x hx => ?_⟩
  refine units_le_ker_localSymbol L v w h ?_
  have h1 := mem_unitFiltrationUnits_zero_iff_valued.1 hx
  have h2 := mem_unitFiltrationUnits_zero_iff_valued.1 (inv_mem hx)
  exact (Submonoid.mem_units_iff _ _).2 ⟨h1.le, h2.le⟩

private theorem loc_pow (η : HChar K) (j : ℕ) (x : (v.adicCompletion K)ˣ) : (η ^ j).loc v x = η.loc v x ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, HChar.loc_mul, ih, pow_succ]

private theorem cnt_of [IsGalois K L] (hl : (Module.finrank K L).Prime) (η : HChar K)
    (hη : ∀ v : HeightOneSpectrum (𝓞 K), (∀ x, η.loc v x ^ Module.finrank K L = 1) ∧
      ∀ w : PlacesOver L v, (η.loc v).ker = (nm w).range ∧
        (unitFiltrationUnits (v.adicCompletion K) 0 ≤ (nm w).range ↔ w.1.asIdeal.ramificationIdx (𝓞 K) = 1)) :
    (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, η.UnrAt v ∧ ∀ w : PlacesOver L v,
        IsPrimitiveRoot (η.val v) (fdeg w) ∧ Fintype.card (PlacesOver L v) * fdeg w = Module.finrank K L) ∧
      ∀ (v : HeightOneSpectrum (𝓞 K)) (w : PlacesOver L v), (η.loc v).comp (nm w) = 1 ∧
        (∀ (w' : PlacesOver L v) (θ : (v.adicCompletion K)ˣ →* ℂˣ), IsUnram (θ.comp (nm w)) → IsUnram (θ.comp (nm w'))) ∧
        ∀ θ : (v.adicCompletion K)ˣ →* ℂˣ, IsSmoothChar θ → IsSmoothChar (θ.comp (nm w)) ∧ (IsUnram θ → IsUnram (θ.comp (nm w))) ∧
          (IsUnram (θ.comp (nm w)) → ((Finset.range (Module.finrank K L)).filter fun j => IsUnram (θ * (η ^ j).loc v)).card =
            ∑ w' : PlacesOver L v, fdeg w') := by
  refine ⟨?_, fun v w => ?_⟩
  · filter_upwards [IdeleNorm.eventually_forall_placesOver K (IdeleNorm.eventually_ramificationIdx_eq_one K L)] with v hv
    have h := fun w : PlacesOver L v =>
      prim η w ((hη v).2 w).1 (by rw [((hη v).2 w).1]; exact ((hη v).2 w).2.2 (hv w))
    obtain ⟨w₀⟩ := nonempty_placesOver L v
    refine ⟨(h w₀).1, fun w => ⟨(h w).2, ?_⟩⟩
    rw [← sum_ef v, Finset.sum_congr rfl fun w' _ => show _ = fdeg w by rw [hv w', one_mul, (gal_e w' w).2]]
    simp
  obtain ⟨hp, hw⟩ := hη v
  refine ⟨MonoidHom.ext fun y => ?_, fun w' θ h => ?_, fun θ hθ => ⟨?_, fun h => ?_, fun h => ?_⟩⟩
  · exact ((hw w).1.ge ⟨y, rfl⟩ :)
  · have h1 := (unr_nm w θ).1 h
    rw [← (hw w).1, (hw w').1] at h1
    exact (unr_nm w' θ).2 h1
  · unfold IsSmoothChar at hθ ⊢
    rw [← MonoidHom.comap_ker]
    exact hθ.preimage (continuous_normUnits (K := v.adicCompletion K) (L := w.1.adicCompletion L))
  · exact (unr_nm w θ).2 fun x hx _ => (unr_iff θ).1 h x hx
  have h1 := (unr_nm w θ).1 h
  have e : ∀ j : ℕ, IsUnram (θ * (η ^ j).loc v) ↔
      ∀ x ∈ unitFiltrationUnits (v.adicCompletion K) 0, θ x * η.loc v x ^ j = 1 := fun j => by
    rw [unr_iff]
    simp only [MonoidHom.mul_apply, loc_pow]
  have hs : w.1.asIdeal.ramificationIdx (𝓞 K) * ∑ w' : PlacesOver L v, fdeg w' = Module.finrank K L := by
    rw [← sum_ef v, Finset.mul_sum]
    exact Finset.sum_congr rfl fun w' _ => by rw [(gal_e w w').1]
  refine (congrArg Finset.card (Finset.filter_congr fun j _ => e j)).trans ?_
  by_cases hr : w.1.asIdeal.ramificationIdx (𝓞 K) = 1
  · rw [hr, one_mul] at hs
    rw [hs, Finset.filter_true_of_mem, Finset.card_range]
    intro j _ x hx
    have h2 := (hw w).2.2 hr hx
    rw [h1 x hx h2, show η.loc v x = 1 from (hw w).1.ge h2, one_pow, one_mul]
  · obtain ⟨u, hu, hu'⟩ := SetLike.not_le_iff_exists.1 (mt (hw w).2.1 hr)
    rw [← (hw w).1] at hu' h1
    rw [← hs] at hl
    have h3 := ((Nat.prime_mul_iff.1 hl).resolve_right fun h => hr h.2).2
    rw [hs] at hl
    rw [h3]
    convert count_one _ _ hl (η.loc v) θ hp h1 u hu hu'

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad.Eta

end

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SmGL
open UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GlobalTheory.HenQ UpperTheory.V.Z.Inf UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar)
open Ad3P.DihedralUnramifiedPlaces (toH)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

theorem UpperTheory.exists_eta_character_imaginary_quadratic :
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∃ η : HeckeCharacter ℚ, EtaOK K η := by
  intro K _ _ _ h2
  haveI : Algebra.IsQuadraticExtension ℚ K := { finrank_eq_two' := h2 }
  have hι : Function.Injective (Quadratic.galChar K) := by
    refine (injective_iff_map_eq_one _).2 fun σ hσ => ?_
    by_contra h
    have h3 := GlobalTheory.CompanionTheory.GlueSign.galChar_val K σ
    rw [hσ, if_neg h] at h3
    norm_num at h3
  have h := Eta.cnt_of (K := ℚ) (L := K) (h2 ▸ Nat.prime_two) (toH (Quadratic.heckeChar K)) fun v =>
    Eta.sym_props _ _ hι v (MonoidHom.ext fun x => Units.ext (GlobalTheory.CompanionTheory.GlueSign.localChar_apply K v x))
  rw [h2] at h
  refine ⟨Quadratic.heckeChar K, ?_, GlobalTheory.CompanionTheory.GlueSign.infiniteComponent_neg_one K, h.1, h.2⟩
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨2, two_pos, ?_⟩
  rw [pow_two, mul_eq_one_iff_eq_inv, GlobalTheory.CompanionTheory.GlueSign.heckeChar_inv]
