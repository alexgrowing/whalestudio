import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LtSeries
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPlaceEmb
import GroundTheory.LocalFields.KroneckerWeber
import GroundTheory.LocalFields.LubinTateLimitGalois
import GroundTheory.LocalFields.MaximalUnramified

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup

namespace GlobalTheory.PZ.LTExist

section Abstract

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem finrank_inf_maximalUnramifiedExtension {Ω : Type} [Field Ω] [Algebra K Ω] [IsSepClosed Ω]
    [IsGalois K Ω] (L : IntermediateField K Ω) [FiniteDimensional K L]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L] :
    Module.finrank K ↥(L ⊓ maximalUnramifiedExtension K Ω) = residueDegree K L := by
  set H : Subgroup (Ω ≃ₐ[K] Ω) := L.fixingSubgroup ⊔ (maximalUnramifiedExtension K Ω).fixingSubgroup with hH
  have hopen : IsOpen (H : Set (Ω ≃ₐ[K] Ω)) :=
    Subgroup.isOpen_mono le_sup_left L.fixingSubgroup_isOpen
  have hfix : IntermediateField.fixedField H = L ⊓ maximalUnramifiedExtension K Ω := by
    apply le_antisymm
    · refine le_inf ?_ ?_
      · conv_rhs => rw [← InfiniteGalois.fixedField_fixingSubgroup L]
        exact IntermediateField.fixedField_le le_sup_left
      · conv_rhs => rw [← InfiniteGalois.fixedField_fixingSubgroup (maximalUnramifiedExtension K Ω)]
        exact IntermediateField.fixedField_le le_sup_right
    · rw [IntermediateField.le_iff_le]
      exact sup_le (IntermediateField.fixingSubgroup_antitone inf_le_left)
        (IntermediateField.fixingSubgroup_antitone inf_le_right)
  have h2 : (IntermediateField.fixedField H).fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨H, H.isClosed_of_isOpen hopen⟩
  rw [IntermediateField.finrank_eq_fixingSubgroup_index, ← hfix, h2, hH, ← ker_unramifiedDegree,
    ← Subgroup.comap_map_eq, Subgroup.index_comap_of_surjective _ unramifiedDegree_surjective]
  exact inertiaDegree_unramifiedDegree_fixingSubgroup L

variable {Ω : Type} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω]

theorem exists_system {F : Type} [Field F] [IsAlgClosed F] {c : F} (hc : c ≠ 0) {q : ℕ} (hq : 1 < q) :
    ∃ z : ℕ → F, z 0 = 0 ∧ z 1 ≠ 0 ∧ ∀ n, c * z (n + 1) + z (n + 1) ^ q = z n := by
  have hstep : ∀ y : F, ∃ x : F, c * x + x ^ q = y := by
    intro y
    have hdeg : (Polynomial.X ^ q + (Polynomial.C c * Polynomial.X - Polynomial.C y) : Polynomial F).degree = q := by
      rw [Polynomial.degree_add_eq_left_of_degree_lt] <;> rw [Polynomial.degree_X_pow]
      refine lt_of_le_of_lt (b := 1) ?_ (by exact_mod_cast hq)
      compute_degree
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ (hdeg.trans_ne (by exact_mod_cast (by omega : q ≠ 0)))
    refine ⟨x, ?_⟩
    simp only [Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C] at hx
    linear_combination hx
  choose s hs using hstep
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (-c) (n := q - 1) (by omega)
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hx
    exact hc (neg_eq_zero.mp hx.symm)
  refine ⟨fun n => match n with | 0 => 0 | n + 1 => s^[n] x, rfl, hx0, fun n => ?_⟩
  cases n with
  | zero =>
    change c * x + x ^ q = 0
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    rw [Nat.add_sub_cancel] at hx
    rw [pow_succ, hx]; ring
  | succ n =>
    change c * s^[n + 1] x + s^[n + 1] x ^ q = s^[n] x
    rw [Function.iterate_succ_apply', hs]

theorem exists_data {π : 𝒪[K]} (hπ : Irreducible π) :
    ∃ (χ : (Ω ≃ₐ[K] Ω) →* (𝒪[K])ˣ) (z : ℕ → Ω), z 0 = 0 ∧ z 1 ≠ 0 ∧
      (∀ n, algebraMap K Ω (π : K) * z (n + 1) + z (n + 1) ^ Nat.card 𝓀[K] = z n) ∧
      ∀ g : Ω ≃ₐ[K] Ω, ∃ φ : PowerSeries 𝒪[K], PowerSeries.constantCoeff φ = 0 ∧
        PowerSeries.coeff 1 φ = (χ g : 𝒪[K]) ∧
        PowerSeries.C π * φ + φ ^ Nat.card 𝓀[K] =
          PowerSeries.subst (PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ Nat.card 𝓀[K] :
            PowerSeries 𝒪[K]) φ ∧
        ∀ n, HasSum (fun k => algebraMap K Ω ((PowerSeries.coeff k φ : 𝒪[K]) : K) * z n ^ k)
          (g (z n)) := by
  have hπ0 : algebraMap K Ω (π : K) ≠ 0 := by
    rw [map_ne_zero]
    exact fun h => hπ.ne_zero (Subtype.ext h)
  obtain ⟨z, hz0, hz1, hz⟩ := exists_system hπ0 (one_lt_card_residueField' K)
  have hf := isLubinTateSeries_ltPoly π
  have hit : ∀ m n, Polynomial.aeval (z (n + m)) ((ltPolyIter π m).map (algebraMap 𝒪[K] K)) = z n := by
    intro m
    induction m with
    | zero => intro n; simp [ltPolyIter_zero]
    | succ m ih =>
      intro n
      rw [ltPolyIter_succ, Polynomial.map_comp, Polynomial.aeval_comp,
        show n + (m + 1) = (n + 1) + m by ring, ih, aeval_ltPoly, hz]
  have hroot : ∀ n, Polynomial.aeval (z n) ((ltPolyIter π n).map (algebraMap 𝒪[K] K)) = 0 := by
    intro n
    have := hit n 0
    rwa [zero_add, hz0] at this
  have hval : ∀ n, valuation Ω (z n) < 1 := fun n =>
    valuation_lt_one_of_aeval_ltPolyIter_eq_zero hπ n (hroot n)
  let e := lubinTateLimitGalEquiv (Ω := Ω) hπ hf
  let χ : (Ω ≃ₐ[K] Ω) →* (𝒪[K])ˣ :=
    e.toMulEquiv.symm.toMonoidHom.comp (AlgEquiv.restrictNormalHom (lubinTateLimit Ω hπ))
  have hpoly : ((ltPoly π : Polynomial 𝒪[K]) : PowerSeries 𝒪[K]) =
      PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ Nat.card 𝓀[K] := by
    simp [ltPoly, Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_pow]
  refine ⟨χ, z, hz0, hz1, hz, fun g => ?_⟩
  set φ := (lubinTateHom hπ hf hf (χ g : 𝒪[K])).toPowerSeries with hφ
  have h0 : PowerSeries.constantCoeff φ = 0 := (lubinTateHom hπ hf hf (χ g : 𝒪[K])).constantCoeff_eq_zero
  refine ⟨φ, h0, coeff_one_lubinTateHom hπ hf hf _, ?_, fun n => ?_⟩
  · have h := subst_lubinTateHom hπ hf hf (χ g : 𝒪[K])
    rw [← hφ, hpoly] at h
    rw [← h]
    have hs : PowerSeries.HasSubst φ := PowerSeries.HasSubst.of_constantCoeff_zero' h0
    rw [PowerSeries.subst_add hs, PowerSeries.subst_pow hs, PowerSeries.subst_X hs,
      powerSeries_subst_C_mul_X hs]
    rfl
  · let x : IdealPoint Ω (lubinTateFormalGroup hπ hf) := IdealPoint.mk (z n) (hval n)
    have hx : x ∈ lubinTateTorsion Ω hf n := (mem_lubinTateTorsion_ltPoly_iff n x).mpr (hroot n)
    have h1 := lubinTateLimitGalEquiv_apply hπ hf (χ g) hx
    have h2 : lubinTateLimitGalEquiv (Ω := Ω) hπ hf (χ g) =
        AlgEquiv.restrictNormalHom (lubinTateLimit Ω hπ) g := e.toMulEquiv.apply_symm_apply _
    rw [h2, AlgEquiv.restrictNormalHom_apply, lubinTate_smul_val] at h1
    change g (z n) = psEval φ (fun _ => z n) at h1
    rw [h1]
    have h3 := hasSum_psEval' (K := K) (σ := Unit) φ (fun _ => z n) (fun _ => hval n)
    let ι : ℕ ≃ (Unit →₀ ℕ) := (Finsupp.equivFunOnFinite.trans (Equiv.funUnique Unit ℕ)).symm
    rw [← ι.hasSum_iff] at h3
    convert h3 using 1
    funext k
    have hk : ι k = Finsupp.single () k := by
      ext
      simp [ι]
    simp only [Function.comp, psTerm, hk, Finsupp.prod_single_index, pow_zero]
    rfl

end Abstract

theorem map_endo {R S : Type} [CommRing R] [CommRing S] (ρ : R →+* S) {q : ℕ} (hq : q ≠ 0) {c a : R}
    {φ : PowerSeries R} (h0 : PowerSeries.constantCoeff φ = 0) (h1 : PowerSeries.coeff 1 φ = a)
    (h2 : PowerSeries.C c * φ + φ ^ q =
      PowerSeries.subst (PowerSeries.C c * PowerSeries.X + PowerSeries.X ^ q : PowerSeries R) φ) :
    PowerSeries.constantCoeff (PowerSeries.map ρ φ) = 0 ∧
      PowerSeries.coeff 1 (PowerSeries.map ρ φ) = ρ a ∧
      PowerSeries.C (ρ c) * PowerSeries.map ρ φ + PowerSeries.map ρ φ ^ q =
        PowerSeries.subst (PowerSeries.C (ρ c) * PowerSeries.X + PowerSeries.X ^ q : PowerSeries S)
          (PowerSeries.map ρ φ) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h0, map_zero]
  · rw [PowerSeries.coeff_map, h1]
  · have hs : PowerSeries.HasSubst
        (PowerSeries.C c * PowerSeries.X + PowerSeries.X ^ q : PowerSeries R) :=
      PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hq])
    have h := congrArg (PowerSeries.map ρ) h2
    have h4 := PowerSeries.map_subst hs (h := ρ) φ
    rw [map_add, map_mul, map_pow, PowerSeries.map_C] at h
    refine h.trans (h4.trans ?_)
    congr 1
    change PowerSeries.map ρ _ = _
    rw [map_add, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X]

section Padic

variable (l : ℕ) [Fact l.Prime]

@[instance_reducible]
def omRel : ValuativeRel (Om l) := .ofValuation (PadicAlgCl.valued l).v

attribute [local instance] omRel

theorem om_compatible : (PadicAlgCl.valued l).v.Compatible := Valuation.Compatible.ofValuation _

theorem om_isValuativeTopology : IsValuativeTopology (Om l) :=
  haveI := om_compatible l
  isValuativeTopology_of_valued

attribute [local instance] om_isValuativeTopology

theorem om_vle_iff (x y : Om l) : x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖ := Iff.rfl

theorem om_valuativeExtension : ValuativeExtension ℚ_[l] (Om l) := ⟨fun a b => by
  rw [om_vle_iff, PadicAlgCl.norm_extends, PadicAlgCl.norm_extends,
    Valuation.Compatible.vle_iff_le (v := Padic.mulValuation) a b,
    GroundTheory.LocalField.Padic.mulValuation_le_iff_norm_le]⟩

attribute [local instance] om_valuativeExtension

variable {l}

theorem finExt_finiteDimensional (K : FinExt l) : FiniteDimensional ℚ_[l] ↥K.1 := K.2

attribute [local instance] finExt_finiteDimensional

theorem mem_integer_iff (K : FinExt l) (x : ↥K.1) : x ∈ 𝒪[↥K.1] ↔ x ∈ OL K := by
  rw [GlobalTheory.EmbThroughCompletion.mem_OL_iff, Valuation.mem_integer_iff, ← map_one (valuation ↥K.1),
    ← (valuation ↥K.1).vle_iff_le, ← IntermediateField.coe_vle_coe_iff, om_vle_iff]
  simp

def intEquiv (K : FinExt l) : 𝒪[↥K.1] ≃+* ↥(OL K) where
  toFun x := ⟨x.1, (mem_integer_iff K x.1).mp x.2⟩
  invFun x := ⟨x.1, (mem_integer_iff K x.1).mpr x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem kur_eq : MaximalUnramifiedExtension l = maximalUnramifiedExtension ℚ_[l] (Om l) := by
  rw [GroundTheory.LocalField.Padic.maximalUnramifiedExtension_eq_adjoin_rootsOfUnity, MaximalUnramifiedExtension]
  congr 1
  ext x
  refine exists_congr fun m => and_congr_right fun _ => and_congr_left fun _ => ?_
  rw [Nat.coprime_comm, (Fact.out : l.Prime).coprime_iff_not_dvd]

theorem card_residueField_eq (K : FinExt l) : Nat.card 𝓀[↥K.1] = resCard K := by
  rw [card_residueField_eq_pow_residueDegree ℚ_[l] ↥K.1, GroundTheory.LocalField.Padic.card_residueField,
    ← finrank_inf_maximalUnramifiedExtension K.1, ← kur_eq]
  rfl

theorem exists_irreducible (K : FinExt l) : ∃ π : ↥(OL K), Irreducible π := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[↥K.1]
  exact ⟨intEquiv K π, (MulEquiv.irreducible_iff (intEquiv K)).mpr hπ⟩

theorem exists_ltData (K : FinExt l) (π : ↥(OL K)) (hπ : Irreducible π) :
    ∃ (χ : ↥(GK K) →* (↥K.1)ˣ) (z : ℕ → Om l), LTData K χ π z := by
  obtain ⟨π', rfl⟩ := (intEquiv K).surjective π
  have hπ' : Irreducible π' := (MulEquiv.irreducible_iff (intEquiv K)).mp hπ
  obtain ⟨χ, z, hz0, hz1, hz, hg⟩ := exists_data (Ω := Om l) hπ'
  rw [card_residueField_eq] at hz hg
  refine ⟨((Units.map (𝒪[↥K.1]).subtype.toMonoidHom).comp χ).comp
    (IntermediateField.fixingSubgroupEquiv K.1).toMonoidHom, z, hπ, hz0, hz1, hz, fun g => ?_⟩
  obtain ⟨φ, h0, h1, h2, h3⟩ := hg (IntermediateField.fixingSubgroupEquiv K.1 g)
  refine ⟨intEquiv K (χ (IntermediateField.fixingSubgroupEquiv K.1 g)), rfl,
    PowerSeries.map (intEquiv K).toRingHom φ, ?_, fun n => ?_⟩
  · exact map_endo (intEquiv K).toRingHom (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) h0 h1 h2
  · simp only [PowerSeries.coeff_map]
    exact h3 n

end Padic

theorem main :
    (∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), Irreducible π →
      ∃ (χ : ↥(GK K) →* (↥K.1)ˣ) (z : ℕ → Om l), GlobalTheory.PZ.LTData K χ π z) ∧
    (∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), ∃ π : ↥(OL K), Irreducible π) :=
  ⟨fun _ _ K π hπ => exists_ltData K π hπ, fun _ _ K => exists_irreducible K⟩

end GlobalTheory.PZ.LTExist

end
