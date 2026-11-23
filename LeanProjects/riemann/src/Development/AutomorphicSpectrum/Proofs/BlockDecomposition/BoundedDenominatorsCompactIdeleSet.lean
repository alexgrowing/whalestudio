import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThPr
import GroundTheory.GlobalFields.Adele.Discrete

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.BasePsi.Den

variable {F : Type} [Field F] [NumberField F]

theorem valued_algebraMap (v : HeightOneSpectrum (𝓞 F)) (t : F) :
    Valued.v (algebraMap F (Fv F v) t) = v.valuation F t :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v t

theorem exists_valued_bound (v : HeightOneSpectrum (𝓞 F)) {C : Set (Fv F v)} (hC : IsCompact C) :
    ∃ γ : WithZero (Multiplicative ℤ), γ ≠ 0 ∧ ∀ x ∈ C, Valued.v x ≤ γ := by
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) :=
    Valued.isOpen_valuationSubring _
  obtain ⟨s, -, hs⟩ := hC.elim_nhds_subcover
    (fun x => {y : Fv F v | y - x ∈ v.adicCompletionIntegers F}) (fun x _ => by
      have hopen : IsOpen {y : Fv F v | y - x ∈ v.adicCompletionIntegers F} :=
        hO.preimage (continuous_id.sub continuous_const)
      exact hopen.mem_nhds (by simp))
  obtain ⟨M, hM⟩ := (s.image fun x => Valued.v x).exists_le
  refine ⟨max M 1, (lt_of_lt_of_le zero_lt_one (le_max_right _ _)).ne', fun y hy => ?_⟩
  obtain ⟨x, hx, hxy⟩ := Set.mem_iUnion₂.mp (hs hy)
  have h1 : Valued.v (y - x) ≤ 1 := hxy
  have h2 : Valued.v x ≤ M := hM _ (Finset.mem_image_of_mem _ hx)
  have h3 : y = (y - x) + x := by ring
  rw [h3]
  exact (Valuation.map_add _ _ _).trans
    (max_le (h1.trans (le_max_right _ _)) (h2.trans (le_max_left _ _)))

theorem exists_finset_inv_integral {D : Set (AF F)ˣ} (hD : IsCompact D) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ u ∈ D, ∀ v, v ∉ T →
      ((u⁻¹ : (AF F)ˣ) : AF F).2 v ∈ v.adicCompletionIntegers F := by
  obtain ⟨s, -, hs⟩ := hD.elim_nhds_subcover
    (fun a : (AF F)ˣ => {u : (AF F)ˣ | a⁻¹ * u ∈ IdeleGroup.standardOpenSubgroup F}) (fun a _ => by
      have hopen : IsOpen {u : (AF F)ˣ | a⁻¹ * u ∈ IdeleGroup.standardOpenSubgroup F} :=
        (IdeleGroup.isOpen_standardOpenSubgroup F).preimage (continuous_const.mul continuous_id)
      exact hopen.mem_nhds (by simp [one_mem]))
  have hfin : ∀ a : (AF F)ˣ, {v : HeightOneSpectrum (𝓞 F) |
      ((a⁻¹ : (AF F)ˣ) : AF F).2 v ∉ v.adicCompletionIntegers F}.Finite := fun a =>
    Filter.eventually_cofinite.mp ((a⁻¹ : (AF F)ˣ) : AF F).2.2
  refine ⟨s.biUnion fun a => (hfin a).toFinset, fun u hu v hv => ?_⟩
  obtain ⟨a, ha, hau⟩ := Set.mem_iUnion₂.mp (hs hu)
  have hav : ((a⁻¹ : (AF F)ˣ) : AF F).2 v ∈ v.adicCompletionIntegers F := by
    by_contra hcon
    exact hv (Finset.mem_biUnion.mpr ⟨a, ha, (hfin a).mem_toFinset.mpr hcon⟩)
  have hh := ((IdeleGroup.mem_standardOpenSubgroup F).mp hau v).2
  have hu' : u⁻¹ = (a⁻¹ * u)⁻¹ * a⁻¹ := by group
  have hmul : ((u⁻¹ : (AF F)ˣ) : AF F).2 v =
      (((a⁻¹ * u)⁻¹ : (AF F)ˣ) : AF F).2 v * ((a⁻¹ : (AF F)ˣ) : AF F).2 v := by
    conv_lhs => rw [hu']
    rfl
  rw [hmul]
  exact mul_mem hh hav

theorem exists_inv_bound {D : Set (AF F)ˣ} (hD : IsCompact D) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ γ : WithZero (Multiplicative ℤ), γ ≠ 0 ∧ ∀ u ∈ D, Valued.v (((u⁻¹ : (AF F)ˣ) : AF F).2 v) ≤ γ := by
  have hc : Continuous fun u : (AF F)ˣ => ((u⁻¹ : (AF F)ˣ) : AF F).2 v :=
    Units.continuous_val.comp ((IdeleGroup.continuous_finiteProj (K := F) v).comp continuous_inv)
  obtain ⟨γ, h0, hγ⟩ := exists_valued_bound v (hD.image hc)
  exact ⟨γ, h0, fun u hu => hγ _ (Set.mem_image_of_mem _ hu)⟩

theorem exists_bound {D : Set (AF F)ˣ} (hD : IsCompact D) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (C : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hC : ∀ v ∈ S, IsCompact (C v)) :
    ∃ (T : Finset (HeightOneSpectrum (𝓞 F))) (A : HeightOneSpectrum (𝓞 F) → WithZero (Multiplicative ℤ)),
      ∀ u ∈ D, ∀ t : F, (∀ v ∈ S, algebraMap F (Fv F v) t * (u : AF F).2 v ∈ C v) →
        (∀ v, v ∉ S → algebraMap F (Fv F v) t * (u : AF F).2 v ∈ v.adicCompletionIntegers F) →
        ∀ v, v.valuation F t ≤ if v ∈ T then A v else 1 := by
  obtain ⟨T₀, hT₀⟩ := exists_finset_inv_integral hD
  choose B _ hB using fun v => exists_inv_bound hD v
  have hG : ∀ v : HeightOneSpectrum (𝓞 F), ∃ γ : WithZero (Multiplicative ℤ), v ∈ S →
      ∀ x ∈ C v, Valued.v x ≤ γ := fun v => by
    by_cases hv : v ∈ S
    · obtain ⟨γ, -, h⟩ := exists_valued_bound v (hC v hv)
      exact ⟨γ, fun _ => h⟩
    · exact ⟨1, fun h => absurd h hv⟩
  choose G hG using hG
  refine ⟨T₀ ∪ S, fun v => max (G v) 1 * B v, fun u hu t h1 h2 v => ?_⟩
  have hinv : (u : AF F).2 v * ((u⁻¹ : (AF F)ˣ) : AF F).2 v = 1 :=
    congrArg (fun a : AF F => a.2 v) (Units.mul_inv u)
  have hx : algebraMap F (Fv F v) t =
      (algebraMap F (Fv F v) t * (u : AF F).2 v) * ((u⁻¹ : (AF F)ˣ) : AF F).2 v := by
    rw [mul_assoc, hinv, mul_one]
  have hval : v.valuation F t = Valued.v (algebraMap F (Fv F v) t * (u : AF F).2 v) *
      Valued.v (((u⁻¹ : (AF F)ˣ) : AF F).2 v) := by
    rw [← valued_algebraMap, ← map_mul, ← hx]
  have hfirst : Valued.v (algebraMap F (Fv F v) t * (u : AF F).2 v) ≤ max (G v) 1 := by
    by_cases hv : v ∈ S
    · exact (hG v hv _ (h1 v hv)).trans (le_max_left _ _)
    · have a : Valued.v (algebraMap F (Fv F v) t * (u : AF F).2 v) ≤ 1 := h2 v hv
      exact a.trans (le_max_right _ _)
  by_cases hvT : v ∈ T₀ ∪ S
  · rw [if_pos hvT, hval]
    exact mul_le_mul' hfirst (hB v u hu)
  · rw [if_neg hvT, hval]
    have hvS : v ∉ S := fun h => hvT (Finset.mem_union_right _ h)
    have hvT₀ : v ∉ T₀ := fun h => hvT (Finset.mem_union_left _ h)
    have a1 : Valued.v (algebraMap F (Fv F v) t * (u : AF F).2 v) ≤ 1 := h2 v hvS
    have a2 : Valued.v (((u⁻¹ : (AF F)ˣ) : AF F).2 v) ≤ 1 := hT₀ u hu v hvT₀
    simpa using mul_le_mul' a1 a2

theorem valuation_natCast_le_one (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    v.valuation F (n : F) ≤ 1 := by
  have := HeightOneSpectrum.valuation_le_one (K := F) v (n : 𝓞 F)
  simpa using this

theorem exists_nat_mul_le_one (v : HeightOneSpectrum (𝓞 F)) (A : WithZero (Multiplicative ℤ)) :
    ∃ n : ℕ, 0 < n ∧ v.valuation F (n : F) * A ≤ 1 := by
  by_cases hA : A = 0
  · exact ⟨1, one_pos, by simp [hA]⟩
  have hlt : v.valuation F ((Ideal.absNorm v.asIdeal : ℕ) : F) < 1 := by
    have h := (v.valuation_lt_one_iff_mem (K := F) ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)).2
      (Ideal.absNorm_mem _)
    simpa using h
  obtain ⟨k, hk⟩ := exists_pow_lt₀ hlt (Units.mk0 _ (inv_ne_zero hA))
  have hpos : 0 < Ideal.absNorm v.asIdeal := by
    refine Nat.pos_of_ne_zero fun h => v.ne_bot ?_
    exact Ideal.absNorm_eq_zero_iff.mp h
  refine ⟨Ideal.absNorm v.asIdeal ^ k, pow_pos hpos k, ?_⟩
  have h3 : v.valuation F (((Ideal.absNorm v.asIdeal ^ k : ℕ)) : F) < A⁻¹ := by
    push_cast
    rw [map_pow]
    exact hk
  calc v.valuation F (((Ideal.absNorm v.asIdeal ^ k : ℕ)) : F) * A ≤ A⁻¹ * A :=
        mul_le_mul' h3.le le_rfl
    _ = 1 := inv_mul_cancel₀ hA

theorem common_denominator (F : Type) [Field F] [NumberField F] (D : Set (AF F)ˣ) (hD : IsCompact D)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (C : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v))
    (hC : ∀ v ∈ S, IsCompact (C v)) :
    ∃ N : ℕ, 0 < N ∧ ∀ u ∈ D, ∀ t : F, (∀ v ∈ S, algebraMap F (Fv F v) t * (u : AF F).2 v ∈ C v) →
      (∀ v, v ∉ S → algebraMap F (Fv F v) t * (u : AF F).2 v ∈ v.adicCompletionIntegers F) →
      ∃ y : 𝓞 F, (y : F) = N * t := by
  obtain ⟨T, A, hA⟩ := exists_bound hD S C hC
  choose n hn0 hn using fun v => exists_nat_mul_le_one (F := F) v (A v)
  refine ⟨∏ v ∈ T, n v, Finset.prod_pos fun v _ => hn0 v, fun u hu t h1 h2 => ?_⟩
  refine exists_eq_of_forall_mem_adicCompletionIntegers F _ fun v => ?_
  rw [coe_mem_adicCompletionIntegers_iff, map_mul]
  have ht := hA u hu t h1 h2 v
  by_cases hv : v ∈ T
  · rw [if_pos hv] at ht
    obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem n hv
    have hN : v.valuation F (((∏ v ∈ T, n v : ℕ)) : F) ≤ v.valuation F (n v : F) := by
      rw [hm]
      push_cast
      rw [map_mul]
      simpa using mul_le_mul' (le_refl (v.valuation F (n v : F))) (valuation_natCast_le_one v m)
    exact (mul_le_mul' hN ht).trans (hn v)
  · rw [if_neg hv] at ht
    simpa using mul_le_mul' (valuation_natCast_le_one v (∏ v ∈ T, n v)) ht

end GlobalTheory.CompanionTheory.BasePsi.Den

end
