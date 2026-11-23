import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteChars
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicIntegersCompact.IsCompactAdicCompletionIntegers
open IsDedekindDomain NumberField

namespace GlobalTheory.LevelChars

theorem exists_finset_close (L : Type) [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) (N : ℕ) :
    ∃ F : Finset (v.adicCompletion L), ∀ x : v.adicCompletion L, Valued.v x ≤ 1 →
      ∃ f ∈ F, Valued.v (x - f) ≤ WithZero.exp (-(N : ℤ)) := by
  classical
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer L v
  set s : v.adicCompletion L := ((π ^ N : L) : v.adicCompletion L) with hsdef
  have hs : Valued.v s = WithZero.exp (-(N : ℤ)) := by
    rw [hsdef, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_pow, hπ, ← WithZero.exp_nsmul]
    congr 1
    simp
  have hball : IsOpen {y : v.adicCompletion L | Valued.v y < Valued.v s} := by
    have h := Valued.isOpen_ball (v.adicCompletion L) (Valued.v.restrict s)
    simpa [Valuation.restrict_lt_iff] using h
  obtain ⟨t, -, ht⟩ := (PI.IntAdCpctOpenWork.isCompact_adicCompletionIntegers (F := L) v).elim_nhds_subcover
    (fun x => {y | Valued.v (y - x) < Valued.v s})
    (fun x _ => (hball.preimage (continuous_id.sub continuous_const)).mem_nhds (by
      show Valued.v (x - x) < Valued.v s
      rw [sub_self, map_zero, hs]
      exact zero_lt_iff.2 WithZero.exp_ne_zero))
  refine ⟨t, fun x hx => ?_⟩
  have hxO : x ∈ (v.adicCompletionIntegers L : Set (v.adicCompletion L)) :=
    by rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]; exact hx
  obtain ⟨f, hf, hxf⟩ := Set.mem_iUnion₂.1 (ht hxO)
  exact ⟨f, hf, le_of_lt (hs ▸ hxf)⟩

end GlobalTheory.LevelChars

namespace GlobalTheory.LevelChars

theorem relIndex_levSub_ne_zero (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ)
    (hS : S.Finite) : (levSub L S N).relIndex (levSub L ∅ 0) ≠ 0 := by
  classical
  haveI : Finite S := hS.to_subtype
  choose F hF using fun v : S => exists_finset_close L v.1 N
  have hint : ∀ a : levSub L ∅ 0, ∀ v, Valued.v (compAt L v (a : (AdeleRing (𝓞 L) L)ˣ)) ≤ 1 :=
    fun a v => le_of_eq (a.2 v).1
  choose g hg hg' using fun (a : levSub L ∅ 0) (v : S) => hF v (compAt L v.1 a) (hint a v.1)
  let φ : levSub L ∅ 0 ⧸ (levSub L S N).subgroupOf (levSub L ∅ 0) → ((v : S) → (F v : Set (v.1.adicCompletion L))) :=
    fun q v => ⟨g q.out v, hg q.out v⟩
  have hφ : Function.Injective φ := by
    intro q q' hqq
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq, Subgroup.mem_subgroupOf]
    intro w
    refine ⟨((q.out⁻¹ * q'.out).2 w).1, fun hw => ?_⟩
    have e1 : g q.out ⟨w, hw⟩ = g q'.out ⟨w, hw⟩ := congrArg Subtype.val (congrFun hqq ⟨w, hw⟩)
    have h1 := hg' q.out ⟨w, hw⟩
    have h2 := hg' q'.out ⟨w, hw⟩
    rw [e1] at h1
    set a : (AdeleRing (𝓞 L) L)ˣ := (q.out : (AdeleRing (𝓞 L) L)ˣ)
    set b : (AdeleRing (𝓞 L) L)ˣ := (q'.out : (AdeleRing (𝓞 L) L)ˣ)
    have hinv : Valued.v (compAt L w a⁻¹) = 1 := ((q.out⁻¹).2 w).1
    have hc : compAt L w a⁻¹ * compAt L w a = 1 := by rw [← compAt_mul, inv_mul_cancel, compAt_one]
    have e2 : compAt L w ((q.out⁻¹ * q'.out : levSub L ∅ 0) : (AdeleRing (𝓞 L) L)ˣ) - 1 =
        compAt L w a⁻¹ * ((compAt L w b - g q'.out ⟨w, hw⟩) - (compAt L w a - g q'.out ⟨w, hw⟩)) := by
      have : ((q.out⁻¹ * q'.out : levSub L ∅ 0) : (AdeleRing (𝓞 L) L)ˣ) = a⁻¹ * b := rfl
      rw [this, compAt_mul]
      linear_combination hc
    rw [e2, map_mul, hinv, one_mul]
    exact (Valuation.map_sub _ _ _).trans (max_le h2 h1)
  haveI : Finite (levSub L ∅ 0 ⧸ (levSub L S N).subgroupOf (levSub L ∅ 0)) := Finite.of_injective φ hφ
  exact Subgroup.index_ne_zero_of_finite

end GlobalTheory.LevelChars

namespace GlobalTheory.LevelChars

theorem levSub_le_levSub_empty (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ) :
    levSub L S N ≤ levSub L ∅ 0 := fun a ha v => ⟨(ha v).1, fun h => absurd h (Set.notMem_empty v)⟩

theorem finiteIndex_range_sup_levSub_empty (L : Type) [Field L] [NumberField L] :
    ((Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom).range ⊔ levSub L ∅ 0).FiniteIndex := by
  classical
  haveI : Finite (ReciprocityTheory.Neutral.Bridge.HCFR.classOf L).range := inferInstance
  haveI := Subgroup.finiteIndex_ker (ReciprocityTheory.Neutral.Bridge.HCFR.classOf L)
  refine Subgroup.finiteIndex_of_le (H := (ReciprocityTheory.Neutral.Bridge.HCFR.classOf L).ker) ?_
  intro a ha
  obtain ⟨k, u, hu, rfl⟩ := (ReciprocityTheory.Neutral.Bridge.HCFR.classOf_eq_one_iff L a).1 ha
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨k, rfl⟩) (Subgroup.mem_sup_right ?_)
  exact fun v => ⟨(ReciprocityTheory.Neutral.Bridge.HCFR.rayUnits_top_iff L u).1 hu v, fun h => absurd h (Set.notMem_empty v)⟩

theorem finiteIndex_range_sup_levSub (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ)
    (hS : S.Finite) :
    ((Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom).range ⊔ levSub L S N).FiniteIndex := by
  set R := (Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom).range
  have hle := levSub_le_levSub_empty L S N
  haveI := finiteIndex_range_sup_levSub_empty L
  have hT : R ⊔ levSub L S N ≤ R ⊔ levSub L ∅ 0 := sup_le_sup_left hle _
  have h1 : (R ⊔ levSub L S N).relIndex (levSub L ∅ 0) ≠ 0 := by
    intro h0
    have hd : (R ⊔ levSub L S N).relIndex (levSub L ∅ 0) ∣ (levSub L S N).relIndex (levSub L ∅ 0) :=
      Subgroup.relIndex_dvd_of_le_left (levSub L ∅ 0) le_sup_right
    rw [h0] at hd
    exact relIndex_levSub_ne_zero L S N hS (Nat.eq_zero_of_zero_dvd hd)
  have h2 : R ⊔ levSub L S N ⊔ levSub L ∅ 0 = R ⊔ levSub L ∅ 0 := by
    rw [sup_assoc, sup_eq_right.2 hle]
  have h3 : (R ⊔ levSub L S N).relIndex (R ⊔ levSub L ∅ 0) ≠ 0 := by
    rw [← h2, Subgroup.relIndex_sup_left]; exact h1
  rw [Subgroup.finiteIndex_iff, ← Subgroup.relIndex_mul_index hT]
  exact mul_ne_zero h3 (Subgroup.FiniteIndex.index_ne_zero)

theorem rayClass_finite : ∀ (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ), S.Finite →
    ((Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom).range ⊔ GlobalTheory.LevelChars.levSub L S N).FiniteIndex :=
  fun L _ _ S N hS => finiteIndex_range_sup_levSub L S N hS

end GlobalTheory.LevelChars
