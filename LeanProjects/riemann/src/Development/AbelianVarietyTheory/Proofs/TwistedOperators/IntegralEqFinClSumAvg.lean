import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ClassFunctionSumIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousReGLSymm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfOfMulFinOf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRightOfMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqVolMulSum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenusMassSignature
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.DefiniteClassReal

theorem isReps_transfer {Γ A B : Type} [Group Γ] [Group A] [Group B] (ι : Γ →* A) (ι' : Γ →* B) (e : A ≃* B)
    (he : ∀ γ, e (ι γ) = ι' γ) (J : Subgroup A) (J' : Subgroup B) (hJ : ∀ a, e a ∈ J' ↔ a ∈ J) {I : Type} (y : I → A)
    (h : Bridge.IsReps ι J y) : Bridge.IsReps ι' J' (fun i => e (y i)) := by
  intro b
  obtain ⟨i, ⟨γ, k, hk⟩, hu⟩ := h (e.symm b)
  refine ⟨i, ⟨γ, ⟨e k, (hJ k).2 k.2⟩, ?_⟩, ?_⟩
  · have := congrArg e hk
    rw [e.apply_symm_apply] at this
    rw [this, map_mul, map_mul, he]
  · rintro j ⟨γ', k', hk'⟩
    refine hu j ⟨γ', ⟨e.symm k', (hJ _).1 (by rw [e.apply_symm_apply]; exact k'.2)⟩, ?_⟩
    apply e.injective
    rw [e.apply_symm_apply, hk', map_mul, map_mul, he, e.apply_symm_apply]

theorem stab_transfer {Γ A B : Type} [Group Γ] [Group A] [Group B] (ι : Γ →* A) (ι' : Γ →* B) (e : A ≃* B)
    (he : ∀ γ, e (ι γ) = ι' γ) (J : Subgroup A) (J' : Subgroup B) (hJ : ∀ a, e a ∈ J' ↔ a ∈ J) (x : A) :
    Bridge.stab ι' J' (e x) = Bridge.stab ι J x := by
  ext γ
  rw [Bridge.mem_stab, Bridge.mem_stab, ← he, ← map_inv, ← map_mul, ← map_mul, hJ]

end GlobalTheory.DefiniteClassReal

namespace GlobalTheory.DefiniteClassReal
open GlobalTheory.FunObj GlobalTheory.ClassRegroup GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral GlobalTheory.DefiniteClassAvg

theorem integral_eq_finClSum_avg : ∀ {D : D7} (V : HSp D), (∀ φ : D.host.E →+* ℂ, (V.gram.map φ).PosDef) →
    ∀ (K K'' : Subgroup (GL (Fin V.rank) (Lev.EAf D))), IsOpenCompactLevel V K → IsOpenCompactLevel V K'' → K'' ≤ K →
    ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), IsMeasDef V K μ 𝓕 → ∀ (Φ : GA D V → ℂ),
    (∀ γ ∈ GQ V, ∀ g, Φ (γ * g) = Φ g) → (∀ k ∈ Lev.levA V K'', ∀ g, Φ (g * k) = Φ g) →
    (∀ z, Continuous fun k : GinfC V => Φ (z * k)) →
    Finite (FinCl V K'') ∧ ∃ κ : Measure (GinfC V), κ.IsHaarMeasure ∧ IsProbabilityMeasure κ ∧
      ∫ g in 𝓕, Φ g ∂μ = ∑ᶠ c : FinCl V K'',
        ((μ ((K''.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V))).toReal : ℂ) / (gamOrd V K'' c.out : ℂ) *
          ∫ k, Φ ((c.out : GA D V) * k) ∂κ := by
  intro D V hV K K'' hK hK'' hle μ 𝓕 hμ Φ hl hr hc

  let V' : HSp D := { V with sig := fun _ => (V.rank, 0) }
  have hS' : V'.SigOK := fun τ => GlobalTheory.Proof.GenusMassSignature.hasSignature_of_posDef (hV τ)
  have hD' : V'.IsDefinite := fun τ => Or.inl rfl
  have hGc : IsCompact (GinfC V : Set (GA D V)) := Formalism.IndefR.Eqv.isCompact_GinfC (V := V') hS' hD'
  haveI : CompactSpace (GinfC V) := isCompact_iff_compactSpace.1 hGc
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have hLC := hT.1
  have hSC := hT.2.1
  have hB := hT.2.2.2.1
  have hG := hT.2.2.2.2.1
  have hC := hT.2.2.2.2.2.2
  have hHaar := hμ.1.1
  have hfin0 : Finite (FinCl V K'') := (finite_finCl_and_gamOrd V K'' hV hK'').1
  letI : Fintype (FinCl V K'') := Fintype.ofFinite _

  let κ : Measure (GinfC V) := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (GinfC V))
  haveI hκH : κ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  have hκ1 : κ Set.univ = 1 := by
    have := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (GinfC V)))
    simpa using this
  haveI : IsProbabilityMeasure κ := ⟨hκ1⟩
  refine ⟨hfin0, κ, hκH, inferInstance, ?_⟩

  let e := finEquiv V
  have he : ∀ γ, e (((finPt V).comp (GQ V).subtype) γ) = Bridge.ratF V γ := fun γ => e.apply_symm_apply _
  have hJe : ∀ a, e a ∈ levelFin V K'' ↔ a ∈ K''.comap (finG V) := fun a => Iff.rfl
  have hy := isReps_transfer _ _ e he _ _ hJe _ (isReps_out V K'')
  let y : FinCl V K'' → Bridge.Gf V := fun c => e (Quotient.out c)
  let z : FinCl V K'' → GA D V := fun c => ((Quotient.out c : GfC V) : GA D V)
  have hz : ∀ c, (finHom V).rangeRestrict (z c) = y c := fun c => rfl

  let J : Subgroup (GA D V) := K''.comap (Lev.finE V)
  let JK : Subgroup (GA D V) := K.comap (Lev.finE V)
  have hJo : IsOpen (J : Set (GA D V)) := hK''.1
  have hJJK : J ≤ JK := fun x hx => hle hx
  have hJK1 : μ JK = 1 := GlobalTheory.Mass.Levels.measure_comap_finE hμ.1
  have hJtop : μ J ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [hJK1]; exact ENNReal.one_ne_top) (measure_mono (fun x hx => hJJK hx))
  have hJ0 : μ J ≠ 0 := (hJo.measure_pos μ ⟨1, J.one_mem⟩).ne'
  have hinfJ : GinfC V ≤ J := by
    show GinfC V ≤ K''.comap (Lev.finE V)
    rw [GlobalTheory.Mass.Levels.comap_finE]
    exact le_sup_right
  have hcont : Continuous Φ := continuous_of_level V K'' hK''.1 Φ hr hc
  have hu : ∀ x : GA D V, ∃! c, ∃ γ ∈ GQ V, ∃ k ∈ J, x = γ * z c * k :=
    existsUnique_doubleCoset (finHom V).rangeRestrict (GQ V) (levelFin V K'') y hy z hz
  have hs : ∀ c, (classGroupAt V K'' (y c) : Set (GQ V)) = {γ : GQ V | (z c)⁻¹ * (γ : GA D V) * z c ∈ J} := by
    intro c
    ext γ
    rw [SetLike.mem_coe, ← hz c, mem_classGroupAt]
    rfl
  have hfinΓ : ∀ c, {γ : GQ V | (z c)⁻¹ * (γ : GA D V) * z c ∈ J}.Finite := fun c =>
    GlobalTheory.InnerClassSum.finite_stab_of_measure μ (GQ V) J hμ.2 hJ0 hJtop (z c)
  have him : ∀ c, {γ : GA D V | γ ∈ GQ V ∧ (z c)⁻¹ * γ * z c ∈ J} =
      Subtype.val '' {γ : GQ V | (z c)⁻¹ * (γ : GA D V) * z c ∈ J} := by
    intro c
    ext γ
    simp only [Set.mem_setOf_eq, Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
    exact ⟨fun h => ⟨h.1, h.2⟩, fun ⟨h, h'⟩ => ⟨h, h'⟩⟩
  have hfin : ∀ c, {γ : GA D V | γ ∈ GQ V ∧ (z c)⁻¹ * γ * z c ∈ J}.Finite := fun c =>
    him c ▸ (hfinΓ c).image _
  have hdec : ∀ k ∈ J, ∃ k' ∈ Lev.levA V K'', ∃ w : GinfC V, k = k' * (GinfC V).subtype w := fun k hk =>
    ⟨finPart V k, finPart_mem_levA V hk, ⟨realPart V k, realPart_mem V k⟩, (finPart_mul_realPart V k).symm⟩
  have hcomm : ∀ k ∈ Lev.levA V K'', ∀ w : GinfC V, k * (GinfC V).subtype w = (GinfC V).subtype w * k :=
    fun k hk w => (Eqv.Act.comm_inf_fin w.2 (Subgroup.mem_inf.1 hk).1).symm
  have hrt : ∀ w : GinfC V, MeasurePreserving (· * (GinfC V).subtype w) μ μ := fun w =>
    measurePreserving_mul_right_of_mem μ J hJo hJ0 hJtop (hinfJ w.2)
  obtain ⟨-, heq⟩ := integral_eq_sum_avg (GA D V) μ (GQ V) J (Lev.levA V K'') 𝓕 hμ.2 hJo hJtop (GinfC V) κ
    (GinfC V).subtype continuous_subtype_val hrt hdec hcomm (FinCl V K'') z hu hfin Φ hcont hl hr
  rw [heq, Finset.mul_sum, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hcard : Nat.card (classGroupAt V K'' (y c)) = gamOrd V K'' (Quotient.out c) := by
    show Nat.card (Bridge.stab (Bridge.ratF V) (levelFin V K'') (e (Quotient.out c))) = _
    rw [stab_transfer _ _ e he _ _ hJe]
    exact card_stab V K'' _
  have hcard' : ((classGroupAt V K'' (y c) : Set (GQ V))).ncard = gamOrd V K'' (Quotient.out c) :=
    (Nat.card_coe_set_eq _).symm.trans hcard
  rw [him, Set.ncard_image_of_injective _ Subtype.val_injective, ← hs, hcard', div_eq_mul_inv, mul_assoc]
  rfl

end GlobalTheory.DefiniteClassReal
