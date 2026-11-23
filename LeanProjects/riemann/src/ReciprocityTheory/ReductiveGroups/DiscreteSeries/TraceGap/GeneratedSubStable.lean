import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.LoweringSpanDiagStable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Transported
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.SecondKernelCoupled
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasimirGapAtNoncompactWeight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ}

section SlopeTestRemainingChoices

variable {N : Type*} [AddCommGroup N] [Module ℂ N]

theorem generatedSub_stable (E : Fin n → Fin n → Module.End ℂ N) (V : Submodule ℂ N) (a b : Fin n) {v : N}
    (hv : v ∈ genSub E V) : E a b v ∈ genSub E V :=
  Submodule.mem_sInf.2 fun T hT => hT.2 a b v (Submodule.mem_sInf.1 hv T hT)

theorem casimir_scalar_on_generated {E : Fin n → Fin n → Module.End ℂ N} (hE : IsGlRep E) {V : Submodule ℂ N} {c : ℂ}
    (hc : ∀ v ∈ V, casimir E v = c • v) : ∀ v ∈ genSub E V, casimir E v = c • v := by
  let T : Submodule ℂ N := LinearMap.ker (casimir E - c • (1 : Module.End ℂ N))
  have hmem : ∀ v, v ∈ T ↔ casimir E v = c • v := by
    intro v
    simp only [T, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]
  have hT : genSub E V ≤ T := by
    refine sInf_le ⟨fun v hv => (hmem v).2 (hc v hv), fun a b v hv => ?_⟩
    rw [hmem] at hv ⊢
    have := LinearMap.congr_fun (casimir_comm hE a b) v
    simp only [Module.End.mul_apply] at this
    rw [this, hv, map_smul]
  exact fun v hv => (hmem v).1 (hT hv)

end SlopeTestRemainingChoices

section Form

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

def tensorFormRight (w : TensorProduct ℂ M (Fock n)) : TensorProduct ℂ M (Fock n) →ₗ[ℂ] ℂ where
  toFun := tform w
  map_add' := tform_add_right w
  map_smul' c y := by rw [tform_smul_right]; rfl

end Form

theorem ker_D_eq_kLowSpan {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hint : ∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)) (hanti : StrictAnti lam)
    (hgap : GapAtLeast ε lam h) (hthr : thrStar ε < h) (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) :
    ∃ z : TensorProduct ℂ D (Fock n), z ≠ 0 ∧ z ∈ tensFock V ∧
      IsKHWVec ε (diagE ε (eT E) cpT cmT) (gaW ε lam) z ∧
      z ∈ LinearMap.range (TensorProduct.map V.subtype (⋀[ℂ]^(sDeg ε) (Fin n × Fin n → ℂ)).subtype) ∧
      LinearMap.ker (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) ⊓ tensFock (genSub E V) ⊓ physicalSubspace ε =
        kLowSpan ε (diagE ε (eT E) cpT cmT) z ∧
      IsKIrrHW ε (diagE ε (eT E) cpT cmT) (gaW ε lam) (kLowSpan ε (diagE ε (eT E) cpT cmT) z) := by
  classical
  have hE : IsGlRep E := hD.glRep
  have hU : IsInfUnitary ε E := isInfUnitary_of_isDerivedOn hσ hD
  have e : (min (pOf ε) (qOf ε) : ℝ) = (S7.q0 ε : ℝ) := by simp [S7.q0, Nat.cast_min]
  have hbig : max ((n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1)
      (16 * (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ) + 8 * Real.sqrt (2 * (min (pOf ε) (qOf ε) : ℝ))) < h := by
    rw [e]; exact hthr
  have hstd : StdGap ε lam := ⟨hanti, h, hgap, lt_of_le_of_lt (le_max_left _ _) hbig⟩
  have hcone : ∀ (μ : Fin n → ℝ) (w : D), w ∈ genSub E V → w ≠ 0 → IsKHWVec ε E μ w →
      Lap.LemK.InRootCone (μ - lowK ε lam) :=
    Lap.LemK.lowestKType_casimir_cone n ε lam h H σ D E V hσ hD hV hc hVK hint hanti hgap hbig hp hq
  have hcas : ∀ v ∈ genSub E V, casimir E v = ((casVal lam : ℝ) : ℂ) • v := casimir_scalar_on_generated hE hc
  have hlowK : ∀ w ∈ genSub E V, IsKHWVec ε E (lowK ε lam) w → w ∈ V :=
    fun w hw hk => khw_lowK_mem hE hU hV hc hstd hw hk
  obtain ⟨z, hzL, hz0⟩ := line_exists hanti hE hV
  have hzD := line_ker hE hU hV hc hzL
  have hzdeg := line_deg hE hU hV hzL
  obtain ⟨⟨hzK', hzT⟩, hzP⟩ := hzL
  have hzK := (mem_highestWeightSub_iff _ _ _ z).1 hzK'
  have hVk : IsKStableSub ε E V := hV.2.1
  have hGk : IsKStableSub ε E (genSub E V) := fun a b _ v hv => generatedSub_stable E V a b hv
  have hVG : V ≤ genSub E V := fun v hv => Submodule.mem_sInf.2 fun T hT => hT.1 hv
  have hK : ∀ a b c d, ε a = ε b → ε c = ε d →
      diagE ε (eT E) cpT cmT a b * diagE ε (eT E) cpT cmT c d -
        diagE ε (eT E) cpT cmT c d * diagE ε (eT E) cpT cmT a b =
      (if b = c then diagE ε (eT E) cpT cmT a d else 0) - (if d = a then diagE ε (eT E) cpT cmT c b else 0) :=
    fun a b c d hab hcd => diagAction_commutator (eT_isGlRep hE) cpT_cmT_isCAR (eT_commutesCAR E) ε a b c d hab hcd
  set A := diagE ε (eT E) cpT cmT with hA
  set KK := LinearMap.ker (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) ⊓ tensFock (genSub E V) ⊓ physicalSubspace ε with hKK
  have hKKs : IsKStableSub ε A KK := by
    intro a b hab y hy
    obtain ⟨⟨hyD, hyT⟩, hyP⟩ := hy
    refine ⟨⟨?_, tensorFock_diagAction_stable ε hGk hab hyT⟩, (physSub_stable ε E).2.1 a b y hyP⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker] at hyD ⊢
    have h1 := LinearMap.congr_fun
      (dOp_comm_diagE (eT_isGlRep hE) cpT_cmT_isCAR (eT_commutesCAR E) ε a b hab) y
    have h2 := LinearMap.congr_fun
      (dOp'_comm_diagE (eT_isGlRep hE) cpT_cmT_isCAR (eT_commutesCAR E) ε a b hab) y
    simp only [Module.End.mul_apply] at h1 h2
    rw [LinearMap.add_apply, h1, h2, ← map_add, ← LinearMap.add_apply, hyD, map_zero]
  have hzKK : z ∈ KK := ⟨⟨hzD, tensorFock_mono hVG hzT⟩, hzP⟩
  have hZs : IsKStableSub ε A (kLowSpan ε A z) := loweringSpan_kStable hK hzK
  have hZKK : kLowSpan ε A z ≤ KK := kLowSpan_le hKKs hzKK
  have huniq : ∀ y ∈ KK, ∀ μ, IsKHWVec ε A μ y → ∃ c : ℂ, y = c • z := by
    intro y hy μ hyK
    obtain ⟨⟨hyD, hyT⟩, hyP⟩ := hy
    exact highestWeight_uniqueness hanti hE hU hV hcone hcas hlowK hyT hyP hyD hyK (tensorFock_mono hVG hzT) hzP hzD hz0 hzK
  have hTVs : IsKStableSub ε A (tensFock V) := fun a b hab y hy => tensorFock_diagAction_stable ε hVk hab hy
  have hZV : kLowSpan ε A z ≤ tensFock V := kLowSpan_le hTVs hzT
  have hZfd : FiniteDimensional ℂ (kLowSpan ε A z) := by
    have := tensorFock_finiteDimensional (n := n) hV.1
    exact Submodule.finiteDimensional_of_le hZV

  have hfill : ∀ Y : Submodule ℂ (TensorProduct ℂ D (Fock n)), FiniteDimensional ℂ Y → IsKStableSub ε A Y →
      Y ≤ KK → kLowSpan ε A z ≤ Y → Y ≤ kLowSpan ε A z := by
    intro Y hYfd hYs hYK hZY
    let Y' : Submodule ℂ (TensorProduct ℂ D (Fock n)) :=
      { carrier := {y | y ∈ Y ∧ ∀ w ∈ kLowSpan ε A z, tform y w = 0}
        add_mem' := fun {x y} hx hy => ⟨Y.add_mem hx.1 hy.1, fun w hw => by
          rw [tform_add_left, hx.2 w hw, hy.2 w hw, add_zero]⟩
        zero_mem' := ⟨Y.zero_mem, fun w _ => by simp [tform]⟩
        smul_mem' := fun c x hx => ⟨Y.smul_mem c hx.1, fun w hw => by
          rw [tensorForm_smul_left, hx.2 w hw, mul_zero]⟩ }
    have hY'Y : Y' ≤ Y := fun y hy => hy.1
    have hY's : IsKStableSub ε A Y' := by
      intro a b hab y hy
      refine ⟨hYs a b hab y hy.1, fun w hw => ?_⟩
      rw [tensorForm_diagAction_adjoint hU hab]
      exact hy.2 _ (hZs b a hab.symm w hw)
    have hY'0 : Y' = ⊥ := by
      by_contra hne
      have : FiniteDimensional ℂ Y' := Submodule.finiteDimensional_of_le hY'Y
      obtain ⟨w, hw, hw0, μ, hwK⟩ := exists_highestWeight_in_stable hE hU this hY's hne
      obtain ⟨c, rfl⟩ := huniq w (hYK hw.1) μ hwK
      have h0 := hw.2 _ (Submodule.smul_mem _ c (self_mem_kLowSpan z))
      have hpos := tform_self_re_pos hw0
      rw [h0] at hpos
      simp at hpos
    let b := Module.finBasis ℂ (kLowSpan ε A z)
    let f : Y →ₗ[ℂ] (Fin (Module.finrank ℂ (kLowSpan ε A z)) → ℂ) :=
      LinearMap.pi fun i => (tensorFormRight ((b i : kLowSpan ε A z) : TensorProduct ℂ D (Fock n))).comp Y.subtype
    have hf : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro y hy
      rw [LinearMap.mem_ker] at hy
      have hfi : ∀ i, tform ((b i : kLowSpan ε A z) : TensorProduct ℂ D (Fock n)) (y : TensorProduct ℂ D (Fock n)) = 0 :=
        fun i => congrFun hy i
      have hyY' : (y : TensorProduct ℂ D (Fock n)) ∈ Y' := by
        refine ⟨y.2, fun w hw => ?_⟩
        have hw' : w = ∑ i, (b.repr ⟨w, hw⟩ i) • ((b i : kLowSpan ε A z) : TensorProduct ℂ D (Fock n)) := by
          have := congrArg Subtype.val (b.sum_repr ⟨w, hw⟩)
          rw [Submodule.coe_sum] at this
          simp only [Submodule.coe_smul] at this
          exact this.symm
        have h1 : tform w (y : TensorProduct ℂ D (Fock n)) = 0 := by
          rw [hw', tform_sum_left]
          exact sum_eq_zero fun i _ => by rw [tensorForm_smul_left, hfi i, mul_zero]
        rw [← tform_conj, h1, star_zero]
      rw [hY'0, Submodule.mem_bot] at hyY'
      exact (Submodule.mem_bot ℂ).2 (Subtype.ext hyY')
    have hle : Module.finrank ℂ Y ≤ Module.finrank ℂ (kLowSpan ε A z) := by
      have := LinearMap.finrank_le_finrank_of_injective hf
      simpa using this
    exact (Submodule.eq_of_le_of_finrank_le hZY hle).symm.le

  have hKKle : KK ≤ kLowSpan ε A z := by
    intro x hx
    have hxT : x ∈ tensFock (genSub E V) := hx.1.2
    rw [genSub_eq_iSup_layer hE hVk] at hxT
    have hdir : Directed (· ≤ ·) (fun k => layer ε E V k) :=
      fun i j => ⟨max i j, layer_mono (le_max_left i j), layer_mono (le_max_right i j)⟩
    have hco : ∀ s, ∃ k, tcoef ((fockBasis n).coord s) x ∈ layer ε E V k :=
      fun s => (Submodule.mem_iSup_of_directed _ hdir).1 (tcoef_mem hxT _)
    choose j hj using hco
    set J := univ.sup j
    have hxJ : x ∈ tensFock (layer ε E V J) :=
      mem_tensorFock_of_coeffs fun s => layer_mono (le_sup (mem_univ s)) (hj s)
    let Y := tensFock (layer ε E V J) ⊓ KK
    have hLs : IsKStableSub ε A (tensFock (layer ε E V J)) :=
      fun a b hab y hy => tensorFock_diagAction_stable ε (layer_kStable hE hVk J) hab hy
    have hYs : IsKStableSub ε A Y := fun a b hab y hy => ⟨hLs a b hab y hy.1, hKKs a b hab y hy.2⟩
    have hYfd : FiniteDimensional ℂ Y := by
      have := tensorFock_finiteDimensional (n := n) (finiteDimensional_layer (ε := ε) (E := E) hV.1 J)
      exact Submodule.finiteDimensional_of_le inf_le_left
    have hzY : z ∈ Y := ⟨tensorFock_mono (layer_mono (Nat.zero_le J)) hzT, hzKK⟩
    exact hfill Y hYfd hYs inf_le_right (kLowSpan_le hYs hzY) ⟨hxJ, hx⟩
  refine ⟨z, hz0, hzT, hzK, hzdeg, le_antisymm hKKle hZKK, hZfd, hZs, ?_, z, self_mem_kLowSpan z, hz0, hzK⟩
  intro S hSle hSs
  by_cases hS0 : S = ⊥
  · exact Or.inl hS0
  right
  have : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hSle
  obtain ⟨w, hw, hw0, μ, hwK⟩ := exists_highestWeight_in_stable hE hU this hSs hS0
  obtain ⟨c, rfl⟩ := huniq w (hZKK (hSle hw)) μ hwK
  have hc0 : c ≠ 0 := fun h0 => hw0 (by rw [h0, zero_smul])
  have hzS : z ∈ S := by
    have := S.smul_mem c⁻¹ hw
    rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at this
  exact le_antisymm hSle (kLowSpan_le hSs hzS)

end ReciprocityTheory.ChartRestriction.DS.TRGap
