import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedVacuumFixedByStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerGlobalEvalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerPairModelGoodDescentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianStabilizerNormalizedHaarFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTripleImplicitIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTripleImplicitUnfoldingStatement

noncomputable section

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB GlobalTheory.ThK.ConeEuler GlobalTheory.UnrEuler
open scoped Classical

namespace GlobalTheory.ConeEulerConst

theorem unrFac_ne_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ν : Chr F E) (𝔞 : FractionalIdeal (𝓞 E)⁰ E) {s : ℂ} (hs : 0 < s.re) (v : HeightOneSpectrum (𝓞 F)) :
    unrFac ν 𝔞 s v ≠ 0 := by
  refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun w _ => mul_ne_zero (Units.ne_zero _) (npow_ne_zero w _))
    (Finset.prod_ne_zero_iff.2 fun w _ => inv_ne_zero (eulerPoly_ne_zero fun b hb => ?_))
  have hb1 : ‖(b : ℂ)‖ = 1 := by
    unfold charFam at hb
    split_ifs at hb
    · rw [Multiset.mem_singleton.1 hb, norm_val]
    · simp at hb
  rw [norm_mul, hb1, one_mul, norm_npow]
  refine Real.rpow_lt_one_of_one_lt_of_neg ?_ (by simpa using hs)
  exact_mod_cast one_lt_absNorm w

theorem cone_pure_eq_const_smul : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    CfgB B G G₁ H H' → IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b)))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F v) → ℂ),
    ei ≠ 0 → (∀ v, ev v (G.M'.vac v) = G₁.M'.vac v ∧ (SB _).map (ev v) = SB _) →
    (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) → e' (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ K : Subgroup (UA σ G.V'.J), IsStab B K →
    ∀ (μK : Measure K) (μ : Measure (AE F E)ˣ), μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ (μKv : ∀ v : Pl F, Measure (KAt K (evFin F v))) (μv : ∀ v : Pl F, Measure (idelesAt E (evFin F v)))
      (μKi : Measure (KAt K (evI F))) (μi : Measure (idelesAt E (evI F))),
    (∀ v, IsNormK K (evFin F v) (μKv v)) → (∀ v, IsNormE E v (μv v)) → IsNormK K (evI F) μKi → μi.IsHaarMeasure →
    ∀ T : Finset (Pl F), X.T ⊆ T → ∃ κ : ℂ, κ ≠ 0 ∧
      ∀ (f : SInf F (Fin (b + 2) × Fin (a + (b + 2)))) (φ : ∀ v : Pl F, (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ),
      (∀ v, φ v ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v)) → (∀ v, v ∉ T → φ v = G.M'.vac v) →
      cone B G.M' om' e' K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (pure f φ) =
        κ • pure (coneInf B G.M' om' ei K μKi μi (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) f)
          (fun v => if v ∈ T then coneFin B G.M' om' v (ev v) K (μKv v) (μv v) (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (φ v)
            else G₁.M'.vac v) := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' X om om' om₁ om₁' hC hT hT₁ e' he' ei' ev' hei' hev' hpure' K hK μK μ hμK hμ
    μKv μv μKI μI hμKv hμv hμKI hμI T hXT
  obtain ⟨κ, hκ, hM⟩ := GlobalTheory.T.hermitian_stabilizer_normalized_haar_factor B hT.base hT.geo.hV' hK μK μ hμK hμ μKI μI hμKI hμI μKv μv hμKv hμv
  have hne : ∏' v : {v : Pl F // v ∉ T},
      unrFac X.ν (H.𝔟⁻¹ * conjI σ H'.𝔟) ((((a - (b + 2)) / 2 + 1 : ℕ) : ℂ)) v.1 ≠ 0 := by
    have hs := (GlobalTheory.T.seesaw_triple_implicit_unfolding hKP B hC hT hT₁ he' ei' ev' hei' hev' hpure' hK μv hμv T hXT 0).2.2.2.2.2
    have h := tprod_one_add_ne_zero_of_summable (f := fun v : {v : Pl F // v ∉ T} =>
      unrFac X.ν (H.𝔟⁻¹ * conjI σ H'.𝔟) ((((a - (b + 2)) / 2 + 1 : ℕ) : ℂ)) v.1 - 1) (fun v => by
        rw [add_sub_cancel]
        refine unrFac_ne_zero _ _ ?_ _
        rw [Complex.natCast_re]
        exact_mod_cast Nat.succ_pos _) hs
    simpa only [add_sub_cancel] using h
  refine ⟨(κ : ℂ) * ∏' v : {v : Pl F // v ∉ T},
      unrFac X.ν (H.𝔟⁻¹ * conjI σ H'.𝔟) ((((a - (b + 2)) / 2 + 1 : ℕ) : ℂ)) v.1,
    mul_ne_zero (Complex.ofReal_ne_zero.2 hκ.ne') hne, fun f' φ' hφ' hvac => ?_⟩
  have hP := (Check.isPair_of_isTriple hT).2
  have hν : Continuous X.ν := by
    have h1 := hT.chars.heckeα.1
    have h2 := hT.chars.heckeβ.1
    show Continuous fun l => X.α l / X.β l
    exact h1.div' h2
  have hfix : ∀ v ∉ T, ∀ k ∈ KAt K (evFin F v), Acts (evFin F v) (om' (k, 1)) (G.M'.vac v) (G.M'.vac v) :=
    fun v hv => (GlobalTheory.T.unramified_vacuum_fixed_by_stabilizer B G X om om' hT v (fun h => hv (hXT h))).2 K hK
  have hfac := GlobalTheory.T.stabilizer_pair_model_good_descent hKP B G.M' G₁.M' hP hT₁.geo.hM' hK e' ei' ev' hev' hpure' (cA σ)
    (Matrix.vecMulVec (incV F H.y) (incV F H'.x)) (shiftB σ H H') (fun _ => rfl) X.ν hν
    ((a - (b + 2)) / 2 + 1) T f' φ' hφ' hvac hfix
  obtain ⟨hloc, hinf⟩ := GlobalTheory.T.seesaw_triple_implicit_identity hKP B hC hT hT₁ he' ei' ev' hei' hev' hpure' hK μKI μI hμKI hμI
    μKv μv hμKv hμv
  have hpol1 := GlobalTheory.T.exists_schwartz_eq_coneInfFun_shiftB hKP.base B G G₁ H H' hC e' he' K hK X om om' om₁ om₁' hT hT₁ ei' ev' hei' hev' hpure' μKI μI
    hμKI hμI f'
  have hU := fun y => GlobalTheory.T.seesaw_triple_implicit_unfolding hKP B hC hT hT₁ he' ei' ev' hei' hev' hpure' hK μv hμv T hXT y
  have hMy := fun y : Fin b × Fin (a + b) → AF F => hM T
      (fun k l => coneInfInt B G.M' om' ei' (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) f' k l (fun i => evI F (y i)))
      (fun v k l => coneFinInt B G.M' om' v (ev' v) (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (φ' v) k l
        (fun i => evFin F v (y i)))
      (fun v l => coneFinInt B G.M' om' v (ev' v) (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (G.M'.vac v) 1 l
        (fun i => evFin F v (y i)))
      (hinf f' _).1 (hinf f' _).2 (fun v _ => (hloc v (φ' v) (hφ' v) _).1) (fun v _ => (hloc v (φ' v) (hφ' v) _).2)
      (hU y).1 (hU y).2.1 (hU y).2.2.1 (hU y).2.2.2.1
  have hI := fun (k : K) (y : Fin b × Fin (a + b) → AF F) => funext fun l => hfac k.1 k.2 l y
  funext y
  obtain ⟨-, -, -, -, hg, hUs⟩ := hU y
  have hcone := (integral_congr_ae (μ := μK) (ae_of_all _ fun k : K =>
    congrArg (fun g : (AE F E)ˣ → ℂ => ∫ l, g l ∂μ) (hI k y))).trans (hMy y).2.2
  change cone B G.M' om' e' K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (pure f' φ') y = _ at hcone
  have hVfin : (Function.mulSupport fun v : Pl F => G₁.M'.vac v (fun i => evFin F v (y i))).Finite := by
    have hev : ∀ᶠ v in cofinite, G₁.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∧
        ∀ i, evFin F v (y i) ∈ v.adicCompletionIntegers F :=
      hT₁.geo.hM'.std.and (Filter.eventually_all.2 fun i => (y i).2.2.mono fun _ hv => hv)
    refine (Filter.eventually_cofinite.1 hev).subset fun v hv hP => hv ?_
    show G₁.M'.vac v _ = 1
    rw [hP.1]
    exact Set.indicator_of_mem (show (fun i => evFin F v (y i)) ∈
      {z : Fin b × Fin (a + b) → Fv F v | ∀ i, z i ∈ v.adicCompletionIntegers F} from hP.2) 1
  set S := hVfin.toFinset with hS
  set U : {v : Pl F // v ∉ T} → ℂ := fun w =>
    unrFac X.ν (H.𝔟⁻¹ * conjI σ H'.𝔟) ((((a - (b + 2)) / 2 + 1 : ℕ) : ℂ)) w.1 with hUdef
  set V : Pl F → ℂ := fun v => G₁.M'.vac v (fun i => evFin F v (y i)) with hVdef
  have hUm : Multipliable U := by
    have := multipliable_one_add_of_summable (f := fun w => U w - 1) hUs
    simpa using this
  have hVt : ∏' w : {v : Pl F // v ∉ T}, V w.1 = ∏ v ∈ S \ T, V v := by
    rw [tprod_eq_prod (s := (S \ T).subtype (fun v => v ∉ T)) ?_]
    · rw [Finset.prod_subtype_eq_prod_filter]
      congr 1
      ext v
      simp only [Finset.mem_filter, Finset.mem_sdiff]
      tauto
    · intro w hw
      by_contra hne
      apply hw
      rw [Finset.mem_subtype, Finset.mem_sdiff, hS, Set.Finite.mem_toFinset]
      exact ⟨hne, w.2⟩
  have hVm : Multipliable fun w : {v : Pl F // v ∉ T} => V w.1 := by
    refine multipliable_of_finite_mulSupport ?_
    exact hVfin.preimage Subtype.val_injective.injOn
  have hgl : ∏' w : {v : Pl F // v ∉ T}, ∫ l : idelesAt E (evFin F w.1),
      coneFinInt B G.M' om' w.1 (ev' w.1) (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (G.M'.vac w.1) 1 l.1
        (fun i => evFin F w.1 (y i)) ∂(μv w.1) = (∏' w, U w) * ∏ v ∈ S \ T, V v := by
    refine (tprod_congr (fun w : {v : Pl F // v ∉ T} => hg w.1 w.2)).trans ?_
    rw [← hVt]
    exact hUm.tprod_mul hVm
  have hpsi : ∏ᶠ v : Pl F, (if v ∈ T then
      coneFin B G.M' om' v (ev' v) K (μKv v) (μv v) (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (φ' v)
      else G₁.M'.vac v) (fun i => evFin F v (y i)) =
      (∏ v ∈ T, coneFin B G.M' om' v (ev' v) K (μKv v) (μv v) (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (φ' v)
        (fun i => evFin F v (y i))) * ∏ v ∈ S \ T, V v := by
    rw [finprod_eq_prod_of_mulSupport_subset (s := T ∪ S)]
    · rw [← Finset.union_sdiff_self_eq_union, Finset.prod_union Finset.disjoint_sdiff]
      congr 1
      · exact Finset.prod_congr rfl fun v hv => by rw [if_pos hv]
      · exact Finset.prod_congr rfl fun v hv => by rw [if_neg (Finset.mem_sdiff.1 hv).2]
    · intro v hv
      rw [Finset.coe_union, Set.mem_union]
      by_cases hvT : v ∈ T
      · exact Or.inl hvT
      · right
        rw [hS, Set.Finite.coe_toFinset]
        simpa [if_neg hvT] using hv
  rw [hcone, hgl, Pi.smul_apply, smul_eq_mul]
  unfold IndefiniteRowSideFullHecke.WeilTensorModels.pure
  rw [hpsi, congrFun (coe_coneInf hpol1)]
  simp only [coneInfFun, coneFin]
  ring

end GlobalTheory.ConeEulerConst

end
