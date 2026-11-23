import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentActionFiniteSetSchwartzInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedTensorSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvIOneSubEInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepIntertwinesAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdelicPureTensorEqProductLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryPreservesPolynomialFock
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot GlobalTheory.ThK.ConeEuler

noncomputable section

namespace GlobalTheory.ThK.Bot.CoefFin

open GlobalTheory.TruncFix (truncU)

theorem finprod_div_finprod {ι : Type} (a b : ι → ℂ) (ha : (Function.mulSupport a).Finite) (h0 : ∏ᶠ v, a v ≠ 0)
    (T : Finset ι) (hb : ∀ v ∉ T, b v = a v) : (∏ᶠ v, b v) / ∏ᶠ v, a v = ∏ v ∈ T, b v / a v := by
  classical
  have hT : T ⊆ T ∪ ha.toFinset := Finset.subset_union_left
  have h1 : Function.mulSupport a ⊆ ((T ∪ ha.toFinset : Finset ι) : Set ι) := fun v hv => by
    simp only [Finset.coe_union, Set.Finite.coe_toFinset]; exact Or.inr hv
  have h2 : Function.mulSupport b ⊆ ((T ∪ ha.toFinset : Finset ι) : Set ι) := fun v hv => by
    simp only [Finset.coe_union, Set.Finite.coe_toFinset]
    by_cases h : v ∈ T
    · exact Or.inl h
    · refine Or.inr ?_
      rw [Function.mem_mulSupport, ← hb v h]; exact hv
  rw [finprod_eq_prod_of_mulSupport_subset _ h1, ← Finset.prod_sdiff hT] at h0 ⊢
  rw [finprod_eq_prod_of_mulSupport_subset _ h2, ← Finset.prod_sdiff hT,
    Finset.prod_congr rfl (fun v hv => hb v (Finset.mem_sdiff.1 hv).2), mul_div_mul_left _ _ (left_ne_zero_of_mul h0),
    Finset.prod_div_distrib]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem mat_archRest {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (k : UA σ J) :
    mat ((compArch σ J k)⁻¹ * k) = eInf F • (1 : Matrix (Fin n) (Fin n) (AE F E)) + (1 - eInf F) • mat k := by
  rw [GlobalTheory.StabHaar.mat_mul, ← map_inv, mat_compArch, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul,
    ← GlobalTheory.StabHaar.mat_mul, inv_mul_cancel, GlobalTheory.StabHaar.mat_one]

theorem archRest_triv {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (k : UA σ J) :
    ∀ u : AF F, At (evI F) u → u • (mat ((compArch σ J k)⁻¹ * k) - 1) = 0 := by
  intro u hu
  have h : u * eInf F = u := by
    have h := partInf_of_at (M := AF F) hu
    rw [partInf, smul_eq_mul] at h
    rw [mul_comm]; exact h
  rw [mat_archRest, smul_sub, smul_add, smul_smul, smul_smul, h, mul_sub, mul_one, h,
    sub_self, zero_smul, add_zero, sub_self]

theorem truncU_archRest {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (k : UA σ J) (v : Pl F) :
    truncU {v} ((compArch σ J k)⁻¹ * k) = compAt σ J v k := by
  refine Subtype.ext (Units.ext ?_)
  show GlobalTheory.TruncFix.truncMat (GlobalTheory.TruncFix.idem {v}) (mat ((compArch σ J k)⁻¹ * k)) = mat (compAt σ J v k)
  rw [GlobalTheory.TruncFix.idem_singleton, GlobalTheory.TruncFix.truncMat, mat_archRest, mat_compAt]
  have h1 : GlobalTheory.LatVac.liftV v 1 * eInf F = 0 := by
    have h := at_partFin (M := AF F) v (1 : AF F) (eInf F) (map_zero (evalV F v))
    rw [partFin, smul_eq_mul, smul_eq_mul, mul_one] at h
    rw [mul_comm]; exact h
  have h2 : GlobalTheory.LatVac.liftV v 1 * (1 - eInf F) = GlobalTheory.LatVac.liftV v 1 := by rw [mul_sub, mul_one, h1, sub_zero]
  rw [smul_sub, smul_add, smul_smul, smul_smul, h1, h2, zero_smul, zero_add, show eFin v = GlobalTheory.LatVac.liftV v 1 from rfl,
    sub_smul, one_smul]
  abel

variable {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
  {r s' r₁ s₁ : ℕ}

theorem om_one (Φ : Fn F n d) : om ((1 : UA σ X.J), (1 : UA σ W.J)) Φ = Φ := by
  rw [← Prod.one_eq_mk, map_one]; rfl

theorem om_pure_of_supp (hA : ActsEx) (hP : IsPair B M χX χW om r s' r₁ s₁) (f : SInf F (Fin n × Fin d))
    (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) (hSB : ∀ v, φ v ∈ SB _) (hcof : ∀ᶠ v in cofinite, φ v = M.vac v)
    (T : Finset (Pl F)) (k : UA σ X.J) (hk : ∀ v ∉ T, compAt σ X.J v k = 1) :
    om (k, 1) (pure f φ) = pure (locOpInf (om (compArch σ X.J k, 1)) f)
      (fun v => locOp v (om (compAt σ X.J v k, 1)) (φ v)) := by
  classical
  have hM := hP.good
  set S : Finset (Pl F) := T ∪ (Filter.eventually_cofinite.1 hcof).toFinset with hS
  have hST : ∀ v ∉ S, v ∉ T := fun v hv h => hv (Finset.mem_union_left _ h)
  have hSφ : ∀ v ∉ S, φ v = M.vac v := fun v hv => by
    by_contra h
    exact hv (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 h))
  have hfix : ∀ v ∉ S, Acts (evFin F v) (om (compAt σ X.J v k, 1)) (M.vac v) (M.vac v) := by
    intro v hv
    rw [hk v (hST v hv)]
    exact fun _ _ => om_one _
  have hvac : ∀ v ∉ S, locOp v (om (compAt σ X.J v k, 1)) (φ v) = M.vac v := by
    intro v hv
    rw [hSφ v hv]
    exact locOp_eq (hM.vac v).1 (hM.vac v).1 (hfix v hv)
  set k' := (compArch σ X.J k)⁻¹ * k with hk'
  have hsplit : (k, (1 : UA σ W.J)) = (compArch σ X.J k, 1) * (k', 1) := by
    rw [Prod.mk_mul_mk, mul_one, hk', mul_inv_cancel_left]
  have h1 : om (k', 1) (pure f φ) = pure f (fun v => locOp v (om (compAt σ X.J v k, 1)) (φ v)) := by
    have := GlobalTheory.TruncFixOm.om_archtriv B M _ _ om _ _ _ _ hA hP k' (archRest_triv X.J k) S f φ hSB hSφ
      (fun v hv => by rw [hk', truncU_archRest]; exact hfix v hv)
    simpa only [hk', truncU_archRest] using this
  have h1mem : (1 : UA σ W.J) ∈ UAt σ W (evI F) := fun u _ => by
    show u • (mat (1 : UA σ W.J) - 1) = 0
    rw [GlobalTheory.StabHaar.mat_one, sub_self, smul_zero]
  obtain ⟨Aop, hAop⟩ := GlobalTheory.FockCompactW.exists_op_of_UAt hP.base.std hP.weil (compArch σ X.J k, 1)
    (compArch_mem k) h1mem
  have hcof' : ∀ᶠ v in Filter.cofinite, locOp v (om (compAt σ X.J v k, 1)) (φ v) = M.vac v :=
    Filter.eventually_cofinite.2 (S.finite_toSet.subset fun v hv => by
      by_contra h; exact hv (hvac v h))
  rw [hsplit, map_mul, Module.End.mul_apply, h1,
    GlobalTheory.ArchPureAct.acts_pure F E σ B.ψ n d X W M om hM _ Aop hAop f _ (fun v => locOp_mem _ _ _) hcof',
    locOpInf_eq (hAop f)]

theorem coef_div_eq_prod : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s' r₁ s₁ : ℕ),
    IsPair B M χX χW om r s' r₁ s₁ →
    ∀ [MeasurableSpace (Fin n × Fin d → AF F)] [BorelSpace (Fin n × Fin d → AF F)] (m : Measure (Fin n × Fin d → AF F)), m.IsAddHaarMeasure →
    ∀ (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) →
    coef m om (pure f φ) 1 ≠ 0 → ∀ (T : Finset (Pl F)) (g : UA σ X.J), (∀ v ∉ T, compAt σ X.J v g = 1) →
      coef m om (pure f φ) g / coef m om (pure f φ) 1 = coef m om (pure f φ) (compArch σ X.J g) / coef m om (pure f φ) 1 *
        ∏ v ∈ T, coef m om (pure f φ) (compAt σ X.J v g) / coef m om (pure f φ) 1 := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s' r₁ s₁ hP _ _ m hm f φ hSB hcof h0 T g hg
  classical
  have hA : ActsEx := GlobalTheory.ThK.LocalOps.actsEx hKP.base
  letI mI : MeasurableSpace (Fin n × Fin d → mixedEmbedding.mixedSpace F) := borel _
  haveI : BorelSpace (Fin n × Fin d → mixedEmbedding.mixedSpace F) := ⟨rfl⟩
  letI mV : ∀ v : Pl F, MeasurableSpace (Fin n × Fin d → Fv F v) := fun _ => borel _
  haveI bV : ∀ v : Pl F, BorelSpace (Fin n × Fin d → Fv F v) := fun _ => ⟨rfl⟩
  haveI := hm
  obtain ⟨μi, hμi⟩ : ∃ μ : Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F), μ.IsAddHaarMeasure :=
    ⟨Measure.addHaar, inferInstance⟩
  obtain ⟨μv, hμv, hμv1⟩ : ∃ μv : ∀ v : Pl F, Measure (Fin n × Fin d → Fv F v), (∀ v, (μv v).IsAddHaarMeasure) ∧
      ∀ v, μv v {x | ∀ i, x i ∈ v.adicCompletionIntegers F} = 1 := by
    let K : ∀ v : Pl F, TopologicalSpace.PositiveCompacts (Fin n × Fin d → Fv F v) := fun v =>
      ⟨⟨Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)),
        isCompact_univ_pi fun _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v⟩, by
          show (interior (Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)))).Nonempty
          rw [(isOpen_set_pi Set.finite_univ fun _ _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_integers v).interior_eq]
          exact ⟨0, fun i _ => (v.adicCompletionIntegers F).zero_mem⟩⟩
    refine ⟨fun v => Measure.addHaarMeasure (K v), fun v => inferInstance, fun v => ?_⟩
    have e : {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} = (K v : Set (Fin n × Fin d → Fv F v)) := by
      ext x; simp [K]
    rw [e]
    exact Measure.addHaarMeasure_self
  haveI := hμv
  obtain ⟨c₀, -, hpure⟩ := GlobalTheory.AdelicHaarPure.integral_pure_haar F (Fin n × Fin d) m μi μv hμv1
  have hstd : ∀ᶠ v in cofinite, φ v = GlobalTheory.RatWeilOp.ind (Fin n × Fin d) v :=
    (hcof.and hP.good.std).mono fun v hv => hv.1.trans hv.2
  have hloc1 : ∀ v, locOp v (om ((1 : UA σ X.J), (1 : UA σ W.J))) (φ v) = φ v := fun v =>
    locOp_of_fix (fun _ _ => om_one _) (hSB v)
  have hinf1 : locOpInf (om ((1 : UA σ X.J), (1 : UA σ W.J))) f = f := locOpInf_eq fun _ _ => om_one _
  let I : UA σ X.J → ℂ := fun k => ∫ z, locOpInf (om (k, 1)) f z * starRingEnd ℂ (f z) ∂μi
  let L : ∀ v : Pl F, UA σ X.J → ℂ := fun v k => ∫ t, locOp v (om (k, 1)) (φ v) t * starRingEnd ℂ (φ v t) ∂(μv v)
  have key : ∀ (S : Finset (Pl F)) (k : UA σ X.J), (∀ v ∉ S, compAt σ X.J v k = 1) →
      coef m om (pure f φ) k = c₀ * I (compArch σ X.J k) * ∏ᶠ v, L v (compAt σ X.J v k) := by
    intro S k hk
    have hfam : GlobalTheory.RatWeilOp.IsFam (fun v => locOp v (om (compAt σ X.J v k, 1)) (φ v)) := by
      refine ⟨fun v => locOp_mem _ _ _, ?_⟩
      filter_upwards [hstd, S.finite_toSet.eventually_cofinite_notMem] with v h1 h2
      rw [hk v h2, hloc1, h1]
    rw [coef, om_pure_of_supp hA hP f φ hSB hcof S k hk]
    exact (GlobalTheory.TensorSquareIntegral.integral_pure_mul_conj m μi μv c₀ hpure _ f _ φ hfam ⟨hSB, hstd⟩).2
  have hfin : (Function.mulSupport fun v => L v 1).Finite := by
    refine (Filter.eventually_cofinite.1 hstd).subset fun v hv h => hv ?_
    show ∫ t, locOp v (om (1, 1)) (φ v) t * starRingEnd ℂ (φ v t) ∂(μv v) = 1
    rw [hloc1, h]
    exact GlobalTheory.TensorSquareIntegral.integral_ind v (μv v) (hμv1 v)
  have k1 : coef m om (pure f φ) 1 = c₀ * I 1 * ∏ᶠ v, L v 1 := by
    simpa only [map_one] using key ∅ 1 fun v _ => map_one _
  rw [k1] at h0 ⊢
  have hP0 : ∏ᶠ v, L v 1 ≠ 0 := right_ne_zero_of_mul h0
  have hc0 : c₀ * I 1 ≠ 0 := left_ne_zero_of_mul h0
  obtain ⟨a1, a2⟩ := (SuppOne.comp_of_supp F E σ n X (compArch σ X.J g)).2 (compArch_mem g)
  have kinf : coef m om (pure f φ) (compArch σ X.J g) = c₀ * I (compArch σ X.J g) * ∏ᶠ v, L v 1 := by
    simpa only [a1, a2] using key ∅ (compArch σ X.J g) fun v _ => a2 v
  have kv : ∀ v, coef m om (pure f φ) (compAt σ X.J v g) / (c₀ * I 1 * ∏ᶠ v, L v 1) = L v (compAt σ X.J v g) / L v 1 := by
    intro v
    obtain ⟨b1, b2, b3⟩ := (SuppOne.comp_of_supp F E σ n X (compAt σ X.J v g)).1 v (compAt_mem v g)
    have b4 : ∀ w ∉ ({v} : Finset (Pl F)), compAt σ X.J w (compAt σ X.J v g) = 1 := fun w hw =>
      b3 w (by simpa using hw)
    rw [key {v} _ b4, b2, mul_div_mul_left _ _ hc0,
      finprod_div_finprod _ _ hfin hP0 {v} (fun w hw => by rw [b4 w hw]), Finset.prod_singleton, b1]
  rw [Finset.prod_congr rfl fun v _ => kv v, kinf, key T g hg, mul_div_mul_right _ _ hP0,
    ← finprod_div_finprod _ _ hfin hP0 T (fun w hw => by rw [hg w hw]), mul_div_mul_comm]

end GlobalTheory.ThK.Bot.CoefFin

end
