import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TmulMemLocId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentActionFiniteSetSchwartzInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompMemOfIsStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyCompFinMemIntLocAdele
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepIntertwinesAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionRestrictedProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorFixesIntegralIndicatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedVacuumFixedByStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBEvaluationInfinitePart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalStabilizerLocallyConstantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBLocalPartPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorIdeleConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerGlobalEval
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableIdelesPowerDecay
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUnitaryOneParameterRealPlaceComponent

open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB
open scoped Classical nonZeroDivisors TensorProduct
open GlobalTheory.Doubling (absE)
open GlobalTheory.LocIdeal (locId tmul_mem_locId)
open GlobalTheory.ThK.ConeEuler
open GlobalTheory.TruncFix (truncU)

noncomputable section

namespace GlobalTheory.ConeMajorant

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem norm_finprod_le {ι : Type} (c : ι → ℂ) (hc : (Function.mulSupport c).Finite) (S : Finset ι) (C : ι → ℝ)
    (hS : ∀ v ∈ S, ‖c v‖ ≤ C v) (h1 : ∀ v ∉ S, ‖c v‖ ≤ 1) : ‖∏ᶠ v, c v‖ ≤ ∏ v ∈ S, C v := by
  rw [finprod_eq_prod_of_mulSupport_subset c (s := S ∪ (hc.toFinset \ S)) (by
    intro v hv
    by_cases h : v ∈ S
    · simp [h]
    · simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_sdiff, Set.Finite.mem_toFinset]
      exact Or.inr ⟨hv, h⟩), Finset.prod_union Finset.disjoint_sdiff, norm_mul, norm_prod, norm_prod]
  have a1 : ∏ v ∈ S, ‖c v‖ ≤ ∏ v ∈ S, C v := Finset.prod_le_prod (fun _ _ => norm_nonneg _) hS
  have a2 : ∏ v ∈ hc.toFinset \ S, ‖c v‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) fun v hv => h1 v (Finset.mem_sdiff.1 hv).2
  exact (mul_le_of_le_one_right (Finset.prod_nonneg fun _ _ => norm_nonneg _) a2).trans a1

omit [NumberField E] in

theorem locId_mono (v : Pl F) {𝔞 𝔟 : FractionalIdeal (𝓞 E)⁰ E} (h : 𝔞 ≤ 𝔟) : locId v 𝔞 ≤ locId v 𝔟 :=
  AddSubgroup.closure_mono fun _ ⟨a, ha, x, hx, e⟩ => ⟨a, ha, x, h hx, e⟩

theorem exists_mul_mem_intLoc (v : Pl F) (z : Fv F v ⊗[F] E) :
    ∃ d : (𝓞 E)⁰, ((1 : Fv F v) ⊗ₜ[F] ((d : 𝓞 E) : E)) * z ∈ intLoc F E v := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨1, by rw [mul_zero]; exact zero_mem _⟩
  | tmul a x =>
    obtain ⟨c, hc, hca⟩ := HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v a
    obtain ⟨n, m, hm, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
    have hm0 : algebraMap (𝓞 E) E m ≠ 0 := by simpa using nonZeroDivisors.ne_zero hm
    have hc' : algebraMap (𝓞 F) (𝓞 E) c ∈ (𝓞 E)⁰ := mem_nonZeroDivisors_of_ne_zero (by
      simpa using nonZeroDivisors.ne_zero hc)
    refine ⟨⟨_, mul_mem hc' hm⟩, ?_⟩
    convert tmul_mem_intLoc (E := E) hca n using 1
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have e : (((algebraMap (𝓞 F) (𝓞 E) c * m : 𝓞 E)) : E) * (algebraMap (𝓞 E) E n / algebraMap (𝓞 E) E m) =
        (c : F) • (n : E) := by
      rw [Algebra.smul_def]
      change algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) c * m) * _ = algebraMap F E (algebraMap (𝓞 F) F c) * algebraMap (𝓞 E) E n
      rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
      field_simp
    rw [e, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_comm]
    rfl
  | add y z hy hz =>
    obtain ⟨c, hc⟩ := hy
    obtain ⟨d, hd⟩ := hz
    refine ⟨c * d, ?_⟩
    have e : ((1 : Fv F v) ⊗ₜ[F] (((c * d : (𝓞 E)⁰) : 𝓞 E) : E)) * (y + z) =
        ((1 : Fv F v) ⊗ₜ[F] ((d : 𝓞 E) : E)) * (((1 : Fv F v) ⊗ₜ[F] ((c : 𝓞 E) : E)) * y) +
        ((1 : Fv F v) ⊗ₜ[F] ((c : 𝓞 E) : E)) * (((1 : Fv F v) ⊗ₜ[F] ((d : 𝓞 E) : E)) * z) := by
      rw [← mul_assoc, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_add]
      simp [mul_comm]
    rw [e]
    exact add_mem (mul_mem (tmul_mem_intLoc (one_mem _) _) hc) (mul_mem (tmul_mem_intLoc (one_mem _) _) hd)

theorem exists_subset_locId (v : Pl F) {C : Set (Fv F v ⊗[F] E)} (hC : IsCompact C) :
    ∃ 𝔞 : FractionalIdeal (𝓞 E)⁰ E, ∀ z ∈ C, z ∈ locId v 𝔞 := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := GlobalTheory.Doubling.isTopologicalRing_tens
  obtain ⟨d, hd⟩ := hC.elim_directed_cover
    (fun d : (𝓞 E)⁰ => {z | ((1 : Fv F v) ⊗ₜ[F] ((d : 𝓞 E) : E)) * z ∈ intLoc F E v})
    (fun d => (isCompact_isOpen_intLoc v).2.preimage (continuous_const_mul _))
    (fun z _ => Set.mem_iUnion.2 (exists_mul_mem_intLoc v z)) (fun c d => ⟨c * d, fun z hz => by
      have := mul_mem (tmul_mem_intLoc (one_mem (v.adicCompletionIntegers F)) (d : 𝓞 E)) hz
      rw [← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul] at this
      simpa [mul_comm] using this, fun z hz => by
      have := mul_mem (tmul_mem_intLoc (one_mem (v.adicCompletionIntegers F)) (c : 𝓞 E)) hz
      rw [← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul] at this
      simpa using this⟩)
  have hd0 : ((d : 𝓞 E) : E) ≠ 0 := by simpa using nonZeroDivisors.ne_zero d.2
  refine ⟨FractionalIdeal.spanSingleton _ ((d : 𝓞 E) : E)⁻¹, fun z hz => ?_⟩
  have e : z = ((1 : Fv F v) ⊗ₜ[F] ((d : 𝓞 E) : E)⁻¹) * (((1 : Fv F v) ⊗ₜ[F] ((d : 𝓞 E) : E)) * z) := by
    rw [← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ hd0, ← Algebra.TensorProduct.one_def,
      one_mul]
  rw [e]
  refine intLoc_induction (p := fun w => ((1 : Fv F v) ⊗ₜ[F] ((d : 𝓞 E) : E)⁻¹) * w ∈ locId v _) (fun a ha x => ?_)
    (by rw [mul_zero]; exact zero_mem _) (fun _ _ h h' => by rw [mul_add]; exact add_mem h h')
    (fun _ h => by rw [mul_neg]; exact neg_mem h) (hd hz)
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  exact tmul_mem_locId ha ((FractionalIdeal.mem_spanSingleton _).2 ⟨x, by rw [Algebra.smul_def, mul_comm]⟩)

theorem mul_eInf {u : AF F} (hu : At (evI F) u) : u * eInf F = u := by
  have h := partInf_of_at (M := AF F) hu
  rw [partInf, smul_eq_mul] at h
  rw [mul_comm]; exact h

theorem mat_finPart {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (k : UA σ J) :
    mat ((compArch σ J k)⁻¹ * k) = eInf F • (1 : Matrix (Fin n) (Fin n) (AE F E)) + (1 - eInf F) • mat k := by
  rw [GlobalTheory.StabHaar.mat_mul, ← map_inv, mat_compArch, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul,
    ← GlobalTheory.StabHaar.mat_mul, inv_mul_cancel, GlobalTheory.StabHaar.mat_one]

theorem truncU_finPart {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (k : UA σ J) (v : Pl F) :
    truncU {v} ((compArch σ J k)⁻¹ * k) = compAt σ J v k := by
  refine Subtype.ext (Units.ext ?_)
  show GlobalTheory.TruncFix.truncMat (GlobalTheory.TruncFix.idem {v}) (mat ((compArch σ J k)⁻¹ * k)) = mat (compAt σ J v k)
  rw [GlobalTheory.TruncFix.idem_singleton, GlobalTheory.TruncFix.truncMat, mat_finPart, mat_compAt]
  have h1 : GlobalTheory.LatVac.liftV v 1 * eInf F = 0 := by
    have h := at_partFin (M := AF F) v (1 : AF F) (eInf F) (map_zero (evalV F v))
    rw [partFin, smul_eq_mul, smul_eq_mul, mul_one, mul_comm] at h
    exact h
  have h2 : GlobalTheory.LatVac.liftV v 1 * (1 - eInf F) = GlobalTheory.LatVac.liftV v 1 := by rw [mul_sub, mul_one, h1, sub_zero]
  rw [smul_sub, smul_add, smul_smul, smul_smul, h1, h2, zero_smul, zero_add, show eFin v = GlobalTheory.LatVac.liftV v 1 from rfl,
    sub_smul, one_smul]
  abel

theorem partFin_shiftB_unitAt {n d n₁ d₁ : ℕ} (H : Plane E n n₁) (H' : Plane E d d₁) (v : Pl F) (l : (AE F E)ˣ) :
    partFin v (shiftB σ H H' (unitAt E v l)) = partFin v (shiftB σ H H' l) := by
  unfold partFin
  rw [smul_shiftB, smul_shiftB]
  congr 2
  show eFin v • (eFin v • (l : AE F E) + (1 - eFin v) • 1) = eFin v • (l : AE F E)
  rw [smul_add, smul_smul, smul_smul, eFin_idem, idem_mul_one_sub (eFin_idem v), zero_smul, add_zero]

theorem om_pure_stab (hP : GlobalTheory.FunPr.Hypotheses₂) {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E}
    {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (hT : IsTriple B G X om om') {K : Subgroup (UA σ G.V'.J)}
    (hK : IsStab B K) {k : UA σ G.V'.J} (hk : k ∈ K) (f : SInf F (Fin a' × Fin (a + a')))
    (φ : ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ) (T : Finset (Pl F)) (hXT : X.T ⊆ T) (hSB : ∀ v, φ v ∈ SB _)
    (hT' : ∀ v ∉ T, φ v = G.M'.vac v) :
    om' (k, 1) (pure f φ) = pure (locOpInf (om' (compArch σ G.V'.J k, 1)) f)
      (fun v => locOp v (om' (compAt σ G.V'.J v k, 1)) (φ v)) ∧
    ∀ v ∉ T, locOp v (om' (compAt σ G.V'.J v k, 1)) (φ v) = G.M'.vac v := by
  have hA := GlobalTheory.ThK.LocalOps.actsEx hP
  have hM := hT.geo.hM'
  have hfix : ∀ v ∉ T, Acts (evFin F v) (om' (compAt σ G.V'.J v k, 1)) (G.M'.vac v) (G.M'.vac v) := fun v hv =>
    (GlobalTheory.T.unramified_vacuum_fixed_by_stabilizer B G X om om' hT v fun h => hv (hXT h)).2 K hK _
      (mem_KAt.2 ⟨(StabComp.comp_mem_of_isStab F E σ B _ _ K hK k hk).1 v, compAt_mem v k⟩)
  have hvac : ∀ v ∉ T, locOp v (om' (compAt σ G.V'.J v k, 1)) (φ v) = G.M'.vac v := by
    intro v hv
    rw [hT' v hv]
    exact locOp_eq (hM.vac v).1 (hM.vac v).1 (hfix v hv)
  refine ⟨?_, hvac⟩
  set k' := (compArch σ G.V'.J k)⁻¹ * k with hk'
  have hsplit : (k, (1 : UA σ G.W.J)) = (compArch σ G.V'.J k, 1) * (k', 1) := by
    rw [Prod.mk_mul_mk, mul_one, hk', mul_inv_cancel_left]
  have h1 : om' (k', 1) (pure f φ) = pure f (fun v => locOp v (om' (compAt σ G.V'.J v k, 1)) (φ v)) := by
    have := GlobalTheory.TruncFixOm.om_archtriv B G.M' _ _ om' _ _ _ _ hA (Inhab.pairV' hT) k' (fun u hu => by
        rw [hk', mat_finPart, smul_sub, smul_add, smul_smul, smul_smul, mul_eInf hu, mul_sub, mul_one, mul_eInf hu,
          sub_self, zero_smul, add_zero, sub_self]) T f φ hSB hT'
      (fun v hv => by rw [hk', truncU_finPart]; exact hfix v hv)
    simpa only [hk', truncU_finPart] using this
  have h1mem : (1 : UA σ G.W.J) ∈ UAt σ G.W (evI F) := fun u _ => by
    show u • (mat (1 : UA σ G.W.J) - 1) = 0
    rw [GlobalTheory.StabHaar.mat_one, sub_self, smul_zero]
  obtain ⟨Aop, hAop⟩ := GlobalTheory.ArchLocalAct.exists_op_of_UAt hT.base.std hT.weil' (compArch σ G.V'.J k, 1)
    (compArch_mem k) h1mem
  have hcof : ∀ᶠ v in Filter.cofinite, locOp v (om' (compAt σ G.V'.J v k, 1)) (φ v) = G.M'.vac v :=
    Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => by
      by_contra h; exact hv (hvac v h))
  rw [hsplit, map_mul, Module.End.mul_apply, h1,
    GlobalTheory.ArchPureAct.acts_pure F E σ B.ψ a' (a + a') G.V' G.W G.M' om' hM _ Aop hAop f _ (fun v => locOp_mem _ _ _) hcof,
    locOpInf_eq (hAop f)]

section Step

variable {B : Base F E} {a b : ℕ} {G : Geo σ a (b + 2)} {G₁ : Geo σ a b} {H : Plane E (b + 2) b}
  {H' : Plane E (a + (b + 2)) (a + b)} {e' : Fn F (b + 2) (a + (b + 2)) →ₗ[ℂ] Fn F b (a + b)}
  {K : Subgroup (UA σ G.V'.J)} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
  {ei : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b))}
  {ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F v) → ℂ}

theorem shift_bound (hP : GlobalTheory.FunPr.Hypotheses₂) (hC : CfgB B G G₁ H H') (he : IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e')
    (hL : LemF.IsLocPart G.M' G₁.M' e' ei ev) (hT : IsTriple B G X om om') (v : Pl F) (y : Fin b × Fin (a + b) → Fv F v)
    (ψ : (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) (hψ : ψ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v)) :
    ∃ (c : ℝ) (C : Set (Fv F v ⊗[F] E)), 0 ≤ c ∧ IsCompact C ∧ ∀ l : (AE F E)ˣ,
      ‖ev v (locOp v (G.M'.co.rho B.ψ (partFin v (shiftB σ H H' l))) ψ) y‖ ≤ c ∧
      (compFin F E v (l : AE F E) ∉ C → ev v (locOp v (G.M'.co.rho B.ψ (partFin v (shiftB σ H H' l))) ψ) y = 0) := by
  obtain ⟨C, hCc, hC0⟩ := LemF.ShiftSupp.ev_shift_eq_zero_off_compact hP F E σ B a b G G₁ H H' hC e' he ei ev hL X om om'
    hT v ψ hψ
  obtain ⟨g, hg, hgl⟩ := GlobalTheory.SchrLocConst.shiftB_locOp_locallyConstant F E σ B G.M' H H' hT.base.std.1 v ψ hψ
  obtain ⟨c, hc⟩ := hCc.exists_bound_of_continuousOn (f := fun z => ev v (g z) y)
    (hg.comp fun w => ev v w y).continuous.continuousOn
  have hu : ∀ l : (AE F E)ˣ, ((GlobalTheory.Doubling.unitFin F E v (unitAt E v l) : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) =
      compFin F E v (l : AE F E) := fun l => compFin_unitAt_self v l
  have h0 : ∀ l : (AE F E)ˣ, compFin F E v (l : AE F E) ∉ C →
      ev v (locOp v (G.M'.co.rho B.ψ (partFin v (shiftB σ H H' l))) ψ) y = 0 := fun l hl => by
    rw [← partFin_shiftB_unitAt, hC0 _ (unitAt_mem v l) (by rwa [hu])]
    rfl
  refine ⟨max c 0, C, le_max_right _ _, hCc, fun l => ⟨?_, h0 l⟩⟩
  by_cases hl : compFin F E v (l : AE F E) ∈ C
  · rw [← partFin_shiftB_unitAt, hgl _ (unitAt_mem v l), hu]
    exact (hc _ hl).trans (le_max_left _ _)
  · rw [h0 l hl, norm_zero]
    exact le_max_right _ _

theorem local_bound (hP : GlobalTheory.FunPr.Hypotheses₂) (hC : CfgB B G G₁ H H') (he : IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e')
    (hL : LemF.IsLocPart G.M' G₁.M' e' ei ev) (hT : IsTriple B G X om om') (hK : IsStab B K) (v : Pl F)
    (y : Fin b × Fin (a + b) → Fv F v)
    (φ : (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) (hφ : φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v)) :
    ∃ (c : ℝ) (𝔞 : FractionalIdeal (𝓞 E)⁰ E), 0 ≤ c ∧ ∀ k ∈ KAt K (evFin F v), ∀ l : (AE F E)ˣ,
      ‖ev v (locOp v (G.M'.co.rho B.ψ (partFin v (shiftB σ H H' l))) (locOp v (om' (k, 1)) φ)) y‖ ≤ c ∧
      (compFin F E v (l : AE F E) ∉ locId v 𝔞 →
        ev v (locOp v (G.M'.co.rho B.ψ (partFin v (shiftB σ H H' l))) (locOp v (om' (k, 1)) φ)) y = 0) := by
  obtain ⟨hc, hlc⟩ := GlobalTheory.T.local_stabilizer_locally_constant hP F E σ B a (b + 2) G X om om' hT K hK v
  have hfin := (hlc φ hφ).range_finite
  haveI := hfin.to_subtype
  haveI := Fintype.ofFinite (Set.range fun k : KAt K (evFin F v) => locOp v (om' (k.1, 1)) φ)
  choose c C hc0 hCc hb using fun ψ : Set.range fun k : KAt K (evFin F v) => locOp v (om' (k.1, 1)) φ =>
    shift_bound hP hC he hL hT v y ψ.1 (by obtain ⟨_, k, rfl⟩ := ψ; exact locOp_mem _ _ _)
  obtain ⟨𝔞, h𝔞⟩ := exists_subset_locId v (isCompact_iUnion hCc)
  refine ⟨∑ ψ, c ψ, 𝔞, Finset.sum_nonneg fun ψ _ => hc0 ψ, fun k hk l => ⟨?_, fun hl => ?_⟩⟩
  · exact (hb ⟨_, ⟨k, hk⟩, rfl⟩ l).1.trans (Finset.single_le_sum (fun ψ _ => hc0 ψ) (Finset.mem_univ _))
  · exact (hb ⟨_, ⟨k, hk⟩, rfl⟩ l).2 fun h => hl (h𝔞 _ (Set.mem_iUnion.2 ⟨_, h⟩))

open GlobalTheory.ConeArchB GlobalTheory.XTermDecay GlobalTheory.HeisSchA GlobalTheory.DiffDecay GlobalTheory.EvZeroInf in

theorem arch_bound (hP : GlobalTheory.FunPr.Hypotheses₂) (hC : CfgB B G G₁ H H') (he : IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e')
    (hL : LemF.IsLocPart G.M' G₁.M' e' ei ev) (hT : IsTriple B G X om om') (hM₁ : G₁.M'.IsGood B.ψ) (hK : IsStab B K)
    (y : Fin b × Fin (a + b) → mixedEmbedding.mixedSpace F) (f : SInf F (Fin (b + 2) × Fin (a + (b + 2)))) (N : ℕ) :
    ∃ c : ℝ, ∀ k ∈ KAt K (evI F), ∀ l : (AE F E)ˣ,
      ‖ei (locOpInf (G.M'.co.rho B.ψ (partInf F (shiftB σ H H' l))) (locOpInf (om' (k, 1)) f)) y‖ ≤
        c / (1 + ∑ w, ‖piInf (B.emb w) (l : AE F E)‖) ^ N := by
  obtain ⟨-, hev, hloc⟩ := hL
  have hM := hT.geo.hM'
  have hψ := hT.base.std
  have hKc : IsCompact (K : Set (UA σ G.V'.J)) := by
    obtain ⟨K', _, _, hK', hc, -, -⟩ := GlobalTheory.StabHaar.stabEx hP F E σ B _ G.V' _ _ hT.base hT.geo.hV'
    rwa [show K = K' from Subgroup.ext fun g => (hK g).trans (hK' g).symm]
  haveI : CompactSpace (KAt K (evI F)) := isCompact_iff_compactSpace.1 (isCompact_KAt hKc _)
  have hSB : ∀ v, G.M'.vac v ∈ SB _ := fun v => (hM.vac v).1
  have hpure : pure f G.M'.vac ∈ schA F _ := GlobalTheory.TensUniq.pure_mem_schA f _ hSB hM.std
  have hei : ∀ f, e' (pure f G.M'.vac) = pure (ei f) G₁.M'.vac := fun f => by
    rw [hloc f _ hSB (Eventually.of_forall fun _ => rfl)]
    exact congrArg _ (funext fun v => (hev v).1)
  set Φ : KAt K (evI F) → SInf F (Fin (b + 2) × Fin (a + (b + 2))) := fun k => locOpInf (om' (k.1, 1)) f with hΦ
  have hΦc : Continuous Φ := by
    obtain ⟨c, hc⟩ := exists_finPart_ne_zero G.M'.vac (fun v => (hM.vac v).2.1) hM.std
    refine continuous_of_weak Φ (g := fun y => ∏ᶠ v, G.M'.vac v fun i => evalV F v (y i)) (c := c)
      (hc (fun i => mk 0 (c i)) fun _ => rfl) fun l hl => ?_
    have hw : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (incM F G.W.J) G.M'.co X.α (X.α / X.β) om' :=
      hT.weil'
    refine ((hw.2.2 l hl _ hpure).comp
      (continuous_subtype_val.prodMk continuous_const : Continuous fun k : KAt K (evI F) => (k.1, (1 : UA σ G.W.J)))).congr
      fun k => congrArg l ?_
    exact acts_locOpInf (GlobalTheory.ArchLocalityX.acts_arch_left hP F E σ _ _ _ _ G.M' B.ψ _ _ om' hT.base.cm hψ hT.weil' k.1 k.2.2 f)
      _ ⟨fun x z hz => finPart_add _ x z hz, hpure⟩
  let L : SInf F (Fin b × Fin (a + b)) →L[ℂ] ℂ := (BoundedContinuousFunction.evalCLM ℂ y).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin b × Fin (a + b) → mixedEmbedding.mixedSpace F) ℂ)
  obtain ⟨c, hc⟩ := shift_decay hT.base hT.geo.hV' hC.hH hC.hH' hM hM₁ he hei Φ (fun p hp => by
      obtain ⟨c, hc⟩ := (isCompact_range (hp.comp hΦc)).bddAbove
      exact ⟨c, fun t => hc ⟨t, rfl⟩⟩)
    ((normSeminorm ℂ ℂ).comp L.toLinearMap) (continuous_norm.comp L.continuous) N
  exact ⟨c, fun k hk l => hc ⟨k, hk⟩ l⟩

end Step

theorem piInf_eq_one {m : (AE F E)ˣ} (hm : m ∈ idelesAt E (fun x : AF F => x.2)) {w : InfinitePlace F} (τ : EmbOver E w) :
    piInf τ (m : AE F E) = 1 := by
  let u : AF F := (1, 0)
  have h := (compInf_smul w u ((m : AE F E) - 1)).symm.trans (congrArg (compInf F E w) (hm u rfl))
  rw [show evInf F w u = 1 from rfl, one_smul, map_zero, map_sub, map_one, sub_eq_zero] at h
  rw [piInf, RingHom.comp_apply, h, map_one]

theorem coneInt_pure_le : GlobalTheory.FunPr.Hypotheses₂ → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E) {a b : ℕ}
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (e' : Fn F (b + 2) (a + (b + 2)) →ₗ[ℂ] Fn F b (a + b)), IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' →
    ∀ (K : Subgroup (UA σ G.V'.J)), IsStab B K →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b)))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F v) → ℂ),
    ei ≠ 0 → (∀ v, ev v (G.M'.vac v) = G₁.M'.vac v ∧ (SB _).map (ev v) = SB _) →
    (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) → e' (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ (f : SInf F (Fin (b + 2) × Fin (a + (b + 2)))) (φ : ∀ v : Pl F, (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ),
    (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) →
    ∀ y : Fin b × Fin (a + b) → AF F, ∃ (g : (AE F E)ˣ → ℝ) (𝔞 : FractionalIdeal (𝓞 E)⁰ E), 𝔞 ≠ 0 ∧ Measurable g ∧
      (∀ l, ∀ m ∈ idelesAt E (fun x : AF F => x.2), g (l * m) = g l) ∧
      (∀ μi : Measure (idelesAt E (evI F)), μi.IsHaarMeasure →
        Integrable (fun m : idelesAt E (evI F) => g m.1 * (absE F E m.1 : ℝ) ^ ((a - (b + 2)) / 2 + 1)) μi) ∧
      ∀ (k : K) (l : (AE F E)ˣ), ‖coneInt B G.M' om' e' (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (pure f φ) k.1 l y‖ ≤
        g l * (if ∀ v : Pl F, compFin F E v (l : AE F E) ∈ locId v 𝔞 then (1 : ℝ) else 0) *
          (absE F E l : ℝ) ^ ((a - (b + 2)) / 2 + 1) := by
  intro hP F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he K hK X om om' om₁ om₁' hT hT₁ ei ev hei hev hloc f φ hφ hφc y
  have hL : LemF.IsLocPart G.M' G₁.M' e' ei ev := ⟨hei, hev, hloc⟩
  have hM := hT.geo.hM'
  have hM₁ := hT₁.geo.hM'
  set z := (a - (b + 2)) / 2 + 1 with hz
  obtain ⟨μ₀, hμ₀⟩ := exists_haar_idelesAt E (evI F)
  obtain ⟨N, hN⟩ := GlobalTheory.ArchIdeleDecay.integrable_absE_pow_div F E σ B hT.base μ₀ hμ₀ z (by omega)
  obtain ⟨c₀, hc₀⟩ := arch_bound hP hC he hL hT hM₁ hK (fun i => evI F (y i)) f N
  choose c 𝔟 hc0 hcb using fun v : Pl F => local_bound hP hC he hL hT hK v (fun i => evFin F v (y i)) (φ v) (hφ v)
  have hfin := eventually_cofinite.1 (hφc.and hM₁.std)
  set S : Finset (Pl F) := hfin.toFinset ∪ X.T with hS
  have hoff : ∀ v ∉ S, φ v = G.M'.vac v ∧
      G₁.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := fun v hv => by
    by_contra h
    exact hv (Finset.mem_union_left _ (hfin.mem_toFinset.2 h))
  set 𝔞 : FractionalIdeal (𝓞 E)⁰ E := 1 ⊔ (H.𝔟⁻¹ * GlobalTheory.UnrEuler.conjI σ H'.𝔟 ⊔ S.sup 𝔟) with h𝔞
  have hP0 : ∀ l : (AE F E)ˣ, 0 < (1 + ∑ w, ‖piInf (B.emb w) (l : AE F E)‖) ^ N := fun l => by positivity
  refine ⟨fun l => (∏ v ∈ S, c v) * (c₀ / (1 + ∑ w, ‖piInf (B.emb w) (l : AE F E)‖) ^ N), 𝔞, fun h => ?_, ?_,
    fun l m hm => ?_, fun μ hμ => ?_, fun k l => ?_⟩
  · have h1 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≤ 𝔞 := le_sup_left
    rw [h] at h1
    exact one_ne_zero (le_bot_iff.1 h1)
  · haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
    refine Continuous.measurable (continuous_const.mul (continuous_const.div (Continuous.pow (continuous_const.add
      (continuous_finset_sum _ fun w _ => ?_)) N) fun l => (hP0 l).ne'))
    exact ((GlobalTheory.ContMapReal.continuous_piInf (B.emb w)).comp Units.continuous_val).norm
  · simp only [Units.val_mul, map_mul, piInf_eq_one hm, mul_one]
  · obtain ⟨r, -, rfl⟩ := haar_idelesAt_eq_smul μ μ₀
    refine ((hN.smul_measure_nnreal (c := r)).const_mul ((∏ v ∈ S, c v) * c₀)).congr (Eventually.of_forall fun m => ?_)
    ring
  · obtain ⟨hA, hvac⟩ := om_pure_stab hP hT hK k.2 f φ S Finset.subset_union_right hφ fun v hv => (hoff v hv).1
    have hk := StabComp.comp_mem_of_isStab F E σ B _ _ K hK k.1 k.2
    set φ₁ : ∀ v : Pl F, (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ :=
      fun v => locOp v (om' (compAt σ G.V'.J v k.1, 1)) (φ v) with hφ₁
    set f₁ := locOpInf (om' (compArch σ G.V'.J k.1, 1)) f with hf₁
    have hcof₁ : ∀ᶠ v in cofinite, φ₁ v = G.M'.vac v :=
      eventually_cofinite.2 (S.finite_toSet.subset fun v hv => by by_contra h; exact hv (hvac v h))
    have hB := GlobalTheory.T.weil_action_restricted_product G.M' B.ψ hT.base.std (shiftB σ H H' l) f₁ φ₁ (fun v => locOp_mem _ _ _)
      ((hcof₁.and hM.std).mono fun v hv => hv.1.trans hv.2)
    set φ₂ : ∀ v : Pl F, (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ :=
      fun v => locOp v (G.M'.co.rho B.ψ (partFin v (shiftB σ H H' l))) (φ₁ v) with hφ₂
    have hcof₂ : ∀ᶠ v in cofinite, φ₂ v = G.M'.vac v := by
      filter_upwards [GlobalTheory.T.local_operator_fixes_integral_indicator G.M' B.ψ hT.base.std (shiftB σ H H' l), hcof₁, hM.std] with v h1 h2 h3
      simp only [hφ₂]
      rw [h2, h3, h1]
    have hsupp := GlobalTheory.PureFactor.mulSupport_finite (fun v => ev v (φ₂ v))
      ((hcof₂.and hM₁.std).mono fun v hv => by rw [hv.1, (hev v).1, hv.2]) y
    have hunr : ∀ v ∉ S, ev v (φ₂ v) =
        if compFin F E v (l : AE F E) ∈ locId v (H.𝔟⁻¹ * GlobalTheory.UnrEuler.conjI σ H'.𝔟) then G₁.M'.vac v else 0 :=
      fun v hv => by
        have := UnrSuppB.evShift_vac B G G₁ H H' hT.base hT.geo hT₁.geo hC e' he ei ev hei hev hloc v (unitAt E v l)
          (unitAt_mem v l)
        rw [partFin_shiftB_unitAt, compFin_unitAt_self] at this
        simp only [hφ₂]
        rw [show φ₁ v = G.M'.vac v from hvac v hv, this]
    have hloc' := fun v => hcb v _ (mem_KAt.2 ⟨hk.1 v, compAt_mem v k.1⟩) l
    rw [coneInt, hA, hB, hloc _ φ₂ (fun v => locOp_mem _ _ _) hcof₂, norm_mul, norm_mul, Circle.norm_coe, mul_one, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, NNReal.abs_eq]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, norm_mul]
    split_ifs with hl
    · rw [mul_one, mul_comm]
      refine mul_le_mul (norm_finprod_le _ hsupp S c (fun v _ => (hloc' v).1) fun v hv => ?_)
        (hc₀ _ (mem_KAt.2 ⟨hk.2, compArch_mem k.1⟩) l) (norm_nonneg _) (Finset.prod_nonneg fun v _ => hc0 v)
      rw [hunr v hv, (hoff v hv).2]
      split_ifs
      · rw [Set.indicator_apply]
        split_ifs <;> simp
      · simp
    · obtain ⟨v, hv⟩ := not_forall.1 hl
      rw [finprod_eq_zero _ v ?_ hsupp, norm_zero, mul_zero, mul_zero]
      by_cases hvS : v ∈ S
      · exact (hloc' v).2 fun h => hv (locId_mono v ((Finset.le_sup hvS).trans (le_sup_right.trans le_sup_right)) h)
      · rw [hunr v hvS, if_neg fun h => hv (locId_mono v (le_sup_left.trans le_sup_right) h)]
        rfl

end GlobalTheory.ConeMajorant

end
