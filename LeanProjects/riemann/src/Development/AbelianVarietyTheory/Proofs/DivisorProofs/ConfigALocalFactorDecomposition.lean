import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBEigenStabilizerIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncMatTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepIntertwinesAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerFixesSphericalVacuumVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerComponentAtPlaceMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentActionFiniteSetSchwartzInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleCharacterNormEulerFactorizationStatement
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)
noncomputable section

namespace GlobalTheory.ThK.ConeEulerFac

open GlobalTheory.TruncFix (truncU)

theorem compAt_mem_of_isStab : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (B : Base F E) {n : ℕ} {X : Spc F E n} (K : Subgroup (UA σ X.J)), IsStab B K →
    ∀ k ∈ K, ∀ v : Pl F, compAt σ X.J v k ∈ K := GlobalTheory.T.stabilizer_component_at_place_mem

theorem om_pure_of_archTriv : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (B : Base F E) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (χX χW : Chr F E)
    (om : Rep σ X W) (r s r' s' : ℕ), ActsEx → IsPair B M χX χW om r s r' s' →
    ∀ k : UA σ X.J, (∀ u : AF F, At (evI F) u → u • (mat k - 1) = 0) →
    ∀ (S : Finset (Pl F)) (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ),
    (∀ v, φ v ∈ SB (Fin n × Fin d → Fv F v)) → (∀ v ∉ S, φ v = M.vac v) →
    (∀ v ∉ S, Acts (evFin F v) (om (truncU {v} k, 1)) (M.vac v) (M.vac v)) →
    om (k, 1) (pure f φ) = pure f (fun v => locOp v (om (truncU {v} k, 1)) (φ v)) := GlobalTheory.T.unipotent_action_finite_set_schwartz_invariant

theorem chr_abs_finprod : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ν : Chr F E), Continuous ν → ∀ (l : (AE F E)ˣ) (z : ℕ),
    (Function.mulSupport fun v : Pl F => (ν (unitAt E v l) : ℂ) * ((absE F E (unitAt E v l) : ℝ) : ℂ) ^ z).Finite ∧
    (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z =
      (ν (unitArch F E l) : ℂ) * ((absE F E (unitArch F E l) : ℝ) : ℂ) ^ z *
        ∏ᶠ v : Pl F, (ν (unitAt E v l) : ℂ) * ((absE F E (unitAt E v l) : ℝ) : ℂ) ^ z := GlobalTheory.T.idele_character_norm_euler_factorization

end GlobalTheory.ThK.ConeEulerFac

namespace GlobalTheory.ThK.ConeEulerFac

open GlobalTheory.TruncFix (truncU)

theorem partInf_shiftA_unitArch {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n d n₁ d₁ : ℕ} (H : Plane E n n₁) (H' : Plane E d d₁) (l : (AE F E)ˣ) :
    partInf F (shiftA H H' (unitArch F E l)) = partInf F (shiftA H H' l) := by
  unfold partInf
  rw [smul_shiftA, smul_shiftA]
  congr 1
  show eInf F • (eInf F • (l : AE F E) + (1 - eInf F) • 1) = eInf F • (l : AE F E)
  rw [smul_add, smul_smul, smul_smul, eInf_idem, idem_mul_one_sub eInf_idem, zero_smul, add_zero]

theorem partFin_shiftA_unitAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n d n₁ d₁ : ℕ} (H : Plane E n n₁) (H' : Plane E d d₁) (v : Pl F) (l : (AE F E)ˣ) :
    partFin v (shiftA H H' (unitAt E v l)) = partFin v (shiftA H H' l) := by
  unfold partFin
  rw [smul_shiftA, smul_shiftA]
  congr 1
  show eFin v • (eFin v • (l : AE F E) + (1 - eFin v) • 1) = eFin v • (l : AE F E)
  rw [smul_add, smul_smul, smul_smul, eFin_idem, idem_mul_one_sub (eFin_idem v), zero_smul, add_zero]

end GlobalTheory.ThK.ConeEulerFac

namespace GlobalTheory.ThK.ConeEulerFac

open GlobalTheory.TruncFix (truncU)

theorem mul_eInf_of_at {F : Type} [Field F] [NumberField F] {u : AF F} (hu : At (evI F) u) : u * eInf F = u := by
  have h := partInf_of_at (M := AF F) hu
  rw [partInf, smul_eq_mul] at h
  rw [mul_comm]; exact h

theorem eInf_mul_eFin {F : Type} [Field F] [NumberField F] (v : Pl F) : eInf F * eFin v = 0 := by
  have h := at_partFin (M := AF F) v (1 : AF F) (eInf F) (map_zero (evalV F v))
  rw [partFin, smul_eq_mul, smul_eq_mul, mul_one] at h
  exact h

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem mat_archRest {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (k : UA σ J) :
    mat ((compArch σ J k)⁻¹ * k) = eInf F • (1 : Matrix (Fin n) (Fin n) (AE F E)) + (1 - eInf F) • mat k := by
  rw [GlobalTheory.StabHaar.mat_mul, ← map_inv, mat_compArch, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul,
    ← GlobalTheory.StabHaar.mat_mul, inv_mul_cancel, GlobalTheory.StabHaar.mat_one]

theorem archRest_triv {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (k : UA σ J) :
    ∀ u : AF F, At (evI F) u → u • (mat ((compArch σ J k)⁻¹ * k) - 1) = 0 := by
  intro u hu
  rw [mat_archRest, smul_sub, smul_add, smul_smul, smul_smul, mul_eInf_of_at hu, mul_sub, mul_one, mul_eInf_of_at hu,
    sub_self, zero_smul, add_zero, sub_self]

theorem truncU_archRest {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (k : UA σ J) (v : Pl F) :
    truncU {v} ((compArch σ J k)⁻¹ * k) = compAt σ J v k := by
  refine Subtype.ext (Units.ext ?_)
  show GlobalTheory.TruncFix.truncMat (GlobalTheory.TruncFix.idem {v}) (mat ((compArch σ J k)⁻¹ * k)) = mat (compAt σ J v k)
  rw [GlobalTheory.TruncFix.idem_singleton, GlobalTheory.TruncFix.truncMat, mat_archRest, mat_compAt]
  have h1 : GlobalTheory.LatVac.liftV v 1 * eInf F = 0 := by rw [mul_comm]; exact eInf_mul_eFin v
  have h2 : GlobalTheory.LatVac.liftV v 1 * (1 - eInf F) = GlobalTheory.LatVac.liftV v 1 := by rw [mul_sub, mul_one, h1, sub_zero]
  rw [smul_sub, smul_add, smul_smul, smul_smul, h1, h2, zero_smul, zero_add, show eFin v = GlobalTheory.LatVac.liftV v 1 from rfl,
    sub_smul, one_smul]
  abel

end GlobalTheory.ThK.ConeEulerFac

namespace GlobalTheory.ThK.ConeEulerFac

open GlobalTheory.TruncFix (truncU)

open Classical in

theorem om_pure_of_stab {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hP : GlobalTheory.FunPr.Hypotheses₂) {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (hT : IsTriple B G X om om') {K : Subgroup (UA σ G.V.J)} (hK : IsStab B K)
    {k : UA σ G.V.J} (hk : k ∈ K) (f : SInf F (Fin a × Fin (a + a'))) (φ : ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ)
    (T : Finset (Pl F)) (hSB : ∀ v, φ v ∈ SB _) (hT' : ∀ v ∉ T, φ v = G.M.vac v) :
    om (k, 1) (pure f φ) = pure (locOpInf (om (compArch σ G.V.J k, 1)) f)
      (fun v => locOp v (om (compAt σ G.V.J v k, 1)) (φ v)) ∧
    ∀ v ∉ T ∪ X.T, locOp v (om (compAt σ G.V.J v k, 1)) (φ v) = G.M.vac v := by
  classical
  have hA := GlobalTheory.T.theta_action_exists hP
  have hPair := Inhab.pairV hT
  have hM := hT.geo.hM
  have hfix : ∀ v ∉ T ∪ X.T, Acts (evFin F v) (om (compAt σ G.V.J v k, 1)) (G.M.vac v) (G.M.vac v) := by
    intro v hv
    rw [Finset.mem_union, not_or] at hv
    exact GlobalTheory.T.stabilizer_fixes_spherical_vacuum_vector σ B G X om om' hT K hK v hv.2 _
      (mem_KAt.2 ⟨compAt_mem_of_isStab B K hK k hk v, compAt_mem v k⟩)
  have hvac : ∀ v ∉ T ∪ X.T, locOp v (om (compAt σ G.V.J v k, 1)) (φ v) = G.M.vac v := by
    intro v hv
    have hvT : v ∉ T := fun h => hv (Finset.mem_union_left _ h)
    rw [hT' v hvT]
    exact locOp_eq (hM.vac v).1 (hM.vac v).1 (hfix v hv)
  refine ⟨?_, hvac⟩
  set k' := (compArch σ G.V.J k)⁻¹ * k with hk'
  have hsplit : (k, (1 : UA σ G.W.J)) = (compArch σ G.V.J k, 1) * (k', 1) := by
    rw [Prod.mk_mul_mk, mul_one, hk', mul_inv_cancel_left]
  have h1 : om (k', 1) (pure f φ) = pure f (fun v => locOp v (om (compAt σ G.V.J v k, 1)) (φ v)) := by
    have := om_pure_of_archTriv B G.M _ _ om _ _ _ _ hA hPair k' (archRest_triv G.V.J k) (T ∪ X.T) f φ hSB
      (fun v hv => hT' v fun h => hv (Finset.mem_union_left _ h))
      (fun v hv => by rw [hk', truncU_archRest]; exact hfix v hv)
    simpa only [hk', truncU_archRest] using this
  have h1mem : (1 : UA σ G.W.J) ∈ UAt σ G.W (evI F) := fun u _ => by
    show u • (mat (1 : UA σ G.W.J) - 1) = 0
    rw [GlobalTheory.StabHaar.mat_one, sub_self, smul_zero]
  obtain ⟨Aop, hAop⟩ := GlobalTheory.ArchLocalAct.exists_op_of_UAt hT.base.std hT.weil (compArch σ G.V.J k, 1)
    (compArch_mem k) h1mem
  have hcof : ∀ᶠ v in Filter.cofinite, locOp v (om (compAt σ G.V.J v k, 1)) (φ v) = G.M.vac v :=
    Filter.eventually_cofinite.2 ((T ∪ X.T).finite_toSet.subset fun v hv => by
      by_contra h; exact hv (hvac v h))
  rw [hsplit, map_mul, Module.End.mul_apply, h1,
    GlobalTheory.ArchPureAct.acts_pure F E σ B.ψ a (a + a') G.V G.W G.M om hM _ Aop hAop f _ (fun v => locOp_mem _ _ _) hcof,
    locOpInf_eq (hAop f)]

end GlobalTheory.ThK.ConeEulerFac

namespace GlobalTheory.ThK.ConeEulerFac

open Classical in

theorem integrand_fac : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), GlobalTheory.FunPr.Hypotheses₂ → ∀ (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (e : Fn F (b + 2) (b + 2 + a') →ₗ[ℂ] Fn F b (b + a')), IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] SInf F (Fin b × Fin (b + a')))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (b + a') → Fv F v) → ℂ),
    (ei ≠ 0 ∧ (∀ v, ev v (G.M.vac v) = G₁.M.vac v ∧ (SB _).map (ev v) = SB _) ∧
      ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → G₁.M.IsGood B.ψ →
    ∀ (f : SInf F (Fin (b + 2) × Fin (b + 2 + a'))) (φ : ∀ v : Pl F, (Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ)
      (T : Finset (Pl F)), (∀ v, φ v ∈ SB _) → (∀ v ∉ T, φ v = G.M.vac v) →
    ∀ k ∈ K, ∀ (l : (AE F E)ˣ) (y : Fin b × Fin (b + a') → AF F) (z : ℕ),
      e (G.M.co.rho B.ψ (shiftA H H' l) (om (k, 1) (pure f φ))) y * (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z =
        coneInfInt B G.M om ei (shiftA H H') X.ν z f (compArch σ G.V.J k) (unitArch F E l) (fun i => evI F (y i)) *
          ∏ᶠ v, coneFinInt B G.M om v (ev v) (shiftA H H') X.ν z (φ v) (compAt σ G.V.J v k) (unitAt E v l)
            (fun i => evFin F v (y i)) := by
  intro F E _ _ _ _ _ σ hP B b a' G G₁ H H' hC e hE ei ev hloc K hK X om om' hT hG f φ T hSB hT' k hk l y z
  have hM := hT.geo.hM
  obtain ⟨hA, hvacA⟩ := om_pure_of_stab hP hT hK hk f φ T hSB hT'
  set φ₁ : ∀ v : Pl F, (Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ :=
    fun v => locOp v (om (compAt σ G.V.J v k, 1)) (φ v) with hφ₁
  set f₁ := locOpInf (om (compArch σ G.V.J k, 1)) f with hf₁
  have hcof₁ : ∀ᶠ v in Filter.cofinite, φ₁ v = G.M.vac v :=
    Filter.eventually_cofinite.2 ((T ∪ X.T).finite_toSet.subset fun v hv => by
      by_contra h; exact hv (hvacA v h))
  have hstd₁ := (hcof₁.and hM.std).mono fun v hv => hv.1.trans hv.2
  obtain ⟨hB, hfixB⟩ := GlobalTheory.ShiftSupport.rho_pure G.M B.ψ hT.base.std (shiftA H H' l) f₁ φ₁
    (fun v => locOp_mem _ _ _) hstd₁
  set φ₂ : ∀ v : Pl F, (Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ :=
    fun v => locOp v (G.M.co.rho B.ψ (partFin v (shiftA H H' l))) (φ₁ v) with hφ₂
  set f₂ := locOpInf (G.M.co.rho B.ψ (partInf F (shiftA H H' l))) f₁ with hf₂
  have hcof₂ : ∀ᶠ v in Filter.cofinite, φ₂ v = G.M.vac v := (hfixB.and hcof₁).mono fun v hv => hv.1.trans hv.2
  rw [hA, hB, hloc.2.2 f₂ φ₂ (fun v => locOp_mem _ _ _) hcof₂]
  have hν : Continuous X.ν := hT.chars.heckeα.1.div' hT.chars.heckeβ.1
  obtain ⟨hfinC, hC⟩ := chr_abs_finprod X.ν hν l z
  have hstdE : ∀ᶠ v in Filter.cofinite, ev v (φ₂ v) =
      Set.indicator {x | ∀ i, x i ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v} 1 :=
    (hcof₂.and hG.std).mono fun v hv => by rw [hv.1, (hloc.2.1 v).1, hv.2]
  have hfinA := GlobalTheory.PureFactor.mulSupport_finite (fun v => ev v (φ₂ v)) hstdE y
  have hR : ∀ v, coneFinInt B G.M om v (ev v) (shiftA H H') X.ν z (φ v) (compAt σ G.V.J v k) (unitAt E v l)
      (fun i => evFin F v (y i)) = ev v (φ₂ v) (fun i => evFin F v (y i)) *
        ((X.ν (unitAt E v l) : ℂ) * ((absE F E (unitAt E v l) : ℝ) : ℂ) ^ z) := by
    intro v
    rw [coneFinInt, partFin_shiftA_unitAt]
    ring
  have hI : coneInfInt B G.M om ei (shiftA H H') X.ν z f (compArch σ G.V.J k) (unitArch F E l) (fun i => evI F (y i)) =
      ei f₂ (fun i => evI F (y i)) * ((X.ν (unitArch F E l) : ℂ) * ((absE F E (unitArch F E l) : ℝ) : ℂ) ^ z) := by
    rw [coneInfInt_apply, partInf_shiftA_unitArch]
    ring
  rw [finprod_congr hR, finprod_mul_distrib hfinA hfinC, hI, mul_assoc _ (X.ν l : ℂ), hC]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
  ring

end GlobalTheory.ThK.ConeEulerFac
