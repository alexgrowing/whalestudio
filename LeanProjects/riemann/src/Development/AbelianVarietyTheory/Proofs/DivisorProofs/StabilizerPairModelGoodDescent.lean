import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBEigenStabilizerIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncMatTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepIntertwinesAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerComponentAtPlaceMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentActionFiniteSetSchwartzInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleCharacterNormEulerFactorization
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB GlobalTheory.ThK.ConeEuler GlobalTheory.UnrEuler
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.ConeIntFac

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

theorem smul_shift_idemUnit {n d : ℕ} (c : AE F E →ₐ[AF F] AE F E) (Z : Matrix (Fin n) (Fin d) (AE F E))
    (ε : AF F) (hε : ε * ε = ε) (l : (AE F E)ˣ) :
    ε • (c (idemUnit E ε hε l).1 • Z) = ε • (c l.1 • Z) := by
  rw [← smul_assoc, ← smul_assoc, ← map_smul, ← map_smul, val_idemUnit, smul_add, smul_smul, smul_smul, hε,
    idem_mul_one_sub hε, zero_smul, add_zero]

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

theorem om_pure_of_stab (hA : ActsEx) {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}
    {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ} (hP : IsPair B M χX χW om r s r' s')
    {K : Subgroup (UA σ X.J)} (hK : IsStab B K) {k : UA σ X.J} (hk : k ∈ K) (f : SInf F (Fin n × Fin d))
    (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) (T : Finset (Pl F)) (hSB : ∀ v, φ v ∈ SB _)
    (hT : ∀ v ∉ T, φ v = M.vac v)
    (hfixK : ∀ v ∉ T, ∀ k ∈ KAt K (evFin F v), Acts (evFin F v) (om (k, 1)) (M.vac v) (M.vac v)) :
    om (k, 1) (pure f φ) = pure (locOpInf (om (compArch σ X.J k, 1)) f)
      (fun v => locOp v (om (compAt σ X.J v k, 1)) (φ v)) ∧
    ∀ v ∉ T, locOp v (om (compAt σ X.J v k, 1)) (φ v) = M.vac v := by
  classical
  have hM := hP.good
  have hfix : ∀ v ∉ T, Acts (evFin F v) (om (compAt σ X.J v k, 1)) (M.vac v) (M.vac v) := fun v hv =>
    hfixK v hv _ (mem_KAt.2 ⟨GlobalTheory.ThK.ConeEuler.StabCompAt.compAt_mem_of_isStab B K hK k hk v, compAt_mem v k⟩)
  have hvac : ∀ v ∉ T, locOp v (om (compAt σ X.J v k, 1)) (φ v) = M.vac v := by
    intro v hv
    rw [hT v hv]
    exact locOp_eq (hM.vac v).1 (hM.vac v).1 (hfix v hv)
  refine ⟨?_, hvac⟩
  set k' := (compArch σ X.J k)⁻¹ * k with hk'
  have hsplit : (k, (1 : UA σ W.J)) = (compArch σ X.J k, 1) * (k', 1) := by
    rw [Prod.mk_mul_mk, mul_one, hk', mul_inv_cancel_left]
  have h1 : om (k', 1) (pure f φ) = pure f (fun v => locOp v (om (compAt σ X.J v k, 1)) (φ v)) := by
    have := GlobalTheory.TruncFixOm.om_archtriv B M _ _ om _ _ _ _ hA hP k' (archRest_triv X.J k) T f φ hSB hT
      (fun v hv => by rw [hk', truncU_archRest]; exact hfix v hv)
    simpa only [hk', truncU_archRest] using this
  have h1mem : (1 : UA σ W.J) ∈ UAt σ W (evI F) := fun u _ => by
    show u • (mat (1 : UA σ W.J) - 1) = 0
    rw [GlobalTheory.StabHaar.mat_one, sub_self, smul_zero]
  obtain ⟨Aop, hAop⟩ := GlobalTheory.ArchLocalAct.exists_op_of_UAt hP.base.std hP.weil (compArch σ X.J k, 1)
    (compArch_mem k) h1mem
  have hcof : ∀ᶠ v in Filter.cofinite, locOp v (om (compAt σ X.J v k, 1)) (φ v) = M.vac v :=
    Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => by
      by_contra h; exact hv (hvac v h))
  rw [hsplit, map_mul, Module.End.mul_apply, h1,
    GlobalTheory.ArchPureAct.acts_pure F E σ B.ψ n d X W M om hM _ Aop hAop f _ (fun v => locOp_mem _ _ _) hcof,
    locOpInf_eq (hAop f)]

theorem finprod_split {ι : Type} (T : Finset ι) (g : ι → ℂ) (hg : (Function.mulSupport g).Finite) :
    ∏ᶠ v, g v = (∏ v ∈ T, g v) * ∏ᶠ (v : ι) (_ : v ∉ T), g v := by
  have h := finprod_mem_union' (f := g) (s := (T : Set ι)) (t := (T : Set ι)ᶜ) disjoint_compl_right
    (hg.inter_of_right _) (hg.inter_of_right _)
  rw [Set.union_compl_self, finprod_mem_univ, finprod_mem_coe_finset] at h
  exact h

theorem coneInt_pure : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (_hKP : KP) (B : Base F E) {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
    (M : Model σ X W) (M₁ : Model σ X₁ W₁) {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ},
    IsPair B M χX χW om r s r' s' → M₁.IsGood B.ψ →
    ∀ {K : Subgroup (UA σ X.J)}, IsStab B K →
    ∀ (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁) (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁))
      (ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ),
    (∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB (Fin n × Fin d → Fv F v)).map (ev v) = SB (Fin n₁ × Fin d₁ → Fv F v)) →
    (∀ (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ),
      (∀ v, φ v ∈ SB (Fin n × Fin d → Fv F v)) → (∀ᶠ v in cofinite, φ v = M.vac v) →
      e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ (c : AE F E →ₐ[AF F] AE F E) (Z : Matrix (Fin n) (Fin d) (AE F E)) (u : (AE F E)ˣ → Matrix (Fin n) (Fin d) (AE F E)),
    (∀ l, u l = c l.1 • Z) →
    ∀ (ν : Chr F E), Continuous ν → ∀ (z : ℕ) (T : Finset (Pl F)) (f : SInf F (Fin n × Fin d))
      (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ),
    (∀ v, φ v ∈ SB (Fin n × Fin d → Fv F v)) → (∀ v ∉ T, φ v = M.vac v) →
    (∀ v ∉ T, ∀ k ∈ KAt K (evFin F v), Acts (evFin F v) (om (k, 1)) (M.vac v) (M.vac v)) →
    ∀ k ∈ K, ∀ (l : (AE F E)ˣ) (y : Fin n₁ × Fin d₁ → AF F),
      coneInt B M om e u ν z (pure f φ) k l y =
        coneInfInt B M om ei u ν z f (compArch σ X.J k) (unitArch F E l) (fun i => evI F (y i)) *
        (∏ v ∈ T, coneFinInt B M om v (ev v) u ν z (φ v) (compAt σ X.J v k) (unitAt E v l) (fun i => evFin F v (y i))) *
        ∏ᶠ (v : Pl F) (_ : v ∉ T), coneFinInt B M om v (ev v) u ν z (M.vac v) 1 (unitAt E v l) (fun i => evFin F v (y i)) := by
  intro F E _ _ _ _ _ σ hKP B n d n₁ d₁ X W X₁ W₁ M M₁ χX χW om r s r' s' hP hG K hK e ei ev hev hpure c Z u hu ν hν z T f φ
    hSB hT hfix k hk l y
  classical
  have hM := hP.good
  obtain ⟨hA, hvacA⟩ := om_pure_of_stab (GlobalTheory.ThK.LocalOps.actsEx hKP.base) hP hK hk f φ T hSB hT hfix
  set φ₁ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ := fun v => locOp v (om (compAt σ X.J v k, 1)) (φ v) with hφ₁
  set f₁ := locOpInf (om (compArch σ X.J k, 1)) f with hf₁
  have hcof₁ : ∀ᶠ v in Filter.cofinite, φ₁ v = M.vac v :=
    Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => by
      by_contra h; exact hv (hvacA v h))
  have hstd₁ := (hcof₁.and hM.std).mono fun v hv => hv.1.trans hv.2
  obtain ⟨hB, hfixB⟩ := GlobalTheory.ShiftSupport.rho_pure M B.ψ hP.base.std (u l) f₁ φ₁ (fun v => locOp_mem _ _ _) hstd₁
  set φ₂ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ := fun v => locOp v (M.co.rho B.ψ (partFin v (u l))) (φ₁ v) with hφ₂
  set f₂ := locOpInf (M.co.rho B.ψ (partInf F (u l))) f₁ with hf₂
  have hcof₂ : ∀ᶠ v in Filter.cofinite, φ₂ v = M.vac v := (hfixB.and hcof₁).mono fun v hv => hv.1.trans hv.2
  have huF : ∀ v, partFin v (u (unitAt E v l)) = partFin v (u l) := fun v => by
    rw [hu, hu]; exact smul_shift_idemUnit c Z (eFin v) (eFin_idem v) l
  have huI : partInf F (u (unitArch F E l)) = partInf F (u l) := by
    rw [hu, hu]; exact smul_shift_idemUnit c Z (eInf F) eInf_idem l
  rw [coneInt, hA, hB, hpure f₂ φ₂ (fun v => locOp_mem _ _ _) hcof₂]
  obtain ⟨hfinC, hC⟩ := GlobalTheory.ThK.ConeEulerChr.chr_abs_eq_finprod ν hν l z
  have hstdE : ∀ᶠ v in Filter.cofinite, ev v (φ₂ v) =
      Set.indicator {x | ∀ i, x i ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v} 1 :=
    (hcof₂.and hG.std).mono fun v hv => by rw [hv.1, (hev v).1, hv.2]
  have hfinA := GlobalTheory.PureFactor.mulSupport_finite (fun v => ev v (φ₂ v)) hstdE y
  set g : Pl F → ℂ := fun v => ev v (φ₂ v) (fun i => evFin F v (y i)) *
    ((ν (unitAt E v l) : ℂ) * ((absE F E (unitAt E v l) : ℝ) : ℂ) ^ z) with hg
  have hR : ∀ v, coneFinInt B M om v (ev v) u ν z (φ v) (compAt σ X.J v k) (unitAt E v l)
      (fun i => evFin F v (y i)) = g v := by
    intro v
    rw [coneFinInt, huF, hg]
    ring
  have hR' : ∀ v ∉ T, coneFinInt B M om v (ev v) u ν z (M.vac v) 1 (unitAt E v l)
      (fun i => evFin F v (y i)) = g v := by
    intro v hv
    have h1 : locOp v (om (1, 1)) (M.vac v) = φ₁ v := by
      rw [show φ₁ v = M.vac v from hvacA v hv]
      exact locOp_eq (hM.vac v).1 (hM.vac v).1 (hfix v hv 1 (one_mem _))
    rw [coneFinInt, huF, h1, hg]
    ring
  have hI : coneInfInt B M om ei u ν z f (compArch σ X.J k) (unitArch F E l) (fun i => evI F (y i)) =
      ei f₂ (fun i => evI F (y i)) * ((ν (unitArch F E l) : ℂ) * ((absE F E (unitArch F E l) : ℝ) : ℂ) ^ z) := by
    rw [coneInfInt_apply, huI]
    ring
  have hfin : (Function.mulSupport g).Finite := (hfinA.union hfinC).subset (Function.mulSupport_mul _ _)
  have hc : (∏ᶠ (v : Pl F) (_ : v ∉ T), coneFinInt B M om v (ev v) u ν z (M.vac v) 1 (unitAt E v l)
      (fun i => evFin F v (y i))) = ∏ᶠ (v : Pl F) (_ : v ∉ T), g v :=
    finprod_congr fun v => finprod_congr fun hv => hR' v hv
  rw [hc, Finset.prod_congr rfl fun v _ => hR v, mul_assoc (coneInfInt B M om ei u ν z f _ _ _), ← finprod_split T g hfin,
    hg, finprod_mul_distrib hfinA hfinC, hI, mul_assoc _ (ν l : ℂ), hC]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
  ring

end GlobalTheory.ThK.ConeIntFac
