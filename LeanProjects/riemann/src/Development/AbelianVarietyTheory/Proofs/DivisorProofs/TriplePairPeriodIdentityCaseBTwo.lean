import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBumpB
import Development.AutomorphicArithmetic.DivisorFrames.FourierSchwartzBruhatPreserved
import Development.AutomorphicArithmetic.DivisorFrames.FourierInjectiveSchwartzBruhat
import Development.AutomorphicArithmetic.DivisorFrames.HaarIntegralUnitsScaling
import Development.AutomorphicArithmetic.DivisorFrames.LocalThetaPartitionTriple
import Development.AutomorphicArithmetic.DivisorFrames.LocalThetaPartitionTripleAlt
import Development.AutomorphicArithmetic.DivisorFrames.ExistsCompactSubgroupCharacter
import Development.AutomorphicArithmetic.DivisorFrames.ThetaLocalOpenSubgroup
import Development.AutomorphicArithmetic.DivisorFrames.ExistsSchwartzCharacterAverage
import Development.AutomorphicArithmetic.DivisorFrames.ExistsSchwartzBruhatNonvanishingIntegral
import Development.AutomorphicArithmetic.DivisorFrames.LocalPartEvaluationConfigOne
import Development.AutomorphicArithmetic.DivisorFrames.LocalPartEvaluationConfigTwo
import Development.AutomorphicArithmetic.DivisorFrames.SchwartzBruhatIntegralIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalStabilizerLocallyConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerThetaEval
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerLocalPartCaseB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactStabilizerLineNormOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermAdaptedCompactOpenVolumeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCompactIdeleVolumeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAbsPowerLocallyConstantStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

section SlopeTestRemainingChoices

open GlobalTheory.ConeBumpB

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl F}
  {ψ : AddChar (Fv F v) ℂ} [MeasurableSpace (Fv F v ⊗[F] E)] {m : Measure (Fv F v ⊗[F] E)}

omit [NumberField E] in
private theorem four_mod (T : Fv F v ⊗[F] E → ℂ) (c t : Fv F v ⊗[F] E) :
    four v ψ m (fun s => ψ (-Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (c * s)) * T s) t = four v ψ m T (t - c) := by
  refine congrArg (integral m) (funext fun s => ?_)
  rw [sub_mul, map_sub, sub_eq_add_neg, AddChar.map_add_eq_mul]
  ring

omit [NumberField E] in
private theorem four_smul (T : Fv F v ⊗[F] E → ℂ) (c : ℂ) (t : Fv F v ⊗[F] E) :
    four v ψ m (fun s => c * T s) t = c * four v ψ m T t := by
  rw [four, four, ← integral_const_mul]
  refine congrArg (integral m) (funext fun s => ?_)
  ring

variable [BorelSpace (Fv F v ⊗[F] E)] [m.IsAddHaarMeasure]

private theorem four_shift (T : Fv F v ⊗[F] E → ℂ) (c t : Fv F v ⊗[F] E) :
    four v ψ m (fun s => T (s + c)) t = ψ (-Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (t * c)) * four v ψ m T t := by
  haveI := GlobalTheory.LocTateInt.isTopologicalRing_Ev (E := E) v
  rw [four, four, ← integral_const_mul,
    ← integral_add_right_eq_self (μ := m) (fun s => ψ (-Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (t * c)) *
      (T s * ψ (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (t * s)))) c]
  refine congrArg (integral m) (funext fun s => ?_)
  rw [mul_left_comm, ← AddChar.map_add_eq_mul, mul_add t, LinearMap.map_add]
  congr 2
  ring

private theorem four_add (hψ : Continuous ψ) {T T' : Fv F v ⊗[F] E → ℂ} (hT : T ∈ SB (Fv F v ⊗[F] E))
    (hT' : T' ∈ SB (Fv F v ⊗[F] E)) (t : Fv F v ⊗[F] E) :
    four v ψ m (fun s => T s + T' s) t = four v ψ m T t + four v ψ m T' t := by
  haveI := GlobalTheory.LocTateInt.isTopologicalRing_Ev (E := E) v
  haveI := GlobalTheory.LocTateInt.isModuleTopology_Ev (E := E) v
  have hc : Continuous fun s : Fv F v ⊗[F] E => ψ (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (t * s)) :=
    hψ.comp ((IsModuleTopology.continuous_of_linearMap (Algebra.trace (Fv F v) (Fv F v ⊗[F] E))).comp
      (continuous_const_mul t))
  have hi : ∀ S ∈ SB (Fv F v ⊗[F] E),
      Integrable (fun s => S s * ψ (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (t * s))) m := fun S hS =>
    (hS.1.continuous.mul hc).integrable_of_hasCompactSupport hS.2.mul_right
  rw [four, four, four, ← integral_add (hi T hT) (hi T' hT')]
  refine congrArg (integral m) (funext fun s => ?_)
  ring

private theorem four_scale (T : Fv F v ⊗[F] E → ℂ) (u : (Fv F v ⊗[F] E)ˣ) :
    four v ψ m (fun s => T ((u : Fv F v ⊗[F] E) * s)) u =
      (((GlobalTheory.Doubling.absEv F E v u : ℝ) : ℂ))⁻¹ * four v ψ m T 1 := by
  rw [four, four, ← UpperTheory.haar_integral_units_scaling F E v m u]
  simp only [one_mul]

end SlopeTestRemainingChoices

private theorem lc_two {P Q S R : Type} [TopologicalSpace P] [TopologicalSpace Q] {f : P → S} (hf : IsLocallyConstant f)
    {g : S → Q → R} (hg : ∀ p, IsLocallyConstant (g (f p))) : IsLocallyConstant fun q : P × Q => g (f q.1) q.2 := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun q => ?_
  have h1 := (continuous_fst.tendsto q).eventually (hf.eventually_eq q.1)
  have h2 := (continuous_snd.tendsto q).eventually ((hg q.1).eventually_eq q.2)
  filter_upwards [h1, h2] with x hx hx'
  rw [hx, hx']

private theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  have hNN : Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ) *
      Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ) = 1 := by
    rw [Matrix.fromBlocks_multiply]; simp [Matrix.fromBlocks_one]
  have hN : IsUnit (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ)) :=
    ⟨⟨_, _, hNN, hNN⟩, rfl⟩
  have h1 := Matrix.rank_of_isUnit _ hN
  have h2 : (Aᵀ * M * A.map star).rank ≤ M.rank := (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  rw [hA, h1] at h2
  simp only [Fintype.card_sum, Fintype.card_fin, hrs] at h2
  have h3 : LinearMap.range M.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have := M.rank_le_width
    simp only [Matrix.rank, Fintype.card_fin] at h2 this
    rw [Module.finrank_fin_fun]; omega
  have hu : IsUnit M := (Matrix.mulVec_surjective_iff_isUnit).mp (LinearMap.range_eq_top.mp h3)
  exact ((Matrix.isUnit_iff_isUnit_det M).mp hu).ne_zero

private theorem det_ne_zero_herm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {m : ℕ} {X : Spc F E m} {r s : ℕ} (hX : X.IsHerm σ B r s) : X.J.det ≠ 0 := by
  obtain w := Classical.arbitrary (InfinitePlace F)
  have h := det_ne_zero_of_hasSig (hX.sig w)
  intro h0
  apply h
  rw [show (X.J.map (B.emb w).1).det = (B.emb w).1 X.J.det from (RingHom.map_det (B.emb w).1 X.J).symm, h0, map_zero]

open GlobalTheory.ConeBumpB GlobalTheory.LatVac in
open GlobalTheory.Doubling (absE) in
open scoped GlobalTheory.VacAny in
theorem _root_.GlobalTheory.T.triple_pair_period_identity_case_b_two : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    CfgB B G G₁ H H' → IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b)))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F v) → ℂ),
    ei ≠ 0 → (∀ v, ev v (G.M'.vac v) = G₁.M'.vac v ∧ (SB _).map (ev v) = SB _) →
    (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) → e' (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ K : Subgroup (UA σ G.V'.J), IsStab B K →
    ∀ (v : Pl F) (μKv : Measure (KAt K (evFin F v))) (μv : Measure (idelesAt E (evFin F v))),
    IsNormK K (evFin F v) μKv → IsNormE E v μv →
    ∀ l : ((Fin b × Fin (a + b) → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
    (∀ g ∈ UAt σ G₁.V' (evFin F v), ∀ ψ ∈ SB (Fin b × Fin (a + b) → Fv F v), ∀ ψ' ∈ SB (Fin b × Fin (a + b) → Fv F v),
      Acts (evFin F v) (om₁' (g, 1)) ψ ψ' → l ψ' = l ψ) →
    (∃ ψ ∈ SB (Fin b × Fin (a + b) → Fv F v), l ψ ≠ 0) →
    ∃ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
      coneFin B G.M' om' v (ev v) K μKv μv (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ ∈ SB (Fin b × Fin (a + b) → Fv F v) ∧
      l (coneFin B G.M' om' v (ev v) K μKv μv (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ) ≠ 0 := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' X om om' om₁ om₁' hC hT hT₁ e' he ei ev hei hev hfac K hK v μK μ hμK hμ
    l hinv hne
  have hP := hKP.base
  have hL : GlobalTheory.ThK.LemF.IsLocPart G.M' G₁.M' e' ei ev := ⟨hei, hev, hfac⟩
  have hA : ActsEx := GlobalTheory.T.theta_action_exists hP
  have P' := (GlobalTheory.ThK.Check.isPair_of_isTriple hT).2
  have P₁' := (GlobalTheory.ThK.Check.isPair_of_isTriple hT₁).2
  have hinv' : ∀ g₀ ∈ UAt σ G₁.V' (evFin F v), ∀ p ∈ SB (Fin b × Fin (a + b) → Fv F v),
      l (locOp v (om₁' (g₀, 1)) p) = l p := fun g₀ hg p hp =>
    hinv g₀ hg p hp _ (locOp_mem _ _ _) (acts_locOp_om hA P₁' hg (mem_UAtSub.1 (one_mem _)) hp)
  have hψ : Continuous B.ψ := hT.base.std.1
  have hψv : Continuous (psiAt B.ψ v) := GlobalTheory.SchrSB.continuous_psiAt B.ψ hψ v
  have hψ1 : psiAt B.ψ v ≠ 1 := GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hT.base.std v
  have hKc : IsCompact (K : Set (UA σ G.V'.J)) :=
    GlobalTheory.T.stabilizer_compact hKP F E σ B (b + 2) G.V' _ _ K hT.base hT.geo.hV' hK
  have hx0 : H.x ≠ 0 := by
    intro h0
    have h1 := hC.hH.xy
    rw [h0] at h1
    simp [form] at h1
  have hνc : Continuous X.ν := (GlobalTheory.ThK.Check.isHecke_div hT.chars.heckeα hT.chars.heckeβ).1
  have hz : 2 ≤ (a - (b + 2)) / 2 + 1 := by have := hT.geo.eBig; omega
  generalize hzdef : (a - (b + 2)) / 2 + 1 = z at hz
  haveI := GlobalTheory.LocTateInt.isTopologicalRing_Ev (E := E) v
  haveI := GlobalTheory.LocTateInt.locallyCompactSpace_Ev (E := E) v
  haveI := GlobalTheory.LocTateInt.isOpenUnits_Ev (E := E) v
  borelize (Fv F v ⊗[F] E)
  obtain ⟨m, hm⟩ : ∃ m : Measure (Fv F v ⊗[F] E), m.IsAddHaarMeasure := ⟨Measure.addHaar, inferInstance⟩
  obtain ⟨Tf, hTf⟩ : ∃ Tf : ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) → Fv F v ⊗[F] E → ℂ,
      Tf = fun φ s => l (evS B G.M' v (ev v) H H' φ s) := ⟨_, rfl⟩
  have hsb : ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v), Tf φ ∈ SB (Fv F v ⊗[F] E) := fun φ hφ => by
    rw [hTf]
    exact UpperTheory.local_part_evaluation_config_one hP F E σ B a b G G₁ H H' hC e' he ei ev hL X om om' om₁ om₁' hT hT₁ v l φ hφ

  obtain ⟨φ₀, hφ₀, hc0⟩ : ∃ φ₀ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
      four v (psiAt B.ψ v) m (Tf φ₀) 1 ≠ 0 := by
    obtain ⟨p, hp, hlp⟩ := hne
    obtain ⟨φ₁, hφ₁, hφp⟩ : p ∈ (SB _).map (ev v) := by rw [(hev v).2]; exact hp
    have h0 : Tf φ₁ 0 = l p := by
      rw [hTf]
      simp only [evS]
      rw [uS_zero, partFin, smul_zero, locOp_of_fix (fun Φ _ => ?_) hφ₁, hφp]
      funext x
      simp [Darboux.rho, schr]
    obtain ⟨t₀, ht₀⟩ : ∃ t₀, four v (psiAt B.ψ v) m (Tf φ₁) t₀ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have := UpperTheory.fourier_injective_schwartz_bruhat F E v _ hψv hψ1 m _ (hsb φ₁ hφ₁) hcon
      rw [this] at h0
      exact hlp h0.symm
    refine ⟨locOp v (G.M'.co.rho B.ψ (partFin v (GlobalTheory.VanishLoc.uAt H H' v (1 - t₀)))) φ₁, locOp_mem _ _ _, ?_⟩
    have e : Tf (locOp v (G.M'.co.rho B.ψ (partFin v (GlobalTheory.VanishLoc.uAt H H' v (1 - t₀)))) φ₁) = fun s =>
        psiAt B.ψ v (-Algebra.trace (Fv F v) (Fv F v ⊗[F] E) ((1 - t₀) * s)) * Tf φ₁ s := by
      funext s
      simp only [hTf]
      rw [UpperTheory.local_theta_partition_triple hP F E σ B a b G G₁ H H' hC e' he ei ev hL X om om' om₁ om₁' hT hT₁ v φ₁ hφ₁, map_smul, smul_eq_mul]
    rw [e, four_mod, sub_sub_cancel]
    exact ht₀

  obtain ⟨χ, hχ⟩ : ∃ χ : idelesAt E (evFin F v) → ℂ, χ = fun t =>
      ((absE F E t.1 : ℝ) : ℂ) * ((X.ν t.1 : ℂ) * ((absE F E t.1 : ℝ) : ℂ) ^ z)⁻¹ := ⟨_, rfl⟩
  have hχlc : IsLocallyConstant χ := by
    have h1 := GlobalTheory.T.character_abs_power_locally_constant F E X.ν hνc z v
    have h2 := GlobalTheory.T.character_abs_power_locally_constant F E 1 continuous_const 1 v
    rw [hχ]
    refine IsLocallyConstant.comp₂ (by simpa using h2) h1 (fun x y => x * y⁻¹)
  have hcomp : Continuous fun t : idelesAt E (evFin F v) => compFin F E v (t.1 : AE F E) :=
    Units.continuous_val.comp (idelesAtEquiv E v).continuous
  have hklc := (GlobalTheory.ThK.LemF.compact_locConst_KAt hP F E σ B a (b + 2) G X om om' hT K hK v).2 φ₀ hφ₀
  have hG0 : IsLocallyConstant fun q : KAt K (evFin F v) × idelesAt E (evFin F v) =>
      four v (psiAt B.ψ v) m (Tf (locOp v (om' (q.1.1, 1)) φ₀)) (compFin F E v (q.2.1 : AE F E)) * χ q.2 :=
    lc_two (g := fun φ (t : idelesAt E (evFin F v)) =>
      four v (psiAt B.ψ v) m (Tf φ) (compFin F E v (t.1 : AE F E)) * χ t) hklc fun k =>
      IsLocallyConstant.comp₂ ((UpperTheory.fourier_schwartz_bruhat_preserved F E v _ hψv hψ1 m _ (hsb _ (locOp_mem _ _ _))).1.comp_continuous hcomp) hχlc (· * ·)
  have hSig : ∀ q : KAt K (evFin F v) × idelesAt E (evFin F v), mat q.1.1 *ᵥ incV F H.x = (q.2.1 : AE F E) • incV F H.x →
      q ∈ {q : KAt K (evFin F v) × idelesAt E (evFin F v) |
        four v (psiAt B.ψ v) m (Tf (locOp v (om' (q.1.1, 1)) φ₀)) (compFin F E v (q.2.1 : AE F E)) * χ q.2 =
          four v (psiAt B.ψ v) m (Tf φ₀) 1} := by
    intro q hq
    have habs : absE F E q.2.1 = 1 := GlobalTheory.T.compact_stabilizer_line_norm_one F E σ (b + 2) G.V' H.x K hKc hx0 v q.1.1 q.1.2 q.2.1 hq
    have e : Tf (locOp v (om' (q.1.1, 1)) φ₀) = fun s => (X.ν q.2.1 : ℂ) *
        Tf φ₀ ((GlobalTheory.Doubling.unitFin F E v q.2.1 : Fv F v ⊗[F] E) * s) := by
      funext s
      simp only [hTf]
      rw [UpperTheory.local_part_evaluation_config_two hP F E σ B a b G G₁ H H' hC e' he ei ev hL X om om' om₁ om₁' hT hT₁ v l hinv' q.1.1 q.1.2.2 q.2.1 hq
        φ₀ hφ₀ s, GlobalTheory.ThK.LemF.fac, habs]
      simp only [NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, mul_one]
      rfl
    have h2 := four_scale (ψ := psiAt B.ψ v) (m := m) (Tf φ₀) (GlobalTheory.Doubling.unitFin F E v q.2.1)
    rw [← absE_of_mem q.2.2, habs] at h2
    show _ = _
    rw [e, four_smul]
    erw [h2]
    have h1 : ((X.ν q.2.1 : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
    simp only [hχ, habs, NNReal.coe_one, Complex.ofReal_one, one_pow, mul_one, inv_one, one_mul]
    field_simp
  obtain ⟨U, hU, C, hCc, hUC⟩ := GlobalTheory.T.herm_adapted_compact_open_volume F E σ B (b + 2) b G.V' G₁.V' _ _ H 0 (b + 1) K hT.base hT.geo.hV' hC.hH hKc v _
    (hG0.isOpen_fiber (four v (psiAt B.ψ v) m (Tf φ₀) 1)) hSig

  obtain ⟨i, hi⟩ : ∃ i, H.x i ≠ 0 := Function.ne_iff.1 hx0
  have hU' : {w : Fin (b + 2) → Fv F v ⊗[F] E | IsUnit (w i + atV v (incV F H.x) i)} ∈ 𝓝 0 := by
    have ho : IsOpen {c : Fv F v ⊗[F] E | IsUnit c} :=
      (IsOpenUnits.isOpenEmbedding_unitsVal (M := Fv F v ⊗[F] E)).isOpen_range
    have hci : Continuous fun w : Fin (b + 2) → Fv F v ⊗[F] E => w i + atV v (incV F H.x) i :=
      (continuous_apply i).add continuous_const
    refine (ho.preimage hci).mem_nhds ?_
    show IsUnit ((0 : Fin (b + 2) → Fv F v ⊗[F] E) i + atV v (incV F H.x) i)
    rw [Pi.zero_apply, zero_add]
    exact ((Ne.isUnit hi).map (inclR (F := F) (AF F))).map (compFin F E v)
  obtain ⟨L, hLc, hVo, hVc, hVU⟩ := UpperTheory.exists_compact_subgroup_character F E σ (b + 2) G.V'.J (det_ne_zero_herm hT.geo.hV') v _ hψv hψ1 _ (inter_mem hU hU')
  obtain ⟨V, hV⟩ : ∃ V : Set (Fin (b + 2) → Fv F v ⊗[F] E), V = {x | ∀ y ∈ L,
      psiAt B.ψ v (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (pairV σ G.V'.J v x y)) = 1} := ⟨_, rfl⟩
  rw [← hV] at hVo hVc hVU
  have h0V : (0 : Fin (b + 2) → Fv F v ⊗[F] E) ∈ V := by
    rw [hV]
    intro y _
    simp [pairV]
  obtain ⟨L', hL'o, hL'⟩ := UpperTheory.theta_local_open_subgroup F E σ B _ _ _ G.V' G.W G.M' H' hψ v φ₀ hφ₀ (atV v (incV F H.x))
  obtain ⟨φ, hφ, hproj⟩ := UpperTheory.exists_schwartz_character_average _ _ (SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v)) L L' hLc hL'o
    (fun y => locOp v (G.M'.co.rho B.ψ (partFin v (yAt H' v y))) φ₀) φ₀ (fun y => locOp_mem _ _ _) (fun y hy => (hL' y hy).1)
    (fun y => psiAt B.ψ v (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (pairV σ G.V'.J v (atV v (incV F H.x)) y)))
    (fun x y => by rw [pairV_add_right, map_add, AddChar.map_add_eq_mul]) (fun y hy => (hL' y hy).2)

  have hlin : ∀ k ∈ UAt σ G.V' (evFin F v), ∀ (c c' : ℂ), ∀ x ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
      ∀ y ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v), Tf (locOp v (om' (k, 1)) (c • x + c' • y)) =
        fun s => c * Tf (locOp v (om' (k, 1)) x) s + c' * Tf (locOp v (om' (k, 1)) y) s := by
    intro k hk c c' x hx y hy
    funext s
    have hρ : IsLinearMap ℂ (G.M'.co.rho B.ψ (partFin v (uS σ H H' v s))) :=
      ⟨fun f g => funext fun x => mul_add _ _ _, fun c f => funext fun x => mul_left_comm _ _ _⟩
    simp only [hTf, evS]
    rw [locOp_lin (om' (k, 1)).isLinear (fun f hf => ⟨_, locOp_mem _ _ _,
        acts_locOp_om hA P' hk (mem_UAtSub.1 (one_mem _)) hf⟩) c c' hx hy,
      locOp_lin hρ (fun f hf => ⟨_, locOp_mem v _ f, (locOp_rho G.M'.co hψ v _ hf).1⟩) c c' (locOp_mem _ _ _)
        (locOp_mem _ _ _)]
    simp only [map_add, map_smul, smul_eq_mul]
  have hloc : ∀ k ∈ UAt σ G.V' (evFin F v), ∀ t : Fv F v ⊗[F] E,
      four v (psiAt B.ψ v) m (Tf (locOp v (om' (k, 1)) φ)) t =
        V.indicator (fun _ => (1 : ℂ)) (dispA v H.x k t) * four v (psiAt B.ψ v) m (Tf (locOp v (om' (k, 1)) φ₀)) t := by
    intro k hk t
    have h := hproj (fun x => four v (psiAt B.ψ v) m (Tf (locOp v (om' (k, 1)) x)) t)
      (fun y => psiAt B.ψ v (-Algebra.trace (Fv F v) (Fv F v ⊗[F] E)
        (t * pairV σ G.V'.J v (atV v (mat k⁻¹ *ᵥ incV F H.x)) y)))
      (fun x hx y hy => by
        have := hlin k hk 1 1 x hx y hy
        simp only [one_smul, one_mul] at this
        rw [this]
        exact four_add hψv (hsb _ (locOp_mem _ _ _)) (hsb _ (locOp_mem _ _ _)) t)
      (fun c x hx => by
        have := hlin k hk c 0 x hx x hx
        simp only [zero_smul, zero_mul, add_zero] at this
        rw [this]
        exact four_smul _ c t)
      (fun x y => by rw [pairV_add_right, mul_add, map_add, neg_add, AddChar.map_add_eq_mul])
      (fun y => by
        rw [← four_shift]
        congr 1
        funext s
        simp only [hTf]
        rw [UpperTheory.local_theta_partition_triple_alt hP F E σ B a b G G₁ H H' hC e' he ei ev hL X om om' om₁ om₁' hT hT₁ v k hk φ₀ hφ₀ y s])
    have hiff : dispA v H.x k t ∈ V ↔ ∀ y ∈ L,
        psiAt B.ψ v (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (pairV σ G.V'.J v (atV v (incV F H.x)) y)) *
          psiAt B.ψ v (-Algebra.trace (Fv F v) (Fv F v ⊗[F] E)
            (t * pairV σ G.V'.J v (atV v (mat k⁻¹ *ᵥ incV F H.x)) y)) = 1 := by
      rw [hV]
      refine forall₂_congr fun y _ => ?_
      rw [dispA, pairV_smul_sub_left, ← AddChar.map_add_eq_mul, map_sub, ← sub_eq_add_neg,
        ← neg_sub (Algebra.trace _ _ (t * _)), AddChar.map_neg_eq_inv, inv_eq_one]
    by_cases hd : dispA v H.x k t ∈ V
    · rw [Set.indicator_of_mem hd, one_mul]
      exact h.1 (hiff.1 hd)
    · rw [Set.indicator_of_notMem hd, zero_mul]
      exact h.2 fun h' => hd (hiff.2 h')
  have hsupp : ∀ k : KAt K (evFin F v), ∀ t, four v (psiAt B.ψ v) m (Tf (locOp v (om' (k.1, 1)) φ)) t ≠ 0 →
      ∃ l' ∈ C, compFin F E v (l'.1 : AE F E) = t := by
    intro k t ht
    rw [hloc k.1 k.2.2] at ht
    have hd : dispA v H.x k.1 t ∈ V := by
      by_contra hd
      rw [Set.indicator_of_notMem hd, zero_mul] at ht
      exact ht rfl
    have hu : IsUnit (dispA v H.x k.1 t i + atV v (incV F H.x) i) := (hVU hd).2
    rw [dispA, Pi.sub_apply, sub_add_cancel, Pi.smul_apply, smul_eq_mul] at hu
    obtain ⟨u, rfl⟩ := isUnit_of_mul_isUnit_left hu
    have hl' : compFin F E v (((idelesAtEquiv E v).symm u).1 : AE F E) = u :=
      congrArg Units.val ((idelesAtEquiv E v).apply_symm_apply u)
    refine ⟨_, (hUC (k, (idelesAtEquiv E v).symm u) ?_).2, hl'⟩
    rw [disp_eq, hl']
    exact (hVU hd).1

  obtain ⟨T₂, hT₂, C₂, hC₂, hs₂, hZ₂⟩ := UpperTheory.exists_schwartz_bruhat_nonvanishing_integral F E v _ hψv hψ1 m μ hμ X.ν hνc z hz
  refine ⟨φ, hφ, ?_, ?_⟩
  · rw [← hzdef]
    exact GlobalTheory.ConeSoB.coneFin_mem_SB_of_norm hP B G G₁ H H' hC e' he K hK X om om' om₁ om₁' hT hT₁ ei ev hei hev hfac v μK μ
      hμK hμ φ hφ
  have hpass := GlobalTheory.ThK.LemF.ConePass.linear_coneFin_eq hP F E σ B a b G G₁ H H' hC e' he ei ev hL K hK X om om' om₁ om₁'
    hT hT₁ v μK μ hμK.1 hμ.1 l φ hφ
  rw [hzdef] at hpass
  rw [hpass]
  intro h0
  have hk : ∀ k : KAt K (evFin F v),
      GlobalTheory.ThK.LemF.coneLin B G.M' om' v (ev v) μ (shiftB σ H H') X.ν z l φ k.1 *
        (∫ t : idelesAt E (evFin F v), four v (psiAt B.ψ v) m T₂ (compFin F E v (t.1 : AE F E)) * χ t ∂μ) =
      (∫ t : idelesAt E (evFin F v), T₂ (compFin F E v (t.1 : AE F E)) * (X.ν t.1 : ℂ) * ((absE F E t.1 : ℝ) : ℂ) ^ z ∂μ) *
        ((∫ t : idelesAt E (evFin F v), V.indicator (fun _ => (1 : ℂ)) (GlobalTheory.ConeBump.disp v H.x k.1 t.1) ∂μ) *
          four v (psiAt B.ψ v) m (Tf φ₀) 1) := by
    intro k
    have h := UpperTheory.schwartz_bruhat_integral_identity F E v _ hψv hψ1 m μ hμ X.ν hνc z (by omega) _ (hsb _ (locOp_mem v (om' (k.1, 1)) φ)) T₂ hT₂ C C₂
      hCc hC₂ (hsupp k) hs₂
    rw [← integral_mul_const (four v (psiAt B.ψ v) m (Tf φ₀) 1), hχ]
    refine Eq.trans ?_ (h.trans ?_)
    · simp only [GlobalTheory.ThK.LemF.coneLin, hTf, evS, partFin_shiftB]
    · refine congrArg (_ * ·) (congrArg (integral μ) (funext fun t => ?_))
      rw [hloc k.1 k.2.2, ← disp_eq]
      by_cases hd : GlobalTheory.ConeBump.disp v H.x k.1 t.1 ∈ V
      · have h3 := (hUC (k, t) (hVU hd).1).1
        rw [Set.indicator_of_mem hd, one_mul, one_mul, ← h3, hχ]
      · rw [Set.indicator_of_notMem hd, zero_mul, zero_mul, zero_mul]
  have hint := congrArg (integral μK) (funext hk)
  rw [integral_mul_const, h0, zero_mul, integral_const_mul, integral_mul_const] at hint
  exact mul_ne_zero hZ₂ (mul_ne_zero (GlobalTheory.T.local_compact_idele_volume F E σ (b + 2) G.V' H.x K v μK μ hμK hμ V hVo hVc h0V C hCc
    (fun q hq => (hUC q (hVU hq).1).2)) hc0) hint.symm
