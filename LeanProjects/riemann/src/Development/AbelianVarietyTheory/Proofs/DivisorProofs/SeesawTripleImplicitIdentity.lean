import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAEvaluationLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorIdeleConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrablePowerNormCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UAtMemIsoB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerLocallyConstantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCoefficientTendstoZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCoefficientIdeleScalingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceCharacterAnnihilatorCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigurationBTriplesReconfigurationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigurationBTripleLocalZetaStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB GlobalTheory.ThK.ConeEuler GlobalTheory.UnrEuler
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.LocConvB

open scoped GlobalTheory.VacAny in

theorem integrable_shiftB {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E) {a b : ℕ} {G : Geo σ a (b + 2)} {G₁ : Geo σ a b} {H : Plane E (b + 2) b}
    {H' : Plane E (a + (b + 2)) (a + b)} (hC : CfgB B G G₁ H H')
    {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {om₁ : Rep σ G₁.V G₁.W} {om₁' : Rep σ G₁.V' G₁.W}
    (hT : IsTriple B G X om om') (hT₁ : IsTriple B G₁ X om₁ om₁')
    {e' : Fn F (b + 2) (a + (b + 2)) →ₗ[ℂ] Fn F b (a + b)} (hE : IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e')
    (ei' : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b)))
    (ev' : ∀ v : Pl F, ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F v) → ℂ)
    (hei : ei' ≠ 0) (hev : ∀ v, ev' v (G.M'.vac v) = G₁.M'.vac v ∧
      (SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v)).map (ev' v) = SB (Fin b × Fin (a + b) → Fv F v))
    (hloc : ∀ (f : SInf F (Fin (b + 2) × Fin (a + (b + 2)))) (φ : ∀ v : Pl F, (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ),
      (∀ v, φ v ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v)) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) →
      e' (pure f φ) = pure (ei' f) fun v => ev' v (φ v))
    (v : Pl F) (μ : Measure (idelesAt E (evFin F v))) (hμ : IsNormE E v μ) (z : ℕ) (hz : 1 ≤ z)
    {ψ : (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ} (hψ : ψ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v))
    (y : Fin b × Fin (a + b) → Fv F v) :
    Integrable (fun l : idelesAt E (evFin F v) =>
      ev' v (locOp v (G.M'.co.rho B.ψ (partFin v (shiftB σ H H' l.1))) ψ) y * (X.ν l.1 : ℂ) *
        ((absE F E l.1 : ℝ) : ℂ) ^ z) μ := by
  have hψc : Continuous B.ψ := hT.base.std.1
  have hψv : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := GlobalTheory.SchrSB.continuous_psiAt B.ψ hψc v
  have hne : GlobalTheory.LatVac.psiAt B.ψ v ≠ 1 := GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hT.base.std v
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evFin F v)
  haveI := hμ.1
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : T2Space (Fv F v ⊗[F] E) := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension

  set U : Set (Fv F v ⊗[F] E) :=
    {t | schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (GlobalTheory.VanishLoc.uAt H H' v t)) ψ = ψ} with hUdef
  have hU : U ∈ 𝓝 0 := (GlobalTheory.T.local_coefficient_tendsto_zero G.M' H H' v).eventually (GlobalTheory.T.schrodinger_locally_constant v (GlobalTheory.LatVac.psiAt B.ψ v) hψv ψ hψ)
  set C : Set (Fv F v ⊗[F] E) :=
    {l | ∀ t ∈ U, GlobalTheory.LatVac.psiAt B.ψ v (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (t * l)) = 1} with hCdef
  have hCc : IsCompact C := GlobalTheory.TraceAnnCompact.isCompact_trace_ann v _ hψv hne U hU
  have hinv := (GlobalTheory.ThK.EvLocParts.locParts F E σ B _ _ _ _ _ _ _ _ G.M' G₁.M' _ _ _ e' hT.base hT.geo.hM' hT₁.geo.hM' hE
    ei' ev' hei hev hloc v).2
  have hvan : ∀ l : (AE F E)ˣ, compFin F E v l ∉ C →
      ev' v (locOp v (G.M'.co.rho B.ψ (partFin v (shiftB σ H H' l))) ψ) = 0 := by
    intro l hl
    simp only [hCdef, Set.mem_setOf_eq, not_forall] at hl
    obtain ⟨t, ht, hne1⟩ := hl
    have ht' : schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (GlobalTheory.VanishLoc.uAt H H' v t)) ψ = ψ := ht
    rw [(locOp_rho G.M'.co hψc v (shiftB σ H H' l) hψ).2]
    have hS : schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (shiftB σ H H' l)) ψ ∈ SB _ :=
      GlobalTheory.SchrSB.schr_mem_SB B.ψ hψc v _ ψ hψ
    have h1 := hinv (GlobalTheory.VanishLoc.uAt H H' v t) (GlobalTheory.VanishLoc.uAt_mem_isoB H H' v t) (GlobalTheory.VanishLoc.at_uAt H H' v t) _ hS
    have h3 := (locOp_rho G.M'.co hψc v (GlobalTheory.VanishLoc.uAt H H' v t) hS).2
    rw [partFin_of_at (GlobalTheory.VanishLoc.at_uAt H H' v t)] at h3
    rw [h3, GlobalTheory.VanishLoc.schr_comm, ht', map_smul, GlobalTheory.T.local_coefficient_idele_scaling B G G₁ H H' hC X om om' hT v t l] at h1
    have h2 : (GlobalTheory.LatVac.psiAt B.ψ v (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (t * compFin F E v l)) - 1) •
        ev' v (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (shiftB σ H H' l)) ψ) = 0 := by
      rw [sub_smul, h1, one_smul, sub_self]
    exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hne1)

  obtain ⟨g, hg, hge⟩ := GlobalTheory.SchrLocConst.shiftB_locOp_locallyConstant F E σ B G.M' H H' hψc v ψ hψ
  have hgy : Continuous fun x => ev' v (g x) y := (hg.comp fun f => ev' v f y).continuous
  have hcl : Continuous fun l : idelesAt E (evFin F v) => compFin F E v l.1.1 :=
    Units.continuous_val.comp ((GlobalTheory.Doubling.continuous_unitFin v).comp continuous_subtype_val)
  have hν : Continuous fun l : (AE F E)ˣ => (X.ν l : ℂ) :=
    continuous_subtype_val.comp
      (show Continuous fun l => X.α l / X.β l from hT.chars.heckeα.1.div' hT.chars.heckeβ.1)
  have habs : Continuous fun l : idelesAt E (evFin F v) => ((absE F E l.1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp (GlobalTheory.Doubling.continuous_absE.comp continuous_subtype_val))
  have he : ∀ l : idelesAt E (evFin F v),
      ev' v (locOp v (G.M'.co.rho B.ψ (partFin v (shiftB σ H H' l.1))) ψ) y = ev' v (g (compFin F E v l.1.1)) y :=
    fun l => by rw [hge l.1 l.2]; rfl
  obtain ⟨R, hR⟩ := hCc.exists_bound_of_continuousOn hgy.continuousOn
  have hI := (GlobalTheory.LocTateInt.integrable_indicator_absE_pow v μ hμ C hCc z hz).const_mul R
  simp only [he]
  refine hI.mono' (((hgy.comp hcl).mul (hν.comp continuous_subtype_val)).mul (habs.pow _)).aestronglyMeasurable
    (ae_of_all _ fun l => ?_)
  by_cases hl : compFin F E v l.1.1 ∈ C
  · rw [Set.indicator_of_mem hl]
    simp only [norm_mul, norm_pow, Circle.norm_coe, mul_one, Complex.norm_real, NNReal.norm_eq]
    exact mul_le_mul_of_nonneg_right (hR _ hl) (by positivity)
  · rw [Set.indicator_of_notMem hl, ← he, hvan l.1 hl]
    simp

set_option synthInstance.maxHeartbeats 100000 in

theorem locConv : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (_hKP : KP) (B : Base F E) {a b : ℕ} {G : Geo σ a (b + 2)} {G₁ : Geo σ a b} {H : Plane E (b + 2) b}
    {H' : Plane E (a + (b + 2)) (a + b)}, CfgB B G G₁ H H' →
    ∀ {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {om₁ : Rep σ G₁.V G₁.W} {om₁' : Rep σ G₁.V' G₁.W},
    IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ {e' : Fn F (b + 2) (a + (b + 2)) →ₗ[ℂ] Fn F b (a + b)}, IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' →
    ∀ (ei' : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b)))
      (ev' : ∀ v : Pl F, ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F v) → ℂ),
    ei' ≠ 0 → (∀ v, ev' v (G.M'.vac v) = G₁.M'.vac v ∧
      (SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v)).map (ev' v) = SB (Fin b × Fin (a + b) → Fv F v)) →
    (∀ (f : SInf F (Fin (b + 2) × Fin (a + (b + 2)))) (φ : ∀ v : Pl F, (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ),
      (∀ v, φ v ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v)) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) →
      e' (pure f φ) = pure (ei' f) fun v => ev' v (φ v)) →
    ∀ {K : Subgroup (UA σ G.V'.J)}, IsStab B K →
    ∀ (μKI : Measure (KAt K (evI F))) (μI : Measure (idelesAt E (evI F))), IsNormK K (evI F) μKI → μI.IsHaarMeasure →
    ∀ (μKv : ∀ v : Pl F, Measure (KAt K (evFin F v))) (μv : ∀ v : Pl F, Measure (idelesAt E (evFin F v))),
    (∀ v, IsNormK K (evFin F v) (μKv v)) → (∀ v, IsNormE E v (μv v)) →
    (∀ (v : Pl F) (φ : (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ), φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) →
      ∀ y : Fin b × Fin (a + b) → Fv F v,
      Integrable (fun p : KAt K (evFin F v) × idelesAt E (evFin F v) =>
        coneFinInt B G.M' om' v (ev' v) (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ p.1.1 p.2.1 y) ((μKv v).prod (μv v)) ∧
      ∀ k ∈ KAt K (evFin F v), Integrable (fun l : idelesAt E (evFin F v) =>
        coneFinInt B G.M' om' v (ev' v) (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ k l.1 y) (μv v)) ∧
    ∀ (f : SInf F (Fin (b + 2) × Fin (a + (b + 2)))) (y : Fin b × Fin (a + b) → mixedEmbedding.mixedSpace F),
      Integrable (fun p : KAt K (evI F) × idelesAt E (evI F) =>
        coneInfInt B G.M' om' ei' (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) f p.1.1 p.2.1 y) (μKI.prod μI) ∧
      ∀ k ∈ KAt K (evI F), Integrable (fun l : idelesAt E (evI F) =>
        coneInfInt B G.M' om' ei' (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) f k l.1 y) μI := by
  intro F E _ _ _ _ _ σ hKP B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ e' hE ei' ev' hei hev hloc K hK μKI μI hμKI hμI
    μKv μv hμKv hμv
  refine ⟨fun v φ hφ y => ?_, fun f y => ?_⟩
  · have hKc : IsCompact (K : Set (UA σ G.V'.J)) := by
      obtain ⟨K₀, -, -, h1, h2, -⟩ := GlobalTheory.StabHaar.stabEx hKP.base F E σ B (b + 2) G.V' _ _ hT.base hT.geo.hV'
      rwa [show K = K₀ from Subgroup.ext fun g => (hK g).trans (h1 g).symm]
    haveI : CompactSpace (KAt K (evFin F v)) := isCompact_iff_compactSpace.1 (isCompact_KAt hKc _)
    obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evFin F v)
    haveI : BorelSpace (UA σ G.V'.J) := ⟨rfl⟩
    haveI := (hμv v).1
    haveI : IsFiniteMeasure (μKv v) := ⟨by rw [(hμKv v).2]; exact ENNReal.one_lt_top⟩
    have hz : 1 ≤ (a - (b + 2)) / 2 + 1 := Nat.le_add_left 1 _
    have hI : ∀ ψ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v), Integrable (fun l : idelesAt E (evFin F v) =>
        ev' v (locOp v (G.M'.co.rho B.ψ (partFin v (shiftB σ H H' l.1))) ψ) y * (X.ν l.1 : ℂ) *
          ((absE F E l.1 : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1)) (μv v) := fun ψ hψ =>
      integrable_shiftB B hC hT hT₁ hE ei' ev' hei hev hloc v (μv v) (hμv v) _ hz hψ y
    refine ⟨GlobalTheory.ThK.ConeLocInt.integrable_prod_of_locallyConstant (μKv v) (μv v)
      (GlobalTheory.ThK.ConeLocInt.isLocallyConstant_locOp_om (GlobalTheory.T.theta_action_exists hKP.base) (GlobalTheory.ThK.Check.isPair_of_isTriple hT).2 K v hφ)
      (fun ψ l => ev' v (locOp v (G.M'.co.rho B.ψ (partFin v (shiftB σ H H' l.1))) ψ) y * (X.ν l.1 : ℂ) *
          ((absE F E l.1 : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1)) fun k => hI _ (locOp_mem v _ φ),
      fun k _ => hI _ (locOp_mem v _ φ)⟩
  · haveI : IsFiniteMeasure μKI := ⟨by rw [hμKI.2]; exact ENNReal.one_lt_top⟩
    obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evI F)
    obtain ⟨hm, hmk⟩ := GlobalTheory.T.configuration_b_triples_reconfiguration hKP B hC hT hT₁ hE ei' ev' hei hev hloc hK μKI μI hμKI hμI f y
    obtain ⟨g, hg, hgb⟩ := GlobalTheory.T.configuration_b_triple_local_zeta hKP B hC hT hT₁ hE ei' ev' hei hev hloc hK μKI μI hμKI hμI f y
    refine ⟨((integrable_const (1 : ℝ)).mul_prod hg).mono' hm (ae_of_all _ fun p => ?_),
      fun k hk => hg.mono' (hmk k hk) (ae_of_all _ fun l => hgb k hk l)⟩
    simpa using hgb p.1.1 p.1.2 p.2

end GlobalTheory.ThK.LocConvB

end
