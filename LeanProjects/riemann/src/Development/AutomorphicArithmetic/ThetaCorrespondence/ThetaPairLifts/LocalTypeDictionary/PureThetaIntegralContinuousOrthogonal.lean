import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedProductDecayVacuum
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaKernelFundamentalProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedProductDecayVacuumStatement

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Filter Topology MeasureTheory
open GlobalTheory.WeilM
noncomputable section
namespace GlobalTheory.SoPureThetaCont
theorem continuous_pure_theta_integral : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → Decay B G om om' →
    ∀ φ : ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
      (∀ᶠ v in cofinite, φ v = G.M'.vac v) → φ B.v₁ ∈ G.M'.SoLoc B.ψ B.τ₁ →
      ∀ h, Continuous fun f : SInf F (Fin a' × Fin (a + a')) => G.M'.I om' (pure f φ) h := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT hD φ hSB hev hSo h
  have hPair := (GlobalTheory.ThK.Check.isPair_of_isTriple hT).2
  have hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
    (hev.and hT.geo.hM'.std).mono fun v hv => hv.1.trans hv.2
  let A : (Fin a' × Fin (a + a') → Af F) → ℂ := fun z => ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (z i)
  have hA : A ∈ SB (Fin a' × Fin (a + a') → Af F) := GlobalTheory.AdelicCoordSB.finprod_mem_SB F _ φ hSB hstd
  have heq : ∀ u : SInf F (Fin a' × Fin (a + a')), pure u φ = pureA F u A := fun _ => rfl
  have hso : ∀ u : SInf F (Fin a' × Fin (a + a')), pure u φ ∈ G.M'.So B.ψ B.τ₁ := fun u =>
    Submodule.subset_span ⟨u, φ, hSB, hev, hSo, rfl⟩
  have hsch : ∀ u : SInf F (Fin a' × Fin (a + a')), pure u φ ∈ schA F _ := fun u =>
    GlobalTheory.TensUniq.pure_mem_schA u φ hSB hstd
  have hpres : ∀ x, ∀ Φ ∈ schA F (Fin a' × Fin (a + a')), om' x Φ ∈ schA F _ := fun x Φ hΦ =>
    hPair.weil.isUSplitting.pres x Φ hΦ
  have hconv : ∀ u : SInf F (Fin a' × Fin (a + a')), IntegrableOn (fun g => theta om' (pure u φ) g h) G.M'.dom G.M'.μ :=
    fun u => (hD.2 _ (hso u)).2.1 h
  have hadd : ∀ (u u' : SInf F (Fin a' × Fin (a + a'))) g,
      theta om' (pure (u + u') φ) g h = theta om' (pure u φ) g h + theta om' (pure u' φ) g h := by
    intro u u' g
    have e : pure (u + u') φ = pure u φ + pure u' φ := funext fun x => by simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]
    simp only [theta, e, map_add]
    exact thetaSum_add F (hpres _ _ (hsch u)) (hpres _ _ (hsch u'))
  have hsmul : ∀ (c : ℂ) (u : SInf F (Fin a' × Fin (a + a'))) g,
      theta om' (pure (c • u) φ) g h = c * theta om' (pure u φ) g h := by
    intro c u g
    have e : pure (c • u) φ = c • pure u φ := funext fun x => by simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]
    simp only [theta, e, map_smul]
    exact thetaSum_smul F c _
  have hcontg : ∀ g, Continuous fun u : SInf F (Fin a' × Fin (a + a')) => theta om' (pure u φ) g h := fun g =>
    (_root_.GlobalTheory.ThKBasic.theta_kernel_basic_properties hP F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hPair).2 A hA g h
  let μd := G.M'.μ.restrict G.M'.dom
  let T : SInf F (Fin a' × Fin (a + a')) → UA σ G.V'.J → ℂ := fun u g => theta om' (pure u φ) g h
  have hfin : ∀ u, (∫⁻ g, ‖T u g‖ₑ ∂μd) ≠ ⊤ := fun u => (hconv u).2.ne
  have hν : ∀ u, ∫ g, ‖T u g‖ ∂μd = (∫⁻ g, ‖T u g‖ₑ ∂μd).toReal := fun u =>
    integral_norm_eq_lintegral_enorm (hconv u).1
  let ν : Seminorm ℂ (SInf F (Fin a' × Fin (a + a'))) :=
    Seminorm.of (fun u => ∫ g, ‖T u g‖ ∂μd)
      (fun u u' => by
        calc ∫ g, ‖T (u + u') g‖ ∂μd ≤ ∫ g, (‖T u g‖ + ‖T u' g‖) ∂μd :=
              integral_mono (hconv (u + u')).norm ((hconv u).norm.add (hconv u').norm)
                fun g => by simp only [T]; rw [hadd]; exact norm_add_le _ _
          _ = _ := integral_add (hconv u).norm (hconv u').norm)
      (fun c u => by
        simp only [T, hsmul, norm_mul]
        exact integral_const_mul _ _)
  haveI : BarrelledSpace ℂ (SInf F (Fin a' × Fin (a + a'))) := by
    classical exact GlobalTheory.schwartzMap_barrelledSpace _
  have hN : LowerSemicontinuous fun u => ∫⁻ g, ‖T u g‖ₑ ∂μd := by
    rw [lowerSemicontinuous_iff_le_liminf]
    intro u
    calc ∫⁻ g, ‖T u g‖ₑ ∂μd ≤ ∫⁻ g, liminf (fun u' => ‖T u' g‖ₑ) (𝓝 u) ∂μd :=
          lintegral_mono fun g => (((hcontg g).tendsto u).enorm.liminf_eq).ge
      _ ≤ _ := lintegral_liminf_le' fun u' => (hconv u').1.enorm
  have hνc : Continuous ν := by
    refine Seminorm.continuous_of_lowerSemicontinuous ν fun u y hy => ?_
    by_cases hy0 : y < 0
    · exact Filter.Eventually.of_forall fun u' => hy0.trans_le (apply_nonneg ν u')
    · push_neg at hy0
      have hy' : y < (∫⁻ g, ‖T u g‖ₑ ∂μd).toReal := by rw [← hν]; exact hy
      have h1 : ENNReal.ofReal y < ∫⁻ g, ‖T u g‖ₑ ∂μd := (ENNReal.ofReal_lt_iff_lt_toReal hy0 (hfin _)).2 hy'
      filter_upwards [hN u _ h1] with u' hu'
      show y < ∫ g, ‖T u' g‖ ∂μd
      rw [hν]
      exact (ENNReal.ofReal_lt_iff_lt_toReal hy0 (hfin _)).1 hu'
  let L : SInf F (Fin a' × Fin (a + a')) →+ ℂ :=
    { toFun := fun u => G.M'.I om' (pure u φ) h
      map_zero' := by
        show ∫ g, T 0 g ∂μd = 0
        have : ∀ g, T 0 g = 0 := fun g => by
          simpa using hsmul 0 0 g
        simp [this]
      map_add' := fun u u' => by
        show ∫ g, T (u + u') g ∂μd = ∫ g, T u g ∂μd + ∫ g, T u' g ∂μd
        simp only [T, hadd]
        exact integral_add (hconv u) (hconv u') }
  have hLb : ∀ u, ‖L u‖ ≤ ν u := fun u => norm_integral_le_integral_norm _
  have hL : Continuous L := by
    refine continuous_of_continuousAt_zero L ?_
    rw [ContinuousAt, map_zero, tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun u => norm_nonneg _) hLb ?_
    simpa using hνc.tendsto (0 : SInf F (Fin a' × Fin (a + a')))
  exact hL
end GlobalTheory.SoPureThetaCont
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pure_theta_integral_continuous_orthogonal : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → Decay B G om om' →
    ∀ φ : ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
      (∀ᶠ v in cofinite, φ v = G.M'.vac v) → φ B.v₁ ∈ G.M'.SoLoc B.ψ B.τ₁ →
      ∀ h, Continuous fun f : SInf F (Fin a' × Fin (a + a')) => G.M'.I om' (pure f φ) h := by
  first | exact @_root_.GlobalTheory.SoPureThetaCont.continuous_pure_theta_integral | exact _root_.GlobalTheory.SoPureThetaCont.continuous_pure_theta_integral | (intros; apply _root_.GlobalTheory.SoPureThetaCont.continuous_pure_theta_integral <;> assumption)
end
