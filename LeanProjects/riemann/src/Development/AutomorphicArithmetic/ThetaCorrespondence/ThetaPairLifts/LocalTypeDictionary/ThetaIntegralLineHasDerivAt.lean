import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleGlobalLiftIdentity
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsWeilRepArchimedeanSmoothOrbit

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open MeasureTheory Filter Topology
open scoped Classical
noncomputable section
namespace GlobalTheory.ThetaIntegralLine
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}
theorem thetaIntegral_line_hasDerivAt (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (χY χW : Chr F E) (om : Rep σ Y W)
    (hcm : IsCMExt F E σ) (hψ : IsStd ψ) (hw : M.IsWeil ψ χY χW om) (hconv : ∀ Φ ∈ schA F (Fin n × Fin d), M.Conv om Φ)
    (hcont : ∀ φ ∈ SB (Fin n × Fin d → Af F), ∀ h, Continuous fun f : SInf F (Fin n × Fin d) => M.I om (pureA F f φ) h)
    {γ : Multiplicative ℝ →* UA σ W.J} (hγ : γ ∈ Lines σ W) {Φ : Fn F n d} (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    ∃ Φ₁ ∈ schA F (Fin n × Fin d), (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) ∧
      ∀ h, HasDerivAt (fun t : ℝ => M.I om Φ (h * γ (Multiplicative.ofAdd t))) (M.I om Φ₁ h) 0 := by
  have hpres : ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ ∈ schA F (Fin n × Fin d) :=
    (GlobalTheory.WeilM.IsUWeilPair.isUSplitting hw).pres
  induction hΦ using Submodule.span_induction with
  | zero =>
    refine ⟨0, Submodule.zero_mem _, fun x => ?_, fun h => ?_⟩
    · simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)
    · have e : ∀ h', M.I om 0 h' = 0 := fun h' => by simpa using I_smul M om 0 0 h'
      simpa [e] using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add Φ Ψ hΦ hΨ ihΦ ihΨ =>
    obtain ⟨Φ₁, m₁, p₁, q₁⟩ := ihΦ
    obtain ⟨Ψ₁, m₂, p₂, q₂⟩ := ihΨ
    refine ⟨Φ₁ + Ψ₁, Submodule.add_mem _ m₁ m₂, fun x => ?_, fun h => ?_⟩
    · simpa only [map_add, Pi.add_apply] using (p₁ x).fun_add (p₂ x)
    · simpa only [I_add M om hpres hconv hΦ hΨ, I_add M om hpres hconv m₁ m₂] using (q₁ h).fun_add (q₂ h)
  | smul c Φ hΦ ih =>
    obtain ⟨Φ₁, m₁, p₁, q₁⟩ := ih
    refine ⟨c • Φ₁, Submodule.smul_mem _ c m₁, fun x => ?_, fun h => ?_⟩
    · simpa only [map_smul, Pi.smul_apply, smul_eq_mul] using (p₁ x).const_mul c
    · simpa only [I_smul] using (q₁ h).const_mul c
  | mem Φ hΦ =>
    obtain ⟨f, φ, hφ, rfl⟩ := hΦ
    obtain ⟨c, c', h0, hlim, hacts⟩ := _root_.GlobalTheory.WeilArchSmooth.exists_weilRep_archimedean_smooth_orbit hP M ψ χY χW om hcm hψ hw γ hγ f
    have hmem : ∀ u : SInf F (Fin n × Fin d), pureA F u φ ∈ schA F (Fin n × Fin d) :=
      fun u => Submodule.subset_span ⟨u, φ, hφ, rfl⟩
    have hR : Rest (evI F) (⇑f) (fun x : Fin n × Fin d → AF F => φ fun i => (x i).2) := by
      refine ⟨fun x z hz => congrArg φ (funext fun i => ?_), hmem f⟩
      show (x i).2 + (z i).2 = (x i).2
      rw [snd_eq_zero_of_at z hz i, add_zero]
    have hc : ∀ t : ℝ, om (1, γ (Multiplicative.ofAdd t)) (pureA F f φ) = pureA F (c t) φ := fun t => hacts t _ hR
    refine ⟨pureA F c' φ, hmem c', fun x => ?_, fun h => ?_⟩
    · have ev : Continuous fun s : SInf F (Fin n × Fin d) => s (fun j => evI F (x j)) :=
        (continuous_eval_const (F := BoundedContinuousFunction (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)
          (fun j => evI F (x j))).comp
          (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ).continuous
      have h2 : HasDerivAt (fun t : ℝ => c t (fun j => evI F (x j)) * φ fun i => (x i).2)
          (c' (fun j => evI F (x j)) * φ fun i => (x i).2) 0 := by
        rw [hasDerivAt_iff_tendsto_slope]
        refine (((ev.tendsto c').comp hlim).mul_const _).congr' (Filter.Eventually.of_forall fun t => ?_)
        rw [slope_def_module, h0]
        simp only [Function.comp_apply, SchwartzMap.smul_apply, SchwartzMap.sub_apply, sub_zero, Complex.real_smul]
        ring
      simp only [hc]
      exact h2
    · let L : SInf F (Fin n × Fin d) →ₗ[ℝ] ℂ :=
        { toFun := fun u => M.I om (pureA F u φ) h
          map_add' := fun u u' => by
            have e : pureA F ⇑(u + u') φ = pureA F u φ + pureA F u' φ := by
              funext x; simp [pureA, add_mul]
            rw [e, I_add M om hpres hconv (hmem u) (hmem u')]
          map_smul' := fun s u => by
            have e : pureA F ⇑(s • u) φ = (s : ℂ) • pureA F u φ := by
              funext x; simp [pureA, mul_assoc, Complex.real_smul]
            rw [e, I_smul, RingHom.id_apply, Complex.real_smul] }
      have hL : Continuous L := hcont φ hφ h
      have hcurve : (fun t : ℝ => M.I om (pureA F f φ) (h * γ (Multiplicative.ofAdd t))) = fun t => L (c t) := by
        funext t
        rw [← I_om_one, hc]
        rfl
      rw [hcurve, hasDerivAt_iff_tendsto_slope]
      refine ((hL.tendsto c').comp hlim).congr' (Filter.Eventually.of_forall fun t => ?_)
      simp only [Function.comp_apply, slope_def_module, h0, sub_zero, map_smul, map_sub]
end GlobalTheory.ThetaIntegralLine
end
end
