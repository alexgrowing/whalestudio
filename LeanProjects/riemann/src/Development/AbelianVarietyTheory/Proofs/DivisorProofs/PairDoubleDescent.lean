import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairAdaptedPlanesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerInvariantFunctionalsLagrangianStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.EvLawUniq

theorem eq_smul_isEv : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (H : Plane E n n₁) (H' : Plane E d d₁) (j₀ j₁ i₀ i₁ : ℕ) (M₁ : Model σ X₁ W₁),
    H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ →
    ∀ e, IsEv B M M₁ H.ι H'.ι (isoA H H') e → ∀ f : Fn F n d →ₗ[ℂ] Fn F n₁ d₁,
    (∀ (z : Matrix (Fin n₁) (Fin d₁) (AE F E)), ∀ Φ ∈ schA F (Fin n × Fin d),
      f (M.co.rho B.ψ (incM F H.ι * z * (incM F H'.ι)ᵀ) Φ) = M₁.co.rho B.ψ z (f Φ)) →
    (∀ u ∈ isoA H H', ∀ Φ ∈ schA F (Fin n × Fin d), f (M.co.rho B.ψ u Φ) = f Φ) →
    ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), f Φ = c • e Φ := by
  intro hP F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M χX χW om r s r' s' hpair H H' j₀ j₁ i₀ i₁ M₁ hH hH' hM₁ e hev f hfh hfi
  have hψ : IsStd B.ψ := hpair.base.std
  have hM : M.IsGood B.ψ := hpair.good
  let ev0 : Fn F n₁ d₁ →ₗ[ℂ] ℂ := LinearMap.proj (R := ℂ) (φ := fun _ : (Fin n₁ × Fin d₁ → AF F) => ℂ) 0
  let j : Matrix (Fin n₁) (Fin d₁) (AE F E) → Matrix (Fin n) (Fin d) (AE F E) :=
    fun z => incM F H.ι * z * (incM F H'.ι)ᵀ
  have hmem : ∀ (w : Matrix (Fin n) (Fin d) (AE F E)) (Φ : Fn F n d), Φ ∈ schA F (Fin n × Fin d) →
      M.co.rho B.ψ w Φ ∈ schA F (Fin n × Fin d) :=
    fun w Φ hΦ => GlobalTheory.HeisSchA.schr_mem_schA B.ψ hψ _ Φ hΦ

  have hrec : ∀ S : Fn F n d →ₗ[ℂ] Fn F n₁ d₁,
      (∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), S (M.co.rho B.ψ (j z) Φ) = M₁.co.rho B.ψ z (S Φ)) →
      ∀ Φ ∈ schA F (Fin n × Fin d), ∀ y, S Φ y = ev0 (S (M.co.rho B.ψ (j (M₁.co.e.symm (y, 0))) Φ)) := by
    intro S hS Φ hΦ y
    rw [hS _ Φ hΦ]
    simp [ev0, Darboux.rho, schr]
  obtain ⟨L, hiso, hrk, hL⟩ := GlobalTheory.T.seesaw_pair_adapted_planes F E σ B n d n₁ d₁ X W X₁ W₁ M χX χW om r s r' s' hpair H H' j₀ j₁ i₀ i₁ M₁ hH hH' hM₁

  have inv : ∀ S : Fn F n d →ₗ[ℂ] Fn F n₁ d₁,
      (∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), S (M.co.rho B.ψ (j z) Φ) = M₁.co.rho B.ψ z (S Φ)) →
      (∀ u ∈ isoA H H', ∀ Φ ∈ schA F (Fin n × Fin d), S (M.co.rho B.ψ u Φ) = S Φ) →
      ∀ (t : AF F), ∀ w ∈ L, ∀ Φ ∈ schA F (Fin n × Fin d),
        (ev0 ∘ₗ S) (schr B.ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) Φ) =
          (ev0 ∘ₗ S) Φ := by
    intro S hS hI t w hw Φ hΦ
    obtain ⟨y, z₂, z, hz, he⟩ := hL t w hw
    have h1 := hmem (j z) Φ hΦ
    have h2 := hmem (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ z₂)) _ h1
    rw [LinearMap.comp_apply, LinearMap.comp_apply, he,
      hI _ (Set.mem_union_left _ ⟨y, rfl⟩) _ h2, hI _ (Set.mem_union_right _ ⟨z₂, rfl⟩) _ h1, hS z Φ hΦ]
    simp [ev0, Darboux.rho, schr, hz]
  have hevh : ∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ (j z) Φ) = M₁.co.rho B.ψ z (e Φ) :=
    fun z Φ hΦ => hev.Heisenberg₂ z Φ hΦ

  obtain ⟨ei, ev, hei, hloc0, hloc⟩ := hev.loc
  have hex : ∀ v : Pl F, ∃ p : (Fin n × Fin d → Fv F v) → ℂ, p ∈ SB _ ∧
      ev v p = Set.indicator {x : Fin n₁ × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∧
      (M₁.vac v = Set.indicator {x : Fin n₁ × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
        p = M.vac v) := by
    intro v
    by_cases h : M₁.vac v = Set.indicator {x : Fin n₁ × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
    · exact ⟨M.vac v, (hM.vac v).1, by rw [← h]; exact (hloc0 v).1, fun _ => rfl⟩
    · have hmem' : Set.indicator {x : Fin n₁ × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∈
          (SB (Fin n × Fin d → Fv F v)).map (ev v) := by
        rw [(hloc0 v).2]; exact GlobalTheory.StdVacuum.indicator_mem_SB v
      obtain ⟨p, hp, hpe⟩ := Submodule.mem_map.1 hmem'
      exact ⟨p, hp, hpe, fun h' => absurd h' h⟩
  choose φ hφSB hφev hφvac using hex
  have hcof : ∀ᶠ v in cofinite, φ v = M.vac v := by
    filter_upwards [hM₁.std] with v hv
    exact hφvac v hv
  have hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
    filter_upwards [hcof, hM.std] with v h1 h2
    rw [h1, h2]
  obtain ⟨g, hg⟩ : ∃ g, ei g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hei (ContinuousLinearMap.ext h)
  have hΦ₀ : pure g φ ∈ schA F (Fin n × Fin d) := (GlobalTheory.ThK.EvUniqInf.rest_pure g φ hφSB hstd).2
  have hne : e (pure g φ) ≠ 0 := by
    rw [hloc g φ hφSB hcof, show (fun v => ev v (φ v)) = fun v =>
      Set.indicator {x : Fin n₁ × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 from funext hφev]
    intro h0
    apply hg
    apply GlobalTheory.ThK.EvUniqInf.eq_of_pure_std (ei g) 0
    rw [h0]
    funext x
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
  obtain ⟨y₀, hy₀⟩ := Function.ne_iff.1 hne
  obtain ⟨c, hc⟩ := GlobalTheory.T.schrodinger_invariant_functionals_lagrangian hP F B.ψ hψ (Fin n × Fin d) L hiso hrk (ev0 ∘ₗ f) (ev0 ∘ₗ e) (inv f hfh hfi) (inv e hevh hev.inv)
    ⟨M.co.rho B.ψ (j (M₁.co.e.symm (y₀, 0))) (pure g φ), hmem _ _ hΦ₀, by
      rw [LinearMap.comp_apply, ← hrec e hevh _ hΦ₀ y₀]; exact hy₀⟩
  refine ⟨c, fun Φ hΦ => funext fun y => ?_⟩
  rw [hrec f hfh Φ hΦ y, Pi.smul_apply, hrec e hevh Φ hΦ y, smul_eq_mul]
  exact hc _ (hmem _ _ hΦ)

end GlobalTheory.ThK.EvLawUniq
