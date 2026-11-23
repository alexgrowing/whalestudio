import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAdelicSchwartzSpaceOfLevelCompactSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAEigenStabilizerTriplesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAEigenStabilizerIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAHaarEigenUnfoldingStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ConeSchwartz

open scoped Classical in

theorem comp_mem_schA' {F : Type} [Field F] [NumberField F] {κ κ' : Type} [Fintype κ] [Fintype κ'] (σ : κ ≃ κ')
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : (fun x : κ' → AF F => Φ (x ∘ σ)) ∈ schA F κ' := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    let A : (κ' → mixedEmbedding.mixedSpace F) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
      (LinearEquiv.funCongrLeft ℝ (mixedEmbedding.mixedSpace F) σ).toContinuousLinearEquiv
    let B : (κ' → FiniteAdeleRing (𝓞 F) F) ≃ₜ (κ → FiniteAdeleRing (𝓞 F) F) :=
      (Homeomorph.piCongrLeft (Y := fun _ => FiniteAdeleRing (𝓞 F) F) σ).symm
    refine Submodule.subset_span ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A f, g ∘ B,
      ⟨hg.1.comp_continuous B.continuous, hg.2.comp_homeomorph B⟩, ?_⟩
    rfl
  | zero => exact Submodule.zero_mem _
  | add Φ Ψ _ _ h1 h2 => exact Submodule.add_mem _ h1 h2
  | smul c Φ _ h => exact Submodule.smul_mem _ c h

end GlobalTheory.ConeSchwartz

namespace GlobalTheory.ConeSchwartz

open GlobalTheory.ThetaTransform in
open scoped Classical in

theorem mem_schA_of_level_gen (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (Φ : (κ → AF F) → ℂ)
    (hU : ∃ U : AddSubgroup (κ → AF F), IsOpen (U : Set (κ → AF F)) ∧ ∀ u ∈ U, (∀ i, (u i).1 = 0) → ∀ x, Φ (x + u) = Φ x)
    (hC : ∃ C : Set (κ → FiniteAdeleRing (𝓞 F) F), IsCompact C ∧ ∀ x, Φ x ≠ 0 → (fun i => (x i).2) ∈ C)
    (hS : ∀ x, ∃ g : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, ∀ t, g t = Φ (x + embR t)) :
    Φ ∈ schA F κ := by
  let s : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  let Φ' : (Fin (Fintype.card κ) → AF F) → ℂ := fun y => Φ (y ∘ s)
  have h' : Φ' ∈ schA F (Fin (Fintype.card κ)) := by
    refine GlobalTheory.LevelSchwartz.mem_schA_of_level F _ Φ' ?_ ?_ ?_
    · obtain ⟨U, hUo, hUi⟩ := hU
      let r : (Fin (Fintype.card κ) → AF F) →+ (κ → AF F) :=
        { toFun := fun y => y ∘ s, map_zero' := rfl, map_add' := fun _ _ => rfl }
      have hr : Continuous r := continuous_pi fun i => continuous_apply _
      refine ⟨U.comap r, hUo.preimage hr, fun u hu hinf x => ?_⟩
      have h0 : ∀ i, (r u i).1 = 0 := fun i => congrFun hinf (s i)
      exact hUi (r u) hu h0 (r x)
    · obtain ⟨C, hCc, hCs⟩ := hC
      let m : (κ → FiniteAdeleRing (𝓞 F) F) → (Fin (Fintype.card κ) → FiniteAdeleRing (𝓞 F) F) :=
        fun f j => f (s.symm j)
      have hm : Continuous m := continuous_pi fun j => continuous_apply _
      refine ⟨m '' C, hCc.image hm, fun x hx => ⟨fun i => (x (s i)).2, hCs _ hx, funext fun j => ?_⟩⟩
      show (x (s (s.symm j))).2 = _
      rw [Equiv.apply_symm_apply]
      rfl
    · intro y
      obtain ⟨g, hg⟩ := hS (y ∘ s)
      let A : (Fin (Fintype.card κ) → mixedEmbedding.mixedSpace F) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
        (LinearEquiv.funCongrLeft ℝ (mixedEmbedding.mixedSpace F) s).toContinuousLinearEquiv
      refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A g, fun t => ?_⟩
      rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, hg]
      rfl
  have h2 := comp_mem_schA' s.symm h'
  have h3 : (fun x : κ → AF F => Φ' (x ∘ s.symm)) = Φ := by
    funext x
    show Φ ((x ∘ s.symm) ∘ s) = Φ x
    congr 1
    funext i
    simp
  rw [← h3]
  exact h2

theorem cone_mem_schA : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')),
      cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) Ψ ∈ schA F (Fin b × Fin (b + a')) := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hC e he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Ψ hΨ
  refine mem_schA_of_level_gen F _ _ ?_ ?_
    (GlobalTheory.T.config_a_haar_eigen_unfolding hKP F E σ B b a' G G₁ H H' hC e he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Ψ hΨ)
  · obtain ⟨U, hUo, hU⟩ := GlobalTheory.T.config_a_eigen_stabilizer_triples F E σ B b a' G G₁ H H' hC e he K hK X om om' om₁ om₁' hT hT₁ Ψ hΨ
    refine ⟨U, hUo, fun u hu h0 x => ?_⟩
    simp only [cone]
    congr 1
    funext k
    congr 1
    funext l
    rw [hU u hu h0 k l x]
  · obtain ⟨C, hCc, hCs⟩ := GlobalTheory.T.config_a_eigen_stabilizer_integral F E σ B b a' G G₁ H H' hC e he K hK X om om' om₁ om₁' hT hT₁ Ψ hΨ
    refine ⟨C, hCc, fun x hx => ?_⟩
    by_contra hn
    apply hx
    simp only [cone]
    have h0 : ∀ (k : K) (l : (AE F E)ˣ), e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, 1) Ψ)) x = 0 :=
      fun k l => hCs k l x hn
    simp [h0]

end GlobalTheory.ConeSchwartz
