import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatLocalApproximationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAtUniformizerNotRootOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalThetaGoodPlaceLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaLatticeSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarFunctionalGoodPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralLinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleUnipotentPeriodIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleUnipotentPeriodIntegralTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFactorizationAwayBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFactorizationBasePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantLocalFunctionalUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSchwartzStableUnderW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugAtStableWUnitaryStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.FacSmall

def tensL {F : Type} [Field F] [NumberField F] {κ : Type} (v : Pl F) (r : (κ → AF F) → ℂ) :
    ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun φ := tens (evFin F v) φ r
  map_add' φ ψ := by funext x; simp only [tens, Pi.add_apply]; ring
  map_smul' c φ := by funext x; simp only [tens, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem tensL_apply {F : Type} [Field F] [NumberField F] {κ : Type} (v : Pl F) (r : (κ → AF F) → ℂ)
    (φ : (κ → Fv F v) → ℂ) : tensL v r φ = tens (evFin F v) φ r := rfl

theorem augAt_le_SB {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (om : Rep σ X W) (v : Pl F) : augAt om v ≤ SB _ := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, -, φ, hφ, φ₁, hφ₁, -, rfl⟩
  exact sub_mem hφ₁ hφ

theorem ctf_om {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} (H' : Plane E d d₁) (μ : Measure (unip σ W H'))
    (𝓕 : Set (unip σ W H')) (M : Model σ X W) (om : Rep σ X W) (Ψ : (Fin n × Fin d → AF F) → ℂ) (k h : UA σ W.J) :
    GlobalTheory.CtTyp.ctf H' μ 𝓕 (M.I om (om (1, k) Ψ)) h = GlobalTheory.CtTyp.ctf H' μ 𝓕 (M.I om Ψ) (h * k) := by
  unfold GlobalTheory.CtTyp.ctf Model.I theta
  congr 1; funext u; congr 1; funext x
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, mul_assoc]

theorem fac : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ (μ : Measure (unip σ G.W H')) (𝓕 : Set (unip σ G.W H')), μ.IsHaarMeasure → IsFundamentalDomain ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) 𝓕 μ → μ 𝓕 = 1 → ∀ v, X.Good v → ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → ∀ g : UA σ G.W.J, ∃ (N : ℕ) (Λ : Fin N → (((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ)) (ψ : Fin N → ((Fin a' × Fin (a + a') → Fv F v) → ℂ)), (∀ j, ψ j ∈ SB (Fin a' × Fin (a + a') → Fv F v)) ∧ (∀ j, ∀ z ∈ augAt om' v, Λ j z = 0) ∧ (∀ j, ∀ n ∈ unip σ G.W H', n ∈ UAt σ G.W (evFin F v) → ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (1, n)) φ φ₁ → Λ j φ₁ = Λ j φ) ∧ ∀ (x : (w.adicCompletion E)ˣ) (m : UA σ G.W.J), IsLevi (W₁ := W₁) H' (locIdele F w x) 1 m → ∃ ψ₁ : Fin N → ((Fin a' × Fin (a + a') → Fv F v) → ℂ), (∀ j, ψ₁ j ∈ SB (Fin a' × Fin (a + a') → Fv F v) ∧ Acts (evFin F v) (om' (1, m)) (ψ j) (ψ₁ j)) ∧ GlobalTheory.CtTyp.ctf H' μ 𝓕 (G.M'.I om' Φ') (m * g) = ∑ j, Λ j (ψ₁ j) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH Φ' hΦ' μ 𝓕 hμ h𝓕 h1 v hv w hw g
  have hP := hKP.base
  have hAE := GlobalTheory.T.theta_action_exists hP F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' G.q (a' - G.q)
    (a + a' - (G.p + G.q)) (G.p + G.q) (GlobalTheory.ThK.Inhab.pairV' hT)
  have hone : ∀ u : Pl F, (1 : UA σ G.V'.J) ∈ UAt σ G.V' (evFin F u) := fun u c _ => by simp [mat]
  have hΦ'' : om' (1, g) Φ' ∈ G.M'.So B.ψ B.τ₁ :=
    GlobalTheory.T.weil_representation_preserves_space hP F E σ B a a' G X om om' hT (1, g) Φ' (Submodule.mem_inf.1 hΦ').2
  have I0 : G.M'.I om' 0 = 0 := by
    funext h; simp [Model.I, theta, thetaSum]
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ((Fin a' × Fin (a + a') → AF F) → ℂ) →ₗ[ℂ] ℂ, ∀ Φ ∈ G.M'.So B.ψ B.τ₁,
      ℓ Φ = GlobalTheory.CtTyp.ctf H' μ 𝓕 (G.M'.I om' Φ) 1 := by
    let ℓ₀ : G.M'.So B.ψ B.τ₁ →ₗ[ℂ] ℂ :=
      { toFun := fun Φ => GlobalTheory.CtTyp.ctf H' μ 𝓕 (G.M'.I om' Φ.1) 1
        map_add' := fun Φ₁ Φ₂ => by
          have e := GlobalTheory.T.theta_integral_linear hKP F E σ B a a' G X om om' hT Φ₁.1 Φ₁.2 Φ₂.1 Φ₂.2 1
          rw [one_smul, one_smul] at e
          simp only [Submodule.coe_add, e, GlobalTheory.CtTyp.ctf, Pi.add_apply]
          exact integral_add (GlobalTheory.T.triple_unipotent_period_integral hKP F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH Φ₁.1 Φ₁.2 μ 𝓕 hμ h𝓕 h1 1)
            (GlobalTheory.T.triple_unipotent_period_integral hKP F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH Φ₂.1 Φ₂.2 μ 𝓕 hμ h𝓕 h1 1)
        map_smul' := fun c Φ => by
          have e := GlobalTheory.T.theta_integral_linear hKP F E σ B a a' G X om om' hT Φ.1 Φ.2 0 (zero_mem _) c
          rw [add_zero, I0, add_zero] at e
          simp only [Submodule.coe_smul, e, GlobalTheory.CtTyp.ctf, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
          exact integral_const_mul c _ }
    obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ℓ₀
    exact ⟨ℓ, fun Φ hΦ => LinearMap.congr_fun hℓ ⟨Φ, hΦ⟩⟩
  have hpair := GlobalTheory.ThK.Inhab.pairV' hT
  by_cases hv1 : v = B.v₁
  · subst hv1
    have hgood := GlobalTheory.T.character_at_uniformizer_not_root_of_unity F E σ B a a' G X om om' hT B.v₁ hv
    obtain ⟨N, ψ, r, hψ, hrest, hso, hsum⟩ := GlobalTheory.T.schwartz_factorization_base_place F E σ B a a' G X om om' hT _ hΦ''
    have hSoSB : ∀ φ ∈ G.M'.SoLoc B.ψ B.τ₁, φ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁) := fun φ hφ => hφ.1
    have hl : ∀ j, ∃ Λ : ((Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ) →ₗ[ℂ] ℂ, augAt om' B.v₁ ≤ LinearMap.ker Λ ∧
        ∀ φ ∈ G.M'.SoLoc B.ψ B.τ₁, Λ φ = (ℓ ∘ₗ tensL B.v₁ (r j)) φ := by
      intro j
      refine GlobalTheory.T.invariant_local_functional_unique hP F E σ B a a' G X om om' hT B.v₁ hv B.τ₁ (ℓ ∘ₗ tensL B.v₁ (r j)) ?_
      intro g' hg' φ hφ φ₁ hφ₁ hA
      rw [LinearMap.comp_apply, LinearMap.comp_apply, tensL_apply, tensL_apply, hℓ _ (hso j φ₁ hφ₁),
        hℓ _ (hso j φ hφ), ← hA (r j) (hrest j φ (hSoSB φ hφ)),
        GlobalTheory.ThetaIntegralInv.integral_translate hP hpair g' _ (hrest j φ (hSoSB φ hφ)).2]
    choose Λ hΛa hΛs using hl
    refine ⟨N, Λ, ψ, fun j => hSoSB _ (hψ j), fun j z hz => LinearMap.mem_ker.1 (hΛa j hz), ?_, ?_⟩
    · intro j n hn hnv φ hφ φ₁ hφ₁ hA
      obtain ⟨φ₀, hφ₀, hd⟩ := GlobalTheory.T.schwartz_bruhat_local_approximation hP F E σ B a a' G X om om' hT B.v₁ hv hgood B.τ₁ φ hφ
      obtain ⟨S, hS, hSlin, -, -⟩ := GlobalTheory.WeilTransferW.local_weil_operator_second_space hP F E σ B a a' G X om om' hT B.v₁ n hnv
      have haSB : φ - φ₀ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁) := augAt_le_SB om' B.v₁ hd
      have h0SB := hSoSB _ hφ₀
      have e1 : φ₁ = S φ₀ + S (φ - φ₀) := by
        rw [((hAE B.v₁).1 1 (hone B.v₁) n hnv φ hφ).unique ⟨hφ₁, hA⟩ (hS φ hφ)]
        have e := hSlin φ₀ h0SB (φ - φ₀) haSB 1
        rw [one_smul, one_smul, add_sub_cancel] at e
        exact e
      have hS0 : S φ₀ ∈ G.M'.SoLoc B.ψ B.τ₁ :=
        GlobalTheory.T.local_schwartz_stable_under_W hP F E σ B a a' G X om om' hT B.v₁ hv B.τ₁ n hnv φ₀ hφ₀ (S φ₀) (hS φ₀ h0SB).1 (hS φ₀ h0SB).2
      have hSa : S (φ - φ₀) ∈ augAt om' B.v₁ :=
        GlobalTheory.T.augAt_stable_W_unitary hP F E σ B a a' G X om om' hT B.v₁ n hnv _ hd _ (hS _ haSB).1 (hS _ haSB).2
      have e2 : Λ j φ = Λ j φ₀ := by
        have e := LinearMap.mem_ker.1 (hΛa j hd)
        rwa [map_sub, sub_eq_zero] at e
      rw [e1, map_add, LinearMap.mem_ker.1 (hΛa j hSa), add_zero, hΛs j _ hS0, e2, hΛs j _ hφ₀,
        LinearMap.comp_apply, LinearMap.comp_apply, tensL_apply, tensL_apply, hℓ _ (hso j _ hS0), hℓ _ (hso j _ hφ₀),
        ← (hS φ₀ h0SB).2 (r j) (hrest j _ h0SB), ctf_om, one_mul]
      have e := GlobalTheory.T.triple_unipotent_period_integral_two hKP F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH _ (hso j _ hφ₀) μ 𝓕 hμ h𝓕 h1 n hn 1
      rwa [mul_one] at e
    · intro x m hm
      have hmv := GlobalTheory.T.local_theta_good_place_lattice F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH B.v₁ w hw x m hm
      choose ψ₁ hψ₁ using fun j => ((hAE B.v₁).1 1 (hone B.v₁) m hmv (ψ j) (hSoSB _ (hψ j))).exists
      have hψ₁S : ∀ j, ψ₁ j ∈ G.M'.SoLoc B.ψ B.τ₁ := fun j =>
        GlobalTheory.T.local_schwartz_stable_under_W hP F E σ B a a' G X om om' hT B.v₁ hv B.τ₁ m hmv (ψ j) (hψ j) (ψ₁ j) (hψ₁ j).1 (hψ₁ j).2
      refine ⟨ψ₁, hψ₁, ?_⟩
      have hm1 : om' (1, m) (om' (1, g) Φ') = ∑ j, tens (evFin F B.v₁) (ψ₁ j) (r j) := by
        rw [hsum, map_sum]
        exact Finset.sum_congr rfl fun j _ => (hψ₁ j).2 (r j) (hrest j (ψ j) (hSoSB _ (hψ j)))
      have hmem : ∑ j, tens (evFin F B.v₁) (ψ₁ j) (r j) ∈ G.M'.So B.ψ B.τ₁ :=
        Submodule.sum_mem _ fun j _ => hso j _ (hψ₁S j)
      calc GlobalTheory.CtTyp.ctf H' μ 𝓕 (G.M'.I om' Φ') (m * g)
          = GlobalTheory.CtTyp.ctf H' μ 𝓕 (G.M'.I om' (om' (1, m) (om' (1, g) Φ'))) 1 := by
            rw [ctf_om, ctf_om, one_mul]
        _ = ℓ (∑ j, tens (evFin F B.v₁) (ψ₁ j) (r j)) := by rw [hm1, hℓ _ hmem]
        _ = ∑ j, Λ j (ψ₁ j) := by
            rw [map_sum]
            exact Finset.sum_congr rfl fun j _ => (hΛs j _ (hψ₁S j)).symm
  · obtain ⟨N, ψ, r, hψ, hr, hsum⟩ := GlobalTheory.T.schwartz_factorization_away_base F E σ B a a' G X om om' hT _ hΦ'' v hv1
    refine ⟨N, fun j => ℓ ∘ₗ tensL v (r j), ψ, hψ, ?_, ?_, ?_⟩
    · intro j z hz
      have hle : augAt om' v ≤ LinearMap.ker (ℓ ∘ₗ tensL v (r j)) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨g', hg', φ, hφ, φ₁, hφ₁, hA, rfl⟩
        rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, sub_eq_zero, LinearMap.comp_apply, LinearMap.comp_apply,
          tensL_apply, tensL_apply, hℓ _ (hr j φ₁ hφ₁).2, hℓ _ (hr j φ hφ).2, ← hA (r j) (hr j φ hφ).1,
          GlobalTheory.ThetaIntegralInv.integral_translate hP hpair g' _ (hr j φ hφ).1.2]
      exact LinearMap.mem_ker.1 (hle hz)
    · intro j n hn hnv φ hφ φ₁ hφ₁ hA
      rw [LinearMap.comp_apply, LinearMap.comp_apply, tensL_apply, tensL_apply, hℓ _ (hr j φ₁ hφ₁).2,
        hℓ _ (hr j φ hφ).2, ← hA (r j) (hr j φ hφ).1, ctf_om, one_mul]
      have e := GlobalTheory.T.triple_unipotent_period_integral_two hKP F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH _ (hr j φ hφ).2 μ 𝓕 hμ h𝓕 h1 n hn 1
      rwa [mul_one] at e
    · intro x m hm
      have hmv := GlobalTheory.T.local_theta_good_place_lattice F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH v w hw x m hm
      choose ψ₁ hψ₁ using fun j => ((hAE v).1 1 (hone v) m hmv (ψ j) (hψ j)).exists
      refine ⟨ψ₁, hψ₁, ?_⟩
      have hm1 : om' (1, m) (om' (1, g) Φ') = ∑ j, tens (evFin F v) (ψ₁ j) (r j) := by
        rw [hsum, map_sum]
        exact Finset.sum_congr rfl fun j _ => (hψ₁ j).2 (r j) (hr j (ψ j) (hψ j)).1
      have hmem : ∑ j, tens (evFin F v) (ψ₁ j) (r j) ∈ G.M'.So B.ψ B.τ₁ :=
        Submodule.sum_mem _ fun j _ => (hr j (ψ₁ j) (hψ₁ j).1).2
      calc GlobalTheory.CtTyp.ctf H' μ 𝓕 (G.M'.I om' Φ') (m * g)
          = GlobalTheory.CtTyp.ctf H' μ 𝓕 (G.M'.I om' (om' (1, m) (om' (1, g) Φ'))) 1 := by
            rw [ctf_om, ctf_om, one_mul]
        _ = ℓ (∑ j, tens (evFin F v) (ψ₁ j) (r j)) := by rw [hm1, hℓ _ hmem]
        _ = ∑ j, (ℓ ∘ₗ tensL v (r j)) (ψ₁ j) := by rw [map_sum]; rfl

end GlobalTheory.FacSmall

end
